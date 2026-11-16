-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_Blind
-- name    : BatchMaxService_Metric_Supplement_Blind
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:02:20.330089+00:00
-- url     : https://prove2.me/theorems/3f5f4130-5ed6-4ab3-9777-e2349490497a
-- title:
--   Blind Algorithms 5 and 6 with virtual identities and actual phase bills
-- statement:
--   The controller retains unresolved announced identities, their oldest arrival, the radius index, discovered identities and revealed locations. Anchor checks remove new hits freely. Positive phases use the ages
--
--   $$r_j=2^j\delta,\qquad c_j=\alpha+r_j.$$
--
--   At an unsuccessful sweep the radius doubles without resetting the oldest clock. The known sites in the closed radius interval are swept in the order anchor, left extreme, right extreme, anchor. Algorithm 5 serves nothing during search and, once every phase identity is discovered, performs the nearer-extreme-first elective cleanup in the same atomic action. Algorithm 6 automatically serves every newly encountered real pending identity in each individual sweep, retains its virtual record, and finally moves directly to a farthest recorded request.
--
--   Completed phase records contain the original virtual request set, starting anchor, endpoint and actual separately billed events. Their radius is the finite maximum request distance. No phase bound is assumed. The one-site case uses only free anchor service, and no search phase is started. This is the data used by Lemma 6.1 and both ratio-84 results.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Section 6, Algorithms 5–6, printed pp. 19–24 / PDF pp. 20–25

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Visible

namespace BatchMaxService.Metric.Supplement

variable {n : ℕ}

/-- A completed positive phase records actual separately billed walks.
    It does not carry any asserted cost estimate. -/
structure BlindPhase (n : ℕ) where
  requests : Finset ℕ
  anchor : Fin n
  endpoint : Fin n
  events : Schedule n

structure BlindState (n : ℕ) where
  anchor : Fin n
  virtual : Finset ℕ
  oldest : ℝ
  radiusIndex : ℕ
  found : Finset ℕ
  known : ℕ → Fin n
  cleanup : Bool
  finalTime : ℝ
  free : Finset ℕ
  freeTime : ℝ
  phaseEvents : Schedule n
  phases : List (BlindPhase n)

def blindInitial (s : Fin n) : BlindState n :=
  ⟨s, ∅, 0, 0, ∅, fun _ => s, false, 0, ∅, 0, [], []⟩

/-- Announcements supply identities and times; only explicit anchor feedback removes
    an identity. In particular the default of `known` is never used for this test. -/
noncomputable def blindReceive (st : BlindState n) (fb : Feedback n) : Charged (BlindState n) := by
  classical
  let atAnchor := (fb.revealed.filter fun qv => qv.2 = st.anchor).map Prod.fst
  let anchorHits := fb.announced ∩ atAnchor.toFinset
  let away := fb.announced \ anchorHits
  let P := st.virtual ∪ away
  exact ({ st with virtual := P,     oldest := if st.virtual = ∅ then fb.time else st.oldest,     known := learn st.known fb.revealed,     free := st.free ∪ (anchorHits \ fb.served), freeTime := fb.time },
    100 * (P.card + n + 1)^4)

/-- Algorithms 5/6 differ only in sweep service and the final cleanup/direct move.
    Choices use announced identities, discovery flags and revealed locations only. -/
noncomputable def blindPolicy (x : Fin n → ℝ) (r : Rule) : Policy n (BlindState n) where
  initial s := (blindInitial s, 1)
  receive := blindReceive
  choose _ _ st := by
    classical
    if st.free ≠ ∅ then
      exact (some ⟨st.freeTime, [st.anchor], st.free⟩, 10 * (st.free.card + 1))
    else if st.virtual = ∅ then
      exact (none, 10)
    else if st.cleanup then
      let A := st.virtual.image st.known
      let walk := if r = .elective then cleanupWalk x st.anchor A
        else lineWalk x [st.anchor, farLine x st.anchor A]
      let batch := if r = .elective then st.virtual else ∅
      exact (some ⟨st.finalTime, walk, batch⟩, 100 * (st.virtual.card + n + 1)^4)
    else
      let radius := (2 : ℝ)^st.radiusIndex * spacing x
      exact (some ⟨st.oldest + radius, sweepWalk x st.anchor radius, ∅⟩,
        100 * (n + st.radiusIndex + 1)^4)
  respond st e fb := by
    classical
    if st.free ≠ ∅ then
      exact ({ st with free := ∅ }, 10 * (st.free.card + 1))
    else if st.cleanup then
      let endpoint := e.walk.getLast?.getD st.anchor
      let record : BlindPhase n := ⟨st.virtual, st.anchor, endpoint, st.phaseEvents ++ [e]⟩
      exact ({ blindInitial endpoint with phases := st.phases ++ [record] },
        100 * (st.virtual.card + n + st.phaseEvents.length + 1)^4)
    else
      let found := st.found ∪ (fb.revealed.map Prod.fst).toFinset
      let success := st.virtual ⊆ found
      exact ({ st with found := found, known := learn st.known fb.revealed,         cleanup := decide success, finalTime := e.time,         radiusIndex := if success then st.radiusIndex else st.radiusIndex + 1,         phaseEvents := st.phaseEvents ++ [e] },
        100 * (st.virtual.card + n + st.phaseEvents.length + 1)^4)

noncomputable def algorithm5 (x : Fin n → ℝ) (I : RequestInput n) :=
  execution .blind .elective (blindPolicy x .elective) I

noncomputable def algorithm6 (x : Fin n → ℝ) (I : RequestInput n) :=
  execution .blind .automatic (blindPolicy x .automatic) I

/-- Finite maximum, zero for an empty record. Completed positive records are
    asserted nonempty in Lemma 6.1; this does not assume its bound. -/
noncomputable def phaseRadius (x : Fin n → ℝ) (I : RequestInput n) (p : BlindPhase n) : ℝ :=
  (p.requests.toList.map fun q => |x (I.location q) - x p.anchor|).foldl max 0

end BatchMaxService.Metric.Supplement


