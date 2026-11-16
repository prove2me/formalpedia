-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_Visible
-- name    : BatchMaxService_Metric_Supplement_Visible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:01:35.576208+00:00
-- url     : https://prove2.me/theorems/5c639302-90ce-4e6b-b34d-4641820baeea
-- title:
--   Operational visible Algorithms 1, 2 and 3 with uniform work counters
-- statement:
--   Algorithm 1 retains the previous hull, initially the singleton start, and every current pending identity. Its oldest arrival clock is retained across complete epochs. With current hull $[L,R]$ and preceding hull $H_{\rm prev}$, its deadline is
--
--   $$\alpha+(R-L)+\operatorname{dist}(H_{\rm prev},[L,R]).$$
--
--   At the trigger it visits the nearer endpoint first, choosing left on a tie, then the other endpoint, and serves the entire pending set. Anchor arrivals are retained in these literal hull phases, including zero-threshold phases.
--
--   Algorithms 2 and 3 freely serve and omit anchor arrivals. They retain the oldest remaining arrival, use respectively the current minimal-subtree or exact-Steiner-tree weight as threshold, and execute an open depth first traversal ending at a farthest actual phase request in that tree. Epochs at the deadline are delivered first. No retained historical MST maximum or Algorithm 4 substitution is used. Work counters charge scans, real arithmetic and comparisons, list/set construction, subtree construction and traversal; waiting is excluded. Polynomial work means one coefficient and degree uniform over the number of sites, requests and all real data. It is a conclusion in Theorem 5.4.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Algorithms 1–3, printed pp. 14, 16–17 / PDF pp. 15, 17–18; Section 4.1, printed p. 9 / PDF p. 10

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Geometry
import Definitions.Def_BatchMaxService_Metric_Supplement_Interaction

namespace BatchMaxService.Metric.Supplement

variable {n : ℕ}

/-- Update only what a feedback message actually reveals. -/
def learn (known : ℕ → Fin n) (revealed : List (ℕ × Fin n)) : ℕ → Fin n :=
  revealed.foldl (fun f qv => Function.update f qv.1 qv.2) known

structure VisibleState (n : ℕ) where
  pending : Finset ℕ
  oldest : ℝ
  known : ℕ → Fin n
  previousHull : ℝ × ℝ
  current : MetricTree n
  threshold : ℝ
  free : Finset ℕ
  freeTime : ℝ

/-- Initial hull is the singleton starting point; no certificate or cost bound is stored. -/
def visibleInitial (x : Fin n → ℝ) (s : Fin n) : VisibleState n :=
  ⟨∅, 0, fun _ => s, (x s, x s), ⟨∅, ∅⟩, 0, ∅, 0⟩

/-- Line Algorithm 1 keeps every request, including anchor requests, in its literal
    hull phase. This avoids changing the preceding hull when free arrivals occur. -/
noncomputable def receiveLine (x : Fin n → ℝ) (s : Fin n)
    (st : VisibleState n) (fb : Feedback n) : Charged (VisibleState n) := by
  classical
  let P := st.pending ∪ fb.announced
  let known := learn st.known fb.revealed
  let lr := extremes x s (P.image known)
  let gap := max (st.previousHull.1 - x lr.2) (max (x lr.1 - st.previousHull.2) 0)
  exact ({ st with pending := P, known := known,     oldest := if st.pending = ∅ then fb.time else st.oldest,     threshold := (x lr.2 - x lr.1) + gap },
    100 * (P.card + n + 1)^4)

noncomputable def linePolicy (x : Fin n → ℝ) : Policy n (VisibleState n) where
  initial s := (visibleInitial x s, 1)
  receive st fb :=
    receiveLine x (st.known 0) st fb
  choose _ s st := by
    classical
    exact (if st.pending = ∅ then none else
      some ⟨st.oldest + st.threshold, cleanupWalk x s (st.pending.image st.known), st.pending⟩,
      100 * (st.pending.card + n + 1)^3)
  respond st _ fb := by
    classical
    let lr := extremes x (st.known 0) (st.pending.image st.known)
    exact ({ st with pending := ∅, oldest := 0, previousHull := (x lr.1, x lr.2),       threshold := 0, known := learn st.known fb.revealed }, 100 * (st.pending.card + n + 1)^3)

/-- A tree provider depends on the current anchor and actual terminal locations. -/
abbrev AnchoredTree (n : ℕ) := Fin n → Finset (Fin n) → Charged (MetricTree n)

/-- State includes the current anchor independently of all request labels. -/
structure TreeState (n : ℕ) where
  anchor : Fin n
  phase : VisibleState n

noncomputable def treePolicy [MetricSpace (Fin n)] (provider : AnchoredTree n) :
    Policy n (TreeState n) where
  initial s := (⟨s, visibleInitial (fun _ => 0) s⟩, 1)
  receive st fb := by
    classical
    let known := learn st.phase.known fb.revealed
    let anchorHits := fb.announced.filter fun q => known q = st.anchor
    let away := fb.announced \ anchorHits
    let P := st.phase.pending ∪ away
    let α := if st.phase.pending = ∅ then fb.time else st.phase.oldest
    let free := st.phase.free ∪ (anchorHits \ fb.served)
    if P = ∅ then
      exact (⟨st.anchor, { st.phase with known := known, free := free, freeTime := fb.time }⟩,
        100 * (fb.announced.card + n + 1)^3)
    else
      let tree := provider st.anchor (insert st.anchor (P.image known))
      exact (⟨st.anchor, { st.phase with pending := P, oldest := α, known := known,         current := tree.1, threshold := treeWeight tree.1, free := free, freeTime := fb.time }⟩,
        tree.2 + 100 * (P.card + n + 1)^4)
  choose _ _ st := by
    classical
    let ph := st.phase
    if ph.free ≠ ∅ then
      exact (some ⟨ph.freeTime, [st.anchor], ph.free⟩, 10 * (ph.free.card + 1))
    else
      match farthestRequest ph.current st.anchor ph.known ph.pending with
      | none => exact (none, 100 * (n + 1)^3)
      | some q =>
          let tour := openTraversal ph.current st.anchor (ph.known q)
          exact (some ⟨ph.oldest + ph.threshold, tour.1, ph.pending⟩,
            tour.2 + 100 * (ph.pending.card + 1) * (n + 1)^6)
  respond st e _ := by
    classical
    if st.phase.free ≠ ∅ then
      exact (⟨st.anchor, { st.phase with free := ∅ }⟩, 10 * (st.phase.free.card + 1))
    else
      exact (⟨e.walk.getLast?.getD st.anchor,
        { st.phase with pending := ∅, oldest := 0, threshold := 0 }⟩,
        100 * (st.phase.pending.card + n + 1)^3)

noncomputable def algorithm1 (x : Fin n → ℝ) (I : RequestInput n) :=
  execution .visible .elective (linePolicy x) I

noncomputable def algorithm2 [MetricSpace (Fin n)] (T : MetricTree n) (r : Rule)
    (I : RequestInput n) :=
  execution .visible r (treePolicy (minimalSubtree T)) I

noncomputable def algorithm3 [MetricSpace (Fin n)] (oracle : Finset (Fin n) → MetricTree n)
    (I : RequestInput n) :=
  execution .visible .elective (treePolicy (fun _ A => (oracle A, 0))) I

/-- One uniform arithmetic/comparison work polynomial. Waiting is not work;
    labels are unit-cost atoms. Coefficient/degree precede all tree sizes and real data. -/
def PolynomialAlgorithm2Work : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n (m : MetricSpace (Fin n)) (T : MetricTree n) (r : Rule)
    (I : RequestInput n),
    letI := m
    IsWeightedTree T → (algorithm2 T r I).work ≤ C * (I.ids.card + n + 1)^d

end BatchMaxService.Metric.Supplement


