-- Prove2me | Definitions.Def_DecDynMatch_Supplement_playerRound
-- name    : DecDynMatch_Supplement_playerRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:29:11.501915+00:00
-- url     : https://prove2.me/theorems/ce793ee5-7e44-4e2b-a876-2f3606b32d6b
-- title:
--   One round of an SC-PC player (Algorithm 2): round start, proposal, feedback
-- statement:
--   A round of an active SC-PC player (Algorithm 2, lines 5–27):
--
--   1. if $\nu\ne$ none, apply StateUpdate$(\nu)$ and clear $\nu$; if $m=$ Replay and $a\ge q$, apply StateUpdate$(\textsc{Seek}_{\rm fresh})$ (replay expiry is processed before the proposal);
--   2. propose: WorkAction in Work; the saved arm $y$ in Replay; the scanned arm $j$ in Root during Scan when busNext is false; BUS otherwise;
--   3. on acceptance observe the realized utility $r$ and set $N_v\leftarrow N_v+1$, $U_v\leftarrow U_v+r$, $\mathrm{lastA}[v]\leftarrow a$;
--   4. CollectionFeedback in Seek or Root, WorkFeedback in Work, and in Replay on a rejection $q\leftarrow\max\{a+1,\ell+H_L\}$ (51);
--   5. $a\leftarrow a+1$.
--
--   **Formalization Note** The round is split into `pStart` (step 1), `pChoose` (step 2) and `pFinish` (steps 3–5). In Replay $\ell\ne\bot$; `ℓ.getD 0` is used only for totality.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithm 2 and eq. (51), pp.30, 35

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_collectionFeedback
import Definitions.Def_DecDynMatch_Supplement_workAction
import Definitions.Def_DecDynMatch_Supplement_workFeedback

namespace DecDynMatch.Supplement

open DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- Round start of an SC-PC player (Algorithm 2, lines 5–8, p.30): "if ν ≠ none then
StateUpdate(ν); ν ← none. if m = Replay and a ≥ q then StateUpdate(Seek_fresh)." Replay expiry
is processed before the proposal. -/
def pStart (st : PState K) : PState K :=
  let st1 : PState K :=
    match st.ν with
    | none => st
    | some u => { stateUpdate u st with ν := none }
  if st1.m = .replay ∧ st1.q ≤ st1.a then stateUpdate .seekFresh st1 else st1

/-- Proposal choice of an SC-PC player (Algorithm 2, lines 9–16, p.30): WorkAction in Work; `y`
in Replay; `j` in Root during Scan when `¬busNext`; BUS otherwise. Returns the state (WorkAction
may update it), the arm and the proposal type (`other` outside Work).

**Formalization Note.** The scanned arm `j ∈ {1, …, K − 1}` is converted to `Fin K`; the fallback
for `j ≥ K` (never reached) is BUS. -/
noncomputable def pChoose (I : Instance K ι) (st : PState K) : PState K × Fin K × PType :=
  match st.m with
  | .work => workAction I st
  | .replay => (st, st.y, .other)
  | .root =>
      if st.s = .scan ∧ st.busNext = false then
        (st, (if hj : st.j < K then ⟨st.j, hj⟩ else bus I), .other)
      else (st, bus I, .other)
  | .seek => (st, bus I, .other)

/-- Feedback of an SC-PC player (Algorithm 2, lines 18–27, p.30) after proposing to `v` with type
`ty` and outcome `o` (`true` = A), with realized utility `r` (read only on A): on A,
`N_v ← N_v + 1, U_v ← U_v + r, lastA[v] ← a`; then CollectionFeedback in Seek/Root, WorkFeedback in
Work, and in Replay on R `q ← max{a + 1, ℓ + H_L}` (51); finally `a ← a + 1`.

**Formalization Note.** In Replay `ℓ ≠ ⊥` (Replay is entered only after a Work output sets
`ℓ`); `ℓ.getD 0` is used for totality. -/
def pFinish (I : Instance K ι) (st : PState K) (v : Fin K) (ty : PType) (o : Bool) (r : ℝ) :
    PState K :=
  let st1 : PState K :=
    if o = true then
      { st with N := Function.update st.N v (st.N v + 1),
                U := Function.update st.U v (st.U v + r),
                lastA := Function.update st.lastA v (some st.a) }
    else st
  let st2 : PState K :=
    match st1.m with
    | .seek => collectionFeedback I v o st1
    | .root => collectionFeedback I v o st1
    | .work => workFeedback v ty o st1
    | .replay =>
        if o = false then { st1 with q := max (st1.a + 1) (st1.l.getD 0 + HL K) } else st1
  { st2 with a := st2.a + 1 }

end DecDynMatch.Supplement


