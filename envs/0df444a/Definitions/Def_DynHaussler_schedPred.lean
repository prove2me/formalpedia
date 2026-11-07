-- Prove2me | Definitions.Def_DynHaussler_schedPred
-- name    : DynHaussler_schedPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:44.29444+00:00
-- url     : https://prove2.me/theorems/873078ad-5ec6-4f2e-8559-5008bc2b7e76
-- title:
--   Simulation of a correction schedule: final prediction $y^J_t$
-- statement:
--   Fix an initial version space $V_0$ and a schedule $J$. The **simulation** of $J$ runs over the rounds as follows.
--
--   1. It starts at $V_0$. On round $t$, after observing $x_t$, its provisional prediction is the center $a(V,x_t)$ of the version space $V$ left by the preceding round.
--   2. If round $t$ is the $s$-th selected round, the simulation executes all entries of $J$ with $s_j=s$, in their listed order. Each entry applies the indicated sign update $V\mapsto V^{\pm}_{x_t}$, and the center is recomputed from the new version space before the next entry.
--   3. The final prediction $y^J_t$ is the center after these updates; on an unselected round there is no update and $y^J_t$ is the provisional prediction.
--   4. An update to an empty fiber makes the simulation invalid: from that update on it stays in an absorbing invalid state and emits $0$, including on the current round. Entries whose ordinal is never reached are not executed.
--
--   The simulation uses only the instance history, the selection history and its fixed schedule; Lemma 13 shows that the simulations of the formal family cover every target pointwise.
--
--   **Formalization Note** The function returns $y^J_t$ from the list of the preceding rounds' pairs $(x_s,\text{selected}_s)$, the current instance $x_t$ and the current selection bit; the state is a version space or the invalid state, together with the number of selected rounds so far. Since the output reads only the past, the current instance and the current selection bit, the simulation is causal by construction.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Section 4.2, "Simulation and prediction timing" and the following paragraph, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_DynHaussler_signUpdate

set_option autoImplicit false

namespace DynHaussler

/-- The **simulation of a correction schedule** `J` from the initial version space `V₀`
(Section 4.2, "Simulation and prediction timing"): the final prediction `y^J_t` on the current
round, given the history of the preceding rounds (instances and selection bits), the current
instance `x_t`, and whether the current round is selected.

The simulation starts at `V₀`. On round `t` its provisional prediction is the center `a(V, x_t)`
of the version space `V` left by the preceding round. If the round is the `s`-th selected round,
it executes all entries of `J` with `s_j = s`, in their listed order; each entry applies the
indicated sign update `V ↦ V^±_{x_t}` (Eq. (33)) and the center is recomputed from the new version
space before the next entry. The final prediction is the center after these updates. An
unselected round makes no update, and its final prediction is the provisional one. An update to an
empty fiber makes the simulation invalid: from that update on it stays in an absorbing invalid
state and emits `0`, including on the current round. Entries with ordinals beyond the selection
history are never executed.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Section 4.2, pp.19–20 (PDF pp.21–22).

**Formalization Note** The state is `Option (Set (X → ℝ))` (`none` is the invalid state) together
with the number of selected rounds so far. `hist` is the list of the preceding rounds' pairs
`(x_s, selected_s)` in order. The output depends only on `hist`, the current instance and the
current selection bit, so the simulation is causal by construction. -/
noncomputable def schedPred {X : Type*} (η : ℝ) (V₀ : Set (X → ℝ)) (J : List (ℕ × Bool))
    (hist : List (X × Bool)) (x : X) (sel : Bool) : ℝ :=
  open Classical in
  -- one sign update; an empty fiber makes the state invalid (absorbing)
  let step : X → Option (Set (X → ℝ)) → Bool → Option (Set (X → ℝ)) := fun y S σ =>
    match S with
    | none => none
    | some V => if (signUpdate η V y σ).Nonempty then some (signUpdate η V y σ) else none
  -- all entries with ordinal `s`, in listed order, at instance `y`
  let updates : ℕ → X → Option (Set (X → ℝ)) → Option (Set (X → ℝ)) := fun s y S =>
    (J.filter (fun e => e.1 = s)).foldl (fun S' e => step y S' e.2) S
  -- one completed round: (state, number of selected rounds so far)
  let round : Option (Set (X → ℝ)) × ℕ → X × Bool → Option (Set (X → ℝ)) × ℕ := fun st yb =>
    if yb.2 then (updates (st.2 + 1) yb.1 st.1, st.2 + 1) else st
  let st := hist.foldl round (some V₀, 0)
  let final := if sel then updates (st.2 + 1) x st.1 else st.1
  match final with
  | none => 0
  | some V => center η V x

end DynHaussler


