-- Prove2me | Definitions.Def_RepairSched_Model_IsIVPSol
-- name    : RepairSched_Model_IsIVPSol
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:05.14407+00:00
-- url     : https://prove2.me/theorems/e24badc8-0fba-423e-8b5f-639f76031331
-- title:
--   $g$ solves the initial value problem (A.2) for $\gamma$
-- statement:
--   A function $g$ solves the initial value problem (A.2) for $\gamma$ if
--   $$g'(w)=F(w,g(w),\gamma)\quad(w\ge0),\qquad g(0)=0.$$
--   Replacing the minimization in the Bellman equations by its value turns them into this first-order problem for $f'$.
--
--   **Formalization Note** The derivative is taken within $[0,\infty)$: two-sided for $w>0$, one-sided at $0$. The paper's $g_\gamma$ is never a chosen function; statements quantify over all solutions.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), (A.2), OA p.3

import Mathlib
import Definitions.Def_RepairSched_Model
import Definitions.Def_RepairSched_Model_ivpField

open Set

namespace RepairSched

/-- **`g` solves the initial value problem (A.2) for `γ`** on `ℝ₊`:
`g′(w) = F(w, g(w), γ)` for all `w ≥ 0`, and `g(0) = 0`.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), (A.2), OA p.3.

**Formalization Note.** The derivative is taken within `[0,∞)`, so it is the two-sided
derivative for `w > 0` and the right derivative at `0`. Values of `g` at `w < 0` are free. The
paper's `g_γ` is never a chosen function: statements quantify over all solutions. -/
def Model.IsIVPSol {n : ℕ} [NeZero n] (M : Model n) (S : Fin n → ℝ) (γ : ℝ) (g : ℝ → ℝ) : Prop :=
  g 0 = 0 ∧ ∀ w, 0 ≤ w → HasDerivWithinAt g (M.ivpField S w (g w) γ) (Ici 0) w

end RepairSched


