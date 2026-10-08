-- Prove2me | Definitions.Def_ResolvingNRM_FRLower_Instance
-- name    : ResolvingNRM_FRLower_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:29:36.454596+00:00
-- url     : https://prove2.me/theorems/4ca6fe00-5fdc-42a1-b94f-c8a1737e6b56
-- title:
--   Appendix C.1 — two-class degenerate network instance
-- statement:
--   The lower-bound instance has two independent rate-one customer classes and one resource. Either class consumes one unit if admitted. Their prices are $r_1$ and $r_2$, and the initial capacity equals the integer horizon $T$:
--
--   $$
--   \lambda=(1,1),\qquad A=(1\;1),\qquad r=(r_1,r_2),\qquad C=T.
--   $$
--
--   This is the explicit instance used to demonstrate the loss from frequent re-solving at a degenerate deterministic LP solution.
--
--   **Formalization Note** The definition accepts nonnegative ordered prices to satisfy the model's standing assumptions. The theorems assume the strict inequalities $0<r_2<r_1$ needed by the paper's analysis. Class and resource indices use `Fin 2` and `Fin 1`.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Sec. 3.1 p. 11; Appendix C.1 p. 32

import Mathlib
import Definitions.Def_ResolvingNRM_FRLower_Model

namespace ResolvingNRM.FRLower

/-- The two-class, one-resource degenerate DLP instance of Section 3.1 and Appendix C.1.
The revenues are parameters; the lower-bound goal assumes `0 < r₂ < r₁`. -/
def twoClass (r₁ r₂ : ℝ) (hr₂ : 0 ≤ r₂) (hr : r₂ ≤ r₁) : Instance 2 1 where
  lam := ![1, 1]
  r := ![r₁, r₂]
  A := !![1, 1]
  lam_pos := by
    intro j
    fin_cases j <;> norm_num
  r_nonneg := by
    intro j
    fin_cases j <;> simp [hr₂, le_trans hr₂ hr]
  A_nonneg := by
    intro l j
    fin_cases l
    fin_cases j <;> norm_num

/-- The horizon-length initial capacity of Appendix C.1. -/
def initialCapacity (T : ℕ) : Fin 1 → ℝ := fun _ => (T : ℝ)

end ResolvingNRM.FRLower


