-- Prove2me | Definitions.Def_NondualOpt_linClassLp
-- name    : NondualOpt_linClassLp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:09.355201+00:00
-- url     : https://prove2.me/theorems/d8fd5588-f560-4228-bb6e-e88bfb871524
-- title:
--   The linear class $L^d_{p,q^*}$
-- statement:
--   For $(X,H)=(B_p^d,B_{q^*}^d)$ with the dot product,
--   $$
--   L^d_{p,q^*}=\{B_{q^*}^d\ni g\mapsto\langle g,u\rangle:\ u\in B_p^d\}.
--   $$
--   Theorem 30 bounds its sequential fat-shattering dimension.
--
--   **Formalization Note** `qs` stands for the conjugate exponent $q^*$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (6) and p.7

import Mathlib
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_linClass

open scoped ENNReal

namespace NondualOpt

/-- The linear class `L^d_{p,q∗} = L_{X,H}` for `(X, H) = (B_p^d, B_{q∗}^d)` with the dot product:
functions `g ↦ ⟨g, u⟩` on `B_{q∗}^d`, for `u ∈ B_p^d`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (6) and the following paragraph, p.7.

**Formalization Note.** `qs` is the conjugate exponent `q∗`; statements assume `q⁻¹ + qs⁻¹ = 1`. -/
def linClassLp (p qs : ℝ≥0∞) (d : ℕ) : Set (lpBall qs d → ℝ) :=
  linClass (dotPair d) (lpBall p d) (lpBall qs d)

end NondualOpt


