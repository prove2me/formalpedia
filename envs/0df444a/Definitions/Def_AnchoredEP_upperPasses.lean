-- Prove2me | Definitions.Def_AnchoredEP_upperPasses
-- name    : AnchoredEP_upperPasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:10.143903+00:00
-- url     : https://prove2.me/theorems/5a6f6b51-253a-4d4f-835b-5df42f5b3c44
-- title:
--   The upper trial terminates the method
-- statement:
--   The upper trial **passes** at outer iteration $k$ if $\psi_k(\bar a_k)\le p!\rho$ with $\rho=1/\sqrt2$; the method then returns $z_{k+1}(\bar a_k)$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, p.38

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_psi
import Definitions.Def_AnchoredEP_abar

namespace AnchoredEP

/-- **The upper trial terminates the method.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, p.38:
"If `ψ_k(ā_k) ≤ p!ρ`, the method returns `z_{k+1}(ā_k)`", with `ρ = 1/√2`. -/
def upperPasses {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L ε : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) : Prop :=
  psi F p L sol z0 s (abar F p L ε s) ≤ (p.factorial : ℝ) * (1 / Real.sqrt 2)

end AnchoredEP


