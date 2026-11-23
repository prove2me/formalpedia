-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsPlaneSearchMinimizer
-- name    : VBSDP_Duality_Supplement_IsPlaneSearchMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:04:25.138261+00:00
-- url     : https://prove2.me/theorems/08c4c56b-1d36-46f7-bcfe-8a1082d78d28
-- title:
--   p. 77 — exact plane search of the potential reduction algorithm (step 2)
-- statement:
--   Let $(x,Z)$ be the current primal–dual pair and $(\delta x,\delta Z)$ the current search directions. Let $\varphi$ be the primal–dual potential (55) with parameter $\nu$,
--
--   $$\varphi(x,Z)=\nu\sqrt n\,\log\operatorname{Tr}F(x)Z+\psi(x,Z).$$
--
--   Real step lengths $p,q$ are an **exact plane-search step** when the new pair $(x+p\,\delta x,\;Z+q\,\delta Z)$ is strictly feasible ($F(x+p\delta x)\succ0$, $Z+q\delta Z\succ0$, $\operatorname{Tr}F_i(Z+q\delta Z)=c_i$ for all $i$) and
--
--   $$\varphi(x+p\,\delta x,\,Z+q\,\delta Z)\le\varphi(x+p'\delta x,\,Z+q'\delta Z)$$
--
--   for every pair of reals $p',q'$ for which $(x+p'\delta x,\,Z+q'\delta Z)$ is strictly feasible.
--
--   This is step 2 of the general potential reduction algorithm ("Find $p,q\in\mathbf R$ that minimize $\varphi(x+p\delta x,Z+q\delta Z)$"), followed by the update $x:=x+p\,\delta x$, $Z:=Z+q\,\delta Z$ of step 3.
--
--   **Formalization Note** The minimization ranges over the strict-feasibility domain of $\varphi$, the set on which the logarithms in (55) are defined; `Real.log` is total in Lean, so minimizing over all real $p,q$ would read junk values. No sign constraint on $p,q$ is imposed, as on the page. The predicate states the minimality property only; it does not assert that a minimizer exists, and it contains no decrease condition. When the directions are zero or the minimizer is not unique, every minimizer qualifies.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 77 (PDF p. 29), potential reduction algorithm, steps 2–3; φ from (55), p. 76 (PDF p. 28); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Potential_IsStrictlyFeasiblePair
import Definitions.Def_VBSDP_Potential_phi

namespace VBSDP.Duality.Supplement

/-- Step 2 of the potential reduction algorithm, p. 77 (the plane search): the step
lengths `p, q ∈ ℝ` minimize `φ(x + p δx, Z + q δZ)` over all real `p', q'` for which the
new pair is strictly feasible, and the minimizing pair is itself strictly feasible. -/
def IsPlaneSearchMinimizer {m n : ℕ} (ν : ℝ) (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ) (p q : ℝ) : Prop :=
  VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + p • δx) (Z + q • δZ) ∧
  ∀ p' q' : ℝ,
    VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + p' • δx) (Z + q' • δZ) →
      VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
        VBSDP.Potential.phi ν F₀ F (x + p' • δx) (Z + q' • δZ)

end VBSDP.Duality.Supplement


