-- Prove2me | Definitions.Def_OTDRO_StrongCvx_Kernel
-- name    : OTDRO_StrongCvx_Kernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:20.606362+00:00
-- url     : https://prove2.me/theorems/b740eca7-8e0b-426b-896c-dd53c21824a3
-- title:
--   Curvature margin φ, section U(x), and canonical maximizer
-- statement:
--   At a parameter $(\beta,\lambda)$ and outcome $x$, the curvature margin of the scalar maximization is
--
--   $$\varphi(\gamma,\beta,\lambda;x)=2\lambda-\sqrt\delta\,q_A(\beta,x)\ell''\bigl(\beta^{\mathsf T}x+\sqrt\delta\,\gamma q_A(\beta,x)\bigr).$$
--
--   The section $U(x)$ consists of parameters in $B\times\mathbb R_+$ for which the maximizer set $\Gamma^*(\beta,\lambda;x)$ contains a $\gamma$ with positive margin. On regions where this set is a singleton, its member is the scalar $g(\beta,\lambda;x)$ of the paper's selection (29).
--
--   This layer expresses the positive-curvature domain and the unique maximizing scalar used by Lemma 8 and Proposition 9.
--
--   **Formalization Note** The canonical scalar is the real infimum of $\Gamma^*$ and is used only where a theorem states that $\Gamma^*$ is a singleton. The section omits the ambient support condition on $x$ because all applications are $P_0$-almost everywhere.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, §5.3, p. 35, (29)–(30)

import Mathlib
import Definitions.Def_OTDRO_StrongCvx_Regions

namespace OTDRO.StrongCvx

/-- The curvature margin φ(γ,β,λ;x) of §5.3, p. 35. -/
noncomputable def kernelPhi {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ γ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x *
    deriv (deriv ℓ) (inner ℝ β x + Real.sqrt δ * γ * OTDRO.Dual.quadInv A β x)

/-- The section U(x) of the set U from §5.3, p. 35: feasible parameters
with a maximizer at which the curvature margin is positive. -/
def UAt {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
  {θ | θ.1 ∈ B ∧ 0 ≤ θ.2 ∧
    ∃ γ ∈ OTDRO.Dual.maximizers ℓ A δ θ.1 θ.2 x,
      0 < kernelPhi ℓ A δ γ θ.1 θ.2 x}

/-- The unique maximizer on the region W, represented by the infimum of Γ*.
The formula is used only where Γ* is a singleton. -/
noncomputable def selectedGamma {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf (OTDRO.Dual.maximizers ℓ A δ β lam x)

end OTDRO.StrongCvx


