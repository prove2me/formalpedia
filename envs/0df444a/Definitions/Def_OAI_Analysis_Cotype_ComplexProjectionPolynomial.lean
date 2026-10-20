-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
-- name    : OAI_Analysis_Cotype_ComplexProjectionPolynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:52:17.466956+00:00
-- url     : https://prove2.me/theorems/aadad48b-fefe-4148-abd8-b6e84e42fe9c
-- title:
--   The complexified projection polynomial
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Let $\widehat T$ denote the complex dual lift of a real operator.
--
--   1. **Complex products.** Ordered products of complex-linear operators.
--   2. **Projection polynomial.** For $z\in\mathbb C$,
--   $$
--   \widehat T(z)=\prod_i\bigl(\widehat{P_i}+z(1-\widehat{P_i})\bigr),
--   $$
--   a polynomial in $z$ extending the real semigroup to complex times.
--   3. **Lift as a map.** $T\mapsto\widehat T$ is a bounded real-linear map, of norm at most $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ComplexProjectionPolynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ComplexProjectionPolynomial.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum

namespace OAI

noncomputable section
namespace Cotype

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

def complexProjectionProduct : {m : ℕ} → (Fin m → Z →L[ℂ] Z) → Z →L[ℂ] Z
  | 0, _ => 1
  | _+1, P => P 0 * complexProjectionProduct (fun i => P i.succ)

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def complexProjectionPolynomial {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (z : ℂ) : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexProjectionProduct (fun i => complexDualLift (P i) + z • (1-complexDualLift (P i)))

def complexDualLiftCLM : (Y →L[ℝ] Y) →L[ℝ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :=
  ({ toFun := complexDualLift
     map_add' := complexDualLift_add
     map_smul' := complexDualLift_smul } :
    (Y →L[ℝ] Y) →ₗ[ℝ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)).mkContinuous 1
      (fun (T : Y →L[ℝ] Y) => by
        change ‖complexDualLift T‖ ≤ (1 : ℝ)*‖T‖
        simp only [complexDualLift_norm, one_mul, le_refl])

@[simp] theorem complexDualLiftCLM_apply (T : Y →L[ℝ] Y) :
    complexDualLiftCLM T = complexDualLift T := rfl

end Cotype

end

end OAI


