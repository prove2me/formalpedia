-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
-- name    : OAI_Algebra_AffineCancellation_ModificationGrading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:57:34.761107+00:00
-- url     : https://prove2.me/theorems/b1bc0fe0-222d-4665-aaf1-19178897e459
-- title:
--   The $\mathbb{Z}$-grading of $R[\tau,V]/(\tau^2V-v)$ with $\tau$ of degree $-1$ and $V$ of degree $2$
-- statement:
--   Let $R$ be a commutative ring and $v\in R$. Let $T_v=R[X_0,X_1]/(X_0^2X_1-v)$ with quotient map $\pi\colon R[X_0,X_1]\to T_v$, and put $\tau=\pi(X_0)$, $V=\pi(X_1)$.
--
--   1. **Weighted grading of the polynomial ring.** Give $X_0$ weight $-1$, $X_1$ weight $2$ and the coefficients weight $0$, so the monomial $X_0^iX_1^l$ has weight $-i+2l$. For $e\in\mathbb{Z}$ let $P_e\subseteq R[X_0,X_1]$ be the $R$-submodule of weighted homogeneous polynomials of degree $e$,
--   $$P_e=\Bigl\{\sum_{-i+2l=e}c_{il}\,X_0^iX_1^l\ :\ c_{il}\in R\Bigr\}.$$
--   Then $R[X_0,X_1]=\bigoplus_{e\in\mathbb{Z}}P_e$ is a $\mathbb{Z}$-graded $R$-algebra.
--   2. **Homogeneity of the relation.** $X_0^2X_1-v\in P_0$; consequently the kernel $(X_0^2X_1-v)$ of $\pi$ is a homogeneous ideal.
--   3. **Induced grading.** With $T_e=\pi(P_e)$,
--   $$T_v=\bigoplus_{e\in\mathbb{Z}}T_e,\qquad T_e\,T_{e'}\subseteq T_{e+e'},\qquad 1\in T_0,$$
--   is a $\mathbb{Z}$-graded $R$-algebra; the image of $R$ lies in degree $0$, $\tau\in T_{-1}$ and $V\in T_2$.
--
--   Because the relation $\tau^2V=v$ has degree $0$, the weights descend to the modification. When $R$ is a domain, the embedding $\tau\mapsto X$, $V\mapsto v/X^2$ of $T_v$ into the rational function field $\operatorname{Frac}(R)(X)$ sends $T_e$ to elements of the form $c\,X^{-e}$ with $c\in R$, so the degree is minus the order in $X$. The grading is used to split derivations of the modification into homogeneous components and to control the shape of homogeneous elements.
--
--   **Formalization Note** `weight = ![-1,2]`; `sourcePieces R e` is Mathlib's `weightedHomogeneousSubmodule R weight e`, graded through the local instance `MvPolynomial.weightedGradedAlgebra` (instance `sourceGrading`). Item 2 is `rel_homogeneous` and `kernel_homogeneous`. In item 3, `pieces R v e` is `QuotientGrading.pieces` (the image of `sourcePieces R e` under the quotient map) and `grading` is the `GradedAlgebra` instance produced by `QuotientGrading.grading` from surjectivity of the quotient map and homogeneity of its kernel.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ModificationGrading.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] (v : R)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight : Fin 2 → ℤ := ![-1,2]
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule R weight e
instance sourceGrading : GradedAlgebra (sourcePieces R) :=
  inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule R weight))
lemma rel_homogeneous : rel R v ∈ sourcePieces R 0 := by
  apply IsWeightedHomogeneous.sub
  · convert ((isWeightedHomogeneous_X R weight 0).pow 2).mul
      (isWeightedHomogeneous_X R weight 1) using 1; norm_num [weight]
  · exact isWeightedHomogeneous_C _ _
lemma kernel_homogeneous : (RingHom.ker (π R v)).IsHomogeneous (sourcePieces R) := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {rel R v}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  have he : r=rel R v := Set.mem_singleton_iff.mp hr
  subst r
  exact ⟨0,rel_homogeneous R v⟩
def pieces : ℤ → Submodule R (T R v) := QuotientGrading.pieces (sourcePieces R) (π R v)
instance grading : GradedAlgebra (pieces R v) := QuotientGrading.grading _ _
  (Ideal.Quotient.mkₐ_surjective R _) (kernel_homogeneous R v)
end ComplexCancellation.AffineModification

end

end OAI


