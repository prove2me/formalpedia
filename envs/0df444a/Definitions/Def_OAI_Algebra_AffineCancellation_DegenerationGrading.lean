-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
-- name    : OAI_Algebra_AffineCancellation_DegenerationGrading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:28:22.659028+00:00
-- url     : https://prove2.me/theorems/44050727-cd1f-4cac-9342-8478f8fa31ee
-- title:
--   The weight grading on the degeneration $G$ with weights $-1,0,0,2,2$
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$, $\hat x=s^2+u^3+p^2F$, $H_{\mathrm{top}}=\hat x^2F-(1+2s\hat x)J-p^2J^2$, and let $G=P/(H_{\mathrm{top}})$ with quotient map $\pi:P\to G$. Give the variables the integer weights
--   $$\omega(p)=-1,\qquad \omega(s)=\omega(u)=0,\qquad \omega(F)=\omega(J)=2 .$$
--
--   1. **The weight grading of $P$.** For $e\in\mathbb{Z}$ let $P_e$ be the $\mathbb{C}$-span of the monomials of total weight $e$. Then $P=\bigoplus_{e\in\mathbb{Z}}P_e$ is a $\mathbb{Z}$-graded $\mathbb{C}$-algebra.
--
--   2. **Homogeneity of the relation.** $\hat x$ is homogeneous of weight $0$ and $H_{\mathrm{top}}$ is homogeneous of weight $2$. Consequently the kernel $(H_{\mathrm{top}})$ of $\pi$ is a homogeneous ideal.
--
--   3. **The induced grading of $G$.** With $G_e=\pi(P_e)$,
--   $$G=\bigoplus_{e\in\mathbb{Z}}G_e$$
--   is a $\mathbb{Z}$-graded $\mathbb{C}$-algebra, in which $p,s,u,F,J$ are homogeneous of degrees $-1,0,0,2,2$.
--
--   The defining polynomial of the main algebra of the construction is $H_{\mathrm{top}}-pu$, and $pu$ has weight $-1$; so $H_{\mathrm{top}}$ is the top-weight part of that polynomial, and this grading is the one in which $G$ arises as its degeneration (an associated graded ring). It is the grading for which homogeneous locally nilpotent derivations of $G$, and homogeneous invariants of positive degree, are considered.
--
--   **Formalization Note** The weight function is `weight : Fin 5 → ℤ` (variables `X 0, …, X 4` = p, s, u, F, J), `sourcePieces e = weightedHomogeneousSubmodule ℂ weight e` with instance `sourceGrading`; `xp_homogeneous`, `relation_homogeneous` and `kernel_homogeneous` are the homogeneity facts; `pieces = QuotientGrading.pieces sourcePieces π` and `grading` is the resulting `GradedAlgebra` instance on `G`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/DegenerationGrading.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/DegenerationGrading.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Degeneration
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight (i : Fin 5) : ℤ := if i=0 then -1 else if i=1 ∨ i=2 then 0 else 2
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule ℂ weight e
instance sourceGrading : GradedAlgebra sourcePieces := inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule ℂ weight))
lemma xp_homogeneous : IsWeightedHomogeneous weight xp 0 := by
  have h₁ : IsWeightedHomogeneous weight ((X 1 : P)^2) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 1).pow 2 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight ((X 2 : P)^3) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 2).pow 3 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((X 0 : P)^2*X 3) 0 := by
    convert ((isWeightedHomogeneous_X ℂ weight 0).pow 2).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.add h₂).add h₃
lemma relation_homogeneous : relation ∈ sourcePieces 2 := by
  have h₁ : IsWeightedHomogeneous weight (xp^2*X 3) 2 := by
    convert (xp_homogeneous.pow 2).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight (1+2*X 1*xp : P) 0 := by
    apply (isWeightedHomogeneous_one ℂ weight).add
    convert ((isWeightedHomogeneous_C weight (2:ℂ)).mul (isWeightedHomogeneous_X ℂ weight 1)).mul xp_homogeneous using 1 <;> try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((1+2*X 1*xp)*X 4 : P) 2 := by
    convert h₂.mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₄ : IsWeightedHomogeneous weight (X 0^2*X 4^2 : P) 2 := by
    convert ((isWeightedHomogeneous_X ℂ weight 0).pow 2).mul ((isWeightedHomogeneous_X ℂ weight 4).pow 2) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.sub h₃).sub h₄
lemma kernel_homogeneous : (RingHom.ker π).IsHomogeneous sourcePieces := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact ⟨2,relation_homogeneous⟩
def pieces : ℤ → Submodule ℂ G := QuotientGrading.pieces sourcePieces π
instance grading : GradedAlgebra pieces := QuotientGrading.grading _ _ (Ideal.Quotient.mkₐ_surjective ℂ _) kernel_homogeneous
end ComplexCancellation.Degeneration

end

end OAI


