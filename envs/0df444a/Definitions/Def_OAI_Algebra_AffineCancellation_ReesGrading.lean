-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
-- name    : OAI_Algebra_AffineCancellation_ReesGrading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:31:54.663187+00:00
-- url     : https://prove2.me/theorems/d200dbaf-8ae5-4aa7-8868-e1f0dca33181
-- title:
--   Weight gradings on the Rees deformation and on the Laurent ring $A[T,T^{-1}]$
-- statement:
--   Let $\hat x=s^2+u^3+p^2F$ and $H_q=\hat x^2F-(1+2s\hat x)J-p^2J^2-q^3pu$ in the polynomial ring $\mathbb{C}[q,p,s,u,F,J]$, let $B=\mathbb{C}[q,p,s,u,F,J]/(H_q)$ with quotient map $\pi$, and let $A=\mathbb{C}[p,s,u,F,J]/(H)$ be the main algebra, where $H=x^2F-(1+2sx)J-p^2J^2-pu$ and $x=s^2+u^3+p^2F$. Give the six variables the integer weights
--   $$\omega(q)=1,\qquad \omega(p)=-1,\qquad \omega(s)=\omega(u)=0,\qquad \omega(F)=\omega(J)=2 .$$
--
--   1. **Grading of the polynomial ring.** The spans of monomials of fixed total weight make $\mathbb{C}[q,p,s,u,F,J]$ a $\mathbb{Z}$-graded $\mathbb{C}$-algebra.
--
--   2. **Homogeneity of the relation.** $\hat x$ is homogeneous of weight $0$, and every term of $H_q$ has weight $2$ (for $q^3pu$: $3-1+0=2$), so $H_q$ is homogeneous of weight $2$ and the kernel $(H_q)$ of $\pi$ is a homogeneous ideal.
--
--   3. **Grading of $B$.** With $B_e=\pi(\text{weight-}e\text{ polynomials})$, one obtains a $\mathbb{Z}$-graded $\mathbb{C}$-algebra $B=\bigoplus_{e\in\mathbb{Z}}B_e$.
--
--   4. **Grading of the Laurent ring.** On $L=A[T,T^{-1}]$ the pieces $L_e=A\,T^{e}$ give the grading by $T$-degree:
--   $$L=\bigoplus_{e\in\mathbb{Z}}A\,T^{e}.$$
--
--   The weights are chosen so that the Laurent embedding $B\to A[T,T^{-1}]$, given by $q\mapsto T$, $p\mapsto pT^{-1}$, $s\mapsto s$, $u\mapsto u$, $F\mapsto FT^2$, $J\mapsto JT^2$, sends each generator to a homogeneous element of the same degree, and so that setting $q=0$ recovers the weights $-1,0,0,2,2$ of $p,s,u,F,J$ on the degeneration. This makes the Rees deformation a graded bridge between $A[T,T^{-1}]$ and the graded degeneration.
--
--   **Formalization Note** `weight : Fin 6 → ℤ` (variables `X 0, …, X 5` = q, p, s, u, F, J), `sourcePieces e = weightedHomogeneousSubmodule ℂ weight e` with instance `sourceGrading`, homogeneity facts `xp_homogeneous`, `relation_homogeneous`, `kernel_homogeneous`, and `pieces`/`grading` the induced grading of `B` via `QuotientGrading`. On `L = LaurentPolynomial A` the pieces are `laurentPieces e = (AddMonoidAlgebra.grade A e).restrictScalars ℂ`, with instance `laurentGrading` taken from the standard grading of the monoid algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesGrading.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesGrading.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def weight (i : Fin 6) : ℤ := if i=0 then 1 else if i=1 then -1 else if i=2 ∨ i=3 then 0 else 2
def sourcePieces (e : ℤ) := weightedHomogeneousSubmodule ℂ weight e
instance sourceGrading : GradedAlgebra sourcePieces := inferInstanceAs (GradedAlgebra (weightedHomogeneousSubmodule ℂ weight))
lemma xp_homogeneous : IsWeightedHomogeneous weight xp 0 := by
  have h₁ : IsWeightedHomogeneous weight ((X 2 : Poly)^2) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 2).pow 2 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight ((X 3 : Poly)^3) 0 := by
    convert (isWeightedHomogeneous_X ℂ weight 3).pow 3 using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((X 1 : Poly)^2*X 4) 0 := by
    convert ((isWeightedHomogeneous_X ℂ weight 1).pow 2).mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact (h₁.add h₂).add h₃
lemma relation_homogeneous : relation ∈ sourcePieces 2 := by
  have h₁ : IsWeightedHomogeneous weight (xp^2*X 4) 2 := by
    convert (xp_homogeneous.pow 2).mul (isWeightedHomogeneous_X ℂ weight 4) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₂ : IsWeightedHomogeneous weight (1+2*X 2*xp : Poly) 0 := by
    apply (isWeightedHomogeneous_one ℂ weight).add
    convert ((isWeightedHomogeneous_C weight (2:ℂ)).mul (isWeightedHomogeneous_X ℂ weight 2)).mul xp_homogeneous using 1 <;> try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₃ : IsWeightedHomogeneous weight ((1+2*X 2*xp)*X 5 : Poly) 2 := by
    convert h₂.mul (isWeightedHomogeneous_X ℂ weight 5) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₄ : IsWeightedHomogeneous weight (X 1^2*X 5^2 : Poly) 2 := by
    convert ((isWeightedHomogeneous_X ℂ weight 1).pow 2).mul ((isWeightedHomogeneous_X ℂ weight 5).pow 2) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  have h₅ : IsWeightedHomogeneous weight (X 0^3*X 1*X 3 : Poly) 2 := by
    convert (((isWeightedHomogeneous_X ℂ weight 0).pow 3).mul (isWeightedHomogeneous_X ℂ weight 1)).mul (isWeightedHomogeneous_X ℂ weight 3) using 1; try simp only [map_ofNat]
    all_goals norm_num [weight,Fin.ext_iff]
  exact ((h₁.sub h₃).sub h₄).sub h₅
lemma kernel_homogeneous : (RingHom.ker π).IsHomogeneous sourcePieces := by
  change (RingHom.ker (Ideal.Quotient.mk (Ideal.span {relation}))).IsHomogeneous _
  rw [Ideal.mk_ker]
  apply Ideal.homogeneous_span
  intro r hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact ⟨2,relation_homogeneous⟩
def pieces : ℤ → Submodule ℂ B := QuotientGrading.pieces sourcePieces π
instance grading : GradedAlgebra pieces := QuotientGrading.grading _ _ (Ideal.Quotient.mkₐ_surjective ℂ _) kernel_homogeneous
abbrev laurentPieces (e : ℤ) : Submodule ℂ L := (AddMonoidAlgebra.grade A e).restrictScalars ℂ
instance laurentGrading : GradedAlgebra laurentPieces := { (AddMonoidAlgebra.grade.gradedAlgebra (R := A) (ι := ℤ)) with }
end ComplexCancellation.Rees

end

end OAI


