-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Rees
-- name    : OAI_Algebra_AffineCancellation_Rees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:17:41.003604+00:00
-- url     : https://prove2.me/theorems/a835af9d-fdf0-457d-a943-6f3f92a3f1bf
-- title:
--   The Rees deformation $B$ of the main algebra and its embedding into $A[T,T^{-1}]$
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$, $x=s^2+u^3+p^2F$, $H=x^2F-(1+2sx)J-p^2J^2-pu$ and $A=P/(H)$; the letters $p,s,u,F,J,x$ also denote their images in $A$. In the polynomial ring $\mathbb{C}[q,p,s,u,F,J]$ in six variables put
--   $$\hat x=s^2+u^3+p^2F,\qquad H_q=\hat x^2F-(1+2s\hat x)J-p^2J^2-q^3pu,$$
--   and let $B=\mathbb{C}[q,p,s,u,F,J]/(H_q)$, again using the same letters for the classes in $B$. Setting $q=1$ turns $H_q$ into $H$, while setting $q=0$ turns it into $\hat x^2F-(1+2s\hat x)J-p^2J^2$. The file proves the following.
--
--   1. **$q$ is a non-zero-divisor** of $B$.
--
--   2. **The Laurent embedding.** Let $L=A[T,T^{-1}]$ be the Laurent polynomial ring in one variable $T$ over $A$. The substitution
--   $$q\mapsto T,\qquad p\mapsto pT^{-1},\qquad s\mapsto s,\qquad u\mapsto u,\qquad F\mapsto FT^2,\qquad J\mapsto JT^2$$
--   sends $\hat x$ to $x$ and $H_q$ to $T^2H=0$, hence defines a $\mathbb{C}$-algebra homomorphism $\varepsilon:B\to L$.
--
--   3. **The backward map.** Let $B_q=B[q^{-1}]$ be the localization of $B$ at the powers of $q$. In $B_q$ the assignment
--   $$p\mapsto qp,\qquad s\mapsto s,\qquad u\mapsto u,\qquad F\mapsto q^{-2}F,\qquad J\mapsto q^{-2}J$$
--   sends $H$ to $q^{-2}H_q=0$, so it defines a homomorphism $A\to B_q$; extending it to Laurent polynomials by $T\mapsto q$ gives $\beta:L\to B_q$, and $\beta\circ\varepsilon$ is the localization map $B\to B_q$.
--
--   4. **Consequences.** The localization map is injective because $q$ is a non-zero-divisor, so $\varepsilon$ is injective. Hence $B$ is an integral domain; it is also Noetherian, being a finitely generated $\mathbb{C}$-algebra.
--
--   The ring $B$ is a one-parameter deformation connecting the main algebra $A$ (at $q=1$) with its degeneration (at $q=0$). Through $\varepsilon$ it becomes a subring of $A[T,T^{-1}]$ containing $T=q$; this is how a locally nilpotent derivation of $A$, extended to $A[T,T^{-1}]$ and multiplied by a suitable power of $q$, is restricted to $B$ before being reduced modulo $q$.
--
--   **Formalization Note** `Poly = MvPolynomial (Fin 6) ℂ` with `X 0, …, X 5` standing for q, p, s, u, F, J; `xp` is $\hat x$ and `relation` is $H_q$. `L = LaurentPolynomial A`, `c : A →ₐ[ℂ] L` is the inclusion of constants, `aπ` the quotient map onto `A`, and `a i` the image in `L` of the `i`-th variable of `P`. The maps are `embedding` and `backward` (built from `backCoefficients`), with `Bq = Localization.Away q`, `loc` the localization map and `Q` the unit $q$ in `Bq`; the key facts are `q_regular`, `eval_relation`, `backEval_H`, `backward_embedding`, `loc_injective` and `embedding_injective`, and `IsDomain B`, `IsNoetherianRing B` are instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Rees.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Rees.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 6) ℂ
def xp : Poly := X 2^2+X 3^3+X 1^2*X 4
def relation : Poly := xp^2*X 4-(1+2*X 2*xp)*X 5-X 1^2*X 5^2-X 0^3*X 1*X 3
abbrev B := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] B := Ideal.Quotient.mkₐ ℂ _
def q : B := π (X 0)
lemma relation_zero : π relation=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
lemma q_regular : IsLeftRegular q := by
  apply Cylinder.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 6 => if i=5 then (1:ℂ) else 0)) h
  norm_num [relation,xp,Fin.ext_iff] at he
abbrev L := LaurentPolynomial A
def c : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
def aπ : P →ₐ[ℂ] A := Ideal.Quotient.mkₐ ℂ _
def a (i : Fin 5) : L := c (aπ (X i))
def values : Fin 6 → L := ![LaurentPolynomial.T 1,a 0*LaurentPolynomial.T (-1),
  a 1,a 2,a 3*LaurentPolynomial.T 2,a 4*LaurentPolynomial.T 2]
def eval : Poly →ₐ[ℂ] L := aeval values
lemma eval_xp : eval xp = c (aπ ComplexCancellation.x) := by
  simp only [xp,eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,
    ComplexCancellation.x,ComplexCancellation.s,ComplexCancellation.p,ComplexCancellation.u,
    ComplexCancellation.F,map_add,map_mul,map_pow,a]
  have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
    rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
  linear_combination c (aπ (X 0))^2*c (aπ (X 3))*ht
lemma eval_relation : eval relation = 0 := by
  have h : c (aπ H) = 0 := by
    rw [show aπ H=0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),map_zero]
  have hh : eval relation = c (aπ H)*LaurentPolynomial.T 2 := by
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,eval_xp]
    simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [H,ComplexCancellation.F,ComplexCancellation.J,ComplexCancellation.p,
      ComplexCancellation.s,ComplexCancellation.u,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,a]
    have ht : (LaurentPolynomial.T (-1):L)^2*LaurentPolynomial.T 2=1 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    have ht' : (LaurentPolynomial.T 1:L)^3*LaurentPolynomial.T (-1)=LaurentPolynomial.T 2 := by
      rw [LaurentPolynomial.T_pow,← LaurentPolynomial.T_add]; norm_num
    linear_combination
      -(c (aπ (X 0)))^2*c (aπ (X 4))^2*LaurentPolynomial.T 2*ht -
      c (aπ (X 0))*c (aπ (X 2))*ht'

  rw [hh,h,zero_mul]
def embedding : B →ₐ[ℂ] L := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma embedding_π (r : Poly) : embedding (π r)=eval r := Ideal.Quotient.lift_mk _ _ _

abbrev Bq := Localization.Away q
def loc : B →ₐ[ℂ] Bq := IsScalarTower.toAlgHom ℂ B Bq
def Q : Bqˣ := (IsLocalization.Away.algebraMap_isUnit q).unit
lemma Q_val : (Q : Bq)=loc q := IsUnit.unit_spec _
lemma loc_injective : Function.Injective loc := by
  apply IsLocalization.injectiveₛ (M := Submonoid.powers q) Bq
  rintro r ⟨n,rfl⟩
  exact isLeftRegular_iff_isRegular.mp (q_regular.pow n)
def backValues : Fin 5 → Bq := ![(Q:Bq)*loc (π (X 1)),loc (π (X 2)),
  loc (π (X 3)),(↑(Q⁻¹):Bq)^2*loc (π (X 4)),(↑(Q⁻¹):Bq)^2*loc (π (X 5))]
def backEval : P →ₐ[ℂ] Bq := aeval backValues
lemma backEval_x : backEval ComplexCancellation.x = loc (π xp) := by
  simp only [ComplexCancellation.x,ComplexCancellation.p,ComplexCancellation.s,
    ComplexCancellation.u,ComplexCancellation.F,backEval,map_add,map_mul,map_pow,aeval_X,
    backValues,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one,xp]
  simp only [mul_pow]
  have h : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
  linear_combination loc (π (X 1))^2*loc (π (X 4))*h
lemma backEval_H : backEval H=0 := by
  have h : loc (π relation)=0 := by rw [relation_zero,map_zero]
  have he : (Q:Bq)^2*backEval H=loc (π relation) := by
    simp only [H,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat,backEval_x]
    simp only [ComplexCancellation.p,ComplexCancellation.s,ComplexCancellation.u,
      ComplexCancellation.F,ComplexCancellation.J,backEval,aeval_X,backValues,
      Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp only [relation,map_sub,map_mul,map_add,map_pow,map_one,map_ofNat]
    rw [show loc (π (X 0))=(Q:Bq) from Q_val.symm]
    have h2 : (Q:Bq)^2*(↑(Q⁻¹):Bq)^2=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    have h4 : (Q:Bq)^4*(↑(Q⁻¹):Bq)^4=1 := by rw [← mul_pow,Units.mul_inv,one_pow]
    linear_combination
      (loc (π xp)^2*loc (π (X 4))-(1+2*loc (π (X 2))*loc (π xp))*loc (π (X 5)))*h2-
      loc (π (X 1))^2*loc (π (X 5))^2*h4
  apply (Q.isUnit.pow 2).mul_right_inj.mp
  rw [mul_zero,he,h]
def backCoefficients : A →ₐ[ℂ] Bq := Ideal.Quotient.liftₐ _ backEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,backEval_H,zero_mul])
@[simp] lemma backCoefficients_aπ (r : P) : backCoefficients (aπ r)=backEval r :=
  Ideal.Quotient.lift_mk _ _ _
def backward : L →ₐ[ℂ] Bq where
  __ := LaurentPolynomial.eval₂ backCoefficients.toRingHom Q
  commutes' r := by
    change LaurentPolynomial.eval₂ backCoefficients.toRingHom Q (LaurentPolynomial.C (algebraMap ℂ A r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact backCoefficients.commutes r
lemma backward_embedding : backward.comp embedding=loc := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change backward (eval (X i))=loc (π (X i))
  fin_cases i <;> simp [eval,values,Matrix.cons_val,backward,a,c,backEval,backValues,
    backCoefficients_aπ,IsScalarTower.toAlgHom]
  · exact Q_val
  · rw [mul_right_comm,Units.mul_inv,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]
  · rw [mul_right_comm,← mul_pow,Units.inv_mul,one_pow,one_mul]
lemma embedding_injective : Function.Injective embedding := by
  apply Function.Injective.of_comp (f := backward)
  rw [← AlgHom.coe_comp,backward_embedding]
  exact loc_injective
instance : IsDomain B := Function.Injective.isDomain embedding embedding_injective
instance : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
end ComplexCancellation.Rees

end

end OAI


