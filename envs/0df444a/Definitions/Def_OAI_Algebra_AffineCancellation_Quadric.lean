-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
-- name    : OAI_Algebra_AffineCancellation_Quadric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:11:11.938178+00:00
-- url     : https://prove2.me/theorems/f9bf1c64-66c6-4b8c-8840-2e9eca34c9ef
-- title:
--   The quadric ring $\mathbb{C}[x,y,z,u]/(xy-z(z+1))$ as a domain inside $\mathbb{C}(t_0,t_1,t_2)$
-- statement:
--   Let $R=\mathbb{C}[x,y,z,u]/\bigl(xy-z(z+1)\bigr)$, where $x,y,z,u$ denote the classes of four independent polynomial variables; $R$ is the coordinate ring of the product of the affine quadric surface $xy=z(z+1)$ with an affine line. This file introduces the following elements and maps and proves their basic properties.
--
--   1. **Distinguished elements.** In $R$ the defining equation $xy=z(z+1)$ holds, and one puts
--   $$s=y-x(x-u^3),\qquad f=x-s^2-u^3,\qquad g=z-sx .$$
--
--   2. **A rational embedding.** Let $K=\mathbb{C}(t_0,t_1,t_2)$ be the field of fractions of the polynomial ring $\mathbb{C}[t_0,t_1,t_2]$. The assignment
--   $$x\mapsto t_0,\qquad y\mapsto\frac{t_1(t_1+1)}{t_0},\qquad z\mapsto t_1,\qquad u\mapsto t_2$$
--   annihilates $xy-z(z+1)$ and so defines a $\mathbb{C}$-algebra homomorphism $\iota:R\to K$. This map is injective; consequently $R$ is an integral domain.
--
--   3. **The base polynomial ring.** Let $\beta:\mathbb{C}[t_0,t_1,t_2]\to R$ be the $\mathbb{C}$-algebra homomorphism with $\beta(t_0)=x$, $\beta(t_1)=z$, $\beta(t_2)=u$. Then $\iota\circ\beta$ is the canonical inclusion $\mathbb{C}[t_0,t_1,t_2]\subset K$, so $\beta$ is injective, i.e. $x,z,u$ are algebraically independent in $R$. Moreover every element of $R$ is moved into this subring by a power of $x$: for each $r\in R$ there are $n\ge0$ and $h\in\mathbb{C}[t_0,t_1,t_2]$ with $x^n r=\beta(h)$ (for the generator $y$ one uses $xy=z(z+1)$).
--
--   4. **The element $x$.** One has $x\ne0$, and $x$ is a non-zero-divisor of $R$: $xr=xr'$ implies $r=r'$.
--
--   The ring $R$ serves as the coefficient ring of a degenerate hypersurface algebra in variables $p,s,u,F,J$, into which it maps with $s$, $f$, $g$ becoming $s$, $p^2F$ and $p^2J$. The rational embedding together with the clearing property is the device used to prove that $R$ is a domain and to compute in its fraction field.
--
--   **Formalization Note** `Poly = MvPolynomial (Fin 4) ℂ`, whose variables `X 0, X 1, X 2, X 3` play the roles of x, y, z, u, and `relation = X 0*X 1-X 2*(X 2+1)`; `Base = MvPolynomial (Fin 3) ℂ` and `K = FractionRing Base`. The embedding is `embedding : R →ₐ[ℂ] K`, induced by `eval = aeval values`; the base map is `baseMap = aeval ![x,z,u]`, and the clearing property is `clears : Clearing.subalgebra baseMap (X 0) = ⊤`. Injectivity is `embedding_injective` and `baseMap_injective`, non-zero-divisibility is `x_regular : IsLeftRegular x`, and the domain property of `R` is a type-class instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Quadric.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Quadric.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Quadric
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Base := MvPolynomial (Fin 3) ℂ
abbrev K := FractionRing Base
def relation : Poly := X 0*X 1-X 2*(X 2+1)
abbrev R := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] R := Ideal.Quotient.mkₐ ℂ _
def x : R := π (X 0)
def y : R := π (X 1)
def z : R := π (X 2)
def u : R := π (X 3)
def s : R := y-x*(x-u^3)
def f : R := x-s^2-u^3
def g : R := z-s*x

def baseEmbedding : Base →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Base K
lemma baseEmbedding_injective : Function.Injective baseEmbedding := IsFractionRing.injective Base K
lemma x_field_nonzero : baseEmbedding (X 0) ≠ 0 := by
  simpa only [map_zero] using baseEmbedding_injective.ne (X_ne_zero (0 : Fin 3))
def values : Fin 4 → K := ![baseEmbedding (X 0),
  baseEmbedding (X 1)*(baseEmbedding (X 1)+1)/baseEmbedding (X 0),
  baseEmbedding (X 1),baseEmbedding (X 2)]
def eval : Poly →ₐ[ℂ] K := aeval values
lemma eval_relation : eval relation = 0 := by
  simp only [relation,eval,map_sub,map_mul,map_add,map_one,aeval_X,values,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [x_field_nonzero]
  ring

def embedding : R →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r := Ideal.Quotient.lift_mk _ _ _
lemma equation : x*y=z*(z+1) := by
  apply sub_eq_zero.mp
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation,map_sub,map_mul,map_add,map_one,x,y,z] using h
lemma x_regular : IsLeftRegular x := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 4 => if i=2 then (1:ℂ) else 0)) h
  norm_num [relation,Fin.ext_iff] at he

def baseMap : Base →ₐ[ℂ] R := aeval ![x,z,u]
lemma baseMap_X_zero : baseMap (X 0) = x := by simp [baseMap]
lemma embedding_baseMap : embedding.comp baseMap = baseEmbedding := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap,x,z,u,eval,values]
lemma clears : Clearing.subalgebra baseMap (X 0) = ⊤ := by
  apply Clearing.top_of_generators π (Ideal.Quotient.mkₐ_surjective ℂ _) _ _
  intro i
  fin_cases i
  · exact ⟨0,X 0,by simp [baseMap,x]⟩
  · refine ⟨1,X 1*(X 1+1),?_⟩
    simp only [pow_one,baseMap,map_mul,map_add,map_one,aeval_X]
    exact equation
  · exact ⟨0,X 1,by simp [baseMap,z]⟩
  · exact ⟨0,X 2,by simp [baseMap,u]⟩
lemma embedding_injective : Function.Injective embedding := by
  apply Clearing.injective_of_clearing embedding baseMap (X 0)
  · rw [embedding_baseMap]; exact baseEmbedding_injective
  · rw [baseMap_X_zero]; exact x_regular
  · exact clears
instance : IsDomain R := Function.Injective.isDomain embedding embedding_injective
lemma baseMap_injective : Function.Injective baseMap := by
  apply Function.Injective.of_comp (f := embedding)
  rw [← AlgHom.coe_comp,embedding_baseMap]
  exact baseEmbedding_injective
lemma x_ne_zero : x ≠ 0 := by
  rw [← baseMap_X_zero]
  simpa only [map_zero] using baseMap_injective.ne (X_ne_zero (0 : Fin 3))

end ComplexCancellation.Quadric

end

end OAI


