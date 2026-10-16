-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
-- name    : OAI_Algebra_AffineCancellation_Bundle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:53:33.9882+00:00
-- url     : https://prove2.me/theorems/526be548-0fd8-4835-9659-9023cc1ee7a2
-- title:
--   Embedding the degenerate hypersurface ring into an affine modification of $\mathrm{SL}_2\times\mathbb{A}^1$
-- statement:
--   Three complex algebras enter.
--
--   - $T=\mathbb{C}[a,b,c,d,u]/(ac-bd-1)$, the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$, which is an integral domain, together with the element $v=a^3b-a^2u^3-d^2\in T$.
--   - $Q=\mathbb{C}[x,y,z,u]/(xy-z(z+1))$, an integral domain, with the elements $s=y-x(x-u^3)$, $f=x-s^2-u^3$ and $g=z-sx$.
--   - $G=\mathbb{C}[p,s,u,F,J]/(H_0)$, where $x_G=s^2+u^3+p^2F$ and $H_0=x_G^2F-(1+2sx_G)J-p^2J^2$; this is the hypersurface of the main construction with the term $-pu$ removed. It receives the $\mathbb{C}$-algebra homomorphism $\kappa\colon Q\to G$ with $\kappa(x)=x_G$, $\kappa(y)=s+x_G(x_G-u^3)$, $\kappa(z)=sx_G+p^2J$, $\kappa(u)=u$ (so that $\kappa$ maps the element $s$ of $Q$ to the variable $s$ of $G$), and $\kappa_p\colon Q[X]\to G$ denotes the extension of $\kappa$ with $X\mapsto p$.
--
--   The file constructs the following.
--
--   1. **The quadric inside $T$.** Since $ab\cdot cd-bd(bd+1)=bd(ac-bd-1)$, the assignment $x\mapsto ab$, $y\mapsto cd$, $z\mapsto bd$, $u\mapsto u$ defines a $\mathbb{C}$-algebra homomorphism $\lambda\colon Q\to T$. It is injective: the chart $T\to\operatorname{Frac}(Q)$ given by $a\mapsto1$, $b\mapsto x$, $c\mapsto z+1$, $d\mapsto z/x$, $u\mapsto u$ composes with $\lambda$ to the canonical embedding $Q\to\operatorname{Frac}(Q)$.
--   2. **Auxiliary elements.** In $T$ put
--   $$h=ab-u^3,\qquad C_1=c^2-b^2h,\qquad \alpha=a^2(1-2bd),\qquad \beta=d^2(3+2bd)+\alpha h.$$
--   Then
--   $$\lambda(s)=cd-ab\,h,\qquad \lambda(f)=C_1\,v,\qquad \lambda(g)=b^2\,v,\qquad \alpha\,C_1+\beta\,b^2=1,$$
--   and $v\neq0$.
--   3. **The modification $B$.** Let $B=T[X_0,X_1]/(X_0^2X_1-v)$, with structure map $j\colon T\to B$ and $\tau$, $V$ the classes of $X_0$, $X_1$. As $v\neq0$, $B$ is an integral domain; moreover $\tau\neq0$ and $\tau^2V=j(v)$.
--   4. **The pullback.** The $\mathbb{C}$-algebra homomorphism $\mathbb{C}[p,s,u,F,J]\to B$ with
--   $$p\mapsto\tau,\quad s\mapsto j(\lambda(s)),\quad u\mapsto j(u),\quad F\mapsto j(C_1)\,V,\quad J\mapsto j(b^2)\,V$$
--   sends the polynomials $x_G$, $s+x_G(x_G-u^3)$, $sx_G+p^2J$ to $j(\lambda(x))$, $j(\lambda(y))$, $j(\lambda(z))$ and kills $H_0$, so it induces a $\mathbb{C}$-algebra homomorphism $\Phi\colon G\to B$. It satisfies $\Phi\circ\kappa=j\circ\lambda$, and $\Phi\circ\kappa_p$ equals the injective map $Q[X]\to B$ that applies $\lambda$ to the coefficients and evaluates at $\tau$. Finally,
--   $$\Phi\colon G\to B\ \text{ is injective.}$$
--
--   Through $\Phi$ the degenerate hypersurface ring $G$ becomes a subring of the domain $B$, an affine modification over the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$: the variable $p$ becomes $\tau$, and $F$ and $J$ become $C_1V$ and $b^2V$, where $V=v/\tau^2$ in the fraction field. The Bézout identity $\alpha C_1+\beta b^2=1$ says that $C_1$ and $b^2$ generate the unit ideal of $T$. This embedding is what allows derivations of $G$ to be studied inside $B$, where the structure coming from $\mathrm{SL}_2$ is available.
--
--   **Formalization Note** The rings $T$, $Q$, $G$ are `Determinant.T`, `Quadric.R` and `Degeneration.G`; in `Determinant.Poly` the variables `X 0, X 1, X 2, X 3, X 4` are $a,d,b,c,u$, and in `Degeneration.P` they are $p,s,u,F,J$. Item 1 is `inclusion` ($\lambda$), `chart`, `chart_inclusion` and `inclusion_injective`; item 2 is `h`, `C₁`, `α`, `β`, `inclusion_s`, `inclusion_f`, `inclusion_g`, `certificate` and `v_ne_zero`; item 3 is `B = AffineModification.T T v` with its `IsDomain` instance (from `AffineModification.embedding_injective`), `j`, `τ`, `V`, `τ_ne_zero` and `equation`; item 4 is `eval` (with `eval_xp`, `eval_yp`, `eval_zp`, `eval_relation`), `pullback` ($\Phi$), `pullback_coefficientMap`, `base`, `base_injective`, `pullback_baseMap` and `pullback_injective`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Bundle.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Bundle.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Bundle
open MvPolynomial
open Determinant

def quadricEval : Quadric.Poly →ₐ[ℂ] T := aeval ![a*b,d*c,d*b,Determinant.u]
lemma quadricEval_relation : quadricEval Quadric.relation=0 := by
  simp only [Quadric.relation,quadricEval,aeval_X,map_sub,map_mul,map_add,map_one,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination b*d*determinant
def inclusion : Quadric.R →ₐ[ℂ] T := Ideal.Quotient.liftₐ _ quadricEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,quadricEval_relation,zero_mul])
@[simp] lemma inclusion_π (r : Quadric.Poly) : inclusion (Quadric.π r)=quadricEval r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma inclusion_x : inclusion Quadric.x=a*b := by simp [Quadric.x,quadricEval]
@[simp] lemma inclusion_y : inclusion Quadric.y=d*c := by simp [Quadric.y,quadricEval]
@[simp] lemma inclusion_z : inclusion Quadric.z=d*b := by simp [Quadric.z,quadricEval,Matrix.cons_val]
@[simp] lemma inclusion_u : inclusion Quadric.u=Determinant.u := by simp [Quadric.u,quadricEval,Matrix.cons_val]

abbrev K := FractionRing Quadric.R
def ι : Quadric.R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Quadric.R K
lemma ι_injective : Function.Injective ι := IsFractionRing.injective Quadric.R K
lemma x_ne_zero : ι Quadric.x ≠ 0 := by simpa using ι_injective.ne Quadric.x_ne_zero
def chartEval : Poly →ₐ[ℂ] K := aeval ![1,ι Quadric.z/ι Quadric.x,ι Quadric.x,
  ι Quadric.z+1,ι Quadric.u]
lemma chartEval_relation : chartEval relation=0 := by
  simp only [relation,chartEval,aeval_X,map_sub,map_mul,map_one,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [x_ne_zero]
  ring
def chart : T →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ chartEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,chartEval_relation,zero_mul])
@[simp] lemma chart_π (r : Poly) : chart (π r)=chartEval r := Ideal.Quotient.lift_mk _ _ _
lemma chart_inclusion : chart.comp inclusion=ι := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chart (inclusion Quadric.x)=ι Quadric.x
    rw [inclusion_x]
    simp [a,b,chartEval,Matrix.cons_val]
  · change chart (inclusion Quadric.y)=ι Quadric.y
    rw [inclusion_y]
    simp only [map_mul,d,c,chart_π,chartEval,aeval_X,Matrix.cons_val,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff x_ne_zero).mpr
    have he := congrArg ι Quadric.equation
    simp only [map_mul,map_add,map_one] at he
    linear_combination -he
  · change chart (inclusion Quadric.z)=ι Quadric.z
    simp [inclusion_z,d,b,chartEval,Matrix.cons_val,x_ne_zero]
  · change chart (inclusion Quadric.u)=ι Quadric.u
    simp [Determinant.u,chartEval,Matrix.cons_val]
lemma inclusion_injective : Function.Injective inclusion := by
  apply Function.Injective.of_comp (f := chart)
  rw [← AlgHom.coe_comp,chart_inclusion]
  exact ι_injective

def h : T := a*b-Determinant.u^3
def C₁ : T := c^2-b^2*h
def α : T := a^2*(1-2*b*d)
def β : T := d^2*(3+2*b*d)+α*h
lemma inclusion_s : inclusion Quadric.s=d*c-a*b*h := by
  simp only [Quadric.s,map_sub,map_mul,map_pow,inclusion_x,inclusion_y,inclusion_u,h]
lemma inclusion_f : inclusion Quadric.f=C₁*v := by
  simp only [Quadric.f,map_sub,map_pow,inclusion_x,inclusion_s,inclusion_u,C₁,h,v]
  linear_combination -(a*b-Determinant.u^3)*(a*c-b*d+1)*determinant
lemma inclusion_g : inclusion Quadric.g=b^2*v := by
  simp only [Quadric.g,map_sub,map_mul,inclusion_z,inclusion_s,inclusion_x,h,v]
  linear_combination -b*d*determinant
lemma certificate : α*C₁+β*b^2=1 := by
  simp only [α,β,C₁]
  linear_combination (1-2*b*d)*(a*c+b*d+1)*determinant
lemma v_ne_zero : v ≠ 0 := by
  intro hv
  have he : baseMap (X 1^3*X 3-X 1^2*X 0^3-X 2^2)=0 := by
    simpa [baseMap,baseValues,Matrix.cons_val,v] using hv
  have hp := baseMap_injective (he.trans (map_zero baseMap).symm)
  have hs := congrArg (MvPolynomial.eval (fun i : Fin 4 => if i=2 then (1:ℂ) else 0)) hp
  norm_num [Fin.ext_iff] at hs
abbrev B := AffineModification.T T v
instance : IsDomain B := Function.Injective.isDomain (AffineModification.embedding T v)
  (AffineModification.embedding_injective T v v_ne_zero)
def j : T →ₐ[ℂ] B := IsScalarTower.toAlgHom ℂ T B
def τ : B := AffineModification.τ T v
def V : B := AffineModification.V T v
lemma τ_ne_zero : τ ≠ 0 := by
  intro hz
  have he := congrArg (AffineModification.embedding T v) hz
  have hx : (RatFunc.X : AffineModification.K T)=0 := by
    simpa [τ,AffineModification.τ,AffineModification.eval,AffineModification.values] using he
  exact RatFunc.X_ne_zero hx
lemma equation : τ^2*V=j v := AffineModification.equation T v

def values : Fin 5 → B := ![τ,j (inclusion Quadric.s),j Determinant.u,j C₁*V,j (b^2)*V]
def eval : Degeneration.P →ₐ[ℂ] B := aeval values
lemma eval_xp : eval Degeneration.xp=j (inclusion Quadric.x) := by
  simp only [Degeneration.xp,eval,map_add,map_mul,map_pow,aeval_X,values,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hf := congrArg j inclusion_f
  simp only [Quadric.f,map_sub,map_pow,inclusion_u,map_mul] at hf
  linear_combination -hf + j C₁*equation
lemma eval_yp : eval Degeneration.yp=j (inclusion Quadric.y) := by
  simp only [Degeneration.yp,map_add,map_mul,map_sub,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [Quadric.s,map_sub,map_mul,map_pow,inclusion_u]
  ring
lemma eval_zp : eval Degeneration.zp=j (inclusion Quadric.z) := by
  simp only [Degeneration.zp,map_add,map_mul,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hg := congrArg j inclusion_g
  simp only [Quadric.g,map_sub,map_mul] at hg
  linear_combination -hg + j (b^2)*equation
lemma eval_relation : eval Degeneration.relation=0 := by
  have hi := congrArg eval Degeneration.identity
  simp only [map_sub,map_mul,map_add,map_pow,map_one,eval_xp,eval_yp,eval_zp] at hi
  have he := congrArg (j.comp inclusion) Quadric.equation
  simp only [AlgHom.comp_apply,map_mul,map_add,map_one] at he
  rw [sub_eq_zero.mpr he] at hi
  have hp : eval (X 0)≠0 := by simpa [eval,values] using τ_ne_zero
  exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 2 hp)
def pullback : Degeneration.G →ₐ[ℂ] B := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma pullback_π (r : Degeneration.P) : pullback (Degeneration.π r)=eval r :=
  Ideal.Quotient.lift_mk _ _ _
lemma pullback_coefficientMap : pullback.comp Degeneration.coefficientMap=j.comp inclusion := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change pullback (Degeneration.coefficientMap Quadric.x)=j (inclusion Quadric.x)
    rw [Degeneration.coefficientMap_x,Degeneration.x,pullback_π,eval_xp]
  · change pullback (Degeneration.coefficientMap Quadric.y)=j (inclusion Quadric.y)
    rw [Degeneration.coefficientMap_y,Degeneration.y,pullback_π,eval_yp]
  · change pullback (Degeneration.coefficientMap Quadric.z)=j (inclusion Quadric.z)
    rw [Degeneration.coefficientMap_z,Degeneration.z,pullback_π,eval_zp]
  · change pullback (Degeneration.coefficientMap Quadric.u)=j (inclusion Quadric.u)
    rw [Degeneration.coefficientMap_u,inclusion_u,Degeneration.u,pullback_π]
    simp [eval,values,Matrix.cons_val]
def base : Polynomial T →ₐ[ℂ] B := (AffineModification.baseMap T v).restrictScalars ℂ
lemma base_injective : Function.Injective base := by
  apply Function.Injective.of_comp (f := AffineModification.embedding T v)
  intro r s he
  change AffineModification.embedding T v (AffineModification.baseMap T v r)=
    AffineModification.embedding T v (AffineModification.baseMap T v s) at he
  have ht := AffineModification.embedding_baseMap T v
  simp only [← AlgHom.comp_apply,ht] at he
  exact AffineModification.baseEmbedding_injective T he
lemma pullback_baseMap : pullback.comp Degeneration.baseMap =
    base.comp (Polynomial.mapAlgHom inclusion) := by
  apply Polynomial.algHom_ext'
  · ext r
    simp only [AlgHom.comp_apply,Polynomial.CAlgHom_apply,Polynomial.coe_mapAlgHom,Polynomial.map_C]
    rw [Degeneration.baseMap_C]
    simp only [base,AlgHom.restrictScalars_apply,AffineModification.baseMap,Polynomial.aeval_C]
    change pullback (Degeneration.coefficientMap r)=j (inclusion r)
    exact DFunLike.congr_fun pullback_coefficientMap r
  · simp only [AlgHom.comp_apply,Polynomial.coe_mapAlgHom,Polynomial.map_X]
    rw [Degeneration.baseMap_X]
    simp only [base,AlgHom.restrictScalars_apply,AffineModification.baseMap,Polynomial.aeval_X]
    change pullback (Degeneration.π (X 0))=τ
    rw [pullback_π]
    simp [eval,values]
lemma pullback_injective : Function.Injective pullback := by
  apply Clearing.injective_of_clearing (S := Polynomial Quadric.R) pullback Degeneration.baseMap Polynomial.X
  · rw [pullback_baseMap]
    exact base_injective.comp (Polynomial.map_injective _ inclusion_injective)
  · rw [Degeneration.baseMap_X]; exact Degeneration.p_regular
  · exact Degeneration.clears
end ComplexCancellation.Bundle

end

end OAI


