-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
-- name    : OAI_Algebra_AffineCancellation_Degeneration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:13:43.063806+00:00
-- url     : https://prove2.me/theorems/2775e80b-d2cc-4a06-9d7d-be27cdb3f6aa
-- title:
--   The degeneration $G=\mathbb{C}[p,s,u,F,J]/(H_{\mathrm{top}})$ and its embedding over the quadric ring
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$ be the polynomial ring in five variables and define
--   $$\hat x=s^2+u^3+p^2F,\qquad \hat y=s+\hat x(\hat x-u^3),\qquad \hat z=s\hat x+p^2J,\qquad H_{\mathrm{top}}=\hat x^2F-(1+2s\hat x)J-p^2J^2 .$$
--   These polynomials satisfy the identity
--   $$\hat x\hat y-\hat z(\hat z+1)=p^2H_{\mathrm{top}} .$$
--   Let $G=P/(H_{\mathrm{top}})$, and write $p,s,u,F,J$ and $x,y,z$ for the images in $G$ of $p,s,u,F,J$ and of $\hat x,\hat y,\hat z$; then $xy=z(z+1)$ holds in $G$. Let $R=\mathbb{C}[x,y,z,u]/(xy-z(z+1))$ be the quadric ring, with its elements $s_R=y-x(x-u^3)$, $f=x-s_R^2-u^3$ and $g=z-s_Rx$; the same letters $x,y,z,u$ are used for the generators of $R$ and for their images in $G$. The file establishes the following.
--
--   1. **The coefficient map.** Because $xy=z(z+1)$ in $G$, there is a $\mathbb{C}$-algebra homomorphism $\kappa:R\to G$ sending $x,y,z,u$ to $x,y,z,u$. It satisfies
--   $$\kappa(s_R)=s,\qquad \kappa(f)=p^2F,\qquad \kappa(g)=p^2J .$$
--
--   2. **A rational embedding.** Let $K_0=\operatorname{Frac}(R)$ and let $K=K_0(\tau)$ be the field of rational functions in one variable $\tau$ over $K_0$. The substitution
--   $$p\mapsto\tau,\qquad s\mapsto s_R,\qquad u\mapsto u,\qquad F\mapsto\frac{f}{\tau^2},\qquad J\mapsto\frac{g}{\tau^2}$$
--   sends $\hat x,\hat y,\hat z$ to $x,y,z\in R\subset K$ and annihilates $H_{\mathrm{top}}$, hence induces a $\mathbb{C}$-algebra homomorphism $\varepsilon:G\to K$, and $\varepsilon\circ\kappa$ is the inclusion $R\subset K$. The map $\varepsilon$ is injective. Therefore $G$ is an integral domain, isomorphic to the subring $\mathbb{C}[\tau,s_R,u,f/\tau^2,g/\tau^2]$ of $K$.
--
--   3. **Clearing powers of $p$.** The element $p$ is a non-zero-divisor of $G$. Let $\beta:R[t]\to G$ be the homomorphism of polynomial rings that acts on coefficients by $\kappa$ and sends $t$ to $p$. Then $\varepsilon\circ\beta$ is the injective map $R[t]\to K_0(\tau)$ that includes the coefficients into $K_0$ and sends $t$ to $\tau$, and for every $w\in G$ there are $n\ge0$ and $h\in R[t]$ with $p^n w=\beta(h)$ (on generators, $n=0$ suffices for $p,s,u$ and $n=2$ for $F,J$).
--
--   The main algebra of the construction is $A=P/(H)$ with $H=\hat x^2F-(1+2s\hat x)J-p^2J^2-pu=H_{\mathrm{top}}-pu$, so $G$ is obtained from $A$ by deleting the term $pu$; for the weights $p\mapsto-1$, $s,u\mapsto0$, $F,J\mapsto2$, the polynomial $H_{\mathrm{top}}$ is exactly the top-weight part of $H$. The ring $G$ is the special fiber of a Rees-type deformation of $A$, and locally nilpotent derivations of $A$ are studied after transfer to $G$; the description $G\cong R[\tau,f/\tau^2,g/\tau^2]$ exhibits it as an algebra over the quadric ring $R$.
--
--   **Formalization Note** `P = MvPolynomial (Fin 5) ℂ` with `X 0, …, X 4` standing for p, s, u, F, J; the polynomials $\hat x,\hat y,\hat z,H_{\mathrm{top}}$ are `xp, yp, zp, relation`, and the displayed identity is `identity`. The map $\kappa$ is `coefficientMap : Quadric.R →ₐ[ℂ] G` (with `coefficientMap_s`, `coefficientMap_f`, `coefficientMap_g`); `K₀ = FractionRing Quadric.R`, `K = RatFunc K₀`, $\varepsilon$ is `embedding`, $\beta$ is `baseMap : Polynomial Quadric.R →ₐ[ℂ] G`, the clearing statement is `clears` (phrased with `Clearing.subalgebra`), `p_regular : IsLeftRegular p`, and the domain property of `G` is a type-class instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Degeneration.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Degeneration.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Degeneration
open MvPolynomial
abbrev P := MvPolynomial (Fin 5) ℂ
def xp : P := X 1^2+X 2^3+X 0^2*X 3
def yp : P := X 1+xp*(xp-X 2^3)
def zp : P := X 1*xp+X 0^2*X 4
def relation : P := xp^2*X 3-(1+2*X 1*xp)*X 4-X 0^2*X 4^2
lemma identity : xp*yp-zp*(zp+1)=X 0^2*relation := by
  simp only [yp,zp,relation,xp]
  ring
abbrev G := P ⧸ Ideal.span {relation}
def π : P →ₐ[ℂ] G := Ideal.Quotient.mkₐ ℂ _
def p : G := π (X 0)
def s : G := π (X 1)
def u : G := π (X 2)
def F : G := π (X 3)
def J : G := π (X 4)
def x : G := π xp
def y : G := π yp
def z : G := π zp
lemma relation_zero : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
lemma equation : x*y=z*(z+1) := by
  apply sub_eq_zero.mp
  have h := congrArg π identity
  simpa only [map_sub,map_mul,map_add,map_one,map_pow,relation_zero,mul_zero,x,y,z] using h

def coeffEval : Quadric.Poly →ₐ[ℂ] G := aeval ![x,y,z,u]
lemma coeffEval_relation : coeffEval Quadric.relation = 0 := by
  simpa [coeffEval,Quadric.relation,Matrix.cons_val] using sub_eq_zero.mpr equation
def coefficientMap : Quadric.R →ₐ[ℂ] G := Ideal.Quotient.liftₐ _ coeffEval (by
  intro r hr
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,coeffEval_relation,zero_mul])
@[simp] lemma coefficientMap_π (r : Quadric.Poly) : coefficientMap (Quadric.π r) = coeffEval r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma coefficientMap_x : coefficientMap Quadric.x=x := by simp [Quadric.x,coeffEval]
@[simp] lemma coefficientMap_y : coefficientMap Quadric.y=y := by simp [Quadric.y,coeffEval]
@[simp] lemma coefficientMap_z : coefficientMap Quadric.z=z := by simp [Quadric.z,coeffEval,Matrix.cons_val]
@[simp] lemma coefficientMap_u : coefficientMap Quadric.u=u := by simp [Quadric.u,coeffEval,Matrix.cons_val]
@[simp] lemma coefficientMap_s : coefficientMap Quadric.s=s := by
  simp only [Quadric.s,map_sub,map_mul,map_pow,coefficientMap_x,coefficientMap_y,coefficientMap_u]
  simp only [x,y,s,u,yp,map_add,map_mul,map_sub,map_pow]
  ring
lemma coefficientMap_f : coefficientMap Quadric.f=p^2*F := by
  simp only [Quadric.f,map_sub,map_pow,coefficientMap_x,coefficientMap_s,coefficientMap_u]
  simp only [x,xp,map_add,map_mul,map_pow,s,u,p,F]
  ring
lemma coefficientMap_g : coefficientMap Quadric.g=p^2*J := by
  simp only [Quadric.g,map_sub,map_mul,coefficientMap_z,coefficientMap_s,coefficientMap_x]
  simp only [z,zp,map_add,map_mul,map_pow,s,p,J,x]
  ring

abbrev K₀ := FractionRing Quadric.R
abbrev K := RatFunc K₀
def ι : Quadric.R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Quadric.R K
lemma τ_ne_zero : (RatFunc.X : K) ≠ 0 := RatFunc.X_ne_zero
def values : Fin 5 → K := ![RatFunc.X,ι Quadric.s,ι Quadric.u,
  ι Quadric.f/RatFunc.X^2,ι Quadric.g/RatFunc.X^2]
def eval : P →ₐ[ℂ] K := aeval values
lemma eval_xp : eval xp=ι Quadric.x := by
  simp only [xp,eval,map_add,map_mul,map_pow,aeval_X,values,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [τ_ne_zero]
  simp only [Quadric.f,map_sub,map_pow]
  ring
lemma eval_yp : eval yp=ι Quadric.y := by
  simp only [yp,map_add,map_mul,map_sub,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  simp only [Quadric.s,map_sub,map_mul,map_pow]
  ring
lemma eval_zp : eval zp=ι Quadric.z := by
  simp only [zp,map_add,map_mul,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [τ_ne_zero]
  simp only [Quadric.g,map_sub,map_mul]
  ring
lemma eval_relation : eval relation=0 := by
  have h := congrArg eval identity
  simp only [map_sub,map_mul,map_add,map_one,map_pow,eval_xp,eval_yp,eval_zp] at h
  have he : ι Quadric.x*ι Quadric.y-ι Quadric.z*(ι Quadric.z+1)=0 := by
    simpa only [map_mul,map_add,map_one] using congrArg ι Quadric.equation |> sub_eq_zero.mpr
  rw [he] at h
  have hp : eval (X 0) ≠ 0 := by simpa [eval,values] using τ_ne_zero
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 hp)

def embedding : G →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma embedding_π (r : P) : embedding (π r)=eval r := Ideal.Quotient.lift_mk _ _ _
lemma embedding_coefficientMap : embedding.comp coefficientMap=ι := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change embedding (coefficientMap Quadric.x)=ι Quadric.x
    rw [coefficientMap_x,x,embedding_π,eval_xp]
  · change embedding (coefficientMap Quadric.y)=ι Quadric.y
    rw [coefficientMap_y,y,embedding_π,eval_yp]
  · change embedding (coefficientMap Quadric.z)=ι Quadric.z
    rw [coefficientMap_z,z,embedding_π,eval_zp]
  · change embedding (coefficientMap Quadric.u)=ι Quadric.u
    rw [coefficientMap_u,u,embedding_π]
    simp [eval,values,Matrix.cons_val]
lemma p_regular : IsLeftRegular p := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 5 => if i=4 then (1:ℂ) else 0)) h
  norm_num [relation,xp,Fin.ext_iff] at he

def baseMap : Polynomial Quadric.R →ₐ[ℂ] G :=
  Polynomial.eval₂AlgHom coefficientMap p (fun _ => Commute.all _ _)
lemma baseMap_X : baseMap Polynomial.X=p := by simp [baseMap]
lemma baseMap_C (r : Quadric.R) : baseMap (Polynomial.C r)=coefficientMap r := by simp [baseMap]
def baseEmbedding : Polynomial Quadric.R →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Polynomial K₀) K).comp
    (Polynomial.mapAlgHom (IsScalarTower.toAlgHom ℂ Quadric.R K₀))
lemma baseEmbedding_injective : Function.Injective baseEmbedding :=
  (RatFunc.algebraMap_injective K₀).comp
    (Polynomial.map_injective _ (IsFractionRing.injective Quadric.R K₀))
lemma embedding_baseMap : embedding.comp baseMap=baseEmbedding := by
  apply Polynomial.algHom_ext'
  · ext r
    change embedding (baseMap (Polynomial.C r))=baseEmbedding (Polynomial.C r)
    rw [baseMap_C]
    have h := DFunLike.congr_fun embedding_coefficientMap r
    simpa [baseEmbedding,ι,IsScalarTower.algebraMap_apply Quadric.R K₀ K,
      RatFunc.algebraMap_eq_C] using h
  · change embedding (baseMap Polynomial.X)=baseEmbedding Polynomial.X
    rw [baseMap_X]
    change eval (X 0)=algebraMap (Polynomial K₀) K (Polynomial.map (algebraMap Quadric.R K₀) Polynomial.X)
    rw [Polynomial.map_X,RatFunc.algebraMap_X]
    simp [eval,values]
lemma clears : Clearing.subalgebra (S := Polynomial Quadric.R) baseMap Polynomial.X=⊤ := by
  apply Clearing.top_of_generators π (Ideal.Quotient.mkₐ_surjective ℂ _) _ _
  intro i
  fin_cases i
  · exact ⟨0,Polynomial.X,by simp [baseMap_X,p]⟩
  · exact ⟨0,Polynomial.C Quadric.s,by simp [baseMap_C,s]⟩
  · exact ⟨0,Polynomial.C Quadric.u,by simp [baseMap_C,u]⟩
  · exact ⟨2,Polynomial.C Quadric.f,by rw [baseMap_X,baseMap_C,coefficientMap_f]; rfl⟩
  · exact ⟨2,Polynomial.C Quadric.g,by rw [baseMap_X,baseMap_C,coefficientMap_g]; rfl⟩
lemma embedding_injective : Function.Injective embedding := by
  apply Clearing.injective_of_clearing (S := Polynomial Quadric.R) embedding baseMap Polynomial.X
  · rw [embedding_baseMap]; exact baseEmbedding_injective
  · rw [baseMap_X]; exact p_regular
  · exact clears
instance : IsDomain G := Function.Injective.isDomain embedding embedding_injective

end ComplexCancellation.Degeneration

end

end OAI


