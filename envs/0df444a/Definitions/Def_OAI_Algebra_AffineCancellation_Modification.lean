-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Modification
-- name    : OAI_Algebra_AffineCancellation_Modification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:49:26.543354+00:00
-- url     : https://prove2.me/theorems/af92e136-4e13-4d59-91c8-2312787e846b
-- title:
--   The affine modification $R[\tau,V]/(\tau^2V-v)$ and its embedding into $\operatorname{Frac}(R)(X)$
-- statement:
--   Let $R$ be an integral domain and $v\in R$. Write $P=R[X_0,X_1]$ for the polynomial ring in two variables over $R$.
--
--   1. **The modification.** Let
--   $$T_v=R[X_0,X_1]/(X_0^2X_1-v),$$
--   let $\pi\colon P\to T_v$ be the quotient map (an $R$-algebra homomorphism), and put $\tau=\pi(X_0)$, $V=\pi(X_1)$. Then $\tau^2V=v$ in $T_v$.
--   2. **A rational model.** Let $F=\operatorname{Frac}(R)$ and let $F(X)$ be the field of rational functions in one variable over $F$. The natural map $\gamma\colon R[X]\to F(X)$, which maps the coefficients into $F$, is injective and sends $X$ to $X$. The $R$-algebra homomorphism $P\to F(X)$ with $X_0\mapsto X$ and $X_1\mapsto v/X^2$ kills $X_0^2X_1-v$ and hence induces an $R$-algebra homomorphism
--   $$\varepsilon\colon T_v\to F(X),\qquad \varepsilon(\tau)=X,\quad \varepsilon(V)=\frac{v}{X^2}.$$
--   3. **The base map.** Let $\beta\colon R[X]\to T_v$ be evaluation at $\tau$, $\beta(q)=q(\tau)$. Then $\varepsilon\circ\beta=\gamma$.
--   4. **Clearing powers of $\tau$.** For every $r\in T_v$ there are $n\ge0$ and $q\in R[X]$ with $\tau^n r=q(\tau)$.
--   5. **Regularity and injectivity.** If $v\neq0$, then $\tau$ is a non-zero-divisor in $T_v$ and $\varepsilon$ is injective.
--
--   For $v\neq0$, item 5 identifies $T_v$ with the subring $R[X,v/X^2]$ of the field $F(X)$; in particular $T_v$ is an integral domain, obtained from $R[\tau]$ by adjoining the fraction $v/\tau^2$. Items 3 and 4 are the inputs of a denominator-clearing argument: because every element of $T_v$ becomes a polynomial in $\tau$ after multiplication by a power of the non-zero-divisor $\tau$, a homomorphism out of $T_v$ is injective as soon as its composite with $\beta$ is. The construction is used with $R$ the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$.
--
--   **Formalization Note** `P R`, `rel R v`, `T R v`, `π`, `τ`, `V` are as above and item 1 is `equation`. In item 2, `K R` is `RatFunc (FractionRing R)`, the map $\gamma$ is `baseEmbedding` (with `baseEmbedding_injective` and `baseEmbedding_X`), and $\varepsilon$ is `embedding`, induced by `eval = aeval (values R v)` via `eval_rel`. Item 3 is `baseMap` with `embedding_baseMap`; item 4 is `clears`, phrased as membership in `Clearing.subalgebra (baseMap R v) X`; item 5 is `τ_regular` (left regularity) and `embedding_injective`. Items 1 and 4 are proved for an arbitrary commutative ring `R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Modification.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Modification.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.AffineModification
open MvPolynomial
variable (R : Type*) [CommRing R] [IsDomain R] (v : R)

abbrev P := MvPolynomial (Fin 2) R
def rel : P R := X 0 ^ 2 * X 1 - C v
abbrev T := P R ⧸ Ideal.span {rel R v}
def π : P R →ₐ[R] T R v := Ideal.Quotient.mkₐ R _
def τ : T R v := π R v (X 0)
def V : T R v := π R v (X 1)

omit [IsDomain R] in
lemma equation : τ R v ^ 2 * V R v = algebraMap R (T R v) v := by
  have h : π R v (rel R v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply sub_eq_zero.mp
  simpa only [rel,map_sub,map_mul,map_pow,τ,V,AlgHom.commutes, MvPolynomial.C_eq_algebraMap] using h

abbrev F := FractionRing R
abbrev K := RatFunc (F R)
def baseEmbedding : Polynomial R →ₐ[R] K R :=
  (IsScalarTower.toAlgHom R (Polynomial (F R)) (K R)).comp
    (Polynomial.mapAlgHom (IsScalarTower.toAlgHom R R (F R)))

lemma baseEmbedding_injective : Function.Injective (baseEmbedding R) :=
  (RatFunc.algebraMap_injective (F R)).comp
    (Polynomial.map_injective _ (IsFractionRing.injective R (F R)))

lemma baseEmbedding_X : baseEmbedding R Polynomial.X = RatFunc.X := by
  change algebraMap (Polynomial (F R)) (K R) (Polynomial.map (algebraMap R (F R)) Polynomial.X) = _
  rw [Polynomial.map_X,RatFunc.algebraMap_X]

lemma X_nonzero : (RatFunc.X : K R) ≠ 0 := RatFunc.X_ne_zero

def values : Fin 2 → K R := ![RatFunc.X, algebraMap R (K R) v / RatFunc.X^2]
def eval : P R →ₐ[R] K R := aeval (values R v)
lemma eval_rel : eval R v (rel R v) = 0 := by
  simp only [rel,eval,map_sub,map_mul,map_pow,aeval_X,aeval_C,values,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [X_nonzero R]
  ring

def embedding : T R v →ₐ[R] K R := Ideal.Quotient.liftₐ _ (eval R v) (by
  intro r hr
  obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_rel,zero_mul])

@[simp] lemma embedding_π (r : P R) : embedding R v (π R v r) = eval R v r :=
  Ideal.Quotient.lift_mk _ _ _

def baseMap : Polynomial R →ₐ[R] T R v := Polynomial.aeval (τ R v)
omit [IsDomain R] in
lemma baseMap_X : baseMap R v Polynomial.X = τ R v := Polynomial.aeval_X _

lemma embedding_baseMap : (embedding R v).comp (baseMap R v) = baseEmbedding R := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,baseMap_X,baseEmbedding_X,τ,embedding_π,eval,aeval_X]
  rfl

lemma τ_regular (hv : v ≠ 0) : IsLeftRegular (τ R v) := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun _ : Fin 2 => (0 : R))) h
  simp [rel,hv] at he

omit [IsDomain R] in
lemma clears (r : T R v) : r ∈ Clearing.subalgebra (baseMap R v) Polynomial.X := by
  have ht : Clearing.subalgebra (baseMap R v) Polynomial.X = ⊤ := by
    apply Clearing.top_of_generators (π R v) (Ideal.Quotient.mkₐ_surjective R _) _ _
    intro i
    fin_cases i
    · exact ⟨0,Polynomial.X,by simp [baseMap_X,τ]⟩
    · refine ⟨2,Polynomial.C v,?_⟩
      rw [baseMap_X]
      change τ R v^2 * V R v = _
      simpa only [baseMap,Polynomial.aeval_C] using equation R v
  rw [ht]
  trivial

lemma embedding_injective (hv : v ≠ 0) : Function.Injective (embedding R v) := by
  apply Clearing.injective_of_clearing (embedding R v) (baseMap R v) Polynomial.X
  · rw [embedding_baseMap]; exact baseEmbedding_injective R
  · rw [baseMap_X]; exact τ_regular R v hv
  · exact top_unique (fun r _ => clears R v r)

end ComplexCancellation.AffineModification

end

end OAI


