-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
-- name    : OAI_Algebra_AffineCancellation_Determinant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:06:42.096844+00:00
-- url     : https://prove2.me/theorems/fa9a48c2-f6ea-4c8e-9d83-afc93cb95358
-- title:
--   The ring $\mathbb{C}[a,b,c,d,u]/(ac-bd-1)$ is a domain embedded in a rational function field
-- statement:
--   Let $\mathbb{C}[X_0,\dots,X_4]$, $\mathcal B=\mathbb{C}[Y_0,Y_1,Y_2,Y_3]$ and $\mathcal C=\mathbb{C}[Z_0,Z_1,Z_2]$ be polynomial rings over $\mathbb{C}$. Let $K_0=\operatorname{Frac}(\mathcal C)$, and let $K=K_0(y)$ be the field of rational functions in one variable $y$ over $K_0$.
--
--   1. **Regularity lemma.** If $R$ is an integral domain, $p\in R$ is prime and $p\nmid h$, then the class of $p$ is a non-zero-divisor in $R/(h)$.
--
--   2. **The determinant ring.** Let
--   $$\mathcal T=\mathbb{C}[X_0,\dots,X_4]/(X_0X_3-X_2X_1-1),$$
--   with quotient map $\pi$, and put $a=\pi(X_0)$, $d=\pi(X_1)$, $b=\pi(X_2)$, $c=\pi(X_3)$, $u=\pi(X_4)$. Then $ac-bd=1$, i.e. $\det\begin{pmatrix}a&b\\d&c\end{pmatrix}=1$, so $\mathcal T$ is the coordinate ring of $\mathrm{SL}_2(\mathbb{C})\times\mathbb{C}$. The file also introduces the element $v=a^3b-a^2u^3-d^2\in\mathcal T$ for later use.
--
--   3. **Base embedding.** $\varepsilon:\mathcal B\to K$ is the $\mathbb{C}$-algebra homomorphism with $\varepsilon(Y_0)=y$ and $\varepsilon(Y_{i+1})=Z_i$ for $i=0,1,2$. It is injective.
--
--   4. **Embedding of $\mathcal T$.** The $\mathbb{C}$-algebra homomorphism $\mathbb{C}[X_0,\dots,X_4]\to K$ given by $X_0\mapsto Z_0$, $X_1\mapsto Z_1$, $X_2\mapsto Z_2$, $X_3\mapsto(1+Z_1Z_2)/Z_0$, $X_4\mapsto y$ is well defined because $Z_0\neq0$, and it kills $X_0X_3-X_2X_1-1$. It therefore induces
--   $$\iota:\mathcal T\to K,\qquad (a,d,b,c,u)\mapsto\Bigl(Z_0,\ Z_1,\ Z_2,\ \frac{1+Z_1Z_2}{Z_0},\ y\Bigr).$$
--
--   5. **Base map.** $\beta:\mathcal B\to\mathcal T$ is the $\mathbb{C}$-algebra homomorphism $(Y_0,Y_1,Y_2,Y_3)\mapsto(u,a,d,b)$. It satisfies $\iota\circ\beta=\varepsilon$ and is therefore injective. Moreover $a$ is a non-zero-divisor of $\mathcal T$.
--
--   6. **Clearing powers of $a$.** For every $r\in\mathcal T$ there are $n\in\mathbb{N}$ and $g\in\mathcal B$ with $a^nr=\beta(g)$. For the generator $c$ this is the identity $ac=1+bd$.
--
--   7. **Integral domain.** $\iota$ is injective, and consequently $\mathcal T$ is an integral domain.
--
--   Items 5 and 6 say that after inverting $a$ the ring $\mathcal T$ becomes the localization $\mathbb{C}[u,a,d,b][a^{-1}]$ of a polynomial ring in four variables. The ring $\mathcal T$ is the setting for later rigidity results about locally nilpotent derivations involving the element $v$.
--
--   **Formalization Note** The rings are `Poly = MvPolynomial (Fin 5) ℂ`, `Base`, `Coeff`, `K₀ = FractionRing Coeff` and `K = RatFunc K₀`, and $\mathcal T$ is called `T` in Lean. In Lean $\varepsilon$ is `baseEmbedding`, built with `MvPolynomial.finSuccEquiv`, $\iota$ is `embedding` and $\beta$ is `baseMap`. The domain property is the instance `IsDomain T`, obtained from `Function.Injective.isDomain`. Non-zero-divisors are expressed with `IsLeftRegular`, and `regular_quotient_of_prime` repeats the lemma of the same name from the cylinder file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Determinant.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Determinant.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
open MvPolynomial

lemma regular_quotient_of_prime {R : Type*} [CommRing R] [IsDomain R]
    {p h : R} (hp : Prime p) (hph : ¬p ∣ h) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {h}) p) := by
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro q hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
  obtain ⟨c, hc⟩ := hq
  have hpc : p ∣ c := (hp.dvd_or_dvd (show p ∣ h * c by rw [← hc]; exact dvd_mul_right _ _)).resolve_left hph
  obtain ⟨d, rfl⟩ := hpc
  have hr : r = h * d := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination hc
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hr]
  exact dvd_mul_right _ _

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Base := MvPolynomial (Fin 4) ℂ
abbrev Coeff := MvPolynomial (Fin 3) ℂ
abbrev K₀ := FractionRing Coeff
abbrev K := RatFunc K₀

def relation : Poly := X 0 * X 3 - X 2 * X 1 - 1
abbrev T := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] T := Ideal.Quotient.mkₐ ℂ _
def a : T := π (X 0)
def d : T := π (X 1)
def b : T := π (X 2)
def c : T := π (X 3)
def u : T := π (X 4)
def v : T := a ^ 3 * b - a ^ 2 * u ^ 3 - d ^ 2

def baseEmbedding : Base →ₐ[ℂ] K :=
  (IsScalarTower.toAlgHom ℂ (Polynomial K₀) K).comp
    ((Polynomial.mapAlgHom (IsScalarTower.toAlgHom ℂ Coeff K₀)).comp
      (finSuccEquiv ℂ 3).toAlgHom)

lemma baseEmbedding_injective : Function.Injective baseEmbedding :=
  (RatFunc.algebraMap_injective K₀).comp
    ((Polynomial.map_injective _ (IsFractionRing.injective Coeff K₀)).comp
      (finSuccEquiv ℂ 3).injective)

def targetValues : Fin 5 → K := ![baseEmbedding (X 1), baseEmbedding (X 2),
  baseEmbedding (X 3), (1 + baseEmbedding (X 3) * baseEmbedding (X 2)) /
    baseEmbedding (X 1), baseEmbedding (X 0)]

def eval : Poly →ₐ[ℂ] K := aeval targetValues

lemma a_field_nonzero : baseEmbedding (X 1) ≠ 0 := by
  intro h
  have hz := baseEmbedding_injective (h.trans (map_zero _).symm)
  exact X_ne_zero (1 : Fin 4) hz

lemma eval_relation : eval relation = 0 := by
  simp only [eval, relation, map_sub, map_mul, map_one, aeval_X]
  simp only [targetValues, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  field_simp [a_field_nonzero]
  ring

def embedding : T →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul, eval_relation, zero_mul])

@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r :=
  Ideal.Quotient.lift_mk _ _ _

lemma determinant : a*c - b*d = 1 := by
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation, map_sub, map_mul, map_one, a, b, c, d, sub_eq_zero] using h

lemma a_regular : IsLeftRegular a := by
  apply regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun _ : Fin 5 => (0 : ℂ))) h
  simp [relation] at he

def baseValues : Fin 4 → T := ![u,a,d,b]
def baseMap : Base →ₐ[ℂ] T := aeval baseValues

lemma embedding_baseMap (r : Base) : embedding (baseMap r) = baseEmbedding r := by
  have he : embedding.comp baseMap = baseEmbedding := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [baseMap, baseValues, u, a, d, b, embedding_π, eval, targetValues]
  exact DFunLike.congr_fun he r

lemma baseMap_injective : Function.Injective baseMap := by
  intro r s hrs
  apply baseEmbedding_injective
  rw [← embedding_baseMap, ← embedding_baseMap, hrs]

lemma clears_generator (i : Fin 5) :
    ∃ n : ℕ, ∃ f : Base, a^n * π (X i) = baseMap f := by
  fin_cases i
  · exact ⟨0, X 1, by simp [baseMap, baseValues, a]⟩
  · exact ⟨0, X 2, by simp [baseMap, baseValues, d]⟩
  · exact ⟨0, X 3, by simp [baseMap, baseValues, b]⟩
  · refine ⟨1, 1 + X 3 * X 2, ?_⟩
    simp only [pow_one, map_add, map_one, map_mul, baseMap, aeval_X]
    change a*c = 1+b*d
    linear_combination determinant
  · exact ⟨0, X 0, by simp [baseMap, baseValues, u]⟩

lemma clears (r : T) : ∃ n : ℕ, ∃ f : Base, a^n * r = baseMap f := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (Ideal.span {relation}) r
  change ∃ n : ℕ, ∃ f : Base, a^n * π r = baseMap f
  induction r using MvPolynomial.induction_on with
  | C z => refine ⟨0, C z, ?_⟩; simp [baseMap, π]
  | add r s hr hs =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := hs
    refine ⟨n+m, X 1 ^ m * f + X 1 ^ n * g, ?_⟩
    simp only [map_add, map_mul, map_pow]
    have hb : baseMap (X 1) = a := by simp [baseMap, baseValues]
    rw [hb, ← hf, ← hg, pow_add]
    ring
  | mul_X r i hr =>
    obtain ⟨n, f, hf⟩ := hr
    obtain ⟨m, g, hg⟩ := clears_generator i
    refine ⟨n+m, f*g, ?_⟩
    rw [map_mul, map_mul, ← hf, ← hg, pow_add]
    ring

lemma embedding_injective : Function.Injective embedding := by
  apply (injective_iff_map_eq_zero embedding).mpr
  intro r hr
  obtain ⟨n, f, hf⟩ := clears r
  have h : baseEmbedding f = 0 := by
    rw [← embedding_baseMap, ← hf, map_mul, hr, mul_zero]
  have hfzero : f = 0 := baseEmbedding_injective (h.trans (map_zero _).symm)
  rw [hfzero, map_zero] at hf
  exact isLeftRegular_iff_right_eq_zero_of_mul.mp (a_regular.pow n) r hf

instance : IsDomain T := Function.Injective.isDomain embedding embedding_injective

end ComplexCancellation.Determinant

end

end OAI


