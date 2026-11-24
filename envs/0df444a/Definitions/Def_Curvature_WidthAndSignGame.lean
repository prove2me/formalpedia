-- Prove2me | Definitions.Def_Curvature_WidthAndSignGame
-- name    : Curvature_WidthAndSignGame
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:08:47.659427+00:00
-- url     : https://prove2.me/theorems/b6324809-3898-4b51-8a39-8f0367bcffdd
-- title:
--   Maximal subexponential mean width, ellipsoids and boxes, and random sign vectors
-- statement:
--   This file defines the maximal subexponential mean width and the sign-vector laws used to lower-bound it. Let $E$ be a finite-dimensional real inner product space and let $\mathcal K\subseteq E$ be nonempty and bounded. Its support function is $\sigma_{\mathcal K}(z)\coloneqq\sup_{w\in\mathcal K}\langle w,z\rangle$. A Borel probability measure $\mu$ on $E$ is an admissible width law if the identity map is $\mu$-integrable with mean zero and, for every $v\in E$ with $\lVert v\rVert\le1$, the function $z\mapsto\exp|\langle v,z\rangle|$ is $\mu$-integrable with integral at most $2$. For a random vector $Z$ with law $\mu$, the last condition is equivalent to $\lVert\langle v,Z\rangle\rVert_{\psi_1}\le1$, where $\lVert X\rVert_{\psi_1}\coloneqq\inf\{s>0:\mathbb E\exp(|X|/s)\le2\}$. The width is
--
--   $$
--   \omega_{\psi_1}(\mathcal K)\coloneqq\sup\Bigl\{\int\sigma_{\mathcal K}\,d\mu:\mu\text{ is an admissible width law}\Bigr\},
--   $$
--
--   so the supremum over random vectors $Z$ in the paper is taken over their laws. The set of these integrals contains $0$ and is bounded above, so its supremum is a real number.
--
--   The file also defines the box $c+U\{z:|z_i|\le a_i\text{ for all }i\}$ and the ellipsoid $c+U\{z:\sum_i(z_i/a_i)^2\le1\}$ of dimension $r$, where $c\in E$, $U$ is a linear isometry from $\mathbb R^r$ into $E$ and $a\in(0,\infty)^r$. Let $E$ be finite-dimensional and $e_1,\ldots,e_r\in E$ orthonormal. The law of $\frac14\sum_i\sigma_ie_i$ with independent uniform signs $\sigma_i\in\{-1,1\}$ is admissible, so $\omega_{\psi_1}(\mathcal K)\ge\frac14\sum_ia_i$ whenever $\mathcal K\subseteq E$ is bounded and contains every point $c+\sum_ia_i\sigma_ie_i$. The width defined in Section 2.2 enters the regret bounds on general domains and the minimax value on the standard domains. Theorem 2 gives the bound on the Euclidean ball in terms of its dimension. In the Lean proof, these sign vectors give a lower bound on the width of domains with orthogonal axes.
-- source:
--   arXiv:2611.27572v1, Section 2.2, p. 5; Appendix A.4.2, pp. 31–32; fixed-axis width comparison in Appendix B.7, pp. 40–41. https://arxiv.org/html/2611.27572v1#A2.SS7

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Logic.Equiv.Bool
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Curvature.SignGame

variable {I : Type*} [DecidableEq I]

def sign (b : Bool) : ℝ := if b then 1 else -1

def flip (i : I) : Equiv.Perm (I → Bool) :=
  Equiv.piCongrRight fun j => if j = i then Equiv.boolNot else Equiv.refl Bool

@[simp] theorem flip_same (i : I) (σ : I → Bool) : flip i σ i = !(σ i) := by
  simp [flip, Equiv.boolNot]

theorem flip_other {i j : I} (hne : j ≠ i) (σ : I → Bool) : flip i σ j = σ j := by
  simp [flip, hne]

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

variable [Fintype I]

theorem expect_pair (i : I) (f : (I → Bool) → ℝ) :
    𝔼 σ, f σ = 𝔼 σ, (f σ + f (flip i σ)) / 2 := by
  have he := Fintype.expect_equiv (flip i) (fun σ => f (flip i σ)) f (fun _ => rfl)
  rw [← Finset.expect_div, Finset.expect_add_distrib, he]
  ring


end Curvature.SignGame

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def widthSupport (K : Set E) (z : E) : ℝ := ⨆ w : K, ⟪w.val,z⟫_ℝ

variable [MeasurableSpace E] [BorelSpace E]

structure AdmissibleWidthLaw (μ : Measure E) : Prop where
  prob : IsProbabilityMeasure μ
  integrable : Integrable (fun z : E => z) μ
  centered : (∫ z : E, z ∂μ) = 0
  exp_integrable : ∀ v : E, ‖v‖ ≤ 1 → Integrable (fun z : E => Real.exp |⟪v,z⟫_ℝ|) μ
  exp_le : ∀ v : E, ‖v‖ ≤ 1 → (∫ z : E, Real.exp |⟪v,z⟫_ℝ| ∂μ) ≤ 2

def widthValues (K : Set E) : Set ℝ :=
  {s | ∃ μ : Measure E, AdmissibleWidthLaw μ ∧ (∫ z, widthSupport K z ∂μ) = s}

def subexponentialWidth (K : Set E) : ℝ := sSup (widthValues K)

theorem widthLaw_dirac_zero [CompleteSpace E] : AdmissibleWidthLaw (Measure.dirac (0 : E)) := by
  refine ⟨inferInstance, integrable_dirac (by simp), by simp, ?_, ?_⟩
  · exact fun _ _ => integrable_dirac (by simp)
  · intro v _
    norm_num

theorem zero_mem_widthValues [CompleteSpace E] (K : Set E) (hn : K.Nonempty) : 0 ∈ widthValues K := by
  let : Nonempty K := hn.to_subtype
  exact ⟨Measure.dirac (0:E), widthLaw_dirac_zero, by simp [widthSupport]⟩

theorem width_le_of_forall [CompleteSpace E] (K : Set E) (hn : K.Nonempty) {B : ℝ}
    (h : ∀ μ : Measure E, AdmissibleWidthLaw μ → (∫ z, widthSupport K z ∂μ) ≤ B) :
    subexponentialWidth K ≤ B := by
  apply csSup_le ⟨0, zero_mem_widthValues K hn⟩
  rintro s ⟨μ, hμ, rfl⟩
  exact h μ hμ

omit [BorelSpace E] in
theorem le_width_of_law (K : Set E) (hb : BddAbove (widthValues K)) {μ : Measure E}
    (hμ : AdmissibleWidthLaw μ) :
    (∫ z, widthSupport K z ∂μ) ≤ subexponentialWidth K :=
  le_csSup hb ⟨μ, hμ, rfl⟩

theorem widthSupport_integrable (K : Set E) (hn : K.Nonempty) (hb : Bornology.IsBounded K)
    {μ : Measure E} (hμ : AdmissibleWidthLaw μ) : Integrable (widthSupport K) μ := by
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_le
  obtain ⟨w₀, hw₀⟩ := hn
  let : Nonempty K := ⟨⟨w₀,hw₀⟩⟩
  have hnorm (z : E) (w : K) : |⟪w.val,z⟫_ℝ| ≤ R*‖z‖ :=
    (abs_real_inner_le_norm w.val z).trans (mul_le_mul_of_nonneg_right (hbound w.val w.prop) (norm_nonneg _))
  have hsup (z : E) : BddAbove (Set.range (fun w : K => ⟪w.val,z⟫_ℝ)) :=
    ⟨R*‖z‖, by rintro _ ⟨w,rfl⟩; exact (le_abs_self _).trans (hnorm z w)⟩
  have hm : Measurable (widthSupport K) := by
    apply LowerSemicontinuous.measurable
    exact lowerSemicontinuous_ciSup hsup fun w => (continuous_const.inner continuous_id).lowerSemicontinuous
  apply (hμ.integrable.norm.const_mul R).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp (hnorm z ⟨w₀,hw₀⟩)).1.trans (le_ciSup (f := fun w : K => ⟪w.val,z⟫_ℝ) (hsup z) ⟨w₀,hw₀⟩)
  · exact ciSup_le fun w => (le_abs_self _).trans (hnorm z w)

omit [BorelSpace E] in
theorem AdmissibleWidthLaw.firstMoment {μ : Measure E} (hμ : AdmissibleWidthLaw μ)
    (v : E) (hv : ‖v‖ ≤ 1) : (∫ z, |⟪v,z⟫_ℝ| ∂μ) ≤ 1 := by
  let := hμ.prob
  have hi := (hμ.integrable.const_inner (𝕜 := ℝ) v).abs
  have h := integral_mono (μ := μ) (hi.add (integrable_const 1)) (hμ.exp_integrable v hv)
    (fun z => Real.add_one_le_exp |⟪v,z⟫_ℝ|)
  change (∫ z : E, |⟪v,z⟫_ℝ| + 1 ∂μ) ≤ _ at h
  rw [integral_add hi (integrable_const 1), integral_const, probReal_univ, one_smul] at h
  linarith [hμ.exp_le v hv]


theorem widthValues_bddAbove [FiniteDimensional ℝ E] (K : Set E) (hn : K.Nonempty)
    (hb : Bornology.IsBounded K) : BddAbove (widthValues K) := by
  obtain ⟨R,hR,hKR⟩ := hb.exists_pos_norm_le
  let d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  have hnrm (z : E) : ‖z‖ ≤ ∑ i : Fin d, |⟪b i,z⟫_ℝ| := by
    calc
      ‖z‖ = ‖∑ i, b.repr z i • b i‖ := by rw [b.sum_repr]
      _ ≤ _ := (norm_sum_le ..).trans_eq (by simp [d, norm_smul, OrthonormalBasis.repr_apply_apply])
  let : Nonempty K := hn.to_subtype
  have hs (z : E) : widthSupport K z ≤ R * ∑ i : Fin d, |⟪b i,z⟫_ℝ| := by
    apply ciSup_le
    intro w
    exact (real_inner_le_norm w.val z).trans (mul_le_mul (hKR _ w.prop) (hnrm z) (norm_nonneg _) hR.le)
  refine ⟨R * d, ?_⟩
  rintro _ ⟨μ,hμ,rfl⟩
  have hi (i : Fin d) : Integrable (fun z : E => |⟪b i,z⟫_ℝ|) μ :=
    (hμ.integrable.const_inner (𝕜 := ℝ) (b i)).abs
  have h := integral_mono (widthSupport_integrable K hn hb hμ)
    ((integrable_finsetSum _ (fun i _ => hi i)).const_mul R) hs
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hR.le
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin d) _ => hμ.firstMoment (b i) (by simp))

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
namespace Curvature.Coordinate

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Axes (r : ℕ) := EuclideanSpace ℝ (Fin r)

def position (c : E) (U : Axes r →ₗᵢ[ℝ] E) (z : Axes r) : E := c + U z


def box (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) : Set E :=
  position c U '' {z : Axes r | ∀ i, |z i| ≤ a i}

def ellipsoid (c : E) (U : Axes r →ₗᵢ[ℝ] E) (a : Fin r → ℝ) : Set E :=
  position c U '' {z : Axes r | ∑ i, (z i / a i)^2 ≤ 1}


end Curvature.Coordinate

end
end

section
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory
namespace Curvature

variable {r : ℕ}

private theorem sign_mgf (c : Fin r → ℝ) (s : Finset (Fin r)) :
    (𝔼 σ : Fin r → Bool, Real.exp (∑ i ∈ s, c i * SignGame.sign (σ i))) =
      ∏ i ∈ s, Real.cosh (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [SignGame.expect_pair i, Finset.prod_insert hi, ← ih, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro σ _
    have hflip : (∑ j ∈ s, c j * SignGame.sign (SignGame.flip i σ j)) =
        ∑ j ∈ s, c j * SignGame.sign (σ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [SignGame.flip_other (by rintro rfl; exact hi hj)]
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hflip, SignGame.flip_same]
    cases σ i <;> simp [SignGame.sign, Real.exp_add, Real.cosh_eq] <;> ring

private theorem sign_mgf_le (c : Fin r → ℝ) :
    (𝔼 σ : Fin r → Bool, Real.exp (∑ i, c i * SignGame.sign (σ i))) ≤
      Real.exp (∑ i, (c i)^2/2) := by
  rw [sign_mgf, Real.exp_sum]
  apply Finset.prod_le_prod
  · exact fun i _ => (Real.cosh_pos _).le
  · exact fun i _ => Real.cosh_le_exp_half_sq _

theorem exp_abs_quarter (x : ℝ) :
    Real.exp (|x|/4) ≤ 1/2 + (Real.exp (x/2) + Real.exp (-(x/2)))/2 := by
  have h (x : ℝ) : 2*Real.exp (x/4) ≤ 1 + Real.exp (x/2) := by
    have he : Real.exp (x/2) = Real.exp (x/4)*Real.exp (x/4) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [sq_nonneg (Real.exp (x/4)-1)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [h x, (Real.exp_pos (-(x/2))).le]
  · rw [abs_of_nonpos hx]
    have hh := h (-x)
    simp only [neg_div] at hh ⊢
    linarith [hh, (Real.exp_pos (x/2)).le]

theorem sign_exp_abs_le (b : Fin r → ℝ) (hb : ∑ i, (b i)^2 ≤ 1) :
    (𝔼 σ : Fin r → Bool, Real.exp (|∑ i, b i * SignGame.sign (σ i)| / 4)) ≤ 2 := by
  let X := fun σ : Fin r → Bool => ∑ i, b i*SignGame.sign (σ i)
  have hg (sgn : ℝ) (hs : sgn^2 = 1) :
      (𝔼 σ : Fin r → Bool, Real.exp (sgn * X σ / 2)) ≤ 3/2 := by
    have he := sign_mgf_le (fun i => sgn * b i / 2)
    have eq₁ (σ : Fin r → Bool) : (∑ i, (sgn*b i/2) * SignGame.sign (σ i)) = sgn*X σ/2 := by
      simp only [X, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have eq₂ : (∑ i, (sgn*b i/2)^2/2) = (∑ i, (b i)^2)/8 := by
      simp only [div_pow, mul_pow, hs, one_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [eq₁, eq₂] at he
    refine he.trans ((Real.exp_le_exp.mpr (show (∑ i, (b i)^2)/8 ≤ 1/8 by linarith)).trans ?_)
    exact (Real.exp_bound_div_one_sub_of_interval (x := 1/8) (by norm_num) (by norm_num)).trans (by norm_num)
  have hp := hg 1 (by norm_num)
  have hn := hg (-1) (by norm_num)
  simp only [one_mul, neg_one_mul, neg_div] at hp hn
  have hpoint := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => exp_abs_quarter (X σ))
  simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.expect_div] at hpoint
  exact hpoint.trans (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

def signVector (e : Fin r → E) (σ : Fin r → Bool) : E :=
  (1/4 : ℝ) • ∑ i, SignGame.sign (σ i) • e i

section UniformLaw
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

def uniformImageLaw (Z : Ω → E) : Measure E :=
  (PMF.uniformOfFintype Ω).toMeasure.map Z

omit [CompleteSpace E] [BorelSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem uniformImage_integralRaw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Z : Ω → E) (f : E → F) (hf : AEStronglyMeasurable f (uniformImageLaw Z)) :
    (∫ z, f z ∂uniformImageLaw Z) = (Fintype.card Ω : ℝ)⁻¹ • ∑ σ, f (Z σ) := by
  rw [uniformImageLaw, integral_map (measurable_of_finite Z).aemeasurable hf, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← Finset.smul_sum]

omit [CompleteSpace E] [BorelSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem uniformImage_integral (Z : Ω → E) (f : E → ℝ) (hf : AEStronglyMeasurable f (uniformImageLaw Z)) :
    (∫ z, f z ∂uniformImageLaw Z) = 𝔼 σ, f (Z σ) := by
  rw [uniformImage_integralRaw Z f hf]
  simp [Finset.expect, NNRat.smul_def]

omit [CompleteSpace E] [BorelSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem uniformImage_integrable {F : Type*} [NormedAddCommGroup F]
    (Z : Ω → E) (f : E → F) (hf : AEStronglyMeasurable f (uniformImageLaw Z)) :
    Integrable f (uniformImageLaw Z) :=
  (integrable_map_measure hf (measurable_of_finite Z).aemeasurable).mpr .of_finite

end UniformLaw

abbrev signVectorLaw (e : Fin r → E) : Measure E := uniformImageLaw (signVector e)

theorem signVector_admissible [FiniteDimensional ℝ E] (e : Fin r → E) (he : Orthonormal ℝ e) :
    AdmissibleWidthLaw (signVectorLaw e) := by
  have hm : Measurable (signVector e) := measurable_of_finite _
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable,
    uniformImage_integrable _ _ aestronglyMeasurable_id, ?_, ?_, ?_⟩
  · rw [uniformImage_integralRaw (signVector e) (fun z => z) aestronglyMeasurable_id]
    have hz (i : Fin r) : (∑ σ : Fin r → Bool, SignGame.sign (σ i)) = 0 := by
      have heq := Fintype.sum_equiv (SignGame.flip i) (fun σ => SignGame.sign (SignGame.flip i σ i)) (fun σ => SignGame.sign (σ i)) (fun _ => rfl)
      simp only [SignGame.flip_same, SignGame.sign_not, Finset.sum_neg_distrib] at heq
      linarith
    simp only [signVector, ← Finset.smul_sum, Finset.sum_comm (s := Finset.univ)
      (t := Finset.univ) (f := fun (σ : Fin r → Bool) (i : Fin r) => SignGame.sign (σ i) • e i), ← Finset.sum_smul,
      hz, zero_smul, Finset.sum_const_zero, smul_zero]
  · intro v _
    apply uniformImage_integrable
    fun_prop
  · intro v hv
    rw [uniformImage_integral (signVector e) _ (by fun_prop)]
    let b := fun i => ⟪v,e i⟫_ℝ
    have hb : ∑ i, (b i)^2 ≤ 1 := by
      have h := he.sum_inner_products_le (s := Finset.univ) v
      simp only [Real.norm_eq_abs, sq_abs] at h
      dsimp [b]
      conv_lhs => enter [2, i]; rw [real_inner_comm (e i) v]
      exact h.trans (by nlinarith [norm_nonneg v] : ‖v‖^2 ≤ 1)
    have hdot (σ : Fin r → Bool) : |⟪v,signVector e σ⟫_ℝ| =
        |∑ i, b i * SignGame.sign (σ i)|/4 := by
      simp [signVector, real_inner_smul_right, inner_sum, abs_mul, b, mul_comm]
      ring
    simp_rw [hdot]
    exact sign_exp_abs_le b hb

theorem signVertices_width [FiniteDimensional ℝ E] (K : Set E) (hb : Bornology.IsBounded K)
    (c : E) (e : Fin r → E) (he : Orthonormal ℝ e) (a : Fin r → ℝ)
    (hvert : ∀ σ : Fin r → Bool, c + ∑ i, (a i * SignGame.sign (σ i)) • e i ∈ K) :
    (∑ i, a i)/4 ≤ subexponentialWidth K := by
  classical
  have hn : K.Nonempty := ⟨_, hvert (fun _ => false)⟩
  have hμ := signVector_admissible e he
  have hsupport := widthSupport_integrable K hn hb hμ
  have mean : (𝔼 σ, ⟪c,signVector e σ⟫_ℝ) = 0 := by
    rw [← uniformImage_integral (signVector e) (fun z => ⟪c,z⟫_ℝ) (by fun_prop)]
    have h := integral_inner (𝕜 := ℝ) hμ.integrable c
    simpa [hμ.centered] using h
  have hpoint (σ : Fin r → Bool) : ⟪c,signVector e σ⟫_ℝ + (∑ i, a i)/4 ≤
      widthSupport K (signVector e σ) := by
    let z := signVector e σ
    let w := c + ∑ i, (a i * SignGame.sign (σ i)) • e i
    have hinner (i : Fin r) : ⟪e i,z⟫_ℝ = SignGame.sign (σ i)/4 := by
      simp [z, signVector, inner_sum, real_inner_smul_right, orthonormal_iff_ite.mp he]
      ring
    have heq : ⟪w,z⟫_ℝ = ⟪c,z⟫_ℝ + (∑ i, a i)/4 := by
      simp only [w, inner_add_left, sum_inner, real_inner_smul_left, hinner, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      cases σ i <;> simp [SignGame.sign] <;> ring
    rw [← heq]
    obtain ⟨R, _, hR⟩ := hb.exists_pos_norm_le
    refine le_ciSup (f := fun w : K => ⟪w.val,z⟫_ℝ) ?_ ⟨w,hvert σ⟩
    refine ⟨R*‖z‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _ y.prop) (norm_nonneg _))
  have hexp := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hpoint σ)
  rw [Finset.expect_add_distrib, Fintype.expect_const, mean, zero_add,
    ← uniformImage_integral (signVector e) _ hsupport.aestronglyMeasurable] at hexp
  exact hexp.trans (le_width_of_law K (widthValues_bddAbove K hn hb) hμ)

end Curvature

end
end


