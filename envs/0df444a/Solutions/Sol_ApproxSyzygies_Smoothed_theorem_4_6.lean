-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T23:10:01.644166+00:00
-- url     : https://prove2.me/submissions/8722663b-faae-4b98-945d-5bc339d20005

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration

section
/-! Blueprint for Theorem 4.6 (vector-valued Carbery–Wright, BCPV19 Thm 4.1). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46

/-- The decoupled product `v_0 ⊗ v_1 ⊗ ⋯ ⊗ v_{D-1}` in `ℝ^{[n]^D}`. -/
noncomputable def decProd {D n : ℕ} (v : Fin D → Fin n → ℝ) : EuclideanSpace ℝ (Fin D → Fin n) :=
  WithLp.toLp 2 fun k => ∏ j, v j (k j)

/-- The standard Gaussian law on the coordinates of `D` independent vectors of `ℝ^n`. -/
noncomputable def gaussDec (D n : ℕ) : Measure (Fin D × Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- The perturbed vectors `x_j + σ_j G_j`. -/
def pert {D n : ℕ} (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (G : Fin D × Fin n → ℝ) :
    Fin D → Fin n → ℝ :=
  fun j k => x j k + σ j * G (j, k)

/-- Standard deviations of the decoupling: `ρ √((D+1)/(2D))` for slot 0, `ρ / √(2D)` otherwise. -/
noncomputable def sigDec (D : ℕ) (ρ : ℝ) (j : Fin D) : ℝ :=
  if (j : ℕ) = 0 then ρ * Real.sqrt (((D : ℝ) + 1) / (2 * D)) else ρ / Real.sqrt (2 * D)

/-- Shifts of the decoupling: `u` in slot 0, `0` otherwise. -/
def shiftDec {D n : ℕ} (u : Fin n → ℝ) (j : Fin D) : Fin n → ℝ :=
  if (j : ℕ) = 0 then u else 0

end ApproxSyzygies.Smoothed.Dev.T46
end

section
/-! Part A of the Theorem 4.6 Blueprint: Gaussian measure facts (convolution, rotation, scaling,
currying of product measures). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

/-- The centred product Gaussian law with variance `v` on `ι → ℝ`. -/
noncomputable def nu (ι : Type) [Fintype ι] (v : NNReal) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 v

instance nu_isProb (ι : Type) [Fintype ι] (v : NNReal) : IsProbabilityMeasure (nu ι v) := by
  unfold nu; infer_instance

lemma map_coord {ι : Type} [Fintype ι] {β : Type} [MeasurableSpace β]
    (μ μ' : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (f : ℝ × ℝ → β)
    (hf : Measurable f) :
    ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => μ')).map
      (fun p : (ι → ℝ) × (ι → ℝ) => fun i => f (p.1 i, p.2 i)) =
    Measure.pi fun _ : ι => (μ.prod μ').map f := by
  have h1 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => μ) (fun _ => μ')).symm
  have : (fun p : (ι → ℝ) × (ι → ℝ) => fun i => f (p.1 i, p.2 i)) =
      (fun q : ι → ℝ × ℝ => fun i => f (q i)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm := by
    ext p i; rfl
  have hP : IsProbabilityMeasure ((μ.prod μ').map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hm : Measurable (fun q : ι → ℝ × ℝ => fun i => f (q i)) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  rw [this, ← Measure.map_map hm (MeasurableEquiv.measurable _), h1.map_eq,
    Measure.pi_map_pi (fun _ => hf.aemeasurable)]

lemma nu_conv (ι : Type) [Fintype ι] (a b : NNReal) :
    ((nu ι a).prod (nu ι b)).map (fun p => p.1 + p.2) = nu ι (a + b) := by
  have h := map_coord (ι := ι) (gaussianReal 0 a) (gaussianReal 0 b) (fun q => q.1 + q.2)
    (by fun_prop)
  have h2 : ((gaussianReal 0 a).prod (gaussianReal 0 b)).map (fun q : ℝ × ℝ => q.1 + q.2) =
      gaussianReal 0 (a + b) := by
    have := gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := a) (v₂ := b)
    rw [add_zero] at this
    rw [← this]; rfl
  unfold nu
  rw [h2] at h
  exact h

lemma gauss_rot1 (v : NNReal) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (fun q : ℝ × ℝ => (q.1 - q.2, q.1 + q.2)) =
      (gaussianReal 0 (2 * v)).prod (gaussianReal 0 (2 * v)) := by
  have hrot := IsGaussian.map_rotation_eq_self (μ := gaussianReal 0 v)
    (by simp [integral_id_gaussianReal]) (-(Real.pi / 4))
  have hF : (fun q : ℝ × ℝ => (q.1 - q.2, q.1 + q.2)) =
      (Prod.map (fun x : ℝ => Real.sqrt 2 * x) (fun x : ℝ => Real.sqrt 2 * x)) ∘
        (ContinuousLinearMap.rotation (-(Real.pi / 4)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) := by
    ext q
    · simp only [Function.comp_apply, ContinuousLinearMap.rotation_apply, Prod.map_fst,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, smul_eq_mul]
      have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linear_combination (q.2 / 2 - q.1 / 2) * this
    · simp only [Function.comp_apply, ContinuousLinearMap.rotation_apply, Prod.map_snd,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, smul_eq_mul]
      have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linear_combination (-q.1 / 2 - q.2 / 2) * this
  rw [hF, ← Measure.map_map (by fun_prop) (ContinuousLinearMap.continuous _).measurable, hrot,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 2 <;> ext <;> simp

lemma nu_rot (ι : Type) [Fintype ι] (v : NNReal) :
    ((nu ι v).prod (nu ι v)).map (fun p => (p.1 - p.2, p.1 + p.2)) =
      (nu ι (2 * v)).prod (nu ι (2 * v)) := by
  have h := map_coord (ι := ι) (gaussianReal 0 v) (gaussianReal 0 v)
    (fun q : ℝ × ℝ => (q.1 - q.2, q.1 + q.2)) (by fun_prop)
  rw [gauss_rot1] at h
  have h1 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => gaussianReal 0 (2 * v))
    (fun _ => gaussianReal 0 (2 * v))).map_eq
  have : (fun p : (ι → ℝ) × (ι → ℝ) => (p.1 - p.2, p.1 + p.2)) =
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) ∘
        (fun p : (ι → ℝ) × (ι → ℝ) => fun i => ((p.1 i - p.2 i, p.1 i + p.2 i) : ℝ × ℝ)) := by
    ext p i <;> rfl
  unfold nu
  rw [this, ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop), h, h1]

lemma nu_smul (ι : Type) [Fintype ι] (c : ℝ) :
    (nu ι 1).map (fun g => c • g) = nu ι ⟨c ^ 2, sq_nonneg _⟩ := by
  unfold nu
  have : (fun g : ι → ℝ => c • g) = fun g i => (fun x : ℝ => c * x) (g i) := by
    ext g i; simp
  rw [this, Measure.pi_map_pi (fun _ => (measurable_const_mul c).aemeasurable)]
  congr 1; ext1 i
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  rfl

/-- Currying of a product measure. -/
lemma pi_map_uncurry (ι κ : Type) [Fintype ι] [Fintype κ] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map (Function.uncurry) =
      Measure.pi fun _ : ι × κ => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_uncurry (MeasurableSet.univ_pi hs)]
  have : (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext x; simp [Set.mem_pi, Prod.forall]
  rw [this, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product', Finset.univ_product_univ]

lemma gaussDec_eq (D n : ℕ) :
    gaussDec D n = (Measure.pi fun _ : Fin D => nu (Fin n) 1).map Function.uncurry := by
  unfold gaussDec nu
  rw [pi_map_uncurry]

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the Cauchy–Schwarz chain of BCPV19 Lemma 4.8 (Lovett's argument). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

/-- `Δ_z f (w) = f (w + z) f (w - z)`. -/
noncomputable def dif {n : ℕ} (z : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ≥0∞) : (Fin n → ℝ) → ℝ≥0∞ :=
  fun w => f (w + z) * f (w - z)

/-- The iterated functional `Φ_k(f, a) = E_{z_1} ⋯ E_{z_k} E_{w ∼ N(0,a)} (Δ_{z_k} ⋯ Δ_{z_1} f)(w)`,
`z_j ∼ N(0, v₀)`. -/
noncomputable def Phi (n : ℕ) (v0 : ℝ≥0) : ℕ → ((Fin n → ℝ) → ℝ≥0∞) → ℝ≥0 → ℝ≥0∞
  | 0, f, a => ∫⁻ w, f w ∂(nu (Fin n) a)
  | k + 1, f, a => ∫⁻ z, Phi n v0 k (dif z f) a ∂(nu (Fin n) v0)

lemma Phi_meas {n : ℕ} (v0 : ℝ≥0) (k : ℕ) (a : ℝ≥0) : ∀ {P : Type} [MeasurableSpace P]
    (F : P × (Fin n → ℝ) → ℝ≥0∞), Measurable F →
    Measurable (fun p => Phi n v0 k (fun w => F (p, w)) a) := by
  induction k with
  | zero => intro P _ F hF; exact hF.lintegral_prod_right'
  | succ k ih =>
    intro P _ F hF
    have h2 : Measurable (fun q : (P × (Fin n → ℝ)) × (Fin n → ℝ) =>
        F (q.1.1, q.2 + q.1.2) * F (q.1.1, q.2 - q.1.2)) := by
      apply Measurable.mul
      · exact hF.comp (by fun_prop)
      · exact hF.comp (by fun_prop)
    exact (ih _ h2).lintegral_prod_right'

lemma sq_lintegral_le {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ≥0∞) (hg : AEMeasurable g μ) : (∫⁻ x, g x ∂μ) ^ 2 ≤ ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  calc (∫⁻ x, g x ∂μ) ^ 2 ≤ ((∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ x, g x ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

lemma base_step {n : ℕ} (v0 a : ℝ≥0) (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (Phi n v0 0 f (a + 2 * v0)) ^ 2 ≤ Phi n v0 1 f (a + v0) := by
  simp only [Phi, dif]
  have e1 : ∫⁻ w, f w ∂(nu (Fin n) (a + 2 * v0)) =
      ∫⁻ w', ∫⁻ x, f (w' + x) ∂(nu (Fin n) (2 * v0)) ∂(nu (Fin n) a) := by
    rw [← nu_conv (Fin n) a (2 * v0), lintegral_map hf (by fun_prop),
      lintegral_prod (fun q : (Fin n → ℝ) × (Fin n → ℝ) => f (q.1 + q.2)) (by fun_prop)]
  have e2 : ∀ w' : Fin n → ℝ, (∫⁻ x, f (w' + x) ∂(nu (Fin n) (2 * v0))) ^ 2 =
      ∫⁻ y, ∫⁻ z, f (w' + (y - z)) * f (w' + (y + z)) ∂(nu (Fin n) v0) ∂(nu (Fin n) v0) := by
    intro w'
    have hm : Measurable fun x : Fin n → ℝ => f (w' + x) := hf.comp (by fun_prop)
    rw [sq, ← lintegral_prod_mul hm.aemeasurable hm.aemeasurable, ← nu_rot (Fin n) v0,
      lintegral_map (by fun_prop) (by fun_prop), lintegral_prod _ (by fun_prop)]
  have hI : Measurable fun w' : Fin n → ℝ => ∫⁻ x, f (w' + x) ∂(nu (Fin n) (2 * v0)) :=
    Measurable.lintegral_prod_right' (f := fun q : (Fin n → ℝ) × (Fin n → ℝ) => f (q.1 + q.2))
      (by fun_prop)
  have hG : Measurable fun q : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      f (q.1.1 + (q.1.2 - q.2)) * f (q.1.1 + (q.1.2 + q.2)) := by fun_prop
  have e3 : ∫⁻ w', ∫⁻ y, ∫⁻ z, f (w' + (y - z)) * f (w' + (y + z)) ∂(nu (Fin n) v0) ∂(nu (Fin n) v0) ∂(nu (Fin n) a) =
      ∫⁻ z, ∫⁻ q, f (q.1 + (q.2 - z)) * f (q.1 + (q.2 + z)) ∂((nu (Fin n) a).prod (nu (Fin n) v0)) ∂(nu (Fin n) v0) := by
    rw [← lintegral_prod _ (Measurable.lintegral_prod_right' hG).aemeasurable]
    exact lintegral_lintegral_swap hG.aemeasurable
  have e4 : ∀ z : Fin n → ℝ, ∫⁻ w, f (w + z) * f (w - z) ∂(nu (Fin n) (a + v0)) =
      ∫⁻ q, f (q.1 + (q.2 - z)) * f (q.1 + (q.2 + z)) ∂((nu (Fin n) a).prod (nu (Fin n) v0)) := by
    intro z
    rw [← nu_conv (Fin n) a v0, lintegral_map (by fun_prop) (by fun_prop)]
    congr 1; ext q
    rw [mul_comm]
    congr 2 <;> abel
  rw [e1]
  calc _ ≤ ∫⁻ w', (∫⁻ x, f (w' + x) ∂(nu (Fin n) (2 * v0))) ^ 2 ∂(nu (Fin n) a) :=
        sq_lintegral_le _ _ hI.aemeasurable
    _ = _ := by simp_rw [e2, e3, e4]

lemma dif_meas {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) (z : Fin n → ℝ) :
    Measurable (dif z f) := by
  unfold dif; fun_prop

lemma Phi_dif_meas {n : ℕ} (v0 : ℝ≥0) (k : ℕ) (b : ℝ≥0) (f : (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) : Measurable (fun z => Phi n v0 k (dif z f) b) :=
  Phi_meas v0 k b (fun q : (Fin n → ℝ) × (Fin n → ℝ) => f (q.2 + q.1) * f (q.2 - q.1))
    (by fun_prop)

lemma chain_step {n : ℕ} (v0 a : ℝ≥0) : ∀ (k : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞), Measurable f →
    (Phi n v0 k f (a + 2 * v0)) ^ 2 ≤ Phi n v0 (k + 1) f (a + v0)
  | 0, f, hf => base_step v0 a f hf
  | k + 1, f, hf => by
    show (∫⁻ z, Phi n v0 k (dif z f) (a + 2 * v0) ∂(nu (Fin n) v0)) ^ 2 ≤
      ∫⁻ z, Phi n v0 (k + 1) (dif z f) (a + v0) ∂(nu (Fin n) v0)
    calc _ ≤ ∫⁻ z, (Phi n v0 k (dif z f) (a + 2 * v0)) ^ 2 ∂(nu (Fin n) v0) :=
          sq_lintegral_le _ _ (Phi_dif_meas v0 k _ f hf).aemeasurable
      _ ≤ _ := lintegral_mono fun z => chain_step v0 a k (dif z f) (dif_meas f hf z)

lemma chain_iter {n : ℕ} (v0 : ℝ≥0) (L : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∀ j : ℕ, j + 1 ≤ L →
      (Phi n v0 0 f (((2 * L : ℕ) : ℝ≥0) * v0)) ^ (2 ^ j) ≤
        Phi n v0 j f (((2 * L - j : ℕ) : ℝ≥0) * v0)
  | 0, _ => by simp
  | j + 1, hj => by
    have ih := chain_iter v0 L f hf j (by omega)
    obtain ⟨c, hc⟩ : ∃ c, 2 * L - j = c + 2 := ⟨2 * L - j - 2, by omega⟩
    have h1 : 2 * L - (j + 1) = c + 1 := by omega
    have hs := chain_step (n := n) v0 ((c : ℝ≥0) * v0) j f hf
    rw [hc] at ih
    rw [h1]
    have e1 : ((c + 2 : ℕ) : ℝ≥0) * v0 = (c : ℝ≥0) * v0 + 2 * v0 := by push_cast; ring
    have e2 : ((c + 1 : ℕ) : ℝ≥0) * v0 = (c : ℝ≥0) * v0 + v0 := by push_cast; ring
    rw [e1] at ih
    rw [e2, pow_succ, pow_mul]
    exact (pow_le_pow_left' ih 2).trans hs

/-- The sign `±1` of a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Closed form of `Δ_{z_k} ⋯ Δ_{z_1} f (w)`: the product of `f` over the `2^k` signed points. -/
noncomputable def Qf {n : ℕ} (k : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞) (Z : Fin k → Fin n → ℝ)
    (w : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ ζ : Fin k → Bool, f (w + ∑ j, sgn (ζ j) • Z j)

lemma Qf_succ {n : ℕ} (k : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞) (Z : Fin (k + 1) → Fin n → ℝ)
    (w : Fin n → ℝ) : Qf (k + 1) f Z w = Qf k (dif (Z 0) f) (Fin.tail Z) w := by
  unfold Qf dif
  rw [← (Fin.consEquiv (fun _ => Bool)).prod_comp, Fintype.prod_prod_type, Fintype.prod_bool,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ζ _ => ?_
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sgn,
    if_true, one_smul, Bool.false_eq_true, if_false, neg_smul, Fin.tail]
  congr 2 <;> abel

lemma Phi_eq {n : ℕ} (v0 b : ℝ≥0) : ∀ (k : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞), Measurable f →
    Phi n v0 k f b = ∫⁻ Z, ∫⁻ w, Qf k f Z w ∂(nu (Fin n) b)
      ∂(Measure.pi fun _ : Fin k => nu (Fin n) v0)
  | 0, f, hf => by
    simp only [Phi, Qf, Finset.univ_unique, Finset.prod_singleton, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, lintegral_const, measure_univ, mul_one]
  | k + 1, f, hf => by
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => nu (Fin n) v0) 0
    simp_rw [Qf_succ]
    have key : ∀ Z : Fin (k + 1) → Fin n → ℝ,
        MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0 Z = (Z 0, Fin.tail Z) := by
      intro Z
      ext1
      · rfl
      · funext j; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
    have hH : Measurable fun p : (Fin n → ℝ) × (Fin k → Fin n → ℝ) =>
        ∫⁻ w, Qf k (dif p.1 f) p.2 w ∂(nu (Fin n) b) := by
      refine Measurable.lintegral_prod_right'
        (f := fun q : ((Fin n → ℝ) × (Fin k → Fin n → ℝ)) × (Fin n → ℝ) =>
          Qf k (dif q.1.1 f) q.1.2 q.2) ?_
      unfold Qf dif
      refine Finset.measurable_prod _ fun ζ _ => Measurable.mul ?_ ?_
      · exact hf.comp (by fun_prop)
      · exact hf.comp (by fun_prop)
    have e := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p => ∫⁻ w, Qf k (dif p.1 f) p.2 w ∂(nu (Fin n) b))
    simp only [key] at e
    rw [e, lintegral_prod _ hH.aemeasurable]
    show ∫⁻ z, Phi n v0 k (dif z f) b ∂(nu (Fin n) v0) = _
    congr 1; ext z
    exact Phi_eq v0 b k (dif z f) (dif_meas f hf z)

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the polarization identity (BCPV19 Lemmas 4.6–4.7) and the triangle inequality step of
Proposition 4.5, for projections onto subspaces of symmetric tensors. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

lemma sum_sgn_pow (e : ℕ) : ∑ b : Bool, sgn b ^ e = 1 + (-1) ^ e := by
  simp [sgn]

/-- Lemma 4.6 in counting form: the signed sum of `∏ᵢ c(φ i)` vanishes unless `φ` is a
bijection. -/
lemma signed_sum_eval (m : ℕ) (φ : Fin (m + 1) → Fin (m + 1)) :
    ∑ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) *
        ∏ i, (Fin.cons (1 : ℝ) (fun j => sgn (ζ j)) : Fin (m + 1) → ℝ) (φ i) =
      if Function.Bijective φ then 2 ^ m else 0 := by
  classical
  set cnt : Fin (m + 1) → ℕ := fun j' => (Finset.univ.filter fun i => φ i = j').card with hcnt
  have hprod : ∀ c : Fin (m + 1) → ℝ, ∏ i, c (φ i) = ∏ j', c j' ^ cnt j' := by
    intro c
    rw [← Finset.prod_fiberwise Finset.univ φ (fun i => c (φ i))]
    refine Finset.prod_congr rfl fun j' _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => c j') (fun i hi => by
      rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
  have hA : ∀ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) *
      ∏ i, (Fin.cons (1 : ℝ) (fun j => sgn (ζ j)) : Fin (m + 1) → ℝ) (φ i) =
      ∏ j, sgn (ζ j) ^ (cnt j.succ + 1) := by
    intro ζ
    rw [hprod, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, one_pow, one_mul, Fin.cons_succ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => by ring
  simp_rw [hA]
  rw [← Fintype.prod_sum (fun (j : Fin m) (b : Bool) => sgn b ^ (cnt j.succ + 1))]
  simp_rw [sum_sgn_pow]
  have hsum : ∑ j', cnt j' = m + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := φ)
      (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  split_ifs with hb
  · have h1 : ∀ j', cnt j' = 1 := by
      intro j'
      obtain ⟨i, hi⟩ := hb.2 j'
      rw [hcnt]; dsimp only
      rw [Finset.card_eq_one]
      refine ⟨i, ?_⟩
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact hb.1 (h.trans hi.symm)
      · rintro rfl; exact hi
    simp only [h1]
    norm_num
  · by_contra hne
    apply hb
    have hodd : ∀ j : Fin m, Odd (cnt j.succ) := by
      intro j
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      apply hne
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [pow_succ, hev.neg_one_pow]; norm_num
    rw [Fin.sum_univ_succ] at hsum
    have hsplit : ∑ j : Fin m, cnt j.succ = ∑ j : Fin m, (2 * (cnt j.succ / 2) + 1) :=
      Finset.sum_congr rfl fun j _ => by
        have := Nat.div_add_mod (cnt j.succ) 2
        rw [Nat.odd_iff.1 (hodd j)] at this
        omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsplit
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hsplit
    have h0 : 1 ≤ cnt 0 := by omega
    have hpos : ∀ j', 1 ≤ cnt j' := by
      intro j'
      refine Fin.cases h0 (fun j => ?_) j'
      obtain ⟨r, hr⟩ := hodd j
      omega
    have hsurj : Function.Surjective φ := by
      intro j'
      have := hpos j'
      rw [hcnt] at this; dsimp only at this
      obtain ⟨i, hi⟩ := Finset.card_pos.1 this
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    exact ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩

/-- Polarization in coordinates. -/
lemma polar_coord (m n : ℕ) (v : Fin (m + 1) → Fin n → ℝ) (k : Fin (m + 1) → Fin n) :
    ∑ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) *
        ∏ i, (v 0 (k i) + ∑ j, sgn (ζ j) * v j.succ (k i)) =
      2 ^ m * ∑ π : Equiv.Perm (Fin (m + 1)), ∏ i, v (π i) (k i) := by
  classical
  have h1 : ∀ ζ : Fin m → Bool, ∀ i, v 0 (k i) + ∑ j, sgn (ζ j) * v j.succ (k i) =
      ∑ j', (Fin.cons (1 : ℝ) (fun j => sgn (ζ j)) : Fin (m + 1) → ℝ) j' * v j' (k i) := by
    intro ζ i
    rw [Fin.sum_univ_succ]
    simp
  simp_rw [h1, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ φ : Fin (m + 1) → Fin (m + 1), ∑ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) *
      ((∏ i, (Fin.cons (1 : ℝ) (fun j => sgn (ζ j)) : Fin (m + 1) → ℝ) (φ i)) *
        ∏ i, v (φ i) (k i)) =
      (if Function.Bijective φ then 2 ^ m else 0) * ∏ i, v (φ i) (k i) := by
    intro φ
    rw [← signed_sum_eval m φ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ζ _ => by ring
  simp_rw [h2, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have h3 : (Finset.univ.filter fun φ : Fin (m + 1) → Fin (m + 1) => Function.Bijective φ) =
      Finset.univ.map ⟨fun π : Equiv.Perm (Fin (m + 1)) => (π : Fin (m + 1) → Fin (m + 1)),
        DFunLike.coe_injective⟩ := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨Equiv.ofBijective φ h, rfl⟩
    · rintro ⟨π, rfl⟩; exact π.bijective
  rw [h3, Finset.sum_map]
  rfl

/-- Polarization for tensors. -/
lemma polar_tensor (m n : ℕ) (x : Fin n → ℝ) (Z : Fin m → Fin n → ℝ) :
    ∑ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) • tensPow (x + ∑ j, sgn (ζ j) • Z j) (m + 1) =
      (2 ^ m : ℝ) • ∑ π : Equiv.Perm (Fin (m + 1)),
        decProd (fun i => (Fin.cons x Z : Fin (m + 1) → Fin n → ℝ) (π i)) := by
  ext k
  have := polar_coord m n (Fin.cons x Z) k
  simp only [Fin.cons_zero, Fin.cons_succ] at this
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    tensPow, decProd, Pi.add_apply]
  convert this using 3

/-- Projections onto subspaces of symmetric tensors do not see a permutation of the slots. -/
lemma proj_perm {D n : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)))
    (hE : E ≤ symTensors n D) (σ : Equiv.Perm (Fin D))
    (X Y : EuclideanSpace ℝ (Fin D → Fin n)) (hXY : ∀ k, Y k = X (k ∘ σ)) :
    E.starProjection Y = E.starProjection X := by
  rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff]
  intro e he
  have hs := hE he
  rw [inner_sub_right, sub_eq_zero]
  simp only [PiLp.inner_apply, hXY]
  have hs' : ∀ k : Fin D → Fin n, e (k ∘ σ) = e k := fun k => hs σ k
  calc ∑ k, inner ℝ (e k) (X (k ∘ σ)) = ∑ k, inner ℝ (e (k ∘ σ)) (X (k ∘ σ)) :=
        Finset.sum_congr rfl fun k _ => by rw [hs' k]
    _ = ∑ k, inner ℝ (e k) (X k) :=
        Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ (fun k => by
          rfl)

lemma decProd_perm {D n : ℕ} (v : Fin D → Fin n → ℝ) (π : Equiv.Perm (Fin D))
    (k : Fin D → Fin n) : decProd (fun i => v (π i)) k = decProd v (k ∘ π.symm) := by
  simp only [decProd, PiLp.toLp_apply, Function.comp_apply]
  exact Fintype.prod_equiv π _ _ (fun i => by simp)

/-- The deterministic step of Proposition 4.5: if all `2^m` signed points are good, the
decoupled product is good. -/
lemma polar_bound (m n : ℕ) (E : Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1) → Fin n)))
    (hE : E ≤ symTensors n (m + 1)) (x : Fin n → ℝ) (Z : Fin m → Fin n → ℝ) (ε : ℝ)
    (h : ∀ ζ : Fin m → Bool,
      ‖E.starProjection (tensPow (x + ∑ j, sgn (ζ j) • Z j) (m + 1))‖ ≤ ε) :
    ‖E.starProjection (decProd (Fin.cons x Z : Fin (m + 1) → Fin n → ℝ))‖ ≤
      ε / ((m + 1).factorial : ℝ) := by
  have hT := congrArg E.starProjection (polar_tensor m n x Z)
  simp only [map_sum, map_smul] at hT
  have hperm : ∀ π : Equiv.Perm (Fin (m + 1)),
      E.starProjection (decProd (fun i => (Fin.cons x Z : Fin (m + 1) → Fin n → ℝ) (π i))) =
        E.starProjection (decProd (Fin.cons x Z : Fin (m + 1) → Fin n → ℝ)) := by
    intro π
    exact proj_perm E hE π.symm _ _ (fun k => decProd_perm _ π k)
  simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hT
  have hle : ‖∑ ζ : Fin m → Bool, (∏ j, sgn (ζ j)) •
      E.starProjection (tensPow (x + ∑ j, sgn (ζ j) • Z j) (m + 1))‖ ≤ 2 ^ m * ε := by
    refine (norm_sum_le _ _).trans ?_
    have hs : ∀ ζ : Fin m → Bool, |∏ j, sgn (ζ j)| = 1 := by
      intro ζ
      rw [Finset.abs_prod]
      exact Finset.prod_eq_one fun j _ => by cases ζ j <;> simp [sgn]
    calc _ ≤ ∑ ζ : Fin m → Bool, ε := Finset.sum_le_sum fun ζ _ => by
          rw [norm_smul, Real.norm_eq_abs, hs, one_mul]; exact h ζ
      _ = 2 ^ m * ε := by simp
  rw [hT, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, norm_smul] at hle
  have hf : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [le_div_iff₀ hf]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  simp only [Real.norm_eq_abs, abs_of_pos h2, abs_of_pos hf] at hle
  nlinarith

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the decoupling inequality (BCPV19 Proposition 4.5 with `t = 0` and the norm
`‖Π_E ·‖`), stub `decoupling` of the Theorem 4.6 Blueprint. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

lemma continuous_tensPow {n : ℕ} (D : ℕ) : Continuous fun a : Fin n → ℝ => tensPow a D := by
  unfold tensPow
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => continuous_finsetProd _ fun j _ => continuous_apply _)

lemma continuous_decProd {D n : ℕ} : Continuous fun v : Fin D → Fin n → ℝ => decProd v := by
  unfold decProd
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => continuous_finsetProd _ fun j _ =>
      (continuous_apply _).comp (continuous_apply _))

/-- The law of `(σ₀ H₀, (σ₁ H_{j+1})_j)` for `H` standard. -/
lemma split_law (m n : ℕ) (s0 s1 : ℝ) :
    (Measure.pi fun _ : Fin (m + 1) => nu (Fin n) 1).map
        (fun H => (s0 • H 0, fun j : Fin m => s1 • H j.succ)) =
      (nu (Fin n) ⟨s0 ^ 2, sq_nonneg _⟩).prod
        (Measure.pi fun _ : Fin m => nu (Fin n) ⟨s1 ^ 2, sq_nonneg _⟩) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => nu (Fin n) 1) 0
  have hΨ : (fun H : Fin (m + 1) → Fin n → ℝ => (s0 • H 0, fun j : Fin m => s1 • H j.succ)) =
      (Prod.map (fun g : Fin n → ℝ => s0 • g) (fun H' : Fin m → Fin n → ℝ =>
        fun j => s1 • H' j)) ∘ MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0 := by
    have key : ∀ H : Fin (m + 1) → Fin n → ℝ,
        MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0 H = (H 0, fun j => H j.succ) := by
      intro H
      ext1
      · rfl
      · funext j; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
    funext H
    simp only [Function.comp_apply, key, Prod.map]
  rw [hΨ, ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _), hmp.map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), nu_smul]
  congr 1
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable fun g : Fin n → ℝ => s1 • g)
    |>.aemeasurable)]
  simp_rw [nu_smul]

end ApproxSyzygies.Smoothed.Dev.T46.PartA

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

open ApproxSyzygies.Smoothed.Dev.T46

theorem decoupling (D : ℕ) (hD : 2 ≤ D) (n : ℕ)
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n))) (hE : E ≤ symTensors n D)
    (u : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {g | ‖E.starProjection (tensPow (u + ρ • g) D)‖ ≤ ε} ≤
      (gaussDec D n {G | ‖E.starProjection (decProd (pert (shiftDec u) (sigDec D ρ) G))‖ ≤
          ε / (D.factorial : ℝ)}) ^ ((1 : ℝ) / 2 ^ (D - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hD0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  set v0 : ℝ≥0 := ⟨ρ ^ 2 / (2 * ((m + 1 : ℕ) : ℝ)), by positivity⟩ with hv0
  set S : Set (Fin n → ℝ) := {v | ‖E.starProjection (tensPow (u + v) (m + 1))‖ ≤ ε} with hS
  have hSm : MeasurableSet S := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    exact continuous_norm.comp ((ContinuousLinearMap.continuous _).comp
      ((continuous_tensPow _).comp (continuous_const.add continuous_id)))
  set f : (Fin n → ℝ) → ℝ≥0∞ := S.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hSm
  -- the bad set of the decoupled side
  set B : Set ((Fin n → ℝ) × (Fin m → Fin n → ℝ)) :=
    {p | ‖E.starProjection (decProd (Fin.cons (u + p.1) p.2 : Fin (m + 1) → Fin n → ℝ))‖ ≤
      ε / ((m + 1).factorial : ℝ)} with hB
  have hBm : MeasurableSet B := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    refine continuous_norm.comp ((ContinuousLinearMap.continuous _).comp
      (continuous_decProd.comp ?_))
    refine continuous_pi fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]; fun_prop
  -- Step A: the left side is `ν_{2(m+1) v₀}(S)`
  have hA : (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {g | ‖E.starProjection (tensPow (u + ρ • g) (m + 1))‖ ≤ ε} =
      Phi n v0 0 f (((2 * (m + 1) : ℕ) : ℝ≥0) * v0) := by
    have h1 : {g : Fin n → ℝ | ‖E.starProjection (tensPow (u + ρ • g) (m + 1))‖ ≤ ε} =
        (fun g => ρ • g) ⁻¹' S := rfl
    have h2 : (((2 * (m + 1) : ℕ) : ℝ≥0) * v0) = ⟨ρ ^ 2, sq_nonneg _⟩ := by
      ext
      show ((((2 * (m + 1) : ℕ) : ℝ≥0) : ℝ) * (ρ ^ 2 / (2 * ((m + 1 : ℕ) : ℝ)))) = ρ ^ 2
      rw [NNReal.coe_natCast]
      push_cast
      field_simp
    show nu (Fin n) 1 _ = _
    rw [h1, h2, ← Measure.map_apply (by fun_prop) hSm, nu_smul]
    simp only [Phi, hf, lintegral_indicator_one hSm]
  -- Step C: the chain
  have hC := chain_iter (n := n) v0 (m + 1) f hfm m (by omega)
  have e2 : 2 * (m + 1) - m = m + 2 := by omega
  rw [e2, Phi_eq v0 _ m f hfm] at hC
  -- Step E: pointwise comparison
  have hE' : ∀ (Z : Fin m → Fin n → ℝ) (w : Fin n → ℝ),
      Qf m f Z w ≤ B.indicator 1 (w, Z) := by
    intro Z w
    by_cases hall : ∀ ζ : Fin m → Bool, w + ∑ j, sgn (ζ j) • Z j ∈ S
    · have hmem : (w, Z) ∈ B := by
        show ‖E.starProjection (decProd (Fin.cons (u + w) Z : Fin (m + 1) → Fin n → ℝ))‖ ≤
          ε / ((m + 1).factorial : ℝ)
        refine polar_bound m n E hE (u + w) Z ε fun ζ => ?_
        have := hall ζ
        simp only [hS, Set.mem_ofPred_eq, ← add_assoc] at this
        exact this
      rw [Set.indicator_of_mem hmem]
      unfold Qf
      refine Finset.prod_le_one (fun _ _ => by simp) fun ζ _ => ?_
      rw [hf]; unfold Set.indicator; split_ifs <;> simp
    · push Not at hall
      obtain ⟨ζ, hζ⟩ := hall
      have : Qf m f Z w = 0 := by
        unfold Qf
        exact Finset.prod_eq_zero (Finset.mem_univ ζ) (Set.indicator_of_notMem hζ _)
      rw [this]; simp
  -- Step F: the decoupled side
  set s0 : ℝ := sigDec (m + 1) ρ 0 with hs0
  set s1 : ℝ := ρ / Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) with hs1
  have hv1 : (⟨s1 ^ 2, sq_nonneg _⟩ : ℝ≥0) = v0 := by
    ext
    simp only [hs1, hv0, NNReal.coe_mk, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤
      2 * ((m + 1 : ℕ) : ℝ))]
  have hvb : (⟨s0 ^ 2, sq_nonneg _⟩ : ℝ≥0) = ((m + 2 : ℕ) : ℝ≥0) * v0 := by
    have hs0' : s0 = ρ * Real.sqrt ((((m + 1 : ℕ) : ℝ) + 1) / (2 * ((m + 1 : ℕ) : ℝ))) := by
      simp [hs0, sigDec]
    ext
    show s0 ^ 2 = (((m + 2 : ℕ) : ℝ≥0) : ℝ) * (ρ ^ 2 / (2 * ((m + 1 : ℕ) : ℝ)))
    rw [hs0', mul_pow, Real.sq_sqrt (by positivity), NNReal.coe_natCast]
    push_cast
    field_simp
    ring
  have hpert : ∀ H : Fin (m + 1) → Fin n → ℝ,
      pert (shiftDec u) (sigDec (m + 1) ρ) (Function.uncurry H) =
        (Fin.cons (u + s0 • H 0) (fun j : Fin m => s1 • H j.succ) :
          Fin (m + 1) → Fin n → ℝ) := by
    intro H
    funext j k
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [pert, shiftDec, hs0]
    · simp [pert, shiftDec, sigDec, hs1, Fin.succ_ne_zero, div_eq_mul_inv]
  have hF : gaussDec (m + 1) n {G | ‖E.starProjection (decProd (pert (shiftDec u)
      (sigDec (m + 1) ρ) G))‖ ≤ ε / ((m + 1).factorial : ℝ)} =
      ((nu (Fin n) (((m + 2 : ℕ) : ℝ≥0) * v0)).prod
        (Measure.pi fun _ : Fin m => nu (Fin n) v0)) B := by
    rw [gaussDec_eq, ← hvb, ← hv1, ← split_law m n s0 s1,
      Measure.map_apply (by fun_prop) hBm]
    have : Function.uncurry = ⇑(MeasurableEquiv.curry (Fin (m + 1)) (Fin n) ℝ).symm := rfl
    rw [this, MeasurableEquiv.map_apply]
    congr 1
    ext H
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hB]
    rw [show (MeasurableEquiv.curry (Fin (m + 1)) (Fin n) ℝ).symm H = Function.uncurry H from rfl,
      hpert]
  have hG : ∫⁻ Z, ∫⁻ w, Qf m f Z w ∂(nu (Fin n) (((m + 2 : ℕ) : ℝ≥0) * v0))
      ∂(Measure.pi fun _ : Fin m => nu (Fin n) v0) ≤
      ((nu (Fin n) (((m + 2 : ℕ) : ℝ≥0) * v0)).prod
        (Measure.pi fun _ : Fin m => nu (Fin n) v0)) B := by
    rw [Measure.prod_apply_symm hBm]
    refine lintegral_mono fun Z => ?_
    calc ∫⁻ w, Qf m f Z w ∂(nu (Fin n) (((m + 2 : ℕ) : ℝ≥0) * v0))
        ≤ ∫⁻ w, ((fun x => (x, Z)) ⁻¹' B).indicator 1 w
            ∂(nu (Fin n) (((m + 2 : ℕ) : ℝ≥0) * v0)) := lintegral_mono fun w => hE' Z w
      _ = _ := lintegral_indicator_one (measurable_prodMk_right hBm)
  -- conclusion
  rw [hA, Nat.add_sub_cancel]
  set X := Phi n v0 0 f (((2 * (m + 1) : ℕ) : ℝ≥0) * v0)
  have hXY : X ^ (2 ^ m) ≤ gaussDec (m + 1) n {G | ‖E.starProjection (decProd (pert (shiftDec u)
      (sigDec (m + 1) ρ) G))‖ ≤ ε / ((m + 1).factorial : ℝ)} := by
    rw [hF]; exact hC.trans hG
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  calc X = (X ^ ((2 : ℝ) ^ m)) ^ ((1 : ℝ) / 2 ^ m) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hpos.ne', ENNReal.rpow_one]
    _ ≤ _ := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        have : X ^ ((2 : ℝ) ^ m) = X ^ (2 ^ m) := by
          rw [← ENNReal.rpow_natCast]; push_cast; rfl
        rw [this]; exact hXY

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the dimension-free small-ball bound for a linear image of a shifted Gaussian vector
(the case `D = 1` of `multilinear_small_ball`), via the Laplace transform and diagonalisation. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

lemma gauss1_laplace (a μ σ : ℝ) (ha : 0 ≤ a) :
    ∫ c, Real.exp (-(a * (μ + σ * c) ^ 2)) ∂(gaussianReal 0 1) ≤
      (1 + 2 * a * σ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  set β := a * σ ^ 2 + 1 / 2 with hβdef
  have hβ : 0 < β := by positivity
  set d := a * σ * μ / β with hd
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ c : ℝ, gaussianPDFReal 0 1 c • Real.exp (-(a * (μ + σ * c) ^ 2)) ≤
      (√(2 * π))⁻¹ * Real.exp (-β * (c + d) ^ 2) := by
    intro c
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    have key : -β * (c + d) ^ 2 - (-c ^ 2 / 2 + -(a * (μ + σ * c) ^ 2)) =
        a * μ ^ 2 / (2 * β) := by
      rw [hd]; field_simp; rw [hβdef]; ring
    have : 0 ≤ a * μ ^ 2 / (2 * β) := by positivity
    linarith
  have hint : Integrable (fun c : ℝ => (√(2 * π))⁻¹ * Real.exp (-β * (c + d) ^ 2)) :=
    ((integrable_exp_neg_mul_sq hβ).comp_add_right d).const_mul _
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun c => ?_) hint
    (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  · exact smul_nonneg (gaussianPDFReal_nonneg _ _ _) (Real.exp_pos _).le
  · rw [integral_const_mul,
      integral_add_right_eq_self (fun c : ℝ => Real.exp (-β * c ^ 2)) d, integral_gaussian,
      Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show 1 + 2 * a * σ ^ 2 = 2 * β by rw [hβdef]; ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    have h1 : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
    have h2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
    have h3 : 0 < √β := Real.sqrt_pos.2 hβ
    field_simp

lemma one_add_sum_le_prod {ι : Type} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    have := hx a
    nlinarith

/-- Hilbert–Schmidt norm is independent of the orthonormal basis. -/
lemma hs_basis {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] W)
    (c : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∑ i, ‖A (c i)‖ ^ 2 =
      ∑ j, ‖LinearMap.adjoint A (stdOrthonormalBasis ℝ W j)‖ ^ 2 := by
  set f := stdOrthonormalBasis ℝ W
  have : ∀ i, ‖A (c i)‖ ^ 2 = ∑ j, (inner ℝ (LinearMap.adjoint A (f j)) (c i)) ^ 2 := by
    intro i
    rw [← f.sum_sq_inner_right (A (c i))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.adjoint_inner_left]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact c.sum_sq_inner_left _

lemma laplace_vec {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] W)
    (hA : ∑ k, ‖A (EuclideanSpace.single k 1)‖ ^ 2 = 1) (x : EuclideanSpace ℝ (Fin n))
    (σ θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ g, Real.exp (-(θ * ‖A (x + σ • WithLp.toLp 2 g)‖ ^ 2))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤
      (1 + 2 * θ * σ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  have hT := LinearMap.isSymmetric_adjoint_comp_self A
  set b := hT.eigenvectorBasis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) with hb
  have horth : ∀ i j, i ≠ j → inner ℝ (A (b i)) (A (b j)) = 0 := by
    intro i j hij
    rw [← LinearMap.adjoint_inner_right]
    have := hT.apply_eigenvectorBasis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j
    rw [← hb] at this
    rw [show LinearMap.adjoint A (A (b j)) = (LinearMap.adjoint A ∘ₗ A) (b j) from rfl, this,
      inner_smul_right, b.orthonormal.2 hij, mul_zero]
  have hnorm : ∀ a : Fin n → ℝ, ‖A (∑ i, a i • b i)‖ ^ 2 = ∑ i, a i ^ 2 * ‖A (b i)‖ ^ 2 := by
    intro a
    rw [← real_inner_self_eq_norm_sq, map_sum]
    simp_rw [map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [horth i j hji.symm]; simp)
      (by simp), real_inner_self_eq_norm_sq]
    simp; ring
  have hHS : ∑ i, ‖A (b i)‖ ^ 2 = 1 := by
    rw [hs_basis A b, ← hs_basis A (EuclideanSpace.basisFun (Fin n) ℝ), ← hA]
    simp
  set lam : Fin n → ℝ := fun i => ‖A (b i)‖ ^ 2 with hlam
  set mu : Fin n → ℝ := fun i => inner ℝ (b i) x with hmu
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y => Real.exp (-(θ * ‖A (x + σ • y)‖ ^ 2))
    with hF
  have hAc : Continuous A := LinearMap.continuous_of_finiteDimensional A
  have hFc : Continuous F := by
    rw [hF]; fun_prop
  have e1 : ∫ g, Real.exp (-(θ * ‖A (x + σ • WithLp.toLp 2 g)‖ ^ 2))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ c, ∏ i, Real.exp (-((θ * lam i) * (mu i + σ * c i) ^ 2))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    have h1 : ∫ g, Real.exp (-(θ * ‖A (x + σ • WithLp.toLp 2 g)‖ ^ 2))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = ∫ y, F y ∂(stdGaussian _) := by
      rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hFc.aestronglyMeasurable]
    have hφ : Continuous fun c : Fin n → ℝ => ∑ i, c i • b i :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    rw [h1, stdGaussian_eq_map_pi_orthonormalBasis b]
    rw [integral_map (φ := fun c : Fin n → ℝ => ∑ i, c i • b i) (f := F) hφ.aemeasurable
      hFc.aestronglyMeasurable]
    congr 1; ext c
    have hx : x + σ • ∑ i, c i • b i = ∑ i, (mu i + σ * c i) • b i := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
    simp only [hF, hx, hnorm, ← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hlam]; ring
  rw [e1, integral_fintype_prod_eq_prod (fun i c => Real.exp (-((θ * lam i) * (mu i + σ * c) ^ 2)))]
  have hl0 : ∀ i, 0 ≤ lam i := fun i => by positivity
  calc ∏ i, ∫ c, Real.exp (-((θ * lam i) * (mu i + σ * c) ^ 2)) ∂(gaussianReal 0 1)
      ≤ ∏ i, (1 + 2 * (θ * lam i) * σ ^ 2) ^ (-(1 / 2 : ℝ)) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun c => (Real.exp_pos _).le)
          (fun i _ => gauss1_laplace _ _ _ (mul_nonneg hθ (hl0 i)))
    _ = (∏ i, (1 + 2 * (θ * lam i) * σ ^ 2)) ^ (-(1 / 2 : ℝ)) :=
        (Real.finsetProd_rpow _ _ (fun i _ => by positivity) _)
    _ ≤ (1 + 2 * θ * σ ^ 2) ^ (-(1 / 2 : ℝ)) := by
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
        have := one_add_sum_le_prod Finset.univ (fun i => 2 * (θ * lam i) * σ ^ 2)
          (fun i => by positivity)
        have hs : ∑ i, 2 * (θ * lam i) * σ ^ 2 = 2 * θ * σ ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
          simp only [hlam]
          rw [show (∑ x, ‖A (b x)‖ ^ 2) = 1 from hHS]; ring
        rw [hs] at this
        exact this

/-- The case `D = 1`: `P[‖A(x + σ g)‖ ≤ t] ≤ e t / σ` for `A` of Hilbert–Schmidt norm `1`. -/
lemma core {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] W)
    (hA : ∑ k, ‖A (EuclideanSpace.single k 1)‖ ^ 2 = 1) (x : Fin n → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (ht : 0 < t) :
    nu (Fin n) 1 {g | ‖A (WithLp.toLp 2 (x + σ • g))‖ ≤ t} ≤
      ENNReal.ofReal (Real.exp 1 * t / σ) := by
  set θ : ℝ := 1 / t ^ 2 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  set F : (Fin n → ℝ) → ℝ := fun g =>
    Real.exp 1 * Real.exp (-(θ * ‖A (WithLp.toLp 2 x + σ • WithLp.toLp 2 g)‖ ^ 2)) with hF
  have hAc := LinearMap.continuous_of_finiteDimensional A
  have hFc : Continuous F := by
    rw [hF]; fun_prop
  set S := {g : Fin n → ℝ | ‖A (WithLp.toLp 2 (x + σ • g))‖ ≤ t} with hS
  have hSm : MeasurableSet S := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    fun_prop
  have hbound : ∀ g, ‖F g‖ ≤ Real.exp 1 := by
    intro g
    rw [hF, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc _ ≤ Real.exp 1 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
          rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      _ = _ := mul_one _
  have hFi : Integrable F (nu (Fin n) 1) :=
    Integrable.of_bound hFc.aestronglyMeasurable (Real.exp 1) (Filter.Eventually.of_forall hbound)
  have hle : ∀ g, S.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) g ≤ ENNReal.ofReal (F g) := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, Pi.one_apply, ENNReal.one_le_ofReal, hF]
      simp only [WithLp.toLp_add, WithLp.toLp_smul] at hg ⊢
      have h1 : θ * ‖A (WithLp.toLp 2 x + σ • WithLp.toLp 2 g)‖ ^ 2 ≤ 1 := by
        rw [hθ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) hg 2
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    · rw [Set.indicator_of_notMem hg]; simp
  calc nu (Fin n) 1 S = ∫⁻ g, S.indicator 1 g ∂(nu (Fin n) 1) :=
        (lintegral_indicator_one hSm).symm
    _ ≤ ∫⁻ g, ENNReal.ofReal (F g) ∂(nu (Fin n) 1) := lintegral_mono hle
    _ = ENNReal.ofReal (∫ g, F g ∂(nu (Fin n) 1)) :=
        (ofReal_integral_eq_lintegral_ofReal hFi
          (Filter.Eventually.of_forall fun g => by positivity)).symm
    _ ≤ ENNReal.ofReal (Real.exp 1 * t / σ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hF, integral_const_mul, mul_div_assoc]
        gcongr
        refine (laplace_vec A hA (WithLp.toLp 2 x) σ θ hθ0).trans ?_
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
        have h1 : σ / t ≤ √(1 + 2 * θ * σ ^ 2) := by
          rw [show σ / t = √((σ / t) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
          apply Real.sqrt_le_sqrt
          rw [hθ, div_pow]
          have : 0 ≤ σ ^ 2 / t ^ 2 := by positivity
          have : 2 * (1 / t ^ 2) * σ ^ 2 = 2 * (σ ^ 2 / t ^ 2) := by ring
          linarith
        rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
        exact h1

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the first-slot tensor map and the Hilbert–Schmidt map of a partial contraction. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

/-- `Y ↦ w ⊗ Y`, the vector `w` in the first tensor slot. -/
noncomputable def tensL {D n : ℕ} (w : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin D → Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (D + 1) → Fin n) where
  toFun Y := WithLp.toLp 2 fun k => w (k 0) * Y (Fin.tail k)
  map_add' Y Y' := by
    ext k
    simp [mul_add]
  map_smul' c Y := by
    ext k
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma tensL_apply {D n : ℕ} (w : Fin n → ℝ) (Y : EuclideanSpace ℝ (Fin D → Fin n))
    (k : Fin (D + 1) → Fin n) : tensL w Y k = w (k 0) * Y (Fin.tail k) := rfl

lemma decProd_cons {D n : ℕ} (w : Fin n → ℝ) (v : Fin D → Fin n → ℝ) :
    decProd (Fin.cons w v : Fin (D + 1) → Fin n → ℝ) = tensL w (decProd v) := by
  ext k
  simp only [decProd, tensL_apply, PiLp.toLp_apply, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.tail]

lemma tensL_add_left {D n : ℕ} (w w' : Fin n → ℝ) (Y : EuclideanSpace ℝ (Fin D → Fin n)) :
    tensL (w + w') Y = tensL w Y + tensL w' Y := by
  ext k
  simp [tensL_apply, add_mul]

lemma tensL_smul_left {D n : ℕ} (c : ℝ) (w : Fin n → ℝ) (Y : EuclideanSpace ℝ (Fin D → Fin n)) :
    tensL (c • w) Y = c • tensL w Y := by
  ext k
  simp only [tensL_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The map `w ↦ T(w ⊗ ·)` into the Hilbert–Schmidt space. -/
noncomputable def hsMap {D n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : EuclideanSpace ℝ (Fin (D + 1) → Fin n) →ₗ[ℝ] V) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] PiLp 2 (fun _ : Fin D → Fin n => V) where
  toFun w := WithLp.toLp 2 fun k' => T (tensL (WithLp.ofLp w) (EuclideanSpace.single k' 1))
  map_add' w w' := by
    ext k'
    simp only [WithLp.ofLp_add, tensL_add_left, map_add, PiLp.toLp_apply, PiLp.add_apply]
  map_smul' c w := by
    ext k'
    simp only [WithLp.ofLp_smul, tensL_smul_left, map_smul, PiLp.toLp_apply, PiLp.smul_apply,
      RingHom.id_apply]

lemma hsMap_norm_sq {D n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : EuclideanSpace ℝ (Fin (D + 1) → Fin n) →ₗ[ℝ] V) (w : Fin n → ℝ) :
    ‖hsMap T (WithLp.toLp 2 w)‖ ^ 2 =
      ∑ k', ‖(T ∘ₗ tensL w) (EuclideanSpace.single k' 1)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

lemma tensL_single {D n : ℕ} (a : Fin n) (k' : Fin D → Fin n) :
    tensL (WithLp.ofLp (EuclideanSpace.single a (1 : ℝ))) (EuclideanSpace.single k' 1) =
      EuclideanSpace.single (Fin.cons a k' : Fin (D + 1) → Fin n) 1 := by
  ext k
  simp only [tensL_apply, EuclideanSpace.single_apply]
  by_cases h : k = Fin.cons a k'
  · subst h; simp [Fin.tail]
  · rw [if_neg h]
    by_cases h0 : k 0 = a
    · have ht : Fin.tail k ≠ k' := by
        intro ht; apply h
        rw [← h0, ← ht, Fin.cons_self_tail]
      simp [ht]
    · simp [h0]

lemma hsMap_hs {D n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : EuclideanSpace ℝ (Fin (D + 1) → Fin n) →ₗ[ℝ] V) :
    ∑ a, ‖hsMap T (EuclideanSpace.single a 1)‖ ^ 2 =
      ∑ k, ‖T (EuclideanSpace.single k 1)‖ ^ 2 := by
  simp_rw [PiLp.norm_sq_eq_of_L2]
  change ∑ a, ∑ k', ‖T (tensL (WithLp.ofLp (EuclideanSpace.single a (1 : ℝ)))
    (EuclideanSpace.single k' 1))‖ ^ 2 = _
  simp_rw [tensL_single]
  rw [← Fintype.sum_prod_type' (f := fun a (k' : Fin D → Fin n) =>
    ‖T (EuclideanSpace.single (Fin.cons a k' : Fin (D + 1) → Fin n) 1)‖ ^ 2)]
  exact (Fin.consEquiv (fun _ => Fin n)).sum_comp
    (fun k => ‖T (EuclideanSpace.single k 1)‖ ^ 2)

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Part A: the dimension-free polynomial small-ball bound for vector-valued multilinear forms in
independent shifted Gaussian vectors, stub `multilinear_small_ball` of the Theorem 4.6
Blueprint. Induction on `D` by conditioning on the first vector. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ApproxSyzygies.Smoothed.Dev.T46.PartA

/-- The statement in curried form (vectors `H j ∈ ℝ^n`), for a given `D`. -/
def MLP (D : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ a : ℝ, 0 < a ∧
    ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (T : EuclideanSpace ℝ (Fin D → Fin n) →ₗ[ℝ] V),
      ∑ k, ‖T (EuclideanSpace.single k 1)‖ ^ 2 = 1 →
      ∀ (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s : ℝ), 0 < s → (∀ j, s ≤ σ j) →
        ∀ ε : ℝ, 0 ≤ ε →
          (Measure.pi fun _ : Fin D => nu (Fin n) 1)
              {H | ‖T (decProd (fun j => x j + σ j • H j))‖ ≤ ε * s ^ D} ≤
            ENNReal.ofReal (C * ε ^ a)

lemma mlp_zero : MLP 0 := by
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro n V _ _ _ T hT x σ s hs hσ ε hε
  have hdec : ∀ v : Fin 0 → Fin n → ℝ,
      decProd v = EuclideanSpace.single (default : Fin 0 → Fin n) 1 := by
    intro v
    ext k
    simp [decProd, Subsingleton.elim k default]
  have hT1 : ‖T (EuclideanSpace.single (default : Fin 0 → Fin n) 1)‖ = 1 := by
    rw [Fintype.sum_unique] at hT
    have h0 : 0 ≤ ‖T (EuclideanSpace.single (default : Fin 0 → Fin n) 1)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T (EuclideanSpace.single (default : Fin 0 → Fin n) 1)‖ - 1)]
  simp only [hdec, hT1, pow_zero, mul_one, Real.rpow_one, one_mul]
  by_cases h1 : 1 ≤ ε
  · refine (prob_le_one).trans ?_
    rw [ENNReal.one_le_ofReal]; exact h1
  · have : {H : Fin 0 → Fin n → ℝ | (1 : ℝ) ≤ ε} = ∅ := by
      ext H; simp [not_le.1 h1]
    rw [this, measure_empty]; simp

lemma continuous_decProd_ml {D n : ℕ} :
    Continuous fun v : Fin D → Fin n → ℝ => decProd v := by
  unfold decProd
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun k => continuous_finsetProd _ fun j _ =>
      (continuous_apply _).comp (continuous_apply _))

lemma piFinSucc_key {D n : ℕ} (H : Fin (D + 1) → Fin n → ℝ) :
    MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0 H = (H 0, fun j => H j.succ) := by
  ext1
  · rfl
  · funext j; simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]

/-- One induction step, for a fixed threshold `η`. -/
lemma step_bound (D : ℕ) (C a : ℝ) (hC : 0 < C) (ha : 0 < a) (ih : ∀ (n : ℕ) {V : Type}
      [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (T : EuclideanSpace ℝ (Fin D → Fin n) →ₗ[ℝ] V),
      ∑ k, ‖T (EuclideanSpace.single k 1)‖ ^ 2 = 1 →
      ∀ (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s : ℝ), 0 < s → (∀ j, s ≤ σ j) →
        ∀ ε : ℝ, 0 ≤ ε →
          (Measure.pi fun _ : Fin D => nu (Fin n) 1)
              {H | ‖T (decProd (fun j => x j + σ j • H j))‖ ≤ ε * s ^ D} ≤
            ENNReal.ofReal (C * ε ^ a))
    (n : ℕ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (T : EuclideanSpace ℝ (Fin (D + 1) → Fin n) →ₗ[ℝ] V)
    (hT : ∑ k, ‖T (EuclideanSpace.single k 1)‖ ^ 2 = 1)
    (x : Fin (D + 1) → Fin n → ℝ) (σ : Fin (D + 1) → ℝ) (s : ℝ) (hs : 0 < s)
    (hσ : ∀ j, s ≤ σ j) (ε : ℝ) (hε : 0 ≤ ε) (η : ℝ) (hη : 0 < η) :
    (Measure.pi fun _ : Fin (D + 1) => nu (Fin n) 1)
        {H | ‖T (decProd (fun j => x j + σ j • H j))‖ ≤ ε * s ^ (D + 1)} ≤
      ENNReal.ofReal (Real.exp 1 * η) + ENNReal.ofReal (C * (ε / η) ^ a) := by
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  set A : Set ((Fin n → ℝ) × (Fin D → Fin n → ℝ)) :=
    {p | ‖T (decProd (Fin.cons (x 0 + σ 0 • p.1) (fun j => x j.succ + σ j.succ • p.2 j) :
      Fin (D + 1) → Fin n → ℝ))‖ ≤ ε * s ^ (D + 1)} with hA
  have hAm : MeasurableSet A := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    refine continuous_norm.comp (hTc.comp (continuous_decProd_ml.comp ?_))
    refine continuous_pi fun j => ?_
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]; fun_prop
  have hset : {H : Fin (D + 1) → Fin n → ℝ | ‖T (decProd (fun j => x j + σ j • H j))‖ ≤
      ε * s ^ (D + 1)} = MeasurableEquiv.piFinSuccAbove (fun _ => Fin n → ℝ) 0 ⁻¹' A := by
    ext H
    simp only [Set.mem_preimage, piFinSucc_key, hA, Set.mem_ofPred_eq]
    have : (fun j => x j + σ j • H j) = (Fin.cons (x 0 + σ 0 • H 0)
        (fun j => x j.succ + σ j.succ • H j.succ) : Fin (D + 1) → Fin n → ℝ) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [this]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => nu (Fin n) 1) 0
  rw [hset, hmp.measure_preimage_equiv, Measure.prod_apply hAm]
  -- the slice bound
  set B := hsMap T with hB
  have hBc : Continuous B := LinearMap.continuous_of_finiteDimensional B
  set G : Set (Fin n → ℝ) := {g | ‖B (WithLp.toLp 2 (x 0 + σ 0 • g))‖ ≤ η * s} with hG
  have hGm : MeasurableSet G := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    fun_prop
  have hslice : ∀ h0 : Fin n → ℝ,
      (Measure.pi fun _ : Fin D => nu (Fin n) 1) (Prod.mk h0 ⁻¹' A) ≤
        G.indicator 1 h0 + ENNReal.ofReal (C * (ε / η) ^ a) := by
    intro h0
    by_cases hg : h0 ∈ G
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      exact prob_le_one.trans le_self_add
    · rw [Set.indicator_of_notMem hg, zero_add]
      set w := x 0 + σ 0 • h0 with hw
      set β := ‖B (WithLp.toLp 2 w)‖ with hβ
      have hβη : η * s < β := lt_of_not_ge hg
      have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβη
      set T'' : EuclideanSpace ℝ (Fin D → Fin n) →ₗ[ℝ] V := β⁻¹ • (T ∘ₗ tensL w) with hT''
      have hT''1 : ∑ k, ‖T'' (EuclideanSpace.single k 1)‖ ^ 2 = 1 := by
        have h2 := hsMap_norm_sq T w
        rw [← hB, ← hβ] at h2
        simp only [hT'', LinearMap.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum, ← h2,
          Real.norm_eq_abs, abs_inv, abs_of_pos hβ0]
        field_simp
      have hsub : Prod.mk h0 ⁻¹' A ⊆ {H : Fin D → Fin n → ℝ |
          ‖T'' (decProd (fun j => x j.succ + σ j.succ • H j))‖ ≤ (ε * s / β) * s ^ D} := by
        intro H hH
        simp only [Set.mem_preimage, hA, Set.mem_ofPred_eq, decProd_cons] at hH
        simp only [Set.mem_ofPred_eq, hT'', LinearMap.smul_apply, LinearMap.comp_apply,
          norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hβ0]
        rw [inv_mul_le_iff₀ hβ0]
        calc _ ≤ ε * s ^ (D + 1) := hH
          _ = _ := by field_simp; ring
      refine (measure_mono hsub).trans ?_
      refine (ih n T'' hT''1 (fun j => x j.succ) (fun j => σ j.succ) s hs (fun j => hσ j.succ)
        (ε * s / β) (by positivity)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ ha.le) hC.le
      rw [div_le_div_iff₀ hβ0 hη]
      nlinarith
  calc ∫⁻ h0, (Measure.pi fun _ : Fin D => nu (Fin n) 1) (Prod.mk h0 ⁻¹' A) ∂(nu (Fin n) 1)
      ≤ ∫⁻ h0, (G.indicator 1 h0 + ENNReal.ofReal (C * (ε / η) ^ a)) ∂(nu (Fin n) 1) :=
        lintegral_mono hslice
    _ = nu (Fin n) 1 G + ENNReal.ofReal (C * (ε / η) ^ a) := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hGm, lintegral_const,
          measure_univ, mul_one]
    _ ≤ _ := by
        gcongr
        have hB1 : ∑ k, ‖B (EuclideanSpace.single k 1)‖ ^ 2 = 1 := by
          rw [hB, hsMap_hs, hT]
        have hσ0 : 0 < σ 0 := lt_of_lt_of_le hs (hσ 0)
        refine (core B hB1 (x 0) (σ 0) hσ0 (η * s) (by positivity)).trans ?_
        apply ENNReal.ofReal_le_ofReal
        rw [mul_div_assoc]
        gcongr
        rw [div_le_iff₀ hσ0]
        nlinarith [hσ 0]

lemma mlp_succ (D : ℕ) (h : MLP D) : MLP (D + 1) := by
  obtain ⟨C, hC, a, ha, ih⟩ := h
  refine ⟨Real.exp 1 + C, by positivity, a / (1 + a), by positivity, ?_⟩
  intro n V _ _ _ T hT x σ s hs hσ ε hε
  rcases hε.eq_or_lt with h0 | hpos
  · subst h0
    have hz : (0 : ℝ) ^ (a / (1 + a)) = 0 := Real.zero_rpow (by positivity)
    rw [hz, mul_zero, ENNReal.ofReal_zero]
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hb := step_bound D C a hC ha ih n T hT x σ s hs hσ 0 le_rfl
      ((δ : ℝ) / Real.exp 1) (by positivity)
    rw [zero_div, Real.zero_rpow ha.ne', mul_zero, ENNReal.ofReal_zero, add_zero,
      mul_div_cancel₀ _ (Real.exp_pos 1).ne', ENNReal.ofReal_coe_nnreal] at hb
    rw [zero_add]; exact hb
  · set a' := a / (1 + a) with ha'
    have hb := step_bound D C a hC ha ih n T hT x σ s hs hσ ε hε (ε ^ a') (by positivity)
    have hpow : (ε / ε ^ a') ^ a = ε ^ a' := by
      rw [← Real.rpow_one_sub' hpos.le (by
        have : a' < 1 := by rw [ha', div_lt_one (by positivity)]; linarith
        linarith), ← Real.rpow_mul hpos.le]
      congr 1
      rw [ha']; field_simp; ring
    rw [hpow, ← ENNReal.ofReal_add (by positivity) (by positivity)] at hb
    refine hb.trans (le_of_eq ?_)
    congr 1; ring

lemma mlp_all : ∀ D, MLP D
  | 0 => mlp_zero
  | D + 1 => mlp_succ D (mlp_all D)

theorem multilinear_small_ball (D : ℕ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℝ, 0 < a ∧
      ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
        (T : EuclideanSpace ℝ (Fin D → Fin n) →ₗ[ℝ] V),
        ∑ k, ‖T (EuclideanSpace.single k 1)‖ ^ 2 = 1 →
        ∀ (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s : ℝ), 0 < s → (∀ j, s ≤ σ j) →
          ∀ ε : ℝ, 0 ≤ ε →
            gaussDec D n {G | ‖T (decProd (pert x σ G))‖ ≤ ε * s ^ D} ≤
              ENNReal.ofReal (C * ε ^ a) := by
  obtain ⟨C, hC, a, ha, h⟩ := mlp_all D
  refine ⟨C, hC, a, ha, ?_⟩
  intro n V _ _ _ T hT x σ s hs hσ ε hε
  rw [gaussDec_eq]
  have : Function.uncurry = ⇑(MeasurableEquiv.curry (Fin D) (Fin n) ℝ).symm := rfl
  rw [this, MeasurableEquiv.map_apply]
  exact h n T hT x σ s hs hσ ε hε

end ApproxSyzygies.Smoothed.Dev.T46.PartA
end

section
/-! Echelon trees (Anari et al. 2018, Theorem 12), in a flat encoding by prefixes. -/

set_option autoImplicit false

open Module

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

variable {D n : ℕ}

abbrev Ten (D n : ℕ) := EuclideanSpace ℝ (Fin D → Fin n)

/-- The prefix of length `m` of a multi-index, padded with `none`. -/
def pre (m : ℕ) (k : Fin D → Fin n) : Fin D → Option (Fin n) :=
  fun j => if (j : ℕ) < m then some (k j) else none

/-- Truncation of a padded prefix to length `p`. -/
def truncO (p : ℕ) (Q : Fin D → Option (Fin n)) : Fin D → Option (Fin n) :=
  fun j => if (j : ℕ) < p then Q j else none

lemma truncO_pre {p m : ℕ} (h : p ≤ m) (k : Fin D → Fin n) : truncO p (pre m k) = pre p k := by
  funext j
  simp only [truncO, pre]
  split_ifs <;> first | rfl | omega

lemma pre_eq_iff (m : ℕ) (k k' : Fin D → Fin n) :
    pre m k = pre m k' ↔ ∀ j : Fin D, (j : ℕ) < m → k j = k' j := by
  constructor
  · intro h j hj
    have := congrFun h j
    simpa [pre, hj] using this
  · intro h
    funext j
    simp only [pre]
    split_ifs with hj
    · rw [h j hj]
    · rfl

lemma pre_eq_of_le {p m : ℕ} (h : p ≤ m) {k k' : Fin D → Fin n} (e : pre m k = pre m k') :
    pre p k = pre p k' := by
  rw [← truncO_pre h, ← truncO_pre h k', e]

lemma pre_D_eq {k k' : Fin D → Fin n} (e : pre D k = pre D k') : k = k' := by
  funext j
  exact (pre_eq_iff D k k').1 e j j.2

abbrev Rk (D n : ℕ) := ℕ → (Fin D → Option (Fin n)) → ℕ

/-- Leaves carry tensors of `U`, pivot `1` at the leaf, entries bounded by `1`. -/
def Basic (U : Submodule ℝ (Ten D n)) (L : Finset (Fin D → Fin n))
    (T : (Fin D → Fin n) → Ten D n) : Prop :=
  ∀ I ∈ L, T I ∈ U ∧ T I I = 1 ∧ ∀ k, |T I k| ≤ 1

/-- Echelon conditions at levels `m ≥ lo`, with sibling ranks `rk m`. -/
def Ech (lo : ℕ) (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n) :
    Prop :=
  ∀ I ∈ L, ∀ I' ∈ L, ∀ m, lo ≤ m → m < D → pre m I = pre m I' →
    (rk m (pre (m + 1) I') < rk m (pre (m + 1) I) →
        ∀ k, pre (m + 1) k = pre (m + 1) I' → T I k = 0) ∧
    (rk m (pre (m + 1) I) = rk m (pre (m + 1) I') → pre (m + 1) I = pre (m + 1) I')

/-- Branching at least `B` at levels `m ≥ lo`. -/
def Branch (lo B : ℕ) (L : Finset (Fin D → Fin n)) : Prop :=
  ∀ I ∈ L, ∀ m, lo ≤ m → m < D →
    B ≤ ((L.filter (fun a => pre m a = pre m I)).image (pre (m + 1))).card

def IsPiece (U : Submodule ℝ (Ten D n)) (p B : ℕ) (L : Finset (Fin D → Fin n))
    (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n) : Prop :=
  Basic U L T ∧ Ech p L T rk ∧ Branch p B L ∧ (∀ I ∈ L, ∀ I' ∈ L, pre p I = pre p I') ∧
    L.Nonempty

def IsTree (U : Submodule ℝ (Ten D n)) (p B : ℕ) (L : Finset (Fin D → Fin n))
    (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n) : Prop :=
  Basic U L T ∧ Ech (p - 1) L T rk ∧ Branch p B L ∧ B * n ^ (p - 1) ≤ (L.image (pre p)).card

/-- Tensors vanishing on a set of multi-indices. -/
def vanish (S : Finset (Fin D → Fin n)) : Submodule ℝ (Ten D n) where
  carrier := {T | ∀ k ∈ S, T k = 0}
  add_mem' := by
    intro a b ha hb k hk
    simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by
    intro c a ha k hk
    simp [ha k hk]

lemma finrank_inf_vanish (U : Submodule ℝ (Ten D n)) (S : Finset (Fin D → Fin n)) :
    finrank ℝ U ≤ finrank ℝ ↥(U ⊓ vanish S) + S.card := by
  let φ : Ten D n →ₗ[ℝ] (S → ℝ) :=
    LinearMap.pi fun k : S => ((EuclideanSpace.proj (k : Fin D → Fin n) : Ten D n →L[ℝ] ℝ) :
      Ten D n →ₗ[ℝ] ℝ)
  have hker : LinearMap.ker φ = vanish S := by
    ext T
    simp only [LinearMap.mem_ker, φ]
    constructor
    · intro h k hk
      have := congrFun h ⟨k, hk⟩
      simpa using this
    · intro h
      funext k
      simpa using h k.1 k.2
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker φ)
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 := Submodule.finrank_le (U ⊔ LinearMap.ker φ)
  have h4 : finrank ℝ (LinearMap.range φ) ≤ S.card := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  rw [hker] at h1 h2 h3
  omega

lemma card_pre_image_le (p : ℕ) (hp : p ≤ D) :
    ((Finset.univ : Finset (Fin D → Fin n)).image (pre p)).card ≤ n ^ p := by
  let g : (Fin p → Fin n) → (Fin D → Option (Fin n)) :=
    fun z j => if h : (j : ℕ) < p then some (z ⟨j, h⟩) else none
  have hsub : (Finset.univ : Finset (Fin D → Fin n)).image (pre p) ⊆
      (Finset.univ : Finset (Fin p → Fin n)).image g := by
    intro Q hQ
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hQ ⊢
    obtain ⟨k, rfl⟩ := hQ
    refine ⟨fun i => k ⟨i, by omega⟩, ?_⟩
    funext j
    simp only [g, pre]
    split_ifs <;> rfl
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin p → Fin n)).card := Finset.card_image_le
    _ = n ^ p := by simp

lemma slice_card (p : ℕ) (hp : p ≤ D) (P : Fin D → Option (Fin n)) :
    (Finset.univ.filter (fun k : Fin D → Fin n => pre p k = P)).card ≤ n ^ (D - p) := by
  have : n ^ (D - p) = (Finset.univ : Finset (Fin (D - p) → Fin n)).card := by simp
  rw [this]
  apply Finset.card_le_card_of_injOn (fun k (j : Fin (D - p)) => k ⟨p + j, by have := j.2; omega⟩)
  · intro _ _; simp
  · intro k hk k' hk' e
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk hk'
    have hpre := (pre_eq_iff p k k').1 (hk.trans hk'.symm)
    funext j
    by_cases hj : (j : ℕ) < p
    · exact hpre j hj
    · have := congrFun e ⟨j - p, by omega⟩
      simp only at this
      have hj' : (⟨p + (j - p), by omega⟩ : Fin D) = j := by ext; simp; omega
      rwa [hj'] at this

lemma vanish_card (p : ℕ) (hp : p ≤ D) (Ps : Finset (Fin D → Option (Fin n))) :
    (Finset.univ.filter (fun k : Fin D → Fin n => pre p k ∈ Ps)).card ≤ Ps.card * n ^ (D - p) := by
  have : Finset.univ.filter (fun k : Fin D → Fin n => pre p k ∈ Ps) =
      Ps.biUnion (fun P => Finset.univ.filter (fun k : Fin D → Fin n => pre p k = P)) := by
    ext k; simp
  rw [this]
  calc _ ≤ ∑ P ∈ Ps, (Finset.univ.filter (fun k : Fin D → Fin n => pre p k = P)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ Ps, n ^ (D - p) := Finset.sum_le_sum fun P _ => slice_card p hp P
    _ = _ := by simp

lemma filter_image_pre_eq {L L' : Finset (Fin D → Fin n)} {m : ℕ} {I : Fin D → Fin n}
    (h : ∀ a ∈ L, pre m a = pre m I → a ∈ L') (h' : L' ⊆ L) :
    L.filter (fun a => pre m a = pre m I) = L'.filter (fun a => pre m a = pre m I) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ha, e⟩; exact ⟨h a ha e, e⟩
  · rintro ⟨ha, e⟩; exact ⟨h' ha, e⟩

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

lemma gaussianPDFReal_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / 2 := by
  rw [gaussianPDFReal]
  have h1 : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := sq_nonneg (x - 0)
    push_cast
    linarith
  have h2 : (2:ℝ) ≤ √(2 * Real.pi * ((1:NNReal):ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    push_cast
    linarith [Real.pi_gt_three]
  have h3 : (√(2 * Real.pi * ((1:NNReal):ℝ)))⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have h4 : 0 ≤ (√(2 * Real.pi * ((1:NNReal):ℝ)))⁻¹ := by positivity
  calc _ ≤ (√(2 * Real.pi * ((1:NNReal):ℝ)))⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 h4
    _ ≤ 1 / 2 := by rw [mul_one]; exact h3

lemma gauss_Ioo (c h : ℝ) :
    gaussianReal 0 1 (Set.Ioo (c - h) (c + h)) ≤ ENNReal.ofReal h := by
  rw [gaussianReal_apply 0 one_ne_zero]
  calc ∫⁻ x in Set.Ioo (c - h) (c + h), gaussianPDF 0 1 x
      ≤ ∫⁻ _ in Set.Ioo (c - h) (c + h), ENNReal.ofReal (1 / 2) := by
        apply lintegral_mono
        intro x
        rw [gaussianPDF]
        exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_half x)
    _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (c + h - (c - h)) := by
        rw [setLIntegral_const, Real.volume_Ioo]
    _ = ENNReal.ofReal h := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

lemma gauss_affine (a b τ : ℝ) (ha : a ≠ 0) :
    gaussianReal 0 1 {t | |a * t + b| < τ} ≤ ENNReal.ofReal (τ / |a|) := by
  have hpos : 0 < |a| := abs_pos.mpr ha
  refine le_trans (measure_mono ?_) (gauss_Ioo (-b / a) (τ / |a|))
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht
  have e : t - (-b / a) = (a * t + b) / a := by field_simp; ring
  have : |t - (-b / a)| < τ / |a| := by
    rw [e, abs_div]
    exact div_lt_div_of_pos_right ht hpos
  rw [abs_sub_lt_iff] at this
  constructor <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma measurable_resample (i : ι) (f : (ι → ℝ) → ENNReal) (hf : Measurable f) :
    Measurable fun x : ι → ℝ => ∫⁻ t, f (Function.update x i t) ∂gaussianReal 0 1 := by
  have h := hf.lmarginal (fun _ : ι => gaussianReal 0 1) (s := {i})
  rwa [lmarginal_singleton] at h

lemma lintegral_resample (i : ι) (f : (ι → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫⁻ x, (∫⁻ t, f (Function.update x i t) ∂gaussianReal 0 1)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have key : ∀ g : (ι → ℝ) → ENNReal, Measurable g → ∀ x0,
      ∫⁻ x, g x ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
        (∫⋯∫⁻_(Finset.univ.erase i), (fun x => ∫⁻ t, g (Function.update x i t) ∂gaussianReal 0 1)
          ∂(fun _ : ι => gaussianReal 0 1)) x0 := by
    intro g hg x0
    rw [lintegral_eq_lmarginal_univ x0, lmarginal_erase' _ hg (Finset.mem_univ i)]
  rw [key f hf 0, key _ (measurable_resample i f hf) 0]
  congr 1
  ext x
  simp only [Function.update_idem, lintegral_const, measure_univ, mul_one]

lemma cond_one (i : ι) (S A : Set (ι → ℝ)) (hS : MeasurableSet S) (hA : MeasurableSet A)
    (hAi : ∀ x t, Function.update x i t ∈ A ↔ x ∈ A) (q : ENNReal)
    (hq : ∀ x, gaussianReal 0 1 {t | Function.update x i t ∈ S} ≤ q) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) (S ∩ A) ≤
      q * (Measure.pi fun _ : ι => gaussianReal 0 1) A := by
  rw [← lintegral_indicator_one (hS.inter hA),
    lintegral_resample i _ (measurable_one.indicator (hS.inter hA)),
    ← lintegral_indicator_one hA, ← lintegral_const_mul _ (measurable_one.indicator hA)]
  apply lintegral_mono
  intro x
  dsimp only
  have hmeas : MeasurableSet {t | Function.update x i t ∈ S} := measurable_update x hS
  by_cases hx : x ∈ A
  · have : (fun t => (S ∩ A).indicator (1 : (ι → ℝ) → ENNReal) (Function.update x i t)) =
        {t | Function.update x i t ∈ S}.indicator 1 := by
      ext t
      by_cases ht : Function.update x i t ∈ S
      · simp [Set.indicator, ht, (hAi x t).mpr hx]
      · simp [Set.indicator, ht]
    rw [this, lintegral_indicator_one hmeas]
    simp [Set.indicator, hx, hq x]
  · have : (fun t => (S ∩ A).indicator (1 : (ι → ℝ) → ENNReal) (Function.update x i t)) = 0 := by
      ext t
      simp [Set.indicator, (hAi x t), hx]
    rw [this, lintegral_zero_fun]
    exact zero_le

lemma seq_cond (C : Finset ι) (ρ : ι → ℕ) (hρ : Set.InjOn ρ C) (S : ι → Set (ι → ℝ))
    (hS : ∀ c ∈ C, MeasurableSet (S c))
    (hind : ∀ c ∈ C, ∀ c' ∈ C, ρ c' < ρ c → ∀ x t, Function.update x c' t ∈ S c ↔ x ∈ S c)
    (q : ENNReal) (hq : ∀ c ∈ C, ∀ x, gaussianReal 0 1 {t | Function.update x c t ∈ S c} ≤ q) :
    (Measure.pi fun _ : ι => gaussianReal 0 1) (⋂ c ∈ C, S c) ≤ q ^ C.card := by
  induction C using Finset.strongInduction with
  | H C ih =>
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨c0, hc0, hmin⟩ := C.exists_min_image ρ hne
  have hsplit : (⋂ c ∈ C, S c) = S c0 ∩ ⋂ c ∈ C.erase c0, S c := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_erase]
    constructor
    · intro h; exact ⟨h c0 hc0, fun c hc => h c hc.2⟩
    · intro h c hc
      by_cases e : c = c0
      · subst e; exact h.1
      · exact h.2 c ⟨e, hc⟩
  have hlt : ∀ c ∈ C.erase c0, ρ c0 < ρ c := by
    intro c hc
    rw [Finset.mem_erase] at hc
    rcases (hmin c hc.2).lt_or_eq with h | h
    · exact h
    · exact absurd (hρ hc0 hc.2 h).symm hc.1
  have hAm : MeasurableSet (⋂ c ∈ C.erase c0, S c) :=
    Finset.measurableSet_biInter _ fun c hc => hS c (Finset.mem_of_mem_erase hc)
  have hAi : ∀ x t, Function.update x c0 t ∈ (⋂ c ∈ C.erase c0, S c) ↔ x ∈ ⋂ c ∈ C.erase c0, S c := by
    intro x t
    simp only [Set.mem_iInter]
    constructor
    · intro h c hc
      exact (hind c (Finset.mem_of_mem_erase hc) c0 hc0 (hlt c hc) x t).mp (h c hc)
    · intro h c hc
      exact (hind c (Finset.mem_of_mem_erase hc) c0 hc0 (hlt c hc) x t).mpr (h c hc)
  rw [hsplit]
  calc _ ≤ q * (Measure.pi fun _ : ι => gaussianReal 0 1) (⋂ c ∈ C.erase c0, S c) :=
        cond_one c0 _ _ (hS c0 hc0) hAm hAi q (hq c0 hc0)
    _ ≤ q * q ^ (C.erase c0).card := by
        gcongr
        exact ih _ (Finset.erase_ssubset hc0) (hρ.mono (by simp [Set.subset_def]; tauto))
          (fun c hc => hS c (Finset.mem_of_mem_erase hc))
          (fun c hc c' hc' => hind c (Finset.mem_of_mem_erase hc) c' (Finset.mem_of_mem_erase hc'))
          (fun c hc => hq c (Finset.mem_of_mem_erase hc))
    _ = q ^ C.card := by
        rw [← pow_succ', Finset.card_erase_of_mem hc0, Nat.sub_add_cancel (Finset.card_pos.mpr hne)]

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
/-! Construction of echelon trees (Anari et al. 2018, Theorem 12), additive dimension count. -/

set_option autoImplicit false

open Module

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

variable {D n : ℕ}

lemma base_piece (p B : ℕ) (hp : D ≤ p) (V : Submodule ℝ (Ten D n)) (hV : 1 ≤ finrank ℝ V) :
    ∃ (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n),
      IsPiece V p B L T rk := by
  classical
  have hne : V ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hV; omega
  obtain ⟨T, hTV, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨k0, hk0⟩ : ∃ k, T k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT0
    ext k
    simpa using h k
  obtain ⟨I, -, hI⟩ := Finset.exists_max_image Finset.univ (fun k => |T k|)
    ⟨k0, Finset.mem_univ _⟩
  have hTI : T I ≠ 0 := by
    intro h
    have := hI k0 (Finset.mem_univ _)
    rw [h, abs_zero] at this
    exact hk0 (abs_nonpos_iff.mp this)
  refine ⟨{I}, fun _ => (T I)⁻¹ • T, fun _ _ => 0, ?_, ?_, ?_, ?_, Finset.singleton_nonempty I⟩
  · intro J hJ
    refine ⟨V.smul_mem _ hTV, ?_, ?_⟩
    · rw [Finset.mem_singleton] at hJ
      subst hJ
      rw [PiLp.smul_apply, smul_eq_mul, inv_mul_cancel₀ hTI]
    · intro k
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr hTI),
        mul_one]
      exact hI k (Finset.mem_univ _)
  · intro J _ J' _ m hm hm'
    omega
  · intro J _ m hm hm'
    omega
  · intro J hJ J' hJ'
    rw [Finset.mem_singleton] at hJ hJ'
    rw [hJ, hJ']

lemma rounds (p B R : ℕ) (hp1 : 1 ≤ p) (hpD : p ≤ D) (U : Submodule ℝ (Ten D n))
    (hpiece : ∀ V : Submodule ℝ (Ten D n), V ≤ U → R ≤ finrank ℝ V →
      ∃ (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n),
        IsPiece V p B L T rk) :
    ∀ g : ℕ, R + g * n ^ (D - p) ≤ finrank ℝ U →
      ∃ (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n),
        Basic U L T ∧ Ech (p - 1) L T rk ∧ Branch p B L ∧ (L.image (pre p)).card = g ∧
        ∀ I ∈ L, rk (p - 1) (pre p I) < g := by
  classical
  intro g
  induction g with
  | zero =>
    intro _
    refine ⟨∅, fun _ => 0, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Basic, Ech, Branch]
  | succ g ih =>
    intro hdim
    obtain ⟨L, T, rk, hB, hE, hBr, hcard, hrk⟩ :=
      ih (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ g)) R) hdim)
    set Ps := L.image (pre p) with hPs
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin D → Fin n),
        S = Finset.univ.filter (fun k : Fin D → Fin n => pre p k ∈ Ps) := ⟨_, rfl⟩
    obtain ⟨V, hV⟩ : ∃ V : Submodule ℝ (Ten D n), V = U ⊓ vanish S := ⟨_, rfl⟩
    have hVdim : R ≤ finrank ℝ V := by
      have h1 : finrank ℝ U ≤ finrank ℝ V + S.card := hV ▸ finrank_inf_vanish U S
      have h2 : S.card ≤ Ps.card * n ^ (D - p) := hS ▸ vanish_card p hpD Ps
      rw [hcard] at h2
      simp only [add_mul, one_mul] at hdim
      omega
    obtain ⟨L', T', rk', hB', hE', hBr', hpre', hne'⟩ := hpiece V (hV ▸ inf_le_left) hVdim
    obtain ⟨I0, hI0⟩ := hne'
    set P := pre p I0 with hPdef
    have hL'P : ∀ I ∈ L', pre p I = P := fun I hI => hpre' I hI I0 hI0
    have hPnot : P ∉ Ps := by
      intro hP
      have h1 := (hB' I0 hI0).1
      have h2 := (hB' I0 hI0).2.1
      rw [hV] at h1
      have := (Submodule.mem_inf.mp h1).2 I0 (by simp [hS, hP, P])
      rw [h2] at this
      exact one_ne_zero this
    have hLPs : ∀ I ∈ L, pre p I ∈ Ps := fun I hI => Finset.mem_image_of_mem _ hI
    have hLne : ∀ I ∈ L, pre p I ≠ P := fun I hI e => hPnot (e ▸ hLPs I hI)
    let T'' : (Fin D → Fin n) → Ten D n := fun I => if pre p I = P then T' I else T I
    let rk'' : Rk D n := fun m Q =>
      if truncO p Q = P then (if m + 1 = p then g else rk' m Q) else rk m Q
    have hTold : ∀ I ∈ L, T'' I = T I := fun I hI => if_neg (hLne I hI)
    have hTnew : ∀ I ∈ L', T'' I = T' I := fun I hI => if_pos (hL'P I hI)
    have hrkold : ∀ I ∈ L, ∀ m, p ≤ m + 1 → rk'' m (pre (m + 1) I) = rk m (pre (m + 1) I) := by
      intro I hI m hm
      simp only [rk'', truncO_pre hm]
      exact if_neg (hLne I hI)
    have hrknew : ∀ I ∈ L', ∀ m, p ≤ m + 1 →
        rk'' m (pre (m + 1) I) = if m + 1 = p then g else rk' m (pre (m + 1) I) := by
      intro I hI m hm
      simp only [rk'', truncO_pre hm]
      exact if_pos (hL'P I hI)
    have hdisj : ∀ I ∈ L, ∀ I' ∈ L', ∀ m, p ≤ m → pre m I ≠ pre m I' := by
      intro I hI I' hI' m hm e
      exact hLne I hI ((pre_eq_of_le hm e).trans (hL'P I' hI'))
    refine ⟨L ∪ L', T'', rk'', ?_, ?_, ?_, ?_, ?_⟩
    · intro I hI
      rcases Finset.mem_union.mp hI with h | h
      · rw [hTold I h]; exact hB I h
      · rw [hTnew I h]
        obtain ⟨a, b, c⟩ := hB' I h
        rw [hV] at a
        exact ⟨(Submodule.mem_inf.mp a).1, b, c⟩
    · intro I hI I' hI' m hm hmD hpm
      by_cases hmp : m + 1 = p
      · have hrk' : ∀ J ∈ L, rk m (pre (m + 1) J) < g := by
          intro J hJ; have := hrk J hJ; rwa [show p - 1 = m by omega, ← hmp] at this
        rcases Finset.mem_union.mp hI with h | h <;>
          rcases Finset.mem_union.mp hI' with h' | h'
        · rw [hrkold I h m (by omega), hrkold I' h' m (by omega), hTold I h]
          exact hE I h I' h' m hm hmD hpm
        · rw [hrkold I h m (by omega), hrknew I' h' m (by omega), if_pos hmp]
          have := hrk' I h
          constructor
          · intro hlt; omega
          · intro heq; omega
        · rw [hrknew I h m (by omega), hrkold I' h' m (by omega), if_pos hmp, hTnew I h]
          have := hrk' I' h'
          constructor
          · intro _ k hk
            have hmem := (Submodule.mem_inf.mp (hV ▸ (hB' I h).1)).2
            apply hmem k
            simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← hmp, hk, hmp]
            exact hLPs I' h'
          · intro heq; omega
        · rw [hrknew I h m (by omega), hrknew I' h' m (by omega), if_pos hmp, if_pos hmp]
          constructor
          · intro hlt; omega
          · intro _
            rw [hmp, hL'P I h, hL'P I' h']
      · have hpm' : p ≤ m := by omega
        rcases Finset.mem_union.mp hI with h | h <;>
          rcases Finset.mem_union.mp hI' with h' | h'
        · rw [hrkold I h m (by omega), hrkold I' h' m (by omega), hTold I h]
          exact hE I h I' h' m hm hmD hpm
        · exact absurd hpm (hdisj I h I' h' m hpm')
        · exact absurd hpm.symm (hdisj I' h' I h m hpm')
        · rw [hrknew I h m (by omega), hrknew I' h' m (by omega), if_neg hmp, if_neg hmp,
            hTnew I h]
          exact hE' I h I' h' m hpm' hmD hpm
    · intro I hI m hm hmD
      rcases Finset.mem_union.mp hI with h | h
      · rw [filter_image_pre_eq (L' := L) (fun a ha e => by
            rcases Finset.mem_union.mp ha with ha | ha
            · exact ha
            · exact absurd e.symm (hdisj I h a ha m hm)) Finset.subset_union_left]
        exact hBr I h m hm hmD
      · rw [filter_image_pre_eq (L' := L') (fun a ha e => by
            rcases Finset.mem_union.mp ha with ha | ha
            · exact absurd e (hdisj a ha I h m hm)
            · exact ha) Finset.subset_union_right]
        exact hBr' I h m hm hmD
    · have himg : L'.image (pre p) = {P} := by
        ext Q
        simp only [Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨I, hI, rfl⟩; exact hL'P I hI
        · rintro rfl; exact ⟨I0, hI0, rfl⟩
      rw [Finset.image_union, himg, Finset.union_comm, ← Finset.insert_eq,
        Finset.card_insert_of_notMem hPnot, hcard]
    · intro I hI
      rcases Finset.mem_union.mp hI with h | h
      · have := hrk I h
        simp only [rk'', truncO_pre le_rfl, if_neg (hLne I h)]
        omega
      · simp only [rk'', truncO_pre le_rfl, if_pos (hL'P I h), if_pos (show p - 1 + 1 = p by omega)]
        omega

lemma piece_of_tree (p B : ℕ) (hpD : p + 1 ≤ D) (hB : 1 ≤ B) (hn : 1 ≤ n)
    (V : Submodule ℝ (Ten D n))
    (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n)
    (h : IsTree V (p + 1) B L T rk) :
    ∃ (L' : Finset (Fin D → Fin n)) (T' : (Fin D → Fin n) → Ten D n) (rk' : Rk D n),
      IsPiece V p B L' T' rk' := by
  classical
  obtain ⟨hB0, hE, hBr, hcard⟩ := h
  simp only [Nat.add_sub_cancel] at hE hcard
  set s := L.image (pre (p + 1)) with hs
  set t := (Finset.univ : Finset (Fin D → Fin n)).image (pre p) with ht
  have hmaps : ∀ a ∈ s, truncO p a ∈ t := by
    intro a ha
    obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp ha
    rw [truncO_pre (Nat.le_succ p)]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hpos : 1 ≤ B * n ^ p := Nat.mul_le_mul hB (Nat.one_le_pow _ _ hn)
  have hsne : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hsne
    exact ⟨_, hmaps a ha⟩
  have hct : t.card * B ≤ s.card :=
    le_trans (Nat.mul_le_mul_right B (card_pre_image_le p (by omega)))
      (by rw [mul_comm]; exact hcard)
  obtain ⟨P, -, hP⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps htne hct
  have hfib : s.filter (fun a => truncO p a = P) =
      (L.filter (fun a => pre p a = P)).image (pre (p + 1)) := by
    rw [hs, Finset.filter_image]
    congr 1
    ext a
    simp [truncO_pre (Nat.le_succ p)]
  rw [hfib] at hP
  refine ⟨L.filter (fun a => pre p a = P), T, rk, ?_, ?_, ?_, ?_, ?_⟩
  · intro I hI
    exact hB0 I (Finset.mem_filter.mp hI).1
  · intro I hI I' hI' m hm hmD hpm
    exact hE I (Finset.mem_filter.mp hI).1 I' (Finset.mem_filter.mp hI').1 m hm hmD hpm
  · intro I hI m hm hmD
    have hIP := (Finset.mem_filter.mp hI).2
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · have : (L.filter (fun a => pre p a = P)).filter (fun a => pre p a = pre p I) =
          L.filter (fun a => pre p a = P) := by
        ext a
        simp only [Finset.mem_filter, hIP]
        tauto
      rw [this]
      exact hP
    · have : (L.filter (fun a => pre p a = P)).filter (fun a => pre m a = pre m I) =
          L.filter (fun a => pre m a = pre m I) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨ha, -⟩, e⟩; exact ⟨ha, e⟩
        · rintro ⟨ha, e⟩; exact ⟨⟨ha, (pre_eq_of_le hlt.le e).trans hIP⟩, e⟩
      rw [this]
      exact hBr I (Finset.mem_filter.mp hI).1 m hlt hmD
  · intro I hI I' hI'
    rw [(Finset.mem_filter.mp hI).2, (Finset.mem_filter.mp hI').2]
  · have : 0 < ((L.filter (fun a => pre p a = P)).image (pre (p + 1))).card := by omega
    exact Finset.image_nonempty.mp (Finset.card_pos.mp this)

lemma tree_exists (B : ℕ) (hB : 1 ≤ B) (hn : 1 ≤ n) :
    ∀ j p, p + j = D → 1 ≤ p → ∀ U : Submodule ℝ (Ten D n),
      1 + (j + 1) * (B * n ^ (D - 1)) ≤ finrank ℝ U →
      ∃ (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n) (rk : Rk D n),
        IsTree U p B L T rk := by
  intro j
  have hpow : ∀ p, 1 ≤ p → p ≤ D → B * n ^ (p - 1) * n ^ (D - p) = B * n ^ (D - 1) := by
    intro p hp1 hpD
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  induction j with
  | zero =>
    intro p hp hp1 U hU
    obtain ⟨L, T, rk, h1, h2, h3, h4, -⟩ := rounds p B 1 hp1 (by omega) U
      (fun V _ hV => base_piece p B (by omega) V hV) (B * n ^ (p - 1))
      (by rw [hpow p hp1 (by omega)]; omega)
    exact ⟨L, T, rk, h1, h2, h3, h4.ge⟩
  | succ j ih =>
    intro p hp hp1 U hU
    obtain ⟨L, T, rk, h1, h2, h3, h4, -⟩ := rounds p B (1 + (j + 1) * (B * n ^ (D - 1)))
      hp1 (by omega) U
      (fun V _ hV => by
        obtain ⟨L, T, rk, h⟩ := ih (p + 1) (by omega) (by omega) V hV
        exact piece_of_tree p B (by omega) hB hn V L T rk h) (B * n ^ (p - 1))
      (by
        rw [hpow p hp1 (by omega)]
        have : 1 + (j + 1) * (B * n ^ (D - 1)) + B * n ^ (D - 1) =
            1 + (j + 1 + 1) * (B * n ^ (D - 1)) := by ring
        omega)
    exact ⟨L, T, rk, h1, h2, h3, h4.ge⟩

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
/-! Partial contractions of a leaf tensor with the perturbed vectors. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

variable {D n : ℕ}

def prodFrom (m : ℕ) (k : Fin D → Fin n) (y : Fin D → Fin n → ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin D => m ≤ (j : ℕ)), y j (k j)

/-- `T(e_{I|m}, y_m, …, y_{D-1})`. -/
def val (A : Ten D n) (I : Fin D → Fin n) (m : ℕ) (y : Fin D → Fin n → ℝ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => pre m k = pre m I), A k * prodFrom m k y

lemma prodFrom_succ (mD : Fin D) (k : Fin D → Fin n) (y : Fin D → Fin n → ℝ) :
    prodFrom mD k y = y mD (k mD) * prodFrom ((mD : ℕ) + 1) k y := by
  unfold prodFrom
  have : Finset.univ.filter (fun j : Fin D => (mD : ℕ) ≤ j) =
      insert mD (Finset.univ.filter (fun j : Fin D => (mD : ℕ) + 1 ≤ j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.eq_or_lt_of_le h with h | h
      · left; exact (Fin.ext h).symm
      · right; omega
    · rintro (h | h)
      · rw [h]
      · omega
  rw [this, Finset.prod_insert (by simp)]

lemma prodFrom_congr (m : ℕ) (k : Fin D → Fin n) (y y' : Fin D → Fin n → ℝ)
    (h : ∀ j : Fin D, m ≤ (j : ℕ) → y j = y' j) : prodFrom m k y = prodFrom m k y' :=
  Finset.prod_congr rfl fun j hj => by
    rw [h j (by simpa using hj)]

lemma val_congr (A : Ten D n) (I : Fin D → Fin n) (m : ℕ) (y y' : Fin D → Fin n → ℝ)
    (h : ∀ j : Fin D, m ≤ (j : ℕ) → y j = y' j) : val A I m y = val A I m y' :=
  Finset.sum_congr rfl fun k _ => by rw [prodFrom_congr m k y y' h]

lemma val_D (A : Ten D n) (I : Fin D → Fin n) (y : Fin D → Fin n → ℝ) : val A I D y = A I := by
  unfold val
  have : Finset.univ.filter (fun k => pre D k = pre D I) = {I} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨pre_D_eq, fun h => h ▸ rfl⟩
  rw [this, Finset.sum_singleton]
  have : prodFrom D I y = 1 := by
    unfold prodFrom
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    omega
  rw [this, mul_one]

lemma val_zero (A : Ten D n) (I : Fin D → Fin n) (y : Fin D → Fin n → ℝ) :
    val A I 0 y = inner ℝ A (decProd y) := by
  unfold val prodFrom decProd
  rw [PiLp.inner_apply]
  have h1 : Finset.univ.filter (fun k => pre 0 k = pre 0 I) = Finset.univ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (pre_eq_iff 0 k I).2 (fun j hj => absurd hj (Nat.not_lt_zero _))
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.filter_true_of_mem, Finset.mem_univ, implies_true, zero_le, Real.inner_apply]
  try simp
  try ring

lemma pre_succ_iff (mD : Fin D) (k I : Fin D → Fin n) :
    pre ((mD : ℕ) + 1) k = pre ((mD : ℕ) + 1) I ↔ pre mD k = pre mD I ∧ k mD = I mD := by
  simp only [pre_eq_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h mD (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact h1 j h
    · have : j = mD := Fin.ext h
      subst this
      exact h2

lemma pert_update_ne (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (G : Fin D × Fin n → ℝ)
    (c : Fin D × Fin n) (t : ℝ) (j : Fin D) (hj : j ≠ c.1) :
    pert x σ (Function.update G c t) j = pert x σ G j := by
  funext k
  have : (j, k) ≠ c := fun h => hj (by rw [← h])
  simp [pert, Function.update_of_ne this]

lemma pert_update_same (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (G : Fin D × Fin n → ℝ)
    (mD : Fin D) (i : Fin n) (t : ℝ) (k : Fin n) :
    pert x σ (Function.update G (mD, i) t) mD k =
      pert x σ (Function.update G (mD, i) 0) mD k + if k = i then σ mD * t else 0 := by
  by_cases hk : k = i
  · subst hk; simp [pert]
  · have : (mD, k) ≠ (mD, i) := fun h => hk (Prod.ext_iff.mp h).2
    simp [pert, Function.update_of_ne this, hk]

lemma val_high_update (A : Ten D n) (I : Fin D → Fin n) (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ)
    (G : Fin D × Fin n → ℝ) (c : Fin D × Fin n) (t : ℝ) (m : ℕ) (hm : (c.1 : ℕ) < m) :
    val A I m (pert x σ (Function.update G c t)) = val A I m (pert x σ G) :=
  val_congr A I m _ _ fun j hj => pert_update_ne x σ G c t j (fun h => by subst h; omega)

lemma val_affine (A : Ten D n) (I : Fin D → Fin n) (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ)
    (G : Fin D × Fin n → ℝ) (mD : Fin D) (t : ℝ) :
    val A I mD (pert x σ (Function.update G (mD, I mD) t)) =
      σ mD * val A I ((mD : ℕ) + 1) (pert x σ G) * t +
        val A I mD (pert x σ (Function.update G (mD, I mD) 0)) := by
  unfold val
  simp_rw [prodFrom_succ mD]
  have hP : ∀ k (s : ℝ), prodFrom ((mD : ℕ) + 1) k (pert x σ (Function.update G (mD, I mD) s)) =
      prodFrom ((mD : ℕ) + 1) k (pert x σ G) := fun k s =>
    prodFrom_congr _ k _ _ fun j hj => pert_update_ne x σ G _ s j (fun h => by subst h; simp at hj)
  simp_rw [hP, pert_update_same x σ G mD (I mD) t]
  have : ∀ k, A k * ((pert x σ (Function.update G (mD, I mD) 0) mD (k mD) +
        if k mD = I mD then σ mD * t else 0) * prodFrom ((mD : ℕ) + 1) k (pert x σ G)) =
      (if k mD = I mD then σ mD * t * (A k * prodFrom ((mD : ℕ) + 1) k (pert x σ G)) else 0) +
        A k * (pert x σ (Function.update G (mD, I mD) 0) mD (k mD) *
          prodFrom ((mD : ℕ) + 1) k (pert x σ G)) := by
    intro k; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    ← Finset.mul_sum, Finset.filter_filter]
  have hf : Finset.univ.filter (fun k : Fin D → Fin n => pre mD k = pre mD I ∧ k mD = I mD) =
      Finset.univ.filter (fun k => pre ((mD : ℕ) + 1) k = pre ((mD : ℕ) + 1) I) := by
    ext k; simp [pre_succ_iff]
  rw [hf]
  ring

lemma val_vanish_update (A : Ten D n) (I : Fin D → Fin n) (x : Fin D → Fin n → ℝ)
    (σ : Fin D → ℝ) (G : Fin D × Fin n → ℝ) (mD : Fin D) (i' : Fin n) (t : ℝ)
    (hA : ∀ k, pre mD k = pre mD I → k mD = i' → A k = 0) :
    val A I mD (pert x σ (Function.update G (mD, i') t)) = val A I mD (pert x σ G) := by
  unfold val
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  by_cases h : k mD = i'
  · rw [hA k hk h, zero_mul, zero_mul]
  · rw [prodFrom_succ mD, prodFrom_succ mD]
    have h1 : prodFrom ((mD : ℕ) + 1) k (pert x σ (Function.update G (mD, i') t)) =
        prodFrom ((mD : ℕ) + 1) k (pert x σ G) :=
      prodFrom_congr _ k _ _ fun j hj => pert_update_ne x σ G _ t j (fun e => by subst e; simp at hj)
    have h2 : pert x σ (Function.update G (mD, i') t) mD (k mD) = pert x σ G mD (k mD) := by
      have : (mD, k mD) ≠ (mD, i') := fun e => h (Prod.ext_iff.mp e).2
      simp [pert, Function.update_of_ne this]
    rw [h1, h2]

lemma continuous_val (A : Ten D n) (I : Fin D → Fin n) (m : ℕ) (x : Fin D → Fin n → ℝ)
    (σ : Fin D → ℝ) : Continuous fun G : Fin D × Fin n → ℝ => val A I m (pert x σ G) := by
  unfold val prodFrom pert
  fun_prop

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
/-! The bottom-up reduction of an echelon tree, one node at a time (Anari et al. 2018, §3.2). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

variable {D n : ℕ}

section
variable (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n)
  (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (w : ℝ)

/-- Node `I|m` is good: some leaf below it has contraction at least `w^(D-m)`. -/
def Good (m : ℕ) (I : Fin D → Fin n) (G : Fin D × Fin n → ℝ) : Prop :=
  ∃ a ∈ L, pre m a = pre m I ∧ w ^ (D - m) ≤ |val (T a) a m (pert x σ G)|

/-- Node `I|m` is bad: all its children are good but it is not. -/
def bad (m : ℕ) (I : Fin D → Fin n) : Set (Fin D × Fin n → ℝ) :=
  {G | (∀ a ∈ L, pre m a = pre m I → Good L T x σ w (m + 1) a G) ∧ ¬ Good L T x σ w m I G}

lemma good_root (hT : ∀ I ∈ L, T I I = 1) (G : Fin D × Fin n → ℝ)
    (hG : ∀ m < D, ∀ I ∈ L, G ∉ bad L T x σ w m I) : ∀ I ∈ L, Good L T x σ w 0 I G := by
  have key : ∀ j, j ≤ D → ∀ I ∈ L, Good L T x σ w (D - j) I G := by
    intro j
    induction j with
    | zero =>
      intro _ I hI
      refine ⟨I, hI, rfl, ?_⟩
      rw [Nat.sub_zero, val_D, hT I hI, Nat.sub_self, pow_zero, abs_one]
    | succ j ih =>
      intro hj I hI
      have h := hG (D - (j + 1)) (by omega) I hI
      simp only [bad, Set.mem_setOf_eq, not_and, not_not] at h
      apply h
      intro a ha _
      have := ih (by omega) a ha
      rwa [show D - (j + 1) + 1 = D - j by omega]
  intro I hI
  simpa using key D le_rfl I hI

end

lemma node_bound (B : ℕ) (L : Finset (Fin D → Fin n)) (T : (Fin D → Fin n) → Ten D n)
    (rk : Rk D n) (hE : Ech 0 L T rk) (hBr : Branch 0 B L)
    (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s w : ℝ) (hs : 0 < s) (hσ : ∀ j, s ≤ σ j)
    (hw : 0 < w) (hws : w ≤ s) (mD : Fin D) (I : Fin D → Fin n) (hI : I ∈ L) :
    gaussDec D n (bad L T x σ w mD I) ≤ ENNReal.ofReal (w / s) ^ B := by
  classical
  set m : ℕ := (mD : ℕ) with hm
  set F := L.filter (fun a => pre m a = pre m I) with hF
  set C : Finset (Fin D × Fin n) := F.image (fun a => (mD, a mD)) with hC
  let g' : Fin D × Fin n → Fin D → Option (Fin n) := fun c j =>
    if (j : ℕ) < m then pre m I j else if (j : ℕ) = m then some c.2 else none
  have hg' : ∀ a ∈ F, g' (mD, a mD) = pre (m + 1) a := by
    intro a ha
    have hpa := (Finset.mem_filter.mp ha).2
    funext j
    simp only [g']
    by_cases h1 : (j : ℕ) < m
    · rw [if_pos h1]
      have := congrFun hpa j
      rw [← this]
      simp only [pre]
      rw [if_pos h1, if_pos (by omega)]
    · by_cases h2 : (j : ℕ) = m
      · rw [if_neg h1, if_pos h2]
        have e : j = mD := Fin.ext (h2.trans hm)
        simp only [pre]
        rw [if_pos (by omega), e]
      · rw [if_neg h1, if_neg h2]
        simp only [pre]
        rw [if_neg (by omega)]
  let ρ : Fin D × Fin n → ℕ := fun c => rk m (g' c)
  -- the cylinder sets
  let w1 : ℝ := w ^ (D - (m + 1))
  let w2 : ℝ := w ^ (D - m)
  let V1 : (Fin D → Fin n) → (Fin D × Fin n → ℝ) → ℝ := fun a G => val (T a) a (m + 1) (pert x σ G)
  let V0 : (Fin D → Fin n) → (Fin D × Fin n → ℝ) → ℝ := fun a G => val (T a) a m (pert x σ G)
  let S : Fin D × Fin n → Set (Fin D × Fin n → ℝ) := fun c =>
    {G | (∃ a, a ∈ F ∧ a mD = c.2 ∧ w1 ≤ |V1 a G|) ∧
      ∀ a, a ∈ F → a mD = c.2 → w1 ≤ |V1 a G| → |V0 a G| < w2}
  have hcard : B ≤ C.card := by
    have h1 := hBr I hI m (Nat.zero_le _) mD.2
    have h2 : (F.image (pre (m + 1))) = C.image g' := by
      rw [hC, Finset.image_image]
      exact (Finset.image_congr fun a ha => (hg' a ha).symm)
    rw [← hF, h2] at h1
    exact h1.trans Finset.card_image_le
  have hsub : bad L T x σ w m I ⊆ ⋂ c ∈ C, S c := by
    intro G hG
    simp only [bad, Set.mem_setOf_eq] at hG
    obtain ⟨hch, hnot⟩ := hG
    simp only [Set.mem_iInter]
    intro c hc
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hc
    have ha0' := Finset.mem_filter.mp ha0
    constructor
    · obtain ⟨a, ha, hpa, hv⟩ := hch a0 ha0'.1 ha0'.2
      have hpa' := (pre_succ_iff mD a a0).1 hpa
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, hpa'.1.trans ha0'.2⟩, hpa'.2, ?_⟩
      exact hv
    · intro a ha _ _
      have ha' := Finset.mem_filter.mp ha
      by_contra hc'
      exact hnot ⟨a, ha'.1, ha'.2, not_lt.mp hc'⟩
  have hmeasS : ∀ c, MeasurableSet (S c) := by
    intro c
    have hP : ∀ a, Measurable fun G => w1 ≤ |V1 a G| := fun a =>
      measurableSet_setOf.mp
        (isClosed_le continuous_const (continuous_abs.comp (continuous_val _ _ _ x σ))).measurableSet
    have hQ : ∀ a, Measurable fun G => |V0 a G| < w2 := fun a =>
      measurableSet_setOf.mp
        (isOpen_lt (continuous_abs.comp (continuous_val _ _ _ x σ)) continuous_const).measurableSet
    exact measurableSet_setOf.mpr
      ((Measurable.exists fun a => measurable_const.and (measurable_const.and (hP a))).and
        (Measurable.forall fun a => measurable_const.imp (measurable_const.imp
          ((hP a).imp (hQ a)))))
  have hinj : Set.InjOn ρ C := by
    intro c1 hc1 c2 hc2 e
    obtain ⟨a1, ha1, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨a2, ha2, rfl⟩ := Finset.mem_image.mp hc2
    simp only [ρ, hg' a1 ha1, hg' a2 ha2] at e
    have h1 := Finset.mem_filter.mp ha1
    have h2 := Finset.mem_filter.mp ha2
    have := (hE a1 h1.1 a2 h2.1 m (Nat.zero_le _) mD.2 (h1.2.trans h2.2.symm)).2 e
    have := ((pre_succ_iff mD a1 a2).1 this).2
    simp [this]
  have hind : ∀ c ∈ C, ∀ c' ∈ C, ρ c' < ρ c → ∀ G t,
      Function.update G c' t ∈ S c ↔ G ∈ S c := by
    intro c hc c' hc' hlt G t
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hc'
    simp only [ρ, hg' a0 ha0, hg' a' ha'] at hlt
    have hV1 : ∀ a, V1 a (Function.update G (mD, a' mD) t) = V1 a G := fun a =>
      val_high_update _ _ x σ G _ t _ (by simp [hm])
    have hV0 : ∀ a ∈ F, a mD = a0 mD →
        V0 a (Function.update G (mD, a' mD) t) = V0 a G := by
      intro a ha haD
      apply val_vanish_update
      intro k hk hkD
      have hA := Finset.mem_filter.mp ha
      have hA' := Finset.mem_filter.mp ha'
      have hpre : pre m a = pre m a' := hA.2.trans hA'.2.symm
      have hrk : rk m (pre (m + 1) a') < rk m (pre (m + 1) a) := by
        have e : pre (m + 1) a = pre (m + 1) a0 :=
          (pre_succ_iff mD a a0).2 ⟨hA.2.trans (Finset.mem_filter.mp ha0).2.symm, haD⟩
        rw [e]; exact hlt
      exact (hE a hA.1 a' hA'.1 m (Nat.zero_le _) mD.2 hpre).1 hrk k
        ((pre_succ_iff mD k a').2 ⟨hk.trans hpre, hkD⟩)
    simp only [S, Set.mem_setOf_eq, hV1]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun a ha haD hv => ?_⟩
      rw [← hV0 a ha haD]; exact h2 a ha haD hv
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun a ha haD hv => ?_⟩
      rw [hV0 a ha haD]; exact h2 a ha haD hv
  have hq : ∀ c ∈ C, ∀ G, gaussianReal 0 1 {t | Function.update G c t ∈ S c} ≤
      ENNReal.ofReal (w / s) := by
    intro c hc G
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hc
    have hV1 : ∀ a t, V1 a (Function.update G (mD, a0 mD) t) = V1 a G := fun a t =>
      val_high_update _ _ x σ G _ t _ (by simp [hm])
    by_cases hex : ∃ a, a ∈ F ∧ a mD = a0 mD ∧ w1 ≤ |V1 a G|
    · obtain ⟨a, ha, haD, hv⟩ := hex
      have hsub2 : {t | Function.update G (mD, a0 mD) t ∈ S (mD, a0 mD)} ⊆
          {t | |(σ mD * V1 a G) * t + V0 a (Function.update G (mD, a mD) 0)| < w2} := by
        intro t ht
        simp only [S, Set.mem_setOf_eq, hV1] at ht
        have := ht.2 a ha haD hv
        simp only [Set.mem_setOf_eq]
        rw [← haD] at this
        simp only [V0] at this
        rw [val_affine] at this
        exact this
      have hw1 : 0 < w1 := pow_pos hw _
      have hσm : 0 < σ mD := lt_of_lt_of_le hs (hσ mD)
      have hV1pos : 0 < |V1 a G| := lt_of_lt_of_le hw1 hv
      have hα : σ mD * V1 a G ≠ 0 := mul_ne_zero hσm.ne' (abs_pos.mp hV1pos)
      refine (measure_mono hsub2).trans ((gauss_affine _ _ _ hα).trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [abs_mul, abs_of_pos hσm, div_le_div_iff₀ (mul_pos hσm hV1pos) hs]
      have hw2 : w2 = w * w1 := by
        simp only [w1, w2]
        rw [← pow_succ']
        congr 1
        have := mD.2
        omega
      rw [hw2]
      have : w * w1 * s ≤ w * (σ mD * |V1 a G|) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hw.le
        rw [mul_comm]
        exact mul_le_mul (hσ mD) hv hw1.le hσm.le
      linarith
    · have : {t | Function.update G (mD, a0 mD) t ∈ S (mD, a0 mD)} = ∅ := by
        ext t
        simp only [S, Set.mem_setOf_eq, hV1, Set.mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd h hex
      rw [this, measure_empty]
      exact zero_le
  calc gaussDec D n (bad L T x σ w mD I) ≤ gaussDec D n (⋂ c ∈ C, S c) := measure_mono hsub
    _ ≤ ENNReal.ofReal (w / s) ^ C.card :=
        seq_cond C ρ hinj S (fun c _ => hmeasS c) hind _ hq
    _ ≤ ENNReal.ofReal (w / s) ^ B := by
        apply pow_le_pow_right_of_le_one' _ hcard
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((div_le_one hs).mpr hws)

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
/-! Part ADM of Theorem 4.6: the decoupled small-ball bound in the regime `δ n ≥ K log (n + 2)`
(Anari et al. 2018, Lemma 6 via echelon trees). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Module

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

lemma norm_le_of_entries {D n : ℕ} (A : Ten D n) (h : ∀ k, |A k| ≤ 1) :
    ‖A‖ ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by
  rw [EuclideanSpace.norm_eq]
  have h1 : ∑ k, ‖A k‖ ^ 2 ≤ ((n : ℝ) ^ D) := by
    calc ∑ k, ‖A k‖ ^ 2 ≤ ∑ _k : Fin D → Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [Real.norm_eq_abs, sq_abs]
          have := h k
          have h0 := abs_nonneg (A k)
          nlinarith [sq_abs (A k)]
      _ = (n : ℝ) ^ D := by simp
  calc √(∑ k, ‖A k‖ ^ 2) ≤ √((n : ℝ) ^ D) := Real.sqrt_le_sqrt h1
    _ = (n : ℝ) ^ ((D : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        ring

lemma real_bound (D n B : ℕ) (hD : 1 ≤ D) (δ : ℝ)
    (hB : δ * n < 2 * D * (B + 1)) (hlog : 15 * D * Real.log (n + 2) ≤ δ * n)
    (hdn : 10 * (D : ℝ) ≤ δ * n) :
    (D : ℝ) * (n : ℝ) ^ D * Real.exp (-(4 * D)) ^ B ≤ Real.exp (-(1 / 2 * δ * n)) := by
  have h1 : (D : ℝ) ≤ Real.exp D := by linarith [Real.add_one_le_exp (D : ℝ)]
  have h2 : (n : ℝ) ^ D ≤ Real.exp (D * Real.log (n + 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) D
  have h3 : Real.exp (-(4 * D)) ^ B = Real.exp (B * (-(4 * D))) := (Real.exp_nat_mul _ B).symm
  rw [h3]
  calc (D : ℝ) * (n : ℝ) ^ D * Real.exp (B * (-(4 * D)))
      ≤ Real.exp D * Real.exp (D * Real.log (n + 2)) * Real.exp (B * (-(4 * D))) := by
        gcongr
    _ = Real.exp (D + D * Real.log (n + 2) + B * (-(4 * D))) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(1 / 2 * δ * n)) := by
        apply Real.exp_le_exp.mpr
        nlinarith

end ApproxSyzygies.Smoothed.Dev.T46.PartB

namespace ApproxSyzygies.Smoothed.Dev.T46.PartB

open ApproxSyzygies.Smoothed.Dev.T46

/-- **Part ADM** (Anari et al. 2018, Lemma 6 via echelon trees, Theorem 12): the decoupled small
ball bound in the regime `δ n ≥ K log (n + 2)`. Shifts `x_j` arbitrary, standard deviations
`σ_j ≥ s > 0`. -/
theorem adm_large (D : ℕ) (hD : 1 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ (n : ℕ) (δ : ℝ), 0 < δ → K * Real.log (n + 2) ≤ δ * n →
        ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)),
          δ * (n : ℝ) ^ D ≤ (Module.finrank ℝ W : ℝ) →
          ∀ (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s : ℝ), 0 < s → (∀ j, s ≤ σ j) →
            gaussDec D n {G | ‖W.starProjection (decProd (pert x σ G))‖ ≤
                c' * s ^ D / (n : ℝ) ^ ((D : ℝ) / 2)}
              ≤ ENNReal.ofReal (Real.exp (-(c * δ * n))) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨15 * D, by positivity, 1 / 2, by norm_num, Real.exp (-(4 * D) * D) / 2, by positivity, ?_⟩
  intro n δ hδ hK W hW x σ s hs hσ
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogn : Real.log 2 ≤ Real.log (n + 2) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hdn : 10 * (D : ℝ) ≤ δ * n := by nlinarith
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hdn; linarith
    · exact h
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the branching number
  set B : ℕ := ⌊δ * n / (2 * D)⌋₊ with hBdef
  have hBle : (B : ℝ) ≤ δ * n / (2 * D) := Nat.floor_le (by positivity)
  have hBlt : δ * n / (2 * D) < B + 1 := Nat.lt_floor_add_one _
  have hB1 : 1 ≤ B := by
    rw [hBdef, Nat.one_le_floor_iff, le_div_iff₀ (by positivity)]
    linarith
  have hBlt' : δ * n < 2 * D * (B + 1) := by
    rw [div_lt_iff₀ (by positivity)] at hBlt
    linarith
  have hBle' : 2 * D * (B : ℝ) ≤ δ * n := by
    rwa [le_div_iff₀ (by positivity), mul_comm] at hBle
  -- the echelon tree
  have hdim : 1 + (D - 1 + 1) * (B * n ^ (D - 1)) ≤ finrank ℝ W := by
    have e : D - 1 + 1 = D := by omega
    rw [e]
    have hpow : (n : ℝ) ^ D = n * (n : ℝ) ^ (D - 1) := by
      rw [← pow_succ', e]
    have h1 : ((1 + D * (B * n ^ (D - 1)) : ℕ) : ℝ) ≤ (finrank ℝ W : ℝ) := by
      push_cast
      have hp1 : (1 : ℝ) ≤ (n : ℝ) ^ (D - 1) := one_le_pow₀ hnR
      have : (D : ℝ) * (B * (n : ℝ) ^ (D - 1)) ≤ δ * (n : ℝ) ^ D / 2 := by
        rw [hpow]
        have : 0 ≤ (n : ℝ) ^ (D - 1) := by positivity
        nlinarith
      have : (1 : ℝ) ≤ δ * (n : ℝ) ^ D / 2 := by
        rw [hpow]
        have h0 : 0 ≤ δ * n := by positivity
        have := mul_le_mul_of_nonneg_left hp1 h0
        have e2 : δ * (n * (n : ℝ) ^ (D - 1)) = δ * n * (n : ℝ) ^ (D - 1) := by ring
        rw [e2]
        linarith
      linarith
    exact_mod_cast h1
  obtain ⟨L, T, rk, hBas, hE, hBr, hroot⟩ :=
    tree_exists (D := D) (n := n) B hB1 hn (D - 1) 1 (by omega) le_rfl W hdim
  simp only [Nat.sub_self, pow_zero, mul_one] at hE hroot
  have hBr0 : Branch 0 B L := by
    intro I hI m _ hmD
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : L.filter (fun a => pre 0 a = pre 0 I) = L := by
        ext a
        simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro _
        exact (pre_eq_iff 0 a I).2 (fun j hj => absurd hj (Nat.not_lt_zero _))
      rw [this]
      exact hroot
    · exact hBr I hI m hm hmD
  -- the scale
  set w : ℝ := s * Real.exp (-(4 * D)) with hwdef
  have hw : 0 < w := by positivity
  have hws : w ≤ s := by
    rw [hwdef]
    have : Real.exp (-(4 * D)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hq : w / s = Real.exp (-(4 * D)) := by
    rw [hwdef]; field_simp
  -- the event is covered by the bad nodes
  have hcover : {G | ‖W.starProjection (decProd (pert x σ G))‖ ≤
      Real.exp (-(4 * D) * D) / 2 * s ^ D / (n : ℝ) ^ ((D : ℝ) / 2)} ⊆
      ⋃ mD ∈ (Finset.univ : Finset (Fin D)), ⋃ I ∈ L, bad L T x σ w mD I := by
    intro G hG
    by_contra hcon
    have hgood := good_root L T x σ w (fun I hI => (hBas I hI).2.1) G
      (fun m hm I hI hb => hcon (Set.mem_iUnion₂.mpr ⟨⟨m, hm⟩, Finset.mem_univ _,
        Set.mem_iUnion₂.mpr ⟨I, hI, hb⟩⟩))
    obtain ⟨I0, hI0⟩ : L.Nonempty := by
      rw [← Finset.image_nonempty (f := pre 1), ← Finset.card_pos]; omega
    obtain ⟨a, ha, -, hval⟩ := hgood I0 hI0
    rw [Nat.sub_zero, val_zero] at hval
    set v := decProd (pert x σ G)
    have hin : inner ℝ (T a) v = inner ℝ (T a) (W.starProjection v) := by
      rw [← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr (hBas a ha).1]
    rw [hin] at hval
    have hcs := abs_real_inner_le_norm (T a) (W.starProjection v)
    have hTn := norm_le_of_entries (T a) (hBas a ha).2.2
    have hnpos : 0 < (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    simp only [Set.mem_ofPred_eq] at hG
    have hP0 : 0 ≤ ‖W.starProjection v‖ := norm_nonneg _
    have key : w ^ D ≤ (n : ℝ) ^ ((D : ℝ) / 2) * ‖W.starProjection v‖ :=
      hval.trans (hcs.trans (mul_le_mul_of_nonneg_right hTn hP0))
    have key2 : (n : ℝ) ^ ((D : ℝ) / 2) * ‖W.starProjection v‖ ≤
        Real.exp (-(4 * D) * D) / 2 * s ^ D := by
      rw [le_div_iff₀ hnpos] at hG
      linarith
    have hwD : w ^ D = Real.exp (-(4 * D) * D) * s ^ D := by
      rw [hwdef, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    have : 0 < Real.exp (-(4 * D) * D) * s ^ D := by positivity
    linarith
  -- union bound
  calc gaussDec D n {G | ‖W.starProjection (decProd (pert x σ G))‖ ≤
        Real.exp (-(4 * D) * D) / 2 * s ^ D / (n : ℝ) ^ ((D : ℝ) / 2)}
      ≤ gaussDec D n (⋃ mD ∈ (Finset.univ : Finset (Fin D)), ⋃ I ∈ L, bad L T x σ w mD I) :=
        measure_mono hcover
    _ ≤ ∑ mD : Fin D, ∑ I ∈ L, gaussDec D n (bad L T x σ w mD I) := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun mD _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _mD : Fin D, ∑ _I ∈ L, ENNReal.ofReal (w / s) ^ B := by
        gcongr with mD _ I hI
        exact node_bound B L T rk hE hBr0 x σ s w hs hσ hw hws mD I hI
    _ = ENNReal.ofReal ((D : ℝ) * (L.card : ℝ) * Real.exp (-(4 * D)) ^ B) := by
        rw [hq, Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (Real.exp_pos _).le, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.exp (-(1 / 2 * δ * n))) := by
        apply ENNReal.ofReal_le_ofReal
        refine le_trans ?_ (real_bound D n B hD δ hBlt' (by linarith) hdn)
        have hL : (L.card : ℝ) ≤ (n : ℝ) ^ D := by
          have := Finset.card_le_univ L
          simp only [Fintype.card_fun, Fintype.card_fin] at this
          exact_mod_cast this
        gcongr

end ApproxSyzygies.Smoothed.Dev.T46.PartB
end

section
/-! Theorem 4.6 (vector-valued Carbery–Wright, BCPV19 Theorem 4.1) from the three parts of the
Blueprint: decoupling (`PartA.decoupling`), the polynomial small-ball bound for multilinear
forms (`PartA.multilinear_small_ball`) and the ADM echelon-tree bound (`PartB.adm_large`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed.Dev.T46.PartC

open ApproxSyzygies.Smoothed.Dev.T46

/-- `n^D ≤ D! · binom(n+D-1, D)`. -/
lemma pow_le_factorial_mul_choose (n D : ℕ) :
    (n : ℝ) ^ D ≤ (D.factorial : ℝ) * ((n + D - 1).choose D : ℝ) := by
  have h := Nat.pow_succ_le_ascFactorial n D
  rw [Nat.ascFactorial_eq_factorial_mul_choose'] at h
  exact_mod_cast h

/-- A unit vector `e` of `W` gives the lower bound `|⟪e, v⟫| ≤ ‖Π_W v‖`. -/
lemma norm_inner_le_proj {ι : Type} [Fintype ι] (W : Submodule ℝ (EuclideanSpace ℝ ι))
    (e : EuclideanSpace ℝ ι) (heW : e ∈ W) (he : ‖e‖ = 1) (v : EuclideanSpace ℝ ι) :
    ‖innerₛₗ ℝ e v‖ ≤ ‖W.starProjection v‖ := by
  rw [innerₛₗ_apply_apply, ← W.starProjection_eq_self_iff.mpr heW,
    W.inner_starProjection_left_eq_right]
  simpa [he] using norm_inner_le_norm (𝕜 := ℝ) e (W.starProjection v)

/-- The functional `⟪e, ·⟫` of a unit vector has Hilbert–Schmidt norm `1`. -/
lemma hs_inner {ι : Type} [Fintype ι] [DecidableEq ι] (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1) :
    ∑ k, ‖(innerₛₗ ℝ e) (EuclideanSpace.single k 1)‖ ^ 2 = 1 := by
  simp only [innerₛₗ_apply_apply, EuclideanSpace.inner_single_right, one_mul]
  have := EuclideanSpace.norm_eq e
  rw [he] at this
  have h2 := congrArg (· ^ 2) this
  simp only [one_pow] at h2
  rw [Real.sq_sqrt (by positivity)] at h2
  simpa using h2.symm

/-- The case `D = 1` needs no decoupling: `a^{⊗1}` is the decoupled product of one vector. -/
lemma transfer_one (n : ℕ) (E : Submodule ℝ (EuclideanSpace ℝ (Fin 1 → Fin n)))
    (abar : Fin n → ℝ) (ρ t : ℝ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {g | ‖E.starProjection (tensPow (abar + ρ • g) 1)‖ ≤ t} =
      gaussDec 1 n {G | ‖E.starProjection (decProd (pert (fun _ => abar) (fun _ => ρ) G))‖ ≤ t} := by
  have hmp := measurePreserving_piCongrLeft (α := fun _ : Fin n => ℝ)
    (fun _ : Fin n => gaussianReal 0 1) (Equiv.uniqueProd (Fin n) (Fin 1))
  have hS : MeasurableSet {g : Fin n → ℝ | ‖E.starProjection (tensPow (abar + ρ • g) 1)‖ ≤ t} := by
    refine (isClosed_le ?_ continuous_const).measurableSet
    refine continuous_norm.comp ((ContinuousLinearMap.continuous _).comp ?_)
    unfold tensPow
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => continuous_finsetProd _ fun j _ =>
      (continuous_apply _).comp (continuous_const.add (continuous_const_smul ρ)))
  rw [gaussDec, ← hmp.measure_preimage hS.nullMeasurableSet]
  congr 1

/-- The decoupled bound in both regimes: for `n ≥ 1` and `dim W ≥ δ n^D`,
`P[‖Π_W (x̃_0 ⊗ ⋯ ⊗ x̃_{D-1})‖ ≤ c' s^D / n^{D/2}] ≤ exp(−c δ n)`. -/
theorem core (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (δ : ℝ), 0 < δ →
        ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)),
          δ * (n : ℝ) ^ D ≤ (Module.finrank ℝ W : ℝ) →
          ∀ (x : Fin D → Fin n → ℝ) (σ : Fin D → ℝ) (s : ℝ), 0 < s → (∀ j, s ≤ σ j) →
            gaussDec D n {G | ‖W.starProjection (decProd (pert x σ G))‖ ≤
                c' * s ^ D / (n : ℝ) ^ ((D : ℝ) / 2)}
              ≤ ENNReal.ofReal (Real.exp (-(c * δ * n))) := by
  classical
  obtain ⟨K, hK, cA, hcA, cA', hcA', hadm⟩ := PartB.adm_large D hD
  obtain ⟨C, hC, a, ha, hml⟩ := PartA.multilinear_small_ball D hD
  set γ : ℝ := 1 / (Real.sqrt 3 * C ^ a⁻¹) with hγ
  have hγpos : 0 < γ := by positivity
  refine ⟨min cA (a / (2 * K)), by positivity, min cA' γ, by positivity, ?_⟩
  intro n hn δ hδ W hW x σ s hs hσ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hND : 0 < (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos hnpos _
  by_cases hreg : K * Real.log (n + 2) ≤ δ * n
  · refine le_trans (measure_mono ?_) ((hadm n δ hδ hreg W hW x σ s hs hσ).trans ?_)
    · intro G hG
      simp only [Set.mem_ofPred_eq] at hG ⊢
      refine hG.trans ?_
      gcongr
      exact min_le_left _ _
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h1 := min_le_left cA (a / (2 * K))
      have h2 : 0 ≤ δ * n := by positivity
      nlinarith
  · push Not at hreg
    have hpos : 0 < Module.finrank ℝ W := by
      have : (0 : ℝ) < δ * (n : ℝ) ^ D := by positivity
      exact_mod_cast this.trans_le hW
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W)
      (by rintro rfl; simp at hpos)
    set e := ‖v‖⁻¹ • v with he_def
    have heW : e ∈ W := W.smul_mem _ hvW
    have he1 : ‖e‖ = 1 := by
      rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    set ε' : ℝ := min cA' γ / (n : ℝ) ^ ((D : ℝ) / 2) with hε'
    have hε'0 : 0 ≤ ε' := by positivity
    refine le_trans (measure_mono ?_)
      ((hml n (innerₛₗ ℝ e) (hs_inner e he1) x σ s hs hσ ε' hε'0).trans ?_)
    · intro G hG
      simp only [Set.mem_ofPred_eq] at hG ⊢
      refine (norm_inner_le_proj W e heW he1 _).trans (hG.trans (le_of_eq ?_))
      rw [hε']; ring
    · apply ENNReal.ofReal_le_ofReal
      -- `C ε'^a ≤ (n+2)^{-a/2} ≤ exp(-c δ n)`
      have hlog : 0 < Real.log (n + 2) := Real.log_pos (by linarith)
      have hcδ : min cA (a / (2 * K)) * δ * n ≤ a / 2 * Real.log (n + 2) := by
        have h1 := min_le_right cA (a / (2 * K))
        have h2 : 0 ≤ δ * n := by positivity
        calc min cA (a / (2 * K)) * δ * n = min cA (a / (2 * K)) * (δ * n) := by ring
          _ ≤ a / (2 * K) * (K * Real.log (n + 2)) := by
              gcongr
          _ = a / 2 * Real.log (n + 2) := by field_simp
      -- `X := C^{1/a} ε' ≤ 1/√(n+2)`
      have hX : C ^ a⁻¹ * ε' ≤ 1 / Real.sqrt (n + 2) := by
        have hCa : 0 < C ^ a⁻¹ := Real.rpow_pos_of_pos hC _
        have h1 : ε' ≤ γ / (n : ℝ) ^ ((D : ℝ) / 2) := by
          rw [hε']; gcongr; exact min_le_right _ _
        have h2 : Real.sqrt n ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow]
          apply Real.rpow_le_rpow_of_exponent_le hn'
          have : (1 : ℝ) ≤ D := by exact_mod_cast hD
          linarith
        have h3 : Real.sqrt (n + 2) ≤ Real.sqrt 3 * Real.sqrt n := by
          rw [← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt (by linarith)
        have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
        calc C ^ a⁻¹ * ε' ≤ C ^ a⁻¹ * (γ / (n : ℝ) ^ ((D : ℝ) / 2)) := by gcongr
          _ = 1 / (Real.sqrt 3 * (n : ℝ) ^ ((D : ℝ) / 2)) := by
              rw [hγ]; field_simp
          _ ≤ 1 / (Real.sqrt 3 * Real.sqrt n) := by gcongr
          _ ≤ 1 / Real.sqrt (n + 2) := by
              gcongr
      have hXa : C * ε' ^ a = (C ^ a⁻¹ * ε') ^ a := by
        rw [Real.mul_rpow (by positivity) hε'0, Real.rpow_inv_rpow hC.le ha.ne']
      have hsq : 0 < Real.sqrt (n + 2) := Real.sqrt_pos.mpr (by linarith)
      have hR : (1 / Real.sqrt (n + 2)) ^ a = Real.exp (-(a / 2 * Real.log (n + 2))) := by
        rw [Real.rpow_def_of_pos (by positivity), one_div, Real.log_inv, Real.log_sqrt (by linarith)]
        congr 1; ring
      rw [hXa]
      calc (C ^ a⁻¹ * ε') ^ a ≤ (1 / Real.sqrt (n + 2)) ^ a := by
            gcongr
        _ = Real.exp (-(a / 2 * Real.log (n + 2))) := hR
        _ ≤ Real.exp (-(min cA (a / (2 * K)) * δ * n)) := by
            apply Real.exp_le_exp.mpr; linarith

end ApproxSyzygies.Smoothed.Dev.T46.PartC

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.T46 ApproxSyzygies.Smoothed.Dev.T46.PartC in
theorem chk_theorem_4_6 (D : ℕ) (hD : 1 ≤ D) :
    ∃ cD : ℝ, 0 < cD ∧ ∃ cD' : ℝ, 0 < cD' ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ < 1 →
        ∀ E : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)), E ≤ symTensors n D →
          θ * ((n + D - 1).choose D : ℝ) ≤ (Module.finrank ℝ E : ℝ) →
          ∀ (abar : Fin n → ℝ) (ρ : ℝ), 0 < ρ →
            (Measure.pi fun _ : Fin n => gaussianReal 0 1)
                {g | ‖E.starProjection (tensPow (abar + ρ • g) D)‖ ≤
                    cD' * ρ ^ D / (n : ℝ) ^ ((D : ℝ) / 2)}
              ≤ ENNReal.ofReal (Real.exp (-(cD * θ * n))) := by
  obtain ⟨c, hc, c', hc', hcore⟩ := core D hD
  have hFpos : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hmpos : (0 : ℝ) < (2 : ℝ) ^ (D - 1) := by positivity
  have h2D : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith)
  have hβ : 0 < Real.sqrt (2 * D) ^ D := by positivity
  refine ⟨c / ((D.factorial : ℝ) * 2 ^ (D - 1)), by positivity,
    c' * (D.factorial : ℝ) / Real.sqrt (2 * D) ^ D, by positivity, ?_⟩
  intro n θ hθ _ E hE hdim abar ρ hρ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  set δ : ℝ := θ / (D.factorial : ℝ) with hδ_def
  have hδ : 0 < δ := by positivity
  have hW : δ * (n : ℝ) ^ D ≤ (Module.finrank ℝ E : ℝ) := by
    refine le_trans ?_ hdim
    rw [hδ_def, div_mul_eq_mul_div, div_le_iff₀ hFpos, mul_assoc]
    gcongr
    rw [mul_comm]
    exact pow_le_factorial_mul_choose n D
  have hND : 0 < (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  rcases (show D = 1 ∨ 2 ≤ D by omega) with rfl | hD2
  · rw [transfer_one]
    refine le_trans (measure_mono ?_)
      ((hcore n hn δ hδ E hW (fun _ => abar) (fun _ => ρ) ρ hρ (fun _ => le_rfl)).trans ?_)
    · intro G hG
      simp only [Set.mem_ofPred_eq] at hG ⊢
      refine hG.trans ?_
      gcongr
      have h1 : (1 : ℝ) ≤ Real.sqrt (2 * ((1 : ℕ) : ℝ)) ^ 1 := by
        rw [pow_one, Real.one_le_sqrt]; norm_num
      calc c' * ((Nat.factorial 1 : ℕ) : ℝ) / Real.sqrt (2 * ((1 : ℕ) : ℝ)) ^ 1
          ≤ c' * ((Nat.factorial 1 : ℕ) : ℝ) / 1 := by gcongr
        _ = c' := by simp
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [hδ_def]
      simp only [Nat.factorial_one, Nat.cast_one, div_one, Nat.sub_self, pow_zero, mul_one,
        le_refl]
  · have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD2
    set s : ℝ := ρ / Real.sqrt (2 * D) with hs_def
    have hs : 0 < s := by positivity
    have hσ : ∀ j, s ≤ sigDec D ρ j := by
      intro j
      unfold sigDec
      split_ifs
      · calc s = ρ * Real.sqrt (1 / (2 * D)) := by
              rw [hs_def, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * D), Real.sqrt_one]; ring
          _ ≤ ρ * Real.sqrt (((D : ℝ) + 1) / (2 * D)) := by gcongr; linarith
      · exact le_rfl
    refine (PartA.decoupling D hD2 n E hE abar ρ hρ _).trans ?_
    have hcd := hcore n hn δ hδ E hW (shiftDec abar) (sigDec D ρ) s hs hσ
    have hexp : (0 : ℝ) ≤ 1 / 2 ^ (D - 1) := by positivity
    calc (gaussDec D n {G | ‖E.starProjection (decProd (pert (shiftDec abar) (sigDec D ρ) G))‖ ≤
            c' * (D.factorial : ℝ) / Real.sqrt (2 * D) ^ D * ρ ^ D / (n : ℝ) ^ ((D : ℝ) / 2) /
              (D.factorial : ℝ)}) ^ ((1 : ℝ) / 2 ^ (D - 1))
        ≤ (ENNReal.ofReal (Real.exp (-(c * δ * n)))) ^ ((1 : ℝ) / 2 ^ (D - 1)) := by
          refine ENNReal.rpow_le_rpow (le_trans (measure_mono ?_) hcd) hexp
          intro G hG
          simp only [Set.mem_ofPred_eq] at hG ⊢
          refine hG.trans (le_of_eq ?_)
          rw [hs_def, div_pow]
          field_simp
      _ = ENNReal.ofReal (Real.exp (-(c / ((D.factorial : ℝ) * 2 ^ (D - 1)) * θ * n))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hexp, ← Real.exp_mul, hδ_def]
          congr 2
          field_simp

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_theorem_4_6 := @ApproxSyzygies.Smoothed.chk_theorem_4_6
