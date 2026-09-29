-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5bde4ffa-2794-5d6d-95d0-b76a3db01ce1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

namespace AutomorphicForm
namespace ArchMirabolic

variable {A : Type} [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A]

private def _root_.AutomorphicForm.ArchMirabolic.mk (c₁ c₂ b d : A) : Fin 2 → Fin 2 → A := ![![c₁, b], ![c₂, d]]

p2m_export "AutomorphicForm.ArchMirabolic" "mk"

def un (x : A) : Matrix (Fin 2) (Fin 2) A := !![(1 : A), x; 0, 1]

noncomputable def ρ (t : A) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ t| ^ 2)⁻¹

@[scoped simp] lemma mk_00 (c₁ c₂ b d : A) : mk c₁ c₂ b d 0 0 = c₁ := rfl
@[scoped simp] lemma mk_01 (c₁ c₂ b d : A) : mk c₁ c₂ b d 0 1 = b := rfl
@[scoped simp] lemma mk_10 (c₁ c₂ b d : A) : mk c₁ c₂ b d 1 0 = c₂ := rfl
@[scoped simp] lemma mk_11 (c₁ c₂ b d : A) : mk c₁ c₂ b d 1 1 = d := rfl

lemma of_mk (c₁ c₂ b d : A) : Matrix.of (mk c₁ c₂ b d) = !![c₁, b; c₂, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma det_mk (c₁ c₂ b d : A) : (Matrix.of (mk c₁ c₂ b d)).det = c₁ * d - b * c₂ := by
  rw [of_mk, Matrix.det_fin_two_of]

lemma col_mk (c₁ c₂ b d : A) : (fun i => mk c₁ c₂ b d i 0) = ![c₁, c₂] := by
  funext i; fin_cases i <;> rfl

lemma mk_mul_un (c₁ c₂ b d x : A) :
    Matrix.of.symm (Matrix.of (mk c₁ c₂ b d) * un x) = mk c₁ c₂ (c₁ * x + b) (c₂ * x + d) := by
  apply Matrix.of.injective
  rw [Equiv.apply_symm_apply, of_mk, of_mk, un]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma un_mul_un (x y : A) : un x * un y = un (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [un, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma of_symm_mul_un_mul_un (Y : Fin 2 → Fin 2 → A) (x y : A) :
    Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of Y * un y)) * un x) =
      Matrix.of.symm (Matrix.of Y * un (y + x)) := by
  rw [Equiv.apply_symm_apply, Matrix.mul_assoc, un_mul_un]

lemma eq_mk (X : Fin 2 → Fin 2 → A) : X = mk (X 0 0) (X 1 0) (X 0 1) (X 1 1) := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

lemma continuous_algNorm : Continuous (Algebra.norm ℝ : A → ℝ) := by
  have h1 : Continuous fun a : A => (ContinuousLinearMap.mul ℝ A a).det :=
    ContinuousLinearMap.continuous_det.comp (ContinuousLinearMap.mul ℝ A).continuous
  have h2 : (fun a : A => (ContinuousLinearMap.mul ℝ A a).det) = (Algebra.norm ℝ : A → ℝ) := by
    funext a; rw [Algebra.norm_apply]; rfl
  rwa [h2] at h1

lemma measurable_ρ : Measurable (ρ : A → ℝ≥0∞) := by
  unfold ρ
  exact ((ENNReal.continuous_ofReal.measurable.comp
    (continuous_abs.measurable.comp continuous_algNorm.measurable)).pow_const 2).inv

lemma isOpen_isUnit : IsOpen {t : A | IsUnit t} := Units.isOpen

lemma measurableSet_isUnit : MeasurableSet {t : A | IsUnit t} := isOpen_isUnit.measurableSet

private lemma _root_.AutomorphicForm.ArchMirabolic.continuous_det : Continuous fun X : Fin 2 → Fin 2 → A => (Matrix.of X).det :=
  Continuous.matrix_det (A := fun X : Fin 2 → Fin 2 → A => Matrix.of X) continuous_id

p2m_export "AutomorphicForm.ArchMirabolic" "continuous_det"
lemma measurable_det : Measurable fun X : Fin 2 → Fin 2 → A => (Matrix.of X).det :=
  continuous_det.measurable

lemma measurableSet_U : MeasurableSet {X : Fin 2 → Fin 2 → A | IsUnit (Matrix.of X).det} :=
  measurableSet_isUnit.preimage measurable_det

lemma measurable_col : Measurable fun X : Fin 2 → Fin 2 → A => fun i => X i 0 :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply 0).comp (measurable_pi_apply i)

lemma continuous_un : Continuous (un : A → Matrix (Fin 2) (Fin 2) A) := by
  unfold un
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

lemma continuous_mulUn :
    Continuous fun p : (Fin 2 → Fin 2 → A) × A => Matrix.of.symm (Matrix.of p.1 * un p.2) := by
  have : Continuous fun p : (Fin 2 → Fin 2 → A) × A => Matrix.of p.1 * un p.2 :=
    Continuous.matrix_mul (continuous_fst) (continuous_un.comp continuous_snd)
  exact this

lemma continuous_mk4 :
    Continuous fun p : (A × A) × (A × A) => mk p.1.1 p.2.1 p.1.2 p.2.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [mk] <;> fun_prop

lemma measurable_mk4 :
    Measurable fun p : (A × A) × (A × A) => mk p.1.1 p.2.1 p.1.2 p.2.2 :=
  continuous_mk4.measurable

lemma measurable_mk {X : Type*} [MeasurableSpace X] {f₁ f₂ f₃ f₄ : X → A}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄) :
    Measurable fun p => mk (f₁ p) (f₂ p) (f₃ p) (f₄ p) :=
  measurable_mk4.comp ((h₁.prodMk h₃).prodMk (h₂.prodMk h₄))

lemma continuous_vec2 : Continuous fun p : A × A => (![p.1, p.2] : Fin 2 → A) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop

variable (μ : Measure A)

noncomputable def fib (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (Y : Fin 2 → Fin 2 → A) : ℝ≥0∞ :=
  ∫⁻ x, w (Matrix.of.symm (Matrix.of Y * un x)) ∂μ

variable {μ}

lemma measurable_fib [SFinite μ] {w : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fib μ w) :=
  Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → Fin 2 → A) × A =>
    w (Matrix.of.symm (Matrix.of p.1 * un p.2))) (hw.comp continuous_mulUn.measurable)

lemma fib_mul_un [μ.IsAddLeftInvariant] (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞)
    (Y : Fin 2 → Fin 2 → A) (y : A) :
    fib μ w (Matrix.of.symm (Matrix.of Y * un y)) = fib μ w Y := by
  unfold fib
  simp_rw [of_symm_mul_un_mul_un]
  exact lintegral_add_left_eq_self (fun x => w (Matrix.of.symm (Matrix.of Y * un x))) y

section Iterated

variable [SFinite μ] [SigmaFinite μ]

def rowsEquiv : (Fin 2 → Fin 2 → A) ≃ᵐ (A × A) × (A × A) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → A)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

lemma rowsEquiv_symm_apply (p : (A × A) × (A × A)) :
    (rowsEquiv.symm p : Fin 2 → Fin 2 → A) = mk p.1.1 p.2.1 p.1.2 p.2.2 := by
  rcases p with ⟨⟨c₁, b⟩, ⟨c₂, d⟩⟩
  rfl

lemma measurePreserving_rowsEquiv :
    MeasurePreserving (rowsEquiv (A := A))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  unfold rowsEquiv
  exact ((measurePreserving_finTwoArrow μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_finTwoArrow (Measure.pi fun _ : Fin 2 => μ))

lemma lintegral_eq_iterated_rows {F : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ c₁, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ ∂μ := by
  have hG : Measurable fun p : (A × A) × (A × A) => F (mk p.1.1 p.2.1 p.1.2 p.2.2) :=
    hF.comp measurable_mk4
  have h1 : ∫⁻ X, F X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ p, F (mk p.1.1 p.2.1 p.1.2 p.2.2) ∂((μ.prod μ).prod (μ.prod μ)) := by
    rw [(measurePreserving_rowsEquiv (μ := μ)).lintegral_map_equiv]
    refine lintegral_congr fun X => ?_
    rw [← rowsEquiv_symm_apply, MeasurableEquiv.symm_apply_apply]
  rw [h1, lintegral_prod _ hG.aemeasurable]
  dsimp only
  have hq : Measurable fun q : A × A => ∫⁻ r, F (mk q.1 r.1 q.2 r.2) ∂(μ.prod μ) :=
    Measurable.lintegral_prod_right'
      (f := fun p : (A × A) × (A × A) => F (mk p.1.1 p.2.1 p.1.2 p.2.2)) hG
  rw [lintegral_prod _ hq.aemeasurable]
  refine lintegral_congr fun c₁ => lintegral_congr fun b => ?_
  have hr : Measurable fun r : A × A => F (mk c₁ r.1 b r.2) :=
    measurable_mk measurable_const measurable_fst measurable_const measurable_snd |> hF.comp
  rw [lintegral_prod _ hr.aemeasurable]

omit [SFinite μ] in

lemma lintegral_eq_iterated_vec {G : (Fin 2 → A) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ c, G c ∂(Measure.pi fun _ : Fin 2 => μ) = ∫⁻ c₁, ∫⁻ c₂, G ![c₁, c₂] ∂μ ∂μ := by
  have h : ∫⁻ c, G c ∂(Measure.pi fun _ : Fin 2 => μ) =
      ∫⁻ c, (fun p : A × A => G ![p.1, p.2]) (MeasurableEquiv.finTwoArrow c)
        ∂(Measure.pi fun _ : Fin 2 => μ) := by
    refine lintegral_congr fun c => ?_
    congr 1
    funext i; fin_cases i <;> rfl
  rw [h, ← (measurePreserving_finTwoArrow μ).lintegral_map_equiv (fun p : A × A => G ![p.1, p.2]),
    lintegral_prod (fun p : A × A => G ![p.1, p.2]) (hG.comp continuous_vec2.measurable).aemeasurable]

end Iterated

section CoV

variable [μ.IsAddHaarMeasure]

def mulLeftEquiv (a : Aˣ) : A ≃ᵐ A where
  toFun x := (a : A) * x
  invFun x := ((a⁻¹ : Aˣ) : A) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  measurable_toFun := (continuous_const.mul continuous_id).measurable
  measurable_invFun := (continuous_const.mul continuous_id).measurable

lemma algNorm_unit_ne_zero (a : Aˣ) : Algebra.norm ℝ (a : A) ≠ 0 :=
  (a.isUnit.map (Algebra.norm ℝ)).ne_zero

lemma lintegral_comp_mul_unit (a : Aˣ) (f : A → ℝ≥0∞) :
    ∫⁻ x, f ((a : A) * x) ∂μ = ENNReal.ofReal |(Algebra.norm ℝ (a : A))⁻¹| * ∫⁻ x, f x ∂μ := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (a : A)) = Algebra.norm ℝ (a : A) := by
    rw [Algebra.norm_apply]; rfl
  have hmap : Measure.map (mulLeftEquiv a) μ =
      ENNReal.ofReal |(Algebra.norm ℝ (a : A))⁻¹| • μ := by
    have : (⇑(mulLeftEquiv a) : A → A) = ⇑(LinearMap.mulLeft ℝ (a : A)) := by
      funext x; rfl
    rw [this, Measure.map_linearMap_addHaar_eq_smul_addHaar μ
      (by rw [hdet]; exact algNorm_unit_ne_zero a), hdet]
  have := lintegral_map_equiv f (mulLeftEquiv (A := A) a) (μ := μ)
  rw [hmap, lintegral_smul_measure] at this
  exact this.symm

lemma lintegral_lintegral_secondColumn (c₁ : Aˣ) (c₂ : A) (F : A → A → ℝ≥0∞) :
    ∫⁻ b, ∫⁻ d, F b d ∂μ ∂μ =
      ∫⁻ x, ∫⁻ δ, F ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) ∂μ ∂μ := by

  have hinner : ∀ x : A, ∫⁻ δ, F ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) ∂μ =
      ENNReal.ofReal |(Algebra.norm ℝ ((c₁⁻¹ : Aˣ) : A))⁻¹| * ∫⁻ δ, F ((c₁ : A) * x) δ ∂μ := by
    intro x
    have h1 := lintegral_comp_mul_unit (μ := μ) c₁⁻¹ (fun t => F ((c₁ : A) * x) (c₂ * x + t))
    rw [h1, lintegral_add_left_eq_self (μ := μ) (fun t => F ((c₁ : A) * x) t) (c₂ * x)]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

  have h2 := lintegral_comp_mul_unit (μ := μ) c₁ (fun b => ∫⁻ δ, F b δ ∂μ)
  rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, ← mul_inv,
    ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, inv_one, abs_one,
    ENNReal.ofReal_one, one_mul]

end CoV

section Main

variable [μ.IsAddHaarMeasure]

lemma mk_secondColumn (c₁ : Aˣ) (c₂ x δ : A) :
    mk (c₁ : A) c₂ ((c₁ : A) * x) (c₂ * x + ((c₁⁻¹ : Aˣ) : A) * δ) =
      Matrix.of.symm (Matrix.of (mk (c₁ : A) c₂ 0 (((c₁⁻¹ : Aˣ) : A) * δ)) * un x) := by
  rw [mk_mul_un, add_zero]

lemma det_g₀ (c₁ : Aˣ) (c₂ δ : A) :
    (Matrix.of (mk (c₁ : A) c₂ 0 (((c₁⁻¹ : Aˣ) : A) * δ))).det = δ := by
  rw [det_mk, zero_mul, sub_zero, ← mul_assoc, Units.mul_inv, one_mul]

lemma det_mul_un (Y : Fin 2 → Fin 2 → A) (x : A) :
    (Matrix.of (Matrix.of.symm (Matrix.of Y * un x))).det = (Matrix.of Y).det := by
  rw [Equiv.apply_symm_apply, Matrix.det_mul, un, Matrix.det_fin_two_of]; simp

lemma ae_fib_g₀_eq_one (hA : ∀ᵐ a ∂μ, IsUnit a)
    {w : (Fin 2 → Fin 2 → A) → ℝ≥0∞} (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det}, fib μ w X = 1) :
    ∀ᵐ c₁ ∂μ, ∀ u : Aˣ, (u : A) = c₁ → ∀ᵐ c₂ ∂μ, ∀ᵐ δ ∂μ, IsUnit δ →
      fib μ w (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 1 := by
  classical

  obtain ⟨Bad, hBad⟩ : ∃ Bad : Set (Fin 2 → Fin 2 → A),
      Bad = {X | IsUnit (Matrix.of X).det ∧ fib μ w X ≠ 1} := ⟨_, rfl⟩
  have hBadm : MeasurableSet Bad := by
    rw [hBad]
    exact measurableSet_U.inter ((measurable_fib hw) (measurableSet_singleton 1)).compl
  have hBad0 : (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) Bad = 0 := by
    rw [ae_restrict_iff' measurableSet_U] at hw1
    rw [← compl_mem_ae_iff]
    filter_upwards [hw1] with X hX
    simp only [hBad, Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_not]
    exact hX
  obtain ⟨χ, hχ⟩ : ∃ χ : (Fin 2 → Fin 2 → A) → ℝ≥0∞, χ = Bad.indicator 1 := ⟨_, rfl⟩
  have hind : Measurable χ := by rw [hχ]; exact measurable_one.indicator hBadm

  have hI : ∫⁻ c₁, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ ∂μ = 0 := by
    rw [← lintegral_eq_iterated_rows hind, hχ, lintegral_indicator hBadm]
    simp [hBad0]

  have hswap : ∀ c₁ : A, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ =
      ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    intro c₁
    refine lintegral_lintegral_swap ?_
    refine (Measurable.lintegral_prod_right' (f := fun p : (A × A) × A =>
      χ (mk c₁ p.1.2 p.1.1 p.2)) ?_).aemeasurable
    exact hind.comp (measurable_mk measurable_const measurable_fst.snd measurable_fst.fst
      measurable_snd)
  simp_rw [hswap] at hI

  have hm2 : ∀ c₁ : A, Measurable fun c₂ : A => ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ := by
    intro c₁
    refine Measurable.lintegral_prod_right' (f := fun q : A × A =>
      ∫⁻ d, χ (mk c₁ q.1 q.2 d) ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun r : (A × A) × A =>
      χ (mk c₁ r.1.1 r.1.2 r.2)) ?_
    exact hind.comp (measurable_mk measurable_const measurable_fst.fst measurable_fst.snd
      measurable_snd)
  have hm3 : Measurable fun c₁ : A => ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    refine Measurable.lintegral_prod_right' (f := fun p : A × A =>
      ∫⁻ b, ∫⁻ d, χ (mk p.1 p.2 b d) ∂μ ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun q : (A × A) × A =>
      ∫⁻ d, χ (mk q.1.1 q.1.2 q.2 d) ∂μ) ?_
    refine Measurable.lintegral_prod_right' (f := fun r : ((A × A) × A) × A =>
      χ (mk r.1.1.1 r.1.1.2 r.1.2 r.2)) ?_
    exact hind.comp (measurable_mk measurable_fst.fst.fst measurable_fst.fst.snd
      measurable_fst.snd measurable_snd)
  rw [lintegral_eq_zero_iff' hm3.aemeasurable] at hI
  filter_upwards [hI] with c₁ hc₁0 u hu
  subst hu
  have hc₁0' : ∫⁻ c₂, ∫⁻ b, ∫⁻ d, χ (mk (u : A) c₂ b d) ∂μ ∂μ ∂μ = 0 := hc₁0
  rw [lintegral_eq_zero_iff' (hm2 (u : A)).aemeasurable] at hc₁0'
  filter_upwards [hc₁0'] with c₂ hc₂0
  have hc₂0' : ∫⁻ b, ∫⁻ d, χ (mk (u : A) c₂ b d) ∂μ ∂μ = 0 := hc₂0

  rw [lintegral_lintegral_secondColumn (μ := μ) u c₂ fun b d => χ (mk (u : A) c₂ b d)] at hc₂0'

  have hinv : ∀ x δ : A, χ (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) =
      χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) := by
    intro x δ
    rw [mk_secondColumn]
    simp only [hχ, Set.indicator, hBad, Set.mem_setOf_eq, det_mul_un, fib_mul_un, Pi.one_apply]
  simp_rw [hinv] at hc₂0'
  rw [lintegral_const, mul_eq_zero] at hc₂0'
  have hμ0 : μ Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
  have hδ0 : ∫⁻ δ, χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) ∂μ = 0 :=
    hc₂0'.resolve_right hμ0
  have hmδ : Measurable fun δ : A => χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) :=
    hind.comp (measurable_mk measurable_const measurable_const measurable_const
      (measurable_id.const_mul _))
  rw [lintegral_eq_zero_iff' hmδ.aemeasurable] at hδ0
  filter_upwards [hδ0] with δ hδ hδu
  have hδ' : χ (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 0 := hδ
  rw [hχ, Set.indicator_apply_eq_zero] at hδ'
  by_contra hne
  have hmem : mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ) ∈ Bad := by
    rw [hBad, Set.mem_setOf_eq, det_g₀]
    exact ⟨hδu, hne⟩
  exact one_ne_zero (hδ' hmem)

theorem main (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det}, fib μ w X = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) * ρ (Matrix.of X).det
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * ρ δ ∂μ ∂(Measure.pi fun _ : Fin 2 => μ) := by
  classical

  obtain ⟨F, hF⟩ : ∃ F : (Fin 2 → Fin 2 → A) → ℝ≥0∞,
      F = {X : Fin 2 → Fin 2 → A | IsUnit (Matrix.of X).det}.indicator
        fun X => w X * Ψ (fun i => X i 0, (Matrix.of X).det) * ρ (Matrix.of X).det := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact ((hw.mul (hΨ.comp (measurable_col.prodMk measurable_det))).mul
      (measurable_ρ.comp measurable_det)).indicator measurableSet_U
  rw [← lintegral_indicator measurableSet_U, ← hF, lintegral_eq_iterated_rows hFm]

  obtain ⟨R, hR⟩ : ∃ R : (Fin 2 → A) → ℝ≥0∞,
      R = fun c => ∫⁻ δ, {δ : A | IsUnit δ}.indicator (fun δ => Ψ (c, δ) * ρ δ) δ ∂μ := ⟨_, rfl⟩
  have hRm : Measurable R := by
    rw [hR]
    refine Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → A) × A =>
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (p.1, δ) * ρ δ) p.2) ?_
    have h1 : Measurable fun p : (Fin 2 → A) × A => Ψ p * ρ p.2 :=
      hΨ.mul (measurable_ρ.comp measurable_snd)
    have h2 : (fun p : (Fin 2 → A) × A =>
        {δ : A | IsUnit δ}.indicator (fun δ => Ψ (p.1, δ) * ρ δ) p.2) =
        (Prod.snd ⁻¹' {δ : A | IsUnit δ}).indicator fun p => Ψ p * ρ p.2 := by
      funext p
      simp only [Set.indicator, Set.mem_preimage, Set.mem_setOf_eq, Prod.mk.eta]
    rw [h2]
    exact h1.indicator (measurableSet_isUnit.preimage measurable_snd)
  have hRHS : (∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * ρ δ ∂μ ∂(Measure.pi fun _ : Fin 2 => μ)) =
      ∫⁻ c, R c ∂(Measure.pi fun _ : Fin 2 => μ) := by
    rw [hR]
    simp_rw [lintegral_indicator measurableSet_isUnit]
  rw [hRHS, lintegral_eq_iterated_vec hRm]

  have hswap : ∀ c₁ : A, ∫⁻ b, ∫⁻ c₂, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ =
      ∫⁻ c₂, ∫⁻ b, ∫⁻ d, F (mk c₁ c₂ b d) ∂μ ∂μ ∂μ := by
    intro c₁
    refine lintegral_lintegral_swap ?_
    refine (Measurable.lintegral_prod_right' (f := fun p : (A × A) × A =>
      F (mk c₁ p.1.2 p.1.1 p.2)) ?_).aemeasurable
    exact hFm.comp (measurable_mk measurable_const measurable_fst.snd measurable_fst.fst
      measurable_snd)
  simp_rw [hswap]

  refine lintegral_congr_ae ?_
  filter_upwards [hA, ae_fib_g₀_eq_one (μ := μ) hA hw hw1] with c₁ hc₁ hgood
  obtain ⟨u, rfl⟩ := hc₁
  refine lintegral_congr_ae ?_
  filter_upwards [hgood u rfl] with c₂ hδ

  rw [lintegral_lintegral_secondColumn (μ := μ) u c₂ fun b d => F (mk (u : A) c₂ b d)]

  have hval : ∀ x δ : A, F (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) =
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (![(u : A), c₂], δ) * ρ δ) δ *
        w (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) := by
    intro x δ
    have hd : (Matrix.of (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ))).det =
        δ := by
      rw [mk_secondColumn, det_mul_un, det_g₀]
    rw [hF]
    simp only [Set.indicator, Set.mem_setOf_eq, hd, col_mk]
    split_ifs with h
    · ring
    · simp
  simp_rw [hval]

  have hwx : ∀ δ : A, Measurable fun x : A =>
      w (mk (u : A) c₂ ((u : A) * x) (c₂ * x + ((u⁻¹ : Aˣ) : A) * δ)) := by
    intro δ
    exact hw.comp (measurable_mk measurable_const measurable_const (measurable_id.const_mul _)
      ((measurable_id.const_mul _).add_const _))
  have hm2 : Measurable fun p : A × A =>
      {δ : A | IsUnit δ}.indicator (fun δ => Ψ (![(u : A), c₂], δ) * ρ δ) p.2 *
        w (mk (u : A) c₂ ((u : A) * p.1) (c₂ * p.1 + ((u⁻¹ : Aˣ) : A) * p.2)) := by
    refine Measurable.mul ?_ ?_
    · have hc : Measurable fun δ : A => ((![(u : A), c₂] : Fin 2 → A), δ) :=
        measurable_const.prodMk measurable_id
      have h1 : Measurable fun δ : A => Ψ (![(u : A), c₂], δ) * ρ δ :=
        (hΨ.comp hc).mul measurable_ρ
      exact (h1.indicator measurableSet_isUnit).comp measurable_snd
    · exact hw.comp (measurable_mk measurable_const measurable_const (measurable_fst.const_mul _)
        ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  rw [lintegral_lintegral_swap hm2.aemeasurable, hR]
  beta_reduce
  refine lintegral_congr_ae ?_
  filter_upwards [hδ] with δ hδ1
  rw [lintegral_const_mul'' _ (hwx δ).aemeasurable]
  by_cases hδu : IsUnit δ
  · have h1 : fib μ w (mk (u : A) c₂ 0 (((u⁻¹ : Aˣ) : A) * δ)) = 1 := hδ1 hδu
    rw [fib] at h1
    simp_rw [← mk_secondColumn] at h1
    rw [h1, mul_one]
  · simp [Set.indicator, hδu]

end Main

end AutomorphicForm.ArchMirabolic
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm.ArchMirabolic"
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one.AutomorphicForm"

open AutomorphicForm.ArchMirabolic in
theorem solution
    (A : Type) [NormedCommRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) (hμ : μ.IsAddHaarMeasure) (hA : ∀ᵐ a ∂μ, IsUnit a)
    (w : (Fin 2 → Fin 2 → A) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ).restrict
        {X | IsUnit (Matrix.of X).det},
      ∫⁻ x, w (Matrix.of.symm (Matrix.of X * !![(1 : A), x; 0, 1])) ∂μ = 1)
    (Ψ : (Fin 2 → A) × A → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ X in {X | IsUnit (Matrix.of X).det},
        w X * Ψ (fun i => X i 0, (Matrix.of X).det) *
          (ENNReal.ofReal |Algebra.norm ℝ (Matrix.of X).det| ^ 2)⁻¹
      ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
    ∫⁻ c, ∫⁻ δ in {δ | IsUnit δ}, Ψ (c, δ) * (ENNReal.ofReal |Algebra.norm ℝ δ| ^ 2)⁻¹ ∂μ
      ∂(Measure.pi fun _ : Fin 2 => μ) := by
  haveI := hμ
  exact main (μ := μ) hA w hw hw1 Ψ hΨ

end S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_mul_apply_col_det_mul_inv_norm_det_sq_eq_lintegral_setLIntegral_of_forall_lintegral_mul_unipotent_eq_one (solution)
