-- Prove2me | Definitions.Def_RHT1000_Support_20261118_B002
-- name    : RHT1000_Support_20261118_B002
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:23:00.873208+00:00
-- url     : https://prove2.me/theorems/c4e217ea-4809-4b7d-9cb0-f0c7c0711996
-- title:
--   Suporte completo para T1000 — bloco 2 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_B001
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
section CertificatePort16
section
open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)
noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)
noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y
noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂
lemma HIntegral_symm :
    HIntegral f x₁ x₂ y = -HIntegral f x₂ x₁ y := integral_symm _ _
lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w
noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' T +
    I • (∫ y : ℝ in Ici T, f (σ' + y * I)) -
    I • (∫ y : ℝ in Ici T, f (σ + y * I))
noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' (-T) -
    I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) +
    I • (∫ y : ℝ in Iic (-T), f (σ + y * I))
noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)
noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)
theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩
theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]
def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im
theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩
theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)
theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel
lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module
lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
set_option linter.style.multiGoal false in
lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, zero_add, add_zero]
theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  simp [RectangleIntegral, HIntegral, VIntegral, smul_add, smul_sub, smul_smul, mul_comm]
theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]
theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]
lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring
lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]
lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)
lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)
lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring
set_option backward.isDefEq.respectTransparency false in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]
lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]
lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf
theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior
lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U
theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)
theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq
def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z
lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)
noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z
end
end CertificatePort16

section CertificatePort17
section
open Finset Interval MeasureTheory
variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop
lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]
lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp
lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)
lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]
theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end
end CertificatePort17

section CertificatePort18
section
set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]
lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]
lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp
lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]
local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta
theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩
theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])
lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf
lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx
set_option backward.isDefEq.respectTransparency false in
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1
lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]
lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s
lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)
lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]
open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub
lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num
lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h
lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]
lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop
open MeasureTheory in
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]
lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)
open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_ofPred_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_ofPred_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, ofPred_subset_ofPred, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [ofPred_subset_ofPred, imp_self, forall_const, mem_ofPred_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd
lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one
lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num
lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)
lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]
lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring
lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz
lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound
lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp
open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos
open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x
open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring
open MeasureTheory in
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring
set_option backward.isDefEq.respectTransparency false in
lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ
set_option backward.isDefEq.respectTransparency false in
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ ζ (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := ζ') ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| ζ')
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const
theorem summable_complex_then_summable_real_part (f : ℕ → ℂ)
    (h : Summable f) : Summable (fun n ↦ (f n).re) := by
  rcases h with ⟨s, hs⟩
  exact ⟨s.re,  hasSum_re hs⟩
open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
open scoped ComplexOrder in
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [add_re, ofReal_re, mul_I_re, ofReal_im]
    ring
  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [ofReal_re]
  let s₀ := σ₀
  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one
  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries
  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one
  have summable_re_von_mangoldt_at_σ₀ :
      Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) σ₀)
      summable_von_mangoldt_at_σ₀
  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ i‖) := by
    rw [summable_norm_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one
  apply le_trans <| norm_tsum_le_tsum_norm summable_abs_value
  rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one]
  unfold LSeries
  rw [← re_eq_norm.mpr, re_tsum summable_von_mangoldt_at_σ₀]
  · apply Summable.tsum_mono summable_abs_value summable_re_von_mangoldt_at_σ₀
    intro n
    beta_reduce
    apply le_trans <| LSeries.norm_term_le_of_re_le_re (s := σ₀) _ _ _
    · rw [re_eq_norm.mpr]
      apply LSeries.term_nonneg
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
    · rwa [s₁_re_eq_sigma, s₀_re_eq_sigma]
  · apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
end
end CertificatePort18

section CertificatePort19
section
open Complex Filter Topology MeasureTheory Set
private lemma norm_sub_one_le_norm_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖z - 1‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [hz]
theorem norm_Gamma_le_strip_quarter_two :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℂ, (1 : ℝ) / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.Gamma w‖ ≤ C₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
  obtain ⟨c₁, c₂, hc₁, hc₁₂, H⟩ :=
    norm_Gamma_vertical_le (a := 1 / 4) (b := 2) (by norm_num) (by norm_num)
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_Icc (a := (1 / 4 : ℝ)) (b := 2)).reProdIm
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      fun w hw ↦ (differentiableAt_Gamma_of_re_pos (by
        rw [mem_reProdIm] at hw; linarith [hw.1.1])).continuousAt.continuousWithinAt
  refine ⟨max c₂ M₀, lt_of_lt_of_le hc₂ (le_max_left _ _), fun w hw1 hw2 ↦ ?_⟩
  have hnormnn : (0 : ℝ) ≤ ‖w‖ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hC₀ : (0 : ℝ) ≤ max c₂ M₀ := hc₂.le.trans (le_max_left _ _)
  by_cases himw : 1 ≤ |w.im|
  ·
    have hexp : Real.exp (-(Real.pi / 2) * |w.im|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg w.im)])
    have hrpow : |w.im| ^ (w.re - 1 / 2) ≤ ‖w‖ ^ ((3 : ℝ) / 2) :=
      (Real.rpow_le_rpow_of_exponent_le himw (by linarith)).trans
        (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm w) (by norm_num))
    have hub := (H w.re hw1 hw2 w.im himw).2
    rw [Complex.re_add_im] at hub
    calc ‖Complex.Gamma w‖
        ≤ c₂ * |w.im| ^ (w.re - 1 / 2) * Real.exp (-(Real.pi / 2) * |w.im|) := hub
      _ ≤ c₂ * ‖w‖ ^ ((3 : ℝ) / 2) * 1 := by gcongr
      _ ≤ max c₂ M₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
            nlinarith [mul_le_mul_of_nonneg_right (le_max_left c₂ M₀) hnormnn]
  ·
    have hwK := hM₀ w (by
      rw [mem_reProdIm]
      exact ⟨⟨hw1, hw2⟩, (abs_lt.mp (not_le.mp himw)).1.le, (abs_lt.mp (not_le.mp himw)).2.le⟩)
    nlinarith [le_max_right c₂ M₀]
theorem norm_Gamma_le_exp_halfplane :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ Real.exp (Cγ * (‖z‖ * Real.log ‖z‖ + 1)) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := norm_Gamma_le_strip_quarter_two
  have aux : ∀ n : ℕ, ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → z.re ≤ 2 + n → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n := by
    intro n
    induction n with
    | zero => exact fun z hz1 hz2 _ ↦ by simpa using hstrip z hz1 (by simpa using hz2)
    | succ n ih =>
        intro z hz1 hz2 hz3
        by_cases hcase : z.re ≤ 2 + n
        · exact (ih z hz1 hcase hz3).trans (by gcongr; exact Nat.le_succ n)
        · have hrebig : (2 : ℝ) < z.re :=
            lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg n)) (not_le.mp hcase)
          have hwre : (z - 1).re = z.re - 1 := by simp
          have hwne : z - 1 ≠ 0 := fun hh ↦ by rw [hh, Complex.zero_re] at hwre; linarith
          have hstep : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
            rw [← Complex.Gamma_add_one (z - 1) hwne]; congr 1; ring
          have hw_norm1 : (1 : ℝ) ≤ ‖z - 1‖ :=
            le_trans (by rw [hwre]; linarith)
              ((le_abs_self _).trans (abs_re_le_norm (z - 1)))
          have hih := ih (z - 1) (by rw [hwre]; linarith)
            (by rw [hwre]; push_cast at hz2 ⊢; linarith) hw_norm1
          have hnorm_le : ‖z - 1‖ ≤ ‖z‖ := norm_sub_one_le_norm_of_half_le_re (by linarith)
          rw [hstep, norm_mul, pow_succ]
          calc ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖
              ≤ ‖z‖ * (C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n) :=
                mul_le_mul hnorm_le (hih.trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
            _ = C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * (‖z‖ ^ n * ‖z‖) := by ring
  refine ⟨max (5 / 2) (Real.log (2 * C₀)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz1 hz3 ↦ ?_⟩
  set N := ‖z‖ with hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hz3
  have hL0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hz3
  have hNL : (0 : ℝ) ≤ N * Real.log N := mul_nonneg hN0.le hL0
  set n := ⌊z.re⌋₊ with hn
  have hn_le : (n : ℝ) ≤ N :=
    (Nat.floor_le (by linarith)).trans ((le_abs_self _).trans (abs_re_le_norm z))
  have hbase := aux n z hz1 (by linarith [Nat.lt_floor_add_one z.re]) hz3
  rw [← hN] at hbase
  have h1le : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := Real.one_le_rpow hz3 (by norm_num)
  have hpow : N ^ n ≤ Real.exp (N * Real.log N) := by
    rw [← Real.rpow_natCast N n, Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn_le hL0])
  have hkey : C₀ * (1 + N ^ ((3 : ℝ) / 2)) * N ^ n
      ≤ Real.exp (Real.log (2 * C₀) + Real.log N * (3 / 2)) * Real.exp (N * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_def_of_pos hN0]
    exact mul_le_mul (by nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr h1le)]) hpow
      (by positivity) (by positivity)
  refine (hbase.trans hkey).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hCγ1 : (5 : ℝ) / 2 ≤ max (5 / 2) (Real.log (2 * C₀)) := le_max_left _ _
  nlinarith [le_max_right (5 / 2 : ℝ) (Real.log (2 * C₀)), hNL,
    mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) hL0, mul_nonneg (sub_nonneg.mpr hCγ1) hNL]
theorem norm_riemannZeta_sub_head_le {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ Real.sqrt 2 * ‖s‖ := by
  have hσpos : 0 < s.re := by linarith
  have key := ZetaBnd_aux1b 2 (by norm_num) (σ := s.re) (t := s.im) hσpos
  simp only [Nat.cast_ofNat, Complex.re_add_im] at key
  have hb2 : (2 : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt 2 := by
    calc (2 : ℝ) ^ (-s.re) / s.re = (2 : ℝ) ^ (-s.re) * (1 / s.re) := by ring
      _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) * 2 :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
            (by rw [div_le_iff₀ hσpos]; linarith) (by positivity)
            (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = Real.sqrt 2 := by
          rw [mul_comm]; nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]; congr 1; norm_num
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (key.trans hb2) (norm_nonneg s)
theorem norm_riemannZeta_le_const_mul_of_half_le_re :
    ∃ Cζ : ℝ, 0 < Cζ ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ → ‖riemannZeta s‖ ≤ Cζ * ‖s‖ := by
  refine ⟨5 + Real.sqrt 2, by positivity, fun s hs hsnorm ↦ ?_⟩
  have hσpos : 0 < s.re := by linarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
  by_cases hcase : 2 ≤ s.re
  ·
    have hb := norm_riemannZeta_sub_one_le_of_two_le_re hcase
    have h2 := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at h2
    nlinarith [Real.sqrt_nonneg 2, Real.pi_le_four, Real.pi_pos,
      mul_nonneg (Real.sqrt_nonneg 2) (by linarith : (0 : ℝ) ≤ ‖s‖)]
  ·
    have hs0 : s ≠ 0 := by rintro rfl; simp at hσpos
    have hexp : riemannZeta s
        = (∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s)
          + (-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)
          + (-(((2 : ℕ) : ℂ) ^ (-s))) / 2
          + s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) :=
      (Zeta0EqZeta (N := 2) (by norm_num) hσpos hs1).symm
    have hA : ‖∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s‖ ≤ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_cpow hs0, Complex.one_cpow,
        div_zero, div_one, zero_add]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_one, norm_natCast_cpow_of_pos (by norm_num : 0 < 2)]
      have hden : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ s.re := by positivity
      linarith [(div_le_one hden).mpr (Real.one_le_rpow (by norm_num) (by linarith))]
    have hB : ‖(-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)‖ ≤ Real.sqrt 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.sub_re,
        Complex.one_re]
      have h1s : (1 : ℝ) ≤ ‖1 - s‖ := by
        rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]
        have hh := norm_sub_norm_le s 1
        rw [norm_one] at hh; linarith
      refine (div_le_self (Real.rpow_nonneg (by norm_num) _) h1s).trans ?_
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hC : ‖(-(((2 : ℕ) : ℂ) ^ (-s))) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re,
        show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -s.re ≤ 0)
    rw [hexp]
    refine norm_add₄_le.trans ((add_le_add (add_le_add (add_le_add hA hB) hC)
      (norm_riemannZeta_sub_head_le hs)).trans ?_)
    linarith
theorem norm_riemannXi_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C * (‖s‖ * Real.log ‖s‖)) := by
  obtain ⟨Cγ, hCγ, hγ⟩ := norm_Gamma_le_exp_halfplane
  obtain ⟨Cζ, hCζ, hζ⟩ := norm_riemannZeta_le_const_mul_of_half_le_re
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₀ : ℝ := Cγ / 2 + 3 + (|Real.log Cζ| + Cγ) / (2 * Real.log 2) with hC₀def
  have hfrac : 0 ≤ (|Real.log Cζ| + Cγ) / (2 * Real.log 2) :=
    div_nonneg (add_nonneg (abs_nonneg _) hCγ.le) (by positivity)
  have hC0 : 0 < C₀ := by rw [hC₀def]; linarith [hfrac, hCγ]
  have main : ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C₀ * (‖s‖ * Real.log ‖s‖)) := by
    intro s hs hsnorm
    have hσpos : 0 < s.re := by linarith
    have hN0 : 0 < ‖s‖ := by linarith
    have hL0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hN0
    have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
    have hhalf : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    set P := ‖s‖ * Real.log ‖s‖ with hP
    have hP0 : 0 ≤ P := mul_nonneg hN0.le hL0
    have hPlow : 2 * Real.log 2 ≤ P := by
      rw [hP]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm, hl2, hL0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 2) hL0]
    have hlogP : Real.log ‖s‖ ≤ P := by
      rw [hP]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 1) hL0]
    have hpre : ‖(1 / 2 : ℂ) * (s * (s - 1))‖ ≤ ‖s‖ ^ 2 := by
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      nlinarith [mul_le_mul_of_nonneg_left (by simpa using norm_sub_le s 1) (norm_nonneg s),
        mul_nonneg (norm_nonneg s) (by linarith : (0 : ℝ) ≤ ‖s‖ - 1)]
    have hΓnorm : ‖Gammaℝ s‖ ≤ Real.exp (Cγ * (1 / 2 * P + 1)) := by
      rw [Gammaℝ_def, norm_mul]
      have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
        rw [Complex.div_ofNat_re, Complex.neg_re]; linarith
      have hG : ‖s / 2‖ * Real.log ‖s / 2‖ ≤ 1 / 2 * P := by
        rw [hhalf, hP]
        have hlogle : Real.log (‖s‖ / 2) ≤ Real.log ‖s‖ :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ ‖s‖ / 2 by linarith),
          mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ ‖s‖ / 2)]
      refine (mul_le_mul hπ (hγ (s / 2) (by rw [Complex.div_ofNat_re]; linarith)
        (by rw [hhalf]; linarith)) (norm_nonneg _) (by norm_num)).trans ?_
      exact (one_mul _).trans_le
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hCγ.le))
    have hcombine : ‖riemannXi s‖ ≤ ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖) := by
      rw [riemannXi_eq_prefactor_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hσpos), norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hpre hΓnorm (norm_nonneg _) (by positivity))
        (hζ s hs hsnorm) (norm_nonneg _) (by positivity)
    have hrw : ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖)
        = Real.exp (Real.log Cζ + 3 * Real.log ‖s‖ + Cγ * (1 / 2 * P + 1)) := by
      have hcube : ‖s‖ ^ 3 = Real.exp (3 * Real.log ‖s‖) := by
        rw [← Real.rpow_natCast ‖s‖ 3, Real.rpow_def_of_pos hN0]; congr 1; push_cast; ring
      rw [Real.exp_add, Real.exp_add, Real.exp_log hCζ, ← hcube]; ring
    refine (hcombine.trans_eq hrw).trans (Real.exp_le_exp.mpr ?_)
    have hconst : Real.log Cζ + Cγ ≤ ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * P :=
      calc Real.log Cζ + Cγ ≤ |Real.log Cζ| + Cγ := by linarith [le_abs_self (Real.log Cζ)]
        _ = ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * (2 * Real.log 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hPlow hfrac
    rw [hC₀def]
    linarith [hconst, hlogP]
  refine ⟨4 * C₀, by linarith [hC0], fun s hsnorm ↦ ?_⟩
  by_cases hcase : (1 : ℝ) / 2 ≤ s.re
  · refine (main s hcase hsnorm).trans (Real.exp_le_exp.mpr ?_)
    linarith [mul_nonneg hC0.le (mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖s‖)))]
  · rw [not_le] at hcase
    have hre' : (1 : ℝ) / 2 ≤ (1 - s).re := by simp; linarith
    have hnorm_ge : ‖s‖ ≤ ‖1 - s‖ := by simpa using norm_sub_one_le_norm_of_half_le_re hre'
    have hnorm_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
      have := norm_sub_le (1 : ℂ) s; rw [norm_one] at this; linarith
    have hloga0 : 0 ≤ Real.log ‖1 - s‖ := Real.log_nonneg (by linarith)
    rw [← riemannXi_one_sub s]
    refine (main (1 - s) hre' (hsnorm.trans hnorm_ge)).trans (Real.exp_le_exp.mpr ?_)
    have hloga : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
      have h1 : Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by linarith) hnorm_le
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm]
    have hala : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 4 * (‖s‖ * Real.log ‖s‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hnorm_le hloga0,
        mul_le_mul_of_nonneg_left hloga (by linarith [norm_nonneg s] : (0 : ℝ) ≤ 2 * ‖s‖)]
    linarith [mul_le_mul_of_nonneg_left hala hC0.le]
end
end CertificatePort19

section CertificatePort20
section
open Complex Filter Topology MeasureTheory Set Function MeromorphicOn Metric
open scoped ENNReal NNReal
private theorem meromorphic_riemannXi : Meromorphic riemannXi :=
  fun z ↦ (analyticOnNhd_riemannXi z (mem_univ z)).meromorphicAt
theorem logCounting_riemannXi_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) R
        ≤ C * (R * Real.log R) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  refine ⟨Cξ + 1 / 2, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  simp only [Set.top_eq_univ]
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      meromorphic_riemannXi hRpos.ne',
    (analyticOnNhd_riemannXi 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero
      (by rw [riemannXi_zero]; norm_num),
    riemannXi_zero,
    show Real.log ‖(1 : ℂ) / 2‖ = -Real.log 2 from by
      rw [Complex.norm_div, norm_one, Complex.norm_ofNat, one_div, Real.log_inv]]
  have hca : Real.circleAverage (fun x ↦ Real.log ‖riemannXi x‖) 0 R ≤ Cξ * (R * Real.log R) := by
    refine Real.circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm (fun z _ ↦ meromorphic_riemannXi z)) fun x hx ↦ ?_
    rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hRpos] at hx
    by_cases hzero : riemannXi x = 0
    · rw [hzero, norm_zero, Real.log_zero]
      exact mul_nonneg hCξ.le (mul_nonneg hRpos.le (Real.log_nonneg (by linarith)))
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero), ← hx]
      exact hξ x (by rw [hx]; exact hR)
  have hl2R : Real.log 2 ≤ 1 / 2 * (R * Real.log R) := by
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR,
      mul_nonneg (show (0 : ℝ) ≤ R - 2 by linarith)
        (Real.log_nonneg (show (1 : ℝ) ≤ R by linarith))]
  linarith
theorem divisor_riemannXi_nonneg : 0 ≤ MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) :=
  analyticOnNhd_riemannXi.divisor_nonneg
theorem divisor_riemannXi_cast_nonneg (z : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast divisor_riemannXi_nonneg z
theorem divisor_riemannXi_toNat_cast (z : ℂ) :
    (((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℕ) : ℝ)
      = ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (divisor_riemannXi_nonneg z)
theorem divisor_riemannXi_apply_zero : MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) 0 = 0 := by
  have hanalytic : AnalyticAt ℂ riemannXi 0 := analyticOnNhd_riemannXi 0 (mem_univ 0)
  change MeromorphicOn.divisor riemannXi univ 0 = 0
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ meromorphic_riemannXi z) (mem_univ 0),
    hanalytic.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannXi_zero]; norm_num))]
  rfl
noncomputable def riemannXiZeroCount (R : ℝ) : ℝ :=
  ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z : ℤ) : ℝ)
theorem divisor_riemannXi_closedBall_eq (R : ℝ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor riemannXi (closedBall 0 R) z = MeromorphicOn.divisor riemannXi ⊤ z := by
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) hz]
  change _ = MeromorphicOn.divisor riemannXi univ z
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) (mem_univ z)]
theorem tsum_toNat_divisor_closedBall (R : ℝ) :
    ∑' z : closedBall (0 : ℂ) R, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
      = ENNReal.ofReal (riemannXiZeroCount R) := by
  have hsupp : (Function.support
      fun w : ℂ ↦ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ)).Finite :=
    ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset fun z hz ↦ by simpa [Function.mem_support] using hz
  have hnn : ∀ w : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ) :=
    fun w ↦ by exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg w
  rw [riemannXiZeroCount, ← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hsupp,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hsupp),
    tsum_subtype (closedBall (0 : ℂ) R)
      (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))]
  refine tsum_congr fun w ↦ ?_
  by_cases hw : w ∈ closedBall (0 : ℂ) R
  · rw [Set.indicator_of_mem hw, divisor_riemannXi_closedBall_eq R hw,
      ← divisor_riemannXi_toNat_cast w, ENNReal.ofReal_natCast]
  · rw [Set.indicator_of_notMem hw,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
    simp
theorem riemannXiZeroCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → riemannXiZeroCount R ≤ C * (R * Real.log R) := by
  obtain ⟨CN, hCN, hN⟩ := logCounting_riemannXi_le
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * CN / Real.log 2, by positivity, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h2Rabs : |2 * R| = 2 * R := abs_of_pos (by linarith)
  have hRHSnn : ∀ z : ℂ, 0 ≤ ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
      (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹) := fun z ↦ by
    by_cases hz2R : z ∈ closedBall (0 : ℂ) (2 * R)
    · rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hznorm : ‖z‖ ≤ 2 * R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz2R
        rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by rwa [h2Rabs])]
        exact mul_nonneg (divisor_riemannXi_cast_nonneg z)
          (Real.log_nonneg (by rw [le_mul_inv_iff₀ hzpos]; linarith))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by rw [h2Rabs]; exact hz2R)]
      simp
  have hkey : Real.log 2 * riemannXiZeroCount R ≤
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R) := by
    rw [show Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R)
          = ∑ᶠ z, ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
              (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹)
            + ((MeromorphicOn.divisor riemannXi ⊤) 0 : ℝ) * Real.log (2 * R) from by
        simp only [Function.locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]]
    rw [divisor_riemannXi_apply_zero, Int.cast_zero, zero_mul, add_zero, riemannXiZeroCount,
      mul_finsum]
    refine finsum_le_finsum' ?_ ?_ ?_
    · refine ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset (fun z hz ↦ ?_)
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hz
      simpa [Function.mem_support] using hz.2
    · refine ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
        (MeromorphicOn.divisor riemannXi ⊤)).finiteSupport
          (isCompact_closedBall 0 |2 * R|)).subset (fun z hz ↦ ?_)
      simpa [Function.mem_support, Int.cast_eq_zero]
        using Function.support_mul_subset_left _ _ hz
    · intro z
      dsimp only
      by_cases hzR : z ∈ closedBall (0 : ℂ) R
      ·
        rw [divisor_riemannXi_closedBall_eq R hzR]
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [divisor_riemannXi_apply_zero]; simp
        · have hznorm : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
          have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by
            rw [h2Rabs]; simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith)]
          have hloglow : Real.log 2 ≤ Real.log (2 * R * ‖z‖⁻¹) :=
            Real.log_le_log (by norm_num) (by rw [le_mul_inv_iff₀ hzpos]; linarith)
          linarith [mul_le_mul_of_nonneg_left hloglow (divisor_riemannXi_cast_nonneg z)]
      ·
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzR, Int.cast_zero, mul_zero]
        exact hRHSnn z
  have hlog2R : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR]
  have hstep : CN * (2 * R * Real.log (2 * R)) ≤ 4 * CN * (R * Real.log R) := by
    rw [show 4 * CN * (R * Real.log R) = CN * (2 * R * (2 * Real.log R)) by ring]
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  linarith [hkey.trans ((hN (2 * R) (by linarith)).trans hstep)]
private theorem exists_dyadic_shell {x : ℝ} (hx : 1 < x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  obtain ⟨n, hn1, hn2⟩ :=
    exists_mem_Ico_zpow (by linarith : (0 : ℝ) < x) (by norm_num : (1 : ℝ) < 2)
  have hn0 : 0 ≤ n := by
    by_contra h
    rw [not_le] at h
    have h1 : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by lia)
    rw [zpow_zero] at h1; linarith
  exact ⟨n.toNat, by rw [← zpow_natCast, Int.toNat_of_nonneg hn0]; exact hn1,
    by rw [← zpow_natCast (2 : ℝ) (n.toNat + 1), Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg hn0]; exact hn2⟩
theorem summable_riemannXiDivisor_norm_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℂ ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) := by
  obtain ⟨Cn, hCn, hn⟩ := riemannXiZeroCount_le
  set g : ℂ → ℝ := fun z ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p) with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z ↦ mul_nonneg (divisor_riemannXi_cast_nonneg z) (by positivity)
  rw [show g = fun z ↦ ((Real.toNNReal (g z) : ℝ≥0) : ℝ) from
      funext fun z ↦ (Real.coe_toNNReal _ (hgnn z)).symm,
    ← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  change (∑' z : ℂ, ENNReal.ofReal (g z)) ≠ ∞
  set s : ℝ := (2 : ℝ) ^ (-p) with hs
  set r : ℝ := 2 * s with hr
  have hreq : r = (2 : ℝ) ^ (1 - p) := by
    rw [hr, hs, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hr0 : 0 < r := by rw [hreq]; positivity
  have hr1 : r < 1 := by
    rw [hreq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A : ℕ → Set ℂ := fun k ↦ {z | (2 : ℝ) ^ k ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (k + 1)}
  have hcover : (univ : Set ℂ) ⊆ closedBall (0 : ℂ) 1 ∪ ⋃ k : ℕ, A k := fun z _ ↦ by
    by_cases h1 : ‖z‖ ≤ 1
    · exact Or.inl (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    · exact Or.inr (mem_iUnion.mpr (exists_dyadic_shell (not_le.mp h1)))
  set B : ℕ → ℝ := fun k ↦ 2 * Cn * Real.log 2 * (((k : ℝ) + 1) * r ^ k) with hB
  have hBnn : ∀ k, 0 ≤ B k := fun k ↦ by rw [hB]; positivity
  have hBsum : Summable B := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0.le])
    rw [hB]
    exact (((h1.add (summable_geometric_of_lt_one hr0.le hr1)).congr
      fun k ↦ by rw [pow_one]; ring).mul_left _)
  have hshell : ∀ k : ℕ, ∑' z : A k, ENNReal.ofReal (g z) ≤ ENNReal.ofReal (B k) := fun k ↦ by
    have h2k1 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      simpa using pow_le_pow_right₀ one_le_two (Nat.le_add_left 1 k)
    have hskeq : ((2 : ℝ) ^ k) ^ (-p) = s ^ k := by
      rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ (-p)) k, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have hlognn : 0 ≤ Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))) :=
      mul_nonneg hCn.le (mul_nonneg (by positivity)
        (Real.log_nonneg (one_le_pow₀ (by norm_num))))
    calc ∑' z : A k, ENNReal.ofReal (g z)
        ≤ ∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
            * ENNReal.ofReal (s ^ k) := by
          refine ENNReal.tsum_le_tsum fun z ↦ ?_
          rw [← ENNReal.ofReal_natCast, divisor_riemannXi_toNat_cast,
            ← ENNReal.ofReal_mul (divisor_riemannXi_cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hg]
          exact mul_le_mul_of_nonneg_left
            (hskeq ▸ Real.rpow_le_rpow_of_nonpos (by positivity) z.2.1 (by linarith))
            (divisor_riemannXi_cast_nonneg _)
      _ = (∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞))
            * ENNReal.ofReal (s ^ k) := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (riemannXiZeroCount (2 ^ (k + 1))) * ENNReal.ofReal (s ^ k) := by
          rw [← tsum_toNat_divisor_closedBall]
          gcongr
          exact ENNReal.tsum_mono_subtype
            (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))
            fun z hz ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2.le
      _ ≤ ENNReal.ofReal (Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))))
            * ENNReal.ofReal (s ^ k) := by gcongr; exact hn _ h2k1
      _ = ENNReal.ofReal (B k) := by
          rw [← ENNReal.ofReal_mul hlognn]
          simp only [hB]
          congr 1
          rw [Real.log_pow, pow_succ, hr, mul_pow]
          push_cast; ring
  have hinner : (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) ≠ ∞ := by
    refine (summable_of_hasFiniteSupport (Set.Finite.subset
      (((MeromorphicOn.divisor riemannXi (closedBall 0 1)).finiteSupport
        (isCompact_closedBall 0 1)).preimage Subtype.coe_injective.injOn)
      fun z hz ↦ ?_)).tsum_ofReal_ne_top
    rw [Set.mem_preimage, Function.mem_support, divisor_riemannXi_closedBall_eq 1 z.2]
    exact fun h0 ↦ hz (by simp only [hg]; rw [h0]; simp)
  have hBtop : (∑' k : ℕ, ENNReal.ofReal (B k)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum]; exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hinner, hBtop⟩) ?_
  calc ∑' z : ℂ, ENNReal.ofReal (g z)
      = ∑' z : (univ : Set ℂ), ENNReal.ofReal (g z) := (tsum_univ _).symm
    _ ≤ ∑' z : (closedBall (0 : ℂ) 1 ∪ (⋃ k : ℕ, A k) : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_mono_subtype (fun w ↦ ENNReal.ofReal (g w)) hcover
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z))
          + ∑' z : (⋃ k : ℕ, A k : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_union_le (fun w ↦ ENNReal.ofReal (g w)) _ _
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) + ∑' k : ℕ, ENNReal.ofReal (B k) := by
        gcongr
        exact (ENNReal.tsum_iUnion_le_tsum (fun w ↦ ENNReal.ofReal (g w)) A).trans
          (ENNReal.tsum_le_tsum hshell)
theorem summable_inv_norm_sq_riemannXiZeros :
    Summable (fun i : (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
        Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat ↦ ‖((i.1 : ℂ))⁻¹‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  refine ((summable_riemannXiDivisor_norm_rpow (show (1 : ℝ) < 2 by norm_num)).subtype
    (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  rw [tsum_fintype]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, divisor_riemannXi_toNat_cast]
  rw [norm_inv, inv_pow, ← Real.rpow_natCast ‖z.1‖ 2, ← Real.rpow_neg (norm_nonneg _)]
  norm_num
end
end CertificatePort20

section CertificatePort21
section
open Complex Filter Topology MeromorphicOn Set Function Metric
abbrev RiemannXiZerosIndex : Type :=
  (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
    Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat
abbrev riemannXiZeros (i : RiemannXiZerosIndex) : ℂ := (i.1 : ℂ)
theorem riemannXiZeros_ne_zero (i : RiemannXiZerosIndex) : riemannXiZeros i ≠ 0 := by
  intro h
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (i.1 : ℂ) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [show (i.1 : ℂ) = 0 from h, divisor_riemannXi_apply_zero] at hmem
  exact hmem rfl
private theorem untop₀_map_natCast (x : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) x).untop₀ = (x.toNat : ℤ) := by
  induction x using ENat.recTopCoe <;> simp
theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ⊤) (z : ℂ) :
    MeromorphicOn.divisor f ⊤ z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ _),
    (hf z (Set.mem_univ _)).meromorphicOrderAt_eq, untop₀_map_natCast]
  rfl
theorem ncard_setOf_riemannXiZeros_eq (z : ℂ) :
    {i | riemannXiZeros i = z}.ncard = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i
      simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset]
    calc {i : RiemannXiZerosIndex |
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)}.ncard
        = Nat.card {i : RiemannXiZerosIndex //
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)} :=
          (Nat.card_coe_set_eq _).symm
      _ = Nat.card (Fin (MeromorphicOn.divisor riemannXi ⊤ z).toNat) :=
          Nat.card_congr (Equiv.sigmaSubtype
            (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support))
      _ = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by simp
  · have hempty : {i | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h
      exact hz (h ▸ i.1.2)
    simp only [Function.mem_support, ne_eq, not_not] at hz
    rw [hempty, Set.ncard_empty, hz, Int.toNat_zero]
theorem divisor_riemannXiCanonicalProduct_riemannXiZeros_eq :
    MeromorphicOn.divisor (riemannXiCanonicalProduct riemannXiZeros) ⊤
      = MeromorphicOn.divisor riemannXi ⊤ := by
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPanalytic : AnalyticOnNhd ℂ (riemannXiCanonicalProduct riemannXiZeros) ⊤ :=
    (differentiable_riemannXiCanonicalProduct riemannXiZeros hsum).differentiableOn.analyticOnNhd
      isOpen_univ
  ext z
  have hξnn : 0 ≤ MeromorphicOn.divisor riemannXi ⊤ z := by
    rw [divisor_eq_analyticOrderNatAt analyticOnNhd_riemannXi z]; positivity
  rw [divisor_eq_analyticOrderNatAt hPanalytic z,
    analyticOrderNatAt_riemannXiCanonicalProduct riemannXiZeros hsum riemannXiZeros_ne_zero z,
    ncard_setOf_riemannXiZeros_eq z, Int.toNat_of_nonneg hξnn]
theorem differentiable_riemannXi_div_canonicalProduct :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ s, g s ≠ 0) ∧
      (∀ s, riemannXi s = g s * riemannXiCanonicalProduct riemannXiZeros s) ∧ g 0 = 1 / 2 := by
  set P := riemannXiCanonicalProduct riemannXiZeros with hP
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPdiff : Differentiable ℂ P := differentiable_riemannXiCanonicalProduct riemannXiZeros hsum
  have hPanalytic : AnalyticOnNhd ℂ P ⊤ := hPdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hξanalytic : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hPmero : MeromorphicOn P ⊤ := hPanalytic.meromorphicOn
  have hξmero : MeromorphicOn riemannXi ⊤ := hξanalytic.meromorphicOn
  have hP0 : P 0 = 1 := riemannXiCanonicalProduct_zero riemannXiZeros
  have hP0ne : P 0 ≠ 0 := by rw [hP0]; norm_num
  set F : ℂ → ℂ := fun s ↦ riemannXi s / P s with hF
  have hFmero : MeromorphicOn F ⊤ := hξmero.div hPmero
  have hmordne : ∀ (f : ℂ → ℂ) (x : ℂ), AnalyticOnNhd ℂ f ⊤ → f x ≠ 0 →
      ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := fun f x hf hx z hz ↦
    meromorphicOrderAt_ne_top_of_isPreconnected hf.meromorphicOn isPreconnected_univ
      (Set.mem_univ x) hz (by
        rw [(hf x (Set.mem_univ _)).meromorphicOrderAt_eq,
          (hf x (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hx]; simp)
  have hξne := hmordne riemannXi 0 hξanalytic (by rw [riemannXi_zero]; norm_num)
  have hPne := hmordne P 0 hPanalytic hP0ne
  have hPinvne : ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt P⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    simpa using hPne z hz
  have hdivF : MeromorphicOn.divisor F ⊤ = 0 := by
    have hFeq : F = riemannXi * P⁻¹ := by
      funext s; simp only [hF, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hFeq, MeromorphicOn.divisor_mul hξmero hPmero.inv hξne hPinvne,
      MeromorphicOn.divisor_inv, hP, divisor_riemannXiCanonicalProduct_riemannXiZeros_eq,
      add_neg_cancel]
  set g := toMeromorphicNFOn F ⊤ with hg
  have hgNF : MeromorphicNFOn g ⊤ := meromorphicNFOn_toMeromorphicNFOn F ⊤
  have hdivg0 : MeromorphicOn.divisor g ⊤ = 0 :=
    (MeromorphicOn.divisor_of_toMeromorphicNFOn hFmero).trans hdivF
  have hganalytic : AnalyticOnNhd ℂ g ⊤ :=
    hgNF.divisor_nonneg_iff_analyticOnNhd.mp (le_of_eq hdivg0.symm)
  have hgdiff : Differentiable ℂ g := fun s ↦ (hganalytic s (Set.mem_univ _)).differentiableAt
  have hFanalytic0 : AnalyticAt ℂ F 0 := by
    rw [hF]; exact (hξanalytic 0 (Set.mem_univ _)).div (hPanalytic 0 (Set.mem_univ _)) hP0ne
  have hF0 : F 0 = 1 / 2 := by
    rw [hF]; change riemannXi 0 / P 0 = 1 / 2; rw [riemannXi_zero, hP0]; norm_num
  have hg0 : g 0 = 1 / 2 := by
    have h1 := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hFmero (Set.mem_univ (0 : ℂ))
    rw [toMeromorphicNFAt_eq_self.mpr hFanalytic0.meromorphicNFAt] at h1
    rw [hg, h1.eq_of_nhds, hF0]
  have hgne : ∀ s, g s ≠ 0 := fun s ↦ by
    rw [← (hgNF (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff]
    have hne : meromorphicOrderAt g s ≠ ⊤ :=
      hmordne g 0 hganalytic (by rw [hg0]; norm_num) s (Set.mem_univ _)
    have hdiv : (meromorphicOrderAt g s).untop₀ = 0 := by
      rw [← MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ s), hdivg0]; rfl
    exact (WithTop.untop₀_eq_zero.mp hdiv).resolve_right hne
  have hFg : F =ᶠ[codiscreteWithin ⊤] g := toMeromorphicNFOn_eqOn_codiscrete hFmero
  have hPneSet : P ⁻¹' {0}ᶜ ∈ codiscreteWithin (⊤ : Set ℂ) :=
    hPanalytic.preimage_zero_mem_codiscreteWithin hP0ne (Set.mem_univ _) isConnected_univ
  have hgPeqξ : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
    have e1 : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] (fun s ↦ F s * P s) :=
      hFg.symm.mul (EventuallyEq.refl _ P)
    have e2 : (fun s ↦ F s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
      filter_upwards [hPneSet] with s hs
      have hsne : P s ≠ 0 := by
        simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      simp only [hF]
      exact div_mul_cancel₀ (riemannXi s) hsne
    exact e1.trans e2
  have hgPanalytic : AnalyticOnNhd ℂ (fun s ↦ g s * P s) ⊤ :=
    fun z hz ↦ (hganalytic z hz).mul (hPanalytic z hz)
  have hle : 𝓝[≠] (0 : ℂ) ≤ codiscreteWithin (⊤ : Set ℂ) := by
    rw [Filter.codiscreteWithin]
    refine le_iSup₂_of_le (0 : ℂ) (Set.mem_univ _) (le_of_eq ?_)
    rw [Set.top_eq_univ, ← Set.compl_eq_univ_sdiff]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun s ↦ g s * P s) z = riemannXi z :=
    (hgPeqξ.filter_mono hle).frequently
  exact ⟨g, hgdiff, hgne, fun s ↦ (hgPanalytic.eqOn_of_preconnected_of_frequently_eq hξanalytic
    isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ s)).symm, hg0⟩
theorem exists_entire_log_riemannXi_div_canonicalProduct :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (1 / 2) ∧
      (∀ s, riemannXi s = Complex.exp (h s) *
        riemannXiCanonicalProduct riemannXiZeros s) := by
  obtain ⟨g, hgdiff, hgne, hgP, hg0⟩ := differentiable_riemannXi_div_canonicalProduct
  set φ : ℂ → ℂ := fun s ↦ deriv g s / g s with hφ
  have hgana : AnalyticOnNhd ℂ g Set.univ := hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hderivdiff : Differentiable ℂ (deriv g) :=
    fun x ↦ (hgana.deriv x (Set.mem_univ _)).differentiableAt
  have hφdiff : Differentiable ℂ φ := hderivdiff.div hgdiff hgne
  obtain ⟨H, hH0, hHderiv⟩ := hφdiff.isExactOn_univ.with_val_at 0 0
  have hHderiv' : ∀ x, HasDerivAt H (φ x) x := fun x ↦ hHderiv x (Set.mem_univ _)
  have hHdiff : Differentiable ℂ H := fun x ↦ (hHderiv' x).differentiableAt
  set k : ℂ → ℂ := fun s ↦ g s * Complex.exp (-H s) with hk
  have hkderiv : ∀ x, HasDerivAt k 0 x := by
    intro x
    have hg_deriv : HasDerivAt g (deriv g x) x := (hgdiff x).hasDerivAt
    have hexp_deriv := ((hHderiv' x).neg).cexp
    have hval : deriv g x * Complex.exp ((-H) x) +
        g x * (Complex.exp ((-H) x) * -φ x) = 0 := by
      simp only [hφ]
      field_simp [hgne x]
      ring
    exact hval ▸ hg_deriv.mul hexp_deriv
  have hkdiff : Differentiable ℂ k := fun x ↦ (hkderiv x).differentiableAt
  have hkconst : ∀ s, k s = k 0 :=
    fun s ↦ is_const_of_deriv_eq_zero hkdiff (fun x ↦ (hkderiv x).deriv) s 0
  have hk0 : k 0 = 1 / 2 := by
    simp only [hk, hH0, neg_zero, Complex.exp_zero, mul_one, hg0]
  refine ⟨fun s ↦ H s + Complex.log (1 / 2), hHdiff.add_const _, by simp [hH0], fun s ↦ ?_⟩
  have hk_eval : g s * Complex.exp (-H s) = 1 / 2 := by
    have := hkconst s; rw [hk0] at this; simpa only [hk] using this
  have hexp : Complex.exp (H s + Complex.log (1 / 2)) = g s := by
    rw [Complex.exp_add, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0), ← hk_eval,
      Complex.exp_neg, mul_comm (g s), ← mul_assoc,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]
  rw [hgP s, hexp]
end
end CertificatePort21

section CertificatePort22
section
open Complex Filter Topology MeasureTheory
theorem neg_le_log_norm_weierstrassE1 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    -4 * ‖w‖ ^ 2 ≤ Real.log ‖weierstrassE1 w‖ := by
  set x : ℝ := 2 * ‖w‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 1 / 2 := by rw [hx]; nlinarith [norm_nonneg w]
  have hpos : 0 < 1 - x := by linarith
  have hge : 1 - x ≤ ‖weierstrassE1 w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (weierstrassE1 w)
    rw [norm_one, norm_sub_rev] at h
    linarith [norm_weierstrassE1_sub_one_le hw]
  have hlog : -(2 * x) ≤ Real.log (1 - x) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - x)⁻¹ by positivity)
    rw [Real.log_inv] at h
    nlinarith [mul_inv_cancel₀ hpos.ne', inv_nonneg.mpr hpos.le,
      mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]
  calc -4 * ‖w‖ ^ 2 = -(2 * x) := by rw [hx]; ring
    _ ≤ Real.log (1 - x) := hlog
    _ ≤ Real.log ‖weierstrassE1 w‖ := Real.log_le_log hpos hge
theorem Real.log_add_one_sq_le {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R + 1) ^ 2 ≤ 16 * R ^ (1 / 2 : ℝ) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hnn : 0 ≤ Real.log R + 1 := by linarith [Real.log_nonneg hR]
  have hle : Real.log R + 1 ≤ 4 * R ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hR0 (1 / 4 : ℝ))
    rw [Real.log_rpow hR0] at h; linarith
  calc (Real.log R + 1) ^ 2 ≤ (4 * R ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
    _ = 16 * R ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hR0.le]; norm_num
theorem finite_setOf_riemannXiZeros_eq (z : ℂ) :
    {i : RiemannXiZerosIndex | riemannXiZeros i = z}.Finite := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i : RiemannXiZerosIndex | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i; simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset, ← Set.finite_coe_iff]
    exact Finite.of_equiv _ (Equiv.sigmaSubtype
      (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)).symm
  · have hempty : {i : RiemannXiZerosIndex | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h; exact hz (h ▸ i.1.2)
    rw [hempty]; exact Set.finite_empty
private def zerosInBall (t : ℝ) : Set ℂ :=
  {z | z ∈ (MeromorphicOn.divisor riemannXi ⊤).support ∧ ‖z‖ ≤ t}
private theorem finite_zerosInBall (t : ℝ) : (zerosInBall t).Finite := by
  refine ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t)).finiteSupport
    (isCompact_closedBall 0 t)).subset fun z hz ↦ ?_
  obtain ⟨hzsupp, hzt⟩ := hz
  have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzt
  rw [Function.mem_support, divisor_riemannXi_closedBall_eq t hzb]
  rwa [Function.mem_support] at hzsupp
private theorem setOf_norm_le_eq_biUnion (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}
      = ⋃ z ∈ zerosInBall t, {i : RiemannXiZerosIndex | riemannXiZeros i = z} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  exact ⟨fun hi ↦ ⟨riemannXiZeros i, ⟨i.1.2, hi⟩, rfl⟩, fun ⟨_, ⟨_, hzt⟩, hz⟩ ↦ hz ▸ hzt⟩
theorem finite_setOf_norm_riemannXiZeros_le (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.Finite := by
  rw [setOf_norm_le_eq_biUnion]
  exact (finite_zerosInBall t).biUnion fun z _ ↦ finite_setOf_riemannXiZeros_eq z
theorem ncard_setOf_norm_riemannXiZeros_le_eq (t : ℝ) :
    (({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ)) = riemannXiZeroCount t := by
  have hZfin := finite_zerosInBall t
  set Zf := hZfin.toFinset
  have hncard : {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard
      = ∑ z ∈ Zf, (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
    rw [setOf_norm_le_eq_biUnion,
      Set.Finite.ncard_biUnion hZfin (fun z _ ↦ finite_setOf_riemannXiZeros_eq z) ?_]
    · rw [← hZfin.coe_toFinset, finsum_mem_coe_finset]
      exact Finset.sum_congr rfl fun z _ ↦ ncard_setOf_riemannXiZeros_eq z
    · intro z₁ _ z₂ _ hne
      refine Set.disjoint_left.mpr fun i hi1 hi2 ↦ hne ?_
      simp only [Set.mem_ofPred_eq] at hi1 hi2
      rw [← hi1, ← hi2]
  have hcount : riemannXiZeroCount t
      = ∑ z ∈ Zf, ((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℝ) := by
    have hdef : riemannXiZeroCount t
        = ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z : ℤ) : ℝ) := rfl
    rw [hdef, finsum_eq_finsetSum_of_support_subset _ (s := Zf) ?subset]
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using (hZfin.mem_toFinset.mp hz).2
      rw [divisor_riemannXi_closedBall_eq t hzb]
      exact (divisor_riemannXi_toNat_cast z).symm
    case subset =>
      intro z hz
      have hzint : MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z ≠ 0 :=
        Int.cast_ne_zero.mp (Function.mem_support.mp hz)
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        by_contra hb
        exact hzint (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb)
      rw [Finset.mem_coe, hZfin.mem_toFinset]
      refine ⟨Function.mem_support.mpr ?_, by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzb⟩
      rw [← divisor_riemannXi_closedBall_eq t hzb]; exact hzint
  rw [hncard, hcount, Nat.cast_sum]
theorem exists_card_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      ({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ) ≤ C * (t * Real.log t) := by
  obtain ⟨C, hC, hbound⟩ := riemannXiZeroCount_le
  exact ⟨C, hC, fun t ht ↦ by rw [ncard_setOf_norm_riemannXiZeros_le_eq t]; exact hbound t ht⟩
theorem exists_mem_Icc_forall_le_dist {S : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hcard : 2 * δ * S.card < b - a) :
    ∃ r ∈ Set.Icc a b, ∀ t ∈ S, δ ≤ |r - t| := by
  classical
  set B : Set ℝ := ⋃ t ∈ S, Set.Ioo (t - δ) (t + δ) with hB
  have hlt : volume B < volume (Set.Icc a b) := by
    have hvolB : volume B ≤ ENNReal.ofReal (2 * δ * S.card) := by
      refine (measure_biUnion_finset_le S _).trans ?_
      rw [show ENNReal.ofReal (2 * δ * S.card) = ∑ _t ∈ S, ENNReal.ofReal (2 * δ) from by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring]
      exact Finset.sum_le_sum fun t _ ↦ le_of_eq (by rw [Real.volume_Ioo]; congr 1; ring)
    rw [Real.volume_Icc]
    exact hvolB.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hcard)
  obtain ⟨r, hrIcc, hrB⟩ : (Set.Icc a b \ B).Nonempty :=
    nonempty_of_measure_ne_zero (μ := volume) fun hzero ↦ absurd
      ((measure_mono (Set.subset_sdiff_union (Set.Icc a b) B)).trans
        ((measure_union_le _ _).trans_eq (by rw [hzero, zero_add]))) (not_le.mpr hlt)
  refine ⟨r, hrIcc, fun t ht ↦ ?_⟩
  have hrt : r ∉ Set.Ioo (t - δ) (t + δ) := fun h ↦ hrB (by rw [hB]; exact Set.mem_biUnion ht h)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hrt
  rcases hrt with h | h
  · exact le_abs.mpr (.inr (by linarith))
  · exact le_abs.mpr (.inl (by linarith))
private lemma inv_rpow_mul_rpow {a : ℝ} (ha : 0 < a) (p q : ℝ) :
    a⁻¹ ^ p * a ^ q = a ^ (q - p) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring
theorem summable_inv_norm_rpow_riemannXiZeros {p : ℝ} (hp : 1 < p) :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ p) := by
  rw [summable_sigma_of_nonneg fun _ ↦ by positivity]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  have hbase := summable_riemannXiDivisor_norm_rpow hp
  refine (hbase.subtype (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  have hz0 : z.1 ≠ 0 := by
    intro h
    have hmem := Function.mem_support.mp z.2
    rw [h, divisor_riemannXi_apply_zero] at hmem
    exact hmem rfl
  rw [tsum_fintype]
  simp only [riemannXiZeros, Function.comp_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show ‖z.1⁻¹‖ ^ p = ‖z.1‖ ^ (-p) from by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)],
    divisor_riemannXi_toNat_cast z.1]
private noncomputable def holderSum : ℝ :=
  ∑' i : RiemannXiZerosIndex, ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)
private theorem summable_inv_norm_rpow_three_halves :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :=
  summable_inv_norm_rpow_riemannXiZeros (by norm_num)
private theorem holderSum_nonneg : 0 ≤ holderSum := tsum_nonneg fun _ ↦ by positivity
private theorem tsum_subtype_le_of_le_mul {s : Set RiemannXiZerosIndex}
    {f : RiemannXiZerosIndex → ℝ} (hfs : Summable fun i : s ↦ f (i : RiemannXiZerosIndex))
    {e : ℝ} (he : 0 ≤ e)
    (hf : ∀ i ∈ s, f i ≤ e * ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :
    ∑' i : s, f (i : RiemannXiZerosIndex) ≤ (holderSum + 1) * e :=
  calc ∑' i : s, f (i : RiemannXiZerosIndex)
      ≤ ∑' i : s, e * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) :=
        Summable.tsum_le_tsum (fun i ↦ hf i i.2) hfs
          ((summable_inv_norm_rpow_three_halves.subtype s).mul_left _)
    _ = e * ∑' i : s, ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ e * holderSum :=
        mul_le_mul_of_nonneg_left
          (summable_inv_norm_rpow_three_halves.tsum_subtype_le _ s fun _ ↦ by positivity) he
    _ ≤ (holderSum + 1) * e := by nlinarith [holderSum_nonneg]
theorem exists_sum_inv_norm_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le t).toFinset, ‖(riemannXiZeros i)⁻¹‖
        ≤ C * t ^ (1 / 2 : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  rw [← Finset.tsum_subtype (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)]
  refine tsum_subtype_le_of_le_mul (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)
    (e := t ^ (1 / 2 : ℝ)) Summable.of_finite (Real.rpow_nonneg ht _) fun i hi ↦ ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  calc a⁻¹
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (1 / 2 - 3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hi (by norm_num)) (by positivity)
    _ = t ^ (1 / 2 : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
theorem exists_sum_inv_norm_sq_riemannXiZeros_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      ∑' i : {i : RiemannXiZerosIndex // t < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 ≤ C * t ^ (-(1 / 2) : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  refine tsum_subtype_le_of_le_mul (s := {i | t < ‖riemannXiZeros i‖})
    (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) (e := t ^ (-(1 / 2) : ℝ))
    (summable_inv_norm_sq_riemannXiZeros.subtype _) (Real.rpow_nonneg ht.le _) fun i hi ↦ ?_
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := lt_trans ht hi
  calc a⁻¹ ^ 2
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (-(1 / 2) - 3 / 2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) by norm_num,
          Real.rpow_mul ha.le, Real.rpow_natCast, Real.rpow_neg_one, ← inv_pow]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ht hi.le (by norm_num)) (by positivity)
    _ = t ^ (-(1 / 2) : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
private lemma self_mul_rpow_half {R : ℝ} (hR : 0 < R) :
    R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]
private lemma far_rpow_id {R : ℝ} (hR : 0 < R) :
    16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ) = 8 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; norm_num
  have hRid : R ^ 2 * R ^ (-(1 / 2) : ℝ) = R ^ (3 / 2 : ℝ) := by
    have h2 : R ^ 2 = R ^ (2 : ℝ) := by rw [← Real.rpow_natCast R 2]; norm_num
    rw [h2, ← Real.rpow_add hR, show (2 : ℝ) + -(1 / 2) = 3 / 2 by norm_num]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 16 * R ^ 2 * (1 / 2 * R ^ (-(1 / 2) : ℝ)) = 8 * (R ^ 2 * R ^ (-(1 / 2) : ℝ)) by ring, hRid]
private lemma near_rpow_id {R : ℝ} (hR : 0 < R) :
    2 * R * (4 * R) ^ (1 / 2 : ℝ) = 4 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 2 * R * (2 * R ^ (1 / 2 : ℝ)) = 4 * (R * R ^ (1 / 2 : ℝ)) by ring, self_mul_rpow_half hR]
theorem exists_tsum_far_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ 2 * R →
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
  obtain ⟨C2, hC2pos, hC2⟩ := exists_sum_inv_norm_sq_riemannXiZeros_tail_le
  refine ⟨8 * C2, by positivity, fun R hR s hs ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hsublog := (summable_log_norm_weierstrassE1 riemannXiZeros
    summable_inv_norm_sq_riemannXiZeros s).subtype {i | 4 * R < ‖riemannXiZeros i‖}
  have hsubinv := (summable_inv_norm_sq_riemannXiZeros.subtype
    {i | 4 * R < ‖riemannXiZeros i‖}).mul_left (-16 * R ^ 2)
  have hterm : ∀ i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
      -16 * R ^ 2 * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2
        ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
    intro i
    set ρ := riemannXiZeros (i : RiemannXiZerosIndex) with hρ
    have hρpos : (0 : ℝ) < ‖ρ‖ := lt_trans h4R i.2
    refine le_trans ?_ (neg_le_log_norm_weierstrassE1
      (show ‖s / ρ‖ ≤ 1 / 2 by rw [norm_div, div_le_iff₀ hρpos]; linarith [i.2]))
    rw [show ‖s / ρ‖ ^ 2 = ‖s‖ ^ 2 * ‖ρ⁻¹‖ ^ 2 by rw [norm_div, norm_inv]; ring]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * R ^ 2 - 4 * ‖s‖ ^ 2 by
      nlinarith [hs, norm_nonneg s, hRpos]) (sq_nonneg ‖ρ⁻¹‖)]
  refine le_trans ?_
    (Summable.tsum_le_tsum (L := SummationFilter.unconditional _) hterm hsubinv hsublog)
  rw [tsum_mul_left]
  calc -(8 * C2 * R ^ (3 / 2 : ℝ))
      = -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ)) := by
        rw [show -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ))
          = -(C2 * (16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ))) by ring, far_rpow_id hRpos]; ring
    _ ≤ -16 * R ^ 2 * ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonpos_left (hC2 (4 * R) h4R) (by nlinarith [sq_nonneg R, hRpos])
theorem exists_finset_near_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (∀ i : RiemannXiZerosIndex, ‖riemannXiZeros i‖ ≤ 4 * R → s ≠ riemannXiZeros i) ∧
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset,
          Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
  obtain ⟨Cn, hCnpos, hCn⟩ := exists_card_riemannXiZeros_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_inv_norm_riemannXiZeros_le
  set Clog : ℝ := Real.log (256 * Cn + 4) + 2 with hClog
  have hlogc : (0 : ℝ) ≤ Real.log (256 * Cn + 4) := Real.log_nonneg (by linarith)
  have hcc : (0 : ℝ) ≤ 12 * Cn * Clog := by rw [hClog]; nlinarith
  refine ⟨4 * C1 + 192 * Cn * Clog, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  set m := F.card with hm
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set δ : ℝ := R / (4 * ((m : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := div_pos hRpos (by positivity)
  have hδid : δ * (4 * ((m : ℝ) + 1)) = R := by rw [hδ]; field_simp
  have hmcard : (m : ℝ) ≤ Cn * (4 * R * Real.log (4 * R)) := by
    rw [hm, hF, ← Set.ncard_eq_toFinset_card _ (finite_setOf_norm_riemannXiZeros_le (4 * R))]
    exact hCn (4 * R) (by linarith)
  obtain ⟨R', hR'mem, hR'dist⟩ :=
    exists_mem_Icc_forall_le_dist (S := F.image fun i ↦ ‖riemannXiZeros i‖) (a := R) (b := 2 * R)
      hδpos (by
        have hci : ((F.image fun i ↦ ‖riemannXiZeros i‖).card : ℝ) ≤ (m : ℝ) := by
          rw [hm]; exact_mod_cast Finset.card_image_le
        nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hci), mul_nonneg hδpos.le hmnn])
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  have hR'le : R' ≤ 2 * R := hR'mem.2
  have hdist : ∀ i ∈ F, δ ≤ ‖s - riemannXiZeros i‖ := fun i hiF ↦
    (hR'dist _ (Finset.mem_image_of_mem _ hiF)).trans <| by
      simpa only [hs] using abs_norm_sub_norm_le s (riemannXiZeros i)
  have hne : ∀ i ∈ F, s ≠ riemannXiZeros i := fun i hiF heq ↦ by
    have hd := hdist i hiF; rw [heq, sub_self, norm_zero] at hd; linarith
  refine ⟨fun i hi ↦ hne i (by rw [hF, Set.Finite.mem_toFinset]; exact hi), ?_⟩
  have hlogd : Real.log δ - Real.log (4 * R) = -Real.log (16 * ((m : ℝ) + 1)) := by
    rw [← Real.log_div hδpos.ne' (by positivity), ← Real.log_inv]
    congr 1
    rw [hδ]; field_simp; ring
  have hpt : ∀ i ∈ F, Real.log δ - Real.log (4 * R) - 2 * R * ‖(riemannXiZeros i)⁻¹‖
      ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
    intro i hiF
    set ρ := riemannXiZeros i with hρ
    have hρne : ρ ≠ 0 := riemannXiZeros_ne_zero i
    have hi4R : ‖ρ‖ ≤ 4 * R := by have h := hiF; rw [hF, Set.Finite.mem_toFinset] at h; exact h
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
    have hsne : s ≠ ρ := hne i hiF
    rw [log_norm_weierstrassE1 (fun h ↦ hsne ((div_eq_one_iff_eq hρne).mp h)),
      show ‖(1 : ℂ) - s / ρ‖ = ‖s - ρ‖ / ‖ρ‖ by
        rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ by rw [sub_div, div_self hρne], norm_div,
          norm_sub_rev],
      Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsne)) hρpos.ne']
    have hb2 : ‖s / ρ‖ ≤ 2 * R * ‖ρ⁻¹‖ := by
      rw [norm_div, norm_inv, hs, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hR'le (by positivity)
    linarith [Real.log_le_log hδpos (hdist i hiF), Real.log_le_log hρpos hi4R,
      (abs_le.mp (Complex.abs_re_le_norm (s / ρ))).1]
  refine le_trans ?_ (Finset.sum_le_sum hpt)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hlogd, mul_neg]
  have h2Rsum : 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖ ≤ 4 * C1 * R ^ (3 / 2 : ℝ) :=
    calc 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖
        ≤ 2 * R * (C1 * (4 * R) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [hF]; exact hC1 (4 * R) (by linarith)) (by linarith)
      _ = C1 * (2 * R * (4 * R) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * C1 * R ^ (3 / 2 : ℝ) := by rw [near_rpow_id hRpos]; ring
  have hmlog : (m : ℝ) * Real.log (16 * ((m : ℝ) + 1)) ≤ 192 * Cn * Clog * R ^ (3 / 2 : ℝ) := by
    have hCn4R : (0 : ℝ) ≤ Cn * (4 * R) := by positivity
    have hm12 : (m : ℝ) ≤ 12 * Cn * R * (Real.log R + 1) := by
      have h : Real.log (4 * R) ≤ 3 * (Real.log R + 1) := by
        rw [Real.log_mul (by norm_num) hRpos.ne']
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hm16 : (m : ℝ) ≤ 16 * Cn * R ^ 2 := by
      have h : Real.log (4 * R) ≤ 4 * R :=
        by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * R by linarith)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hlogm : Real.log (16 * ((m : ℝ) + 1)) ≤ Clog * (Real.log R + 1) := by
      have hmono := Real.log_le_log (show (0 : ℝ) < 16 * ((m : ℝ) + 1) by positivity)
        (show 16 * ((m : ℝ) + 1) ≤ (256 * Cn + 4) * R ^ 2 by nlinarith [hm16])
      rw [Real.log_mul (by positivity) (by positivity : (R : ℝ) ^ 2 ≠ 0), Real.log_pow] at hmono
      rw [hClog]
      push_cast at hmono ⊢
      nlinarith [mul_nonneg hlogc hlogR]
    have hRL2 : R * (Real.log R + 1) ^ 2 ≤ 16 * R ^ (3 / 2 : ℝ) := by
      rw [← self_mul_rpow_half hRpos]
      nlinarith [Real.log_add_one_sq_le hR1, hRpos]
    have hstep := mul_le_mul hm12 hlogm (Real.log_nonneg (by linarith))
      (by positivity : (0 : ℝ) ≤ 12 * Cn * R * (Real.log R + 1))
    nlinarith [mul_le_mul_of_nonneg_left hRL2 hcc]
  linarith only [hmlog, h2Rsum]
theorem exists_circle_log_norm_riemannXiCanonicalProduct_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      riemannXiCanonicalProduct riemannXiZeros s ≠ 0 ∧
        -(C * R ^ (3 / 2 : ℝ)) ≤ Real.log ‖riemannXiCanonicalProduct riemannXiZeros s‖ := by
  obtain ⟨CF, hCFpos, hCF⟩ := exists_tsum_far_log_norm_weierstrassE1_ge
  obtain ⟨CN, hCNpos, hCN⟩ := exists_finset_near_log_norm_weierstrassE1_ge
  refine ⟨CF + CN, by linarith, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hCN R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hne_near, hnear⟩ := hR' s hs
  have hs2R : ‖s‖ ≤ 2 * R := by rw [hs]; exact hR'mem.2
  have hsum := summable_inv_norm_sq_riemannXiZeros
  have hsumlog := summable_log_norm_weierstrassE1 riemannXiZeros hsum s
  have hsne : ∀ i, s ≠ riemannXiZeros i := by
    intro i
    rcases le_or_gt ‖riemannXiZeros i‖ (4 * R) with hle | hlt
    · exact hne_near i hle
    · intro heq
      rw [← heq, hs] at hlt
      linarith [hR'mem.2]
  refine ⟨riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros hsum hsne, ?_⟩
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  have hfar : -(CF * R ^ (3 / 2 : ℝ))
      ≤ ∑' x : ↥((↑F : Set RiemannXiZerosIndex)ᶜ),
          Real.log ‖weierstrassE1 (s / riemannXiZeros (x : RiemannXiZerosIndex))‖ := by
    rw [show ((↑F : Set RiemannXiZerosIndex)ᶜ) = {i | 4 * R < ‖riemannXiZeros i‖} by
      rw [hF, Set.Finite.coe_toFinset]
      ext i; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
    exact hCF R hR s hs2R
  rw [log_norm_riemannXiCanonicalProduct riemannXiZeros hsum hsne,
    ← hsumlog.sum_add_tsum_compl (s := F)]
  linarith [hnear, hfar]
end
end CertificatePort22

section CertificatePort23
section
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ f z / z) 0 (deriv f 0)
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ)
    (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  apply Function.update_of_ne z_ne_0
lemma AnalyticOn_divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) :
    AnalyticOn ℂ (divRemovable_zero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0]
  constructor
  · have (x) (hx : x ∈ s \ {0}) : x ≠ 0 := by
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      exact hx.right
    rw [differentiableOn_congr (fun x hyp_x => Function.update_of_ne (this x hyp_x) _ _)]
    exact
      (analytic.mono Set.sdiff_subset).differentiableOn.fun_div
      (differentiableOn_id.mono (Set.subset_univ (s \ {0})))
      this
  · have U :=
      HasDerivAt.continuousAt_div (c := 0) (a := deriv f 0)
        (f := f)
        (DifferentiableOn.hasDerivAt
          ((Complex.analyticOn_iff_differentiableOn o).mp analytic)
          sInNhds0)
    simpa [divRemovable_zero, zero] using U
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ}
    {R : ℝ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) :
    AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  simp only [Metric.mem_closedBall, dist_zero_right] at x_hyp
  cases x_hyp.eq_or_lt with
  | inl h =>
    use Metric.ball x (R / 2)
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp [Rpos]
    · have (x₂) (hyp_x₂ : x₂ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2)) : x₂ ≠ 0 := by
        rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
          Set.mem_ofPred_eq] at hyp_x₂
        rw [← norm_pos_iff]
        calc 0
          _ < R - ‖x₂ - x‖ := by
            obtain ⟨-, v⟩ := hyp_x₂
            linarith
          _ = ‖x‖ - ‖x - x₂‖ := by
            rw [h, norm_sub_rev]
          _ ≤ ‖x - (x - x₂)‖ := norm_sub_norm_le ..
          _ ≤ ‖x₂‖ := by rw [sub_sub_cancel]
      apply AnalyticOn.congr
      · exact (analytic.mono Set.inter_subset_left).div analyticOn_id this
      · intro x₃ hyp_x₃
        exact divRemovable_zero_of_ne_zero _ (this _ hyp_x₃)
  | inr h =>
    use Metric.ball 0 R
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp only [ball_eq, sub_zero, Set.mem_ofPred_eq, h]
    · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R =
        Metric.ball (0 : ℂ) R := by
        apply Set.inter_eq_self_of_subset_right
        exact Metric.ball_subset_closedBall
      rw [si]
      exact AnalyticOn_divRemovable_zero
        (Metric.ball_mem_nhds 0 Rpos)
        zero Metric.isOpen_ball
        (analytic.mono Metric.ball_subset_closedBall)
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) :
    ℂ → ℂ :=
  fun z ↦ divRemovable_zero f z / (2 * M - f z)
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ}
    (M : ℝ) (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) :
    AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) :=
  AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos analytic zero)
    (AnalyticOn.sub analyticOn_const analytic) nonzero
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ}
    {x : ℂ} (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) :
    ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  rw [calc
    (2 * M - x).re * (2 * M - x).re +
        (2 * M - x).im * (2 * M - x).im =
      (2 * M - x.re) * (2 * M - x.re) +
        x.im * x.im := by simp
    _ = x.re * x.re +
        (x.im * x.im + 4 * M * (M - x.re)) := by ring]
  bound
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ}
    {f : ℂ → ℂ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have zInSFunc :
      ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    exact Set.mem_of_mem_of_subset hyp_z <|
      (Metric.sphere_subset_closedBall).trans
        (Metric.closedBall_subset_closedBall hyp_r)
  have fPosAll :
      ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, sub_pos]
      linarith [realPartBounded z zInS])
  have schwartzQuotientBounded :
      ∀ z ∈ Metric.sphere 0 R,
      ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc R le_rfl z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z
    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by
        simp only [Complex.norm_div, divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left
            (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le
              Mpos (realPartBounded z zInS))
      _ ≤ 1 / ‖z‖ := by
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (div_self_le_one _) (norm_nonneg _)
      _ = 1 / R := by rw [hyp_z]
  have maxMod (z) (hz : z ∈ Metric.closedBall 0 R) : ‖schwartzQuotient f M z‖ ≤ 1 / R :=
    AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      schwartzQuotientBounded hz
  have boundForF :
      ∀ r < R, 0 < r →
      ∀ z ∈ Metric.sphere 0 r,
      ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc r hyp_r.le z zOnR
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by
      rwa [← norm_pos_iff, zOnR]
    simp only [divRemovable_zero_of_ne_zero f U, Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by
      simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq, fPosAll z zInS,
        not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 :
        ‖f z‖ ≤ 2 * M * r / R + (r / R) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          grw [norm_sub_le]
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          simp [Mpos.le]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by
          ring_nf
    rw [← tsub_le_iff_right, ← one_sub_mul, ← le_div_iff₀'] at U0
    · have hR : (R : ℝ) ≠ 0 := Rpos.ne'
      have hRr : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyp_r).symm
      have heq : 2 * M * r / (R - r) = 2 * M * r / R / (1 - r / R) := by
        rw [one_sub_div hR]; field_simp
      rw [heq]
      exact U0
    · rwa [sub_pos, div_lt_one₀ Rpos]
  have maxBoundForF
      (r) (hyp_r : r < R) (pos_r : 0 < r)
      (z) (hz : z ∈ Metric.closedBall 0 r) :
      ‖f z‖ ≤ 2 * M * r / (R - r) :=
    AnalyticOn.norm_le_of_norm_le_on_sphere hyp_r.le analytic (boundForF r hyp_r pos_r) hz
  have U : 0 ≤ r := by
    rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
    exact (norm_nonneg z).trans hyp_z
  cases U.eq_or_lt' with
  | inl pos_r =>
    obtain rfl : z = 0 := by
      rwa [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z
    rwa [pos_r, mul_zero, sub_zero, zero_div, norm_le_zero_iff]
  | inr pos_r =>
    exact maxBoundForF r hyp_r pos_r z hyp_z
end
end CertificatePort23

section CertificatePort24
section
open Complex Filter Topology Set Metric
theorem re_log_riemannXi_div_canonicalProduct_le {h : ℂ → ℂ}
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (h s).re ≤ C * R ^ (3 / 2 : ℝ) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  obtain ⟨CP, hCP, hP⟩ := exists_circle_log_norm_riemannXiCanonicalProduct_ge
  refine ⟨Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP, by positivity, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hP R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hPne, hlogP⟩ := hR' s hs
  set P := riemannXiCanonicalProduct riemannXiZeros
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hs ▸ hR.trans hR'mem.1
  have hPpos : 0 < ‖P s‖ := norm_pos_iff.mpr hPne
  have hnormξ : ‖riemannXi s‖ = Real.exp ((h s).re) * ‖P s‖ := by
    rw [hrep s, norm_mul, Complex.norm_exp]
  have hξpos : 0 < ‖riemannXi s‖ := by rw [hnormξ]; positivity
  have hre_eq : (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := by
    rw [hnormξ, Real.log_mul (Real.exp_pos _).ne' hPpos.ne', Real.log_exp, add_sub_cancel_right]
  have hlogξ : Real.log ‖riemannXi s‖ ≤ Cξ * (‖s‖ * Real.log ‖s‖) :=
    (Real.log_le_iff_le_exp hξpos).2 (hξ s hs2)
  have hsl : ‖s‖ * Real.log ‖s‖ ≤ 2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hR0]
    have hlog : Real.log ‖s‖ ≤ 2 * ‖s‖ ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (norm_nonneg s) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hmul : ‖s‖ * ‖s‖ ^ (1 / 2 : ℝ) = ‖s‖ ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have hpow : ‖s‖ ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg s) (hs ▸ hR'mem.2) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hlog (norm_nonneg s)]
  calc (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := hre_eq
    _ ≤ Cξ * (‖s‖ * Real.log ‖s‖) + CP * R ^ (3 / 2 : ℝ) := by linarith
    _ ≤ Cξ * (2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ))) + CP * R ^ (3 / 2 : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hsl hCξ.le]
    _ = (Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP) * R ^ (3 / 2 : ℝ) := by ring
end
end CertificatePort24

section CertificatePort25
section
open Complex Filter Topology Set Metric
theorem exists_affine_log_riemannXi_div_canonicalProduct {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ A B : ℂ, ∀ s, h s = A + B * s := by
  obtain ⟨C, hCpos, hgrow⟩ := re_log_riemannXi_div_canonicalProduct_le hrep
  have hderivdiff : Differentiable ℂ (deriv h) := fun x ↦
    ((analyticOnNhd_univ_iff_differentiable.mpr hdiff).deriv x (mem_univ x)).differentiableAt
  set C₀ : ℝ := 2 * C + 3 * ‖h 0‖ + 2 with hC₀def
  have claimA : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖h z‖ ≤ C₀ * R ^ (3 / 2 : ℝ) := by
    intro R hR z hz
    obtain ⟨R', hR'mem, hR'⟩ := hgrow R hR
    have hR'pos : 0 < R' := by linarith [hR'mem.1]
    have hRpow1 : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCR : 0 ≤ C * R ^ (3 / 2 : ℝ) :=
      mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _)
    have hmax : ∀ w : ℂ, ‖w‖ ≤ R' → (h w).re ≤ C * R ^ (3 / 2 : ℝ) := by
      intro w hw
      have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) R'),
          ‖Complex.exp (h ζ)‖ ≤ Real.exp (C * R ^ (3 / 2 : ℝ)) := fun ζ hζ ↦ by
        rw [frontier_ball 0 hR'pos.ne'] at hζ
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hR' ζ (by simpa using mem_sphere_iff_norm.mp hζ))
      have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        hdiff.cexp.diffContOnCl hfront
        (by rw [closure_ball 0 hR'pos.ne']; simpa [mem_closedBall, dist_eq_norm] using hw)
      rw [Complex.norm_exp] at hle
      exact Real.exp_le_exp.mp hle
    have hbc := borelCaratheodory_closedBall (f := fun s ↦ h s - h 0) (z := z) (r := R' / 2)
      (M := C * R ^ (3 / 2 : ℝ) + ‖h 0‖ + 1) hR'pos
      ((analyticOn_univ_iff_differentiable.mpr (hdiff.sub_const (h 0))).mono (subset_univ _))
      (by simp) (by linarith [norm_nonneg (h 0)])
      (fun ζ hζ ↦ by
        rw [mem_closedBall, dist_eq_norm, sub_zero] at hζ
        simp only [Complex.sub_re]
        linarith [hmax ζ hζ, (neg_le_abs (h 0).re).trans (abs_re_le_norm (h 0))])
      (by linarith) (by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith [hR'mem.1])
    rw [show R' - R' / 2 = R' / 2 by ring, mul_div_assoc, div_self (half_pos hR'pos).ne',
      mul_one] at hbc
    rw [hC₀def]
    nlinarith [hbc, norm_sub_norm_le (h z) (h 0), norm_nonneg (h 0),
      mul_nonneg (norm_nonneg (h 0)) (sub_nonneg.mpr hRpow1)]
  have claimB : ∀ c : ℂ, iteratedDeriv 2 h c = 0 := by
    intro c
    have htend : Tendsto (fun R : ℝ ↦ 32 * C₀ * R ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (32 * C₀)
    refine norm_le_zero_iff.mp <| ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop (4 * ‖c‖ + 2)] with R hR
    have hR2 : 2 ≤ R := by linarith [norm_nonneg c]
    have hRpos : 0 < R := by linarith
    set ρ : ℝ := R / 2 - ‖c‖ with hρdef
    have hρ4 : R / 4 ≤ ρ := by rw [hρdef]; linarith
    have hρpos : 0 < ρ := by linarith
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρpos
      hdiff.diffContOnCl (fun z hz ↦ claimA R hR2 z (by
        have hzc := norm_sub_norm_le z c
        rw [mem_sphere_iff_norm.mp hz, hρdef] at hzc
        linarith))
    rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]] at hcauchy
    have hpowid : R ^ (3 / 2 : ℝ) / R ^ 2 = R ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_sub hRpos]; norm_num
    calc ‖iteratedDeriv 2 h c‖ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / ρ ^ 2 := hcauchy
      _ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / (R ^ 2 / 16) := by
          gcongr; nlinarith [hρ4, hρpos]
      _ = 32 * C₀ * (R ^ (3 / 2 : ℝ) / R ^ 2) := by ring
      _ = 32 * C₀ * R ^ (-(1 / 2) : ℝ) := by rw [hpowid]
  have hderivconst : ∀ x : ℂ, deriv h x = deriv h 0 := fun x ↦
    is_const_of_deriv_eq_zero hderivdiff
      (fun y ↦ by simpa [iteratedDeriv_succ, iteratedDeriv_one] using claimB y) x 0
  refine ⟨h 0, deriv h 0, fun s ↦ ?_⟩
  have key : h s - deriv h 0 * s = h 0 := by
    simpa using is_const_of_deriv_eq_zero (f := fun y : ℂ ↦ h y - deriv h 0 * y)
      (hdiff.sub (differentiable_id.const_mul _))
      (fun x ↦ by
        have hd : HasDerivAt (fun y : ℂ ↦ h y - deriv h 0 * y) (deriv h x - deriv h 0) x :=
          (hdiff x).hasDerivAt.sub (by simpa using (hasDerivAt_id x).const_mul (deriv h 0))
        rw [hd.deriv, hderivconst x]; ring) s 0
  linear_combination key
end
end CertificatePort25

section CertificatePort26
section
open Complex Filter Topology Set
open scoped ComplexConjugate
theorem logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) 0 = 0 := by
  set ρ := riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i) with hf
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hf0 : ∀ i, f i 0 = 1 := fun i ↦ by simp [hf]
  have hlog0 : ∀ i, logDeriv (f i) 0 = 0 := fun i ↦ by
    have hu : HasDerivAt (fun s : ℂ ↦ s / ρ i) (ρ i)⁻¹ 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℂ)).div_const (ρ i)
    have hde : HasDerivAt (f i) 0 0 := by
      simpa [hf, Function.comp_def] using (hasDerivAt_weierstrassE1 ((0 : ℂ) / ρ i)).comp 0 hu
    rw [logDeriv_apply, hde.deriv, hf0 i, zero_div]
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ (0 : ℂ))
    (fun i ↦ by rw [hf0 i]; norm_num) hd (by simp only [hlog0]; exact summable_zero)
    ((hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ
      summable_inv_norm_sq_riemannXiZeros).multipliableLocallyUniformlyOn)
    (by simp only [hf0, tprod_one]; norm_num)
  simp only [hlog0, tsum_zero] at hkey
  exact hkey
theorem logDeriv_riemannXi_zero_eq_deriv {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = deriv h 0 := by
  have hP0ne : riemannXiCanonicalProduct riemannXiZeros 0 ≠ 0 := by
    rw [riemannXiCanonicalProduct_zero]; norm_num
  rw [funext hrep, logDeriv_mul (f := fun s ↦ Complex.exp (h s))
      (g := riemannXiCanonicalProduct riemannXiZeros) 0 (Complex.exp_ne_zero _) hP0ne
      (hdiff 0).hasDerivAt.cexp.differentiableAt
      (differentiable_riemannXiCanonicalProduct riemannXiZeros
        summable_inv_norm_sq_riemannXiZeros 0),
    show (fun s ↦ Complex.exp (h s)) = Complex.exp ∘ h from rfl,
    logDeriv_comp (Complex.differentiable_exp (h 0)) (hdiff 0), Complex.logDeriv_exp,
    logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero]
  simp
theorem log_riemannXi_div_canonicalProduct_const_eq {h : ℂ → ℂ} {A B : ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s)
    (haffine : ∀ s, h s = A + B * s) :
    Complex.exp A = 1 / 2 ∧ B = logDeriv riemannXi 0 ∧ conj B = B := by
  have hexpA : Complex.exp A = 1 / 2 := by
    have h0 := hrep 0
    rw [riemannXi_zero, riemannXiCanonicalProduct_zero, mul_one, haffine 0, mul_zero,
      add_zero] at h0
    exact h0.symm
  have hBeq : B = logDeriv riemannXi 0 := by
    rw [logDeriv_riemannXi_zero_eq_deriv hdiff hrep, funext haffine]; simp
  have hsym : conj ∘ riemannXi ∘ conj = riemannXi := by
    funext s; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have hreal : conj (deriv riemannXi 0) = deriv riemannXi 0 := by
    simpa using congrFun (by rw [← deriv_conj_conj, hsym] :
      conj ∘ deriv riemannXi ∘ conj = deriv riemannXi) 0
  refine ⟨hexpA, hBeq, ?_⟩
  rw [hBeq, logDeriv_apply, map_div₀, hreal, riemannXi_zero, map_div₀, map_one, map_ofNat]
theorem riemannXi_eq_hadamard_product :
    ∃ B : ℝ, ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s := by
  obtain ⟨h, hdiff, _, hrep⟩ := exists_entire_log_riemannXi_div_canonicalProduct
  obtain ⟨A, B, haffine⟩ := exists_affine_log_riemannXi_div_canonicalProduct hdiff hrep
  obtain ⟨hexpA, _, hBreal⟩ := log_riemannXi_div_canonicalProduct_const_eq hdiff hrep haffine
  refine ⟨B.re, fun s ↦ ?_⟩
  have hBre : (B.re : ℂ) = B := Complex.conj_eq_iff_re.mp hBreal
  rw [hrep s, haffine s, Complex.exp_add, hexpA, hBre]
end
end CertificatePort26


