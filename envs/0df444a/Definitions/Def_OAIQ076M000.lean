-- Prove2me | Definitions.Def_OAIQ076M000
-- name    : OAIQ076M000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:42.8853+00:00
-- url     : https://prove2.me/theorems/0c73ae5f-8335-48da-8eec-48e672352c46
-- title:
--   Definitions bundle OAIQ076M000 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 342 declarations of OpenAI's Lean: 153 definitions, 4 inductive types or structures, 5 instances and 180 theorems. The definitions and types are `OAI.MinUncut.BinaryFourier.F₂`, `OAI.MinUncut.BinaryFourier.character`, `OAI.MinUncut.BinaryFourier.coefficient`, `OAI.MinUncut.BinaryFourier.convolution`, `OAI.MinUncut.BinaryFourier.densityFourierDecidableEq`, `OAI.MinUncut.BinaryFourier.densityProjectedDecidableEq`, `OAI.MinUncut.BinaryFourier.dualFintype`, `OAI.MinUncut.BinaryFourier.f2DecidableEq`, `OAI.MinUncut.BinaryFourier.f2DualDecidableEq`, `OAI.MinUncut.BinaryFourier.largePart`, `OAI.MinUncut.BinaryFourier.largeSpectrum`, `OAI.MinUncut.BinaryFourier.remainder`, `OAI.MinUncut.BinaryFourier.sign`, `OAI.MinUncut.Box.Local`, `OAI.MinUncut.Box.correlation`, `OAI.MinUncut.Box.moment`, `OAI.MinUncut.Box.vertex`, `OAI.MinUncut.BoxGaussian.Outside`, `OAI.MinUncut.BoxGaussian.indexEquiv`, `OAI.MinUncut.BoxGaussian.join`, `OAI.MinUncut.BoxGaussian.joinEquiv`, `OAI.MinUncut.BoxGaussian.singletonEmbed`, `OAI.MinUncut.CodeEffective.Layout.Cell`, `OAI.MinUncut.CodeEffective.Layout.binary`, `OAI.MinUncut.CodeEffective.Layout.cells`, `OAI.MinUncut.CodeEffective.Layout.flattenCell`, `OAI.MinUncut.CodeEffective.Layout.pack`, `OAI.MinUncut.CodeEffective.Layout.shift`, `OAI.MinUncut.CodeEffective.Layout.unary`, `OAI.MinUncut.CodeEffective.NCode`, `OAI.MinUncut.CodeEffective.embed`, `OAI.MinUncut.CodeEffective.fold`, `OAI.MinUncut.CodeEffective.normalize`, `OAI.MinUncut.CodeEffective.retract`, `OAI.MinUncut.Composition.TripleIndex`, `OAI.MinUncut.Composition.adaptiveKernel`, `OAI.MinUncut.Composition.labelList`, `OAI.MinUncut.Composition.listMatch`, `OAI.MinUncut.Composition.restrictedFourth`, `OAI.MinUncut.Composition.rowDistance` and 117 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FaceCorrelation`, `MinUncut_Analysis_FreshCorrelation`, `MinUncut_Analysis_GaussianAssembly`, `MinUncut_Analysis_Gradient`, `MinUncut_Analysis_Hermite`, `MinUncut_Analysis_HermiteComponent`, `MinUncut_Analysis_LowGradient`, `MinUncut_Analysis_MaskHermite`, `MinUncut_Analysis_OddAtom`, `MinUncut_Analysis_SelectedProjectGaussianLocal`, `MinUncut_Encoding_LocalDecoder`, `MinUncut_Estimates_ArraySum`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_CodeComputability`, `MinUncut_Estimates_CodeContinuations`, `MinUncut_Estimates_CollisionIndicator`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_EraseAway`, `MinUncut_Estimates_EuclideanInvariantScore`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FaceUpdateSelf`, `MinUncut_Estimates_FourthTest`, `MinUncut_Estimates_HeapInitializationMath`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_Rest`, `MinUncut_Estimates_SecondFailureIndicator`, `MinUncut_Estimates_SelectedProject`, `MinUncut_Games_AdaptiveKernel`, `MinUncut_Games_AffineLabels`, `MinUncut_Games_MaskRowKernel`, `MinUncut_Games_TripleKernel`, `MinUncut_Graphs_Vertex`, `MinUncut_Machines_MachineRegularTableRuntime`, `MinUncut_Search_CodeFoldComputable`, `MinUncut_Search_CodeLayoutComputable`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M009`, `OAIQ076M010`, `OAIQ076M011`, `OAIQ076M012` and `OAIQ076M013`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ076_MU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MinUncut.BinaryFourier

abbrev F₂ := ZMod 2

def sign (b : F₂) : ℝ := if b = 0 then 1 else -1

@[simp] lemma sign_zero : sign 0 = 1 := by norm_num [sign]
@[simp] lemma sign_one : sign 1 = -1 := by norm_num [sign]
@[simp] lemma sign_sq (b : F₂) : sign b ^ 2 = 1 := by
  unfold sign; split_ifs <;> norm_num
@[simp] lemma sign_abs (b : F₂) : |sign b| = 1 := by
  unfold sign; split_ifs <;> norm_num
lemma sign_add (a b : F₂) : sign (a + b) = sign a * sign b := by
  have h : ∀ a : F₂, a = 0 ∨ a = 1 := by decide
  have h2 : (1 + 1 : F₂) = 0 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;> simp [h2]

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

lemma self_add (w : W) : w + w = 0 := by
  have h : (1 + 1 : F₂) = 0 := by decide
  have hh := congrArg (fun t : F₂ => t • w) h
  simpa only [add_smul, one_smul, zero_smul] using hh

lemma neg_eq (w : W) : -w = w := neg_eq_iff_add_eq_zero.mpr (self_add w)

lemma add_eq_zero_iff (v w : W) : v + w = 0 ↔ v = w := by
  rw [add_eq_zero_iff_eq_neg, neg_eq]

def character (α : Module.Dual F₂ W) (w : W) : ℝ := sign (α w)

@[simp] lemma character_zero (w : W) : character (0 : Module.Dual F₂ W) w = 1 := by
  simp [character]
@[simp] lemma character_at_zero (α : Module.Dual F₂ W) : character α 0 = 1 := by
  simp [character]
@[simp] lemma character_sq (α : Module.Dual F₂ W) (w : W) : character α w ^ 2 = 1 := by
  simp [character]
@[simp] lemma character_abs (α : Module.Dual F₂ W) (w : W) : |character α w| = 1 := by
  simp [character]
lemma character_add (α : Module.Dual F₂ W) (v w : W) :
    character α (v + w) = character α v * character α w := by
  simp [character, sign_add]
lemma character_add_dual (α β : Module.Dual F₂ W) (w : W) :
    character (α + β) w = character α w * character β w := by
  simp [character, sign_add]

variable [Fintype W]

omit [Module F₂ W] in
lemma expect_translate (f : W → ℝ) (v : W) : (𝔼 w, f (v + w)) = 𝔼 w, f w := by
  exact Fintype.expect_equiv (Equiv.addLeft v) _ _ (fun _ => rfl)

lemma character_mean (α : Module.Dual F₂ W) :
    (𝔼 w, character α w) = if α = 0 then 1 else 0 := by
  classical
  by_cases hα : α = 0
  · simp [hα]
  rw [ite_eq_right hα]
  have hex : ∃ v, α v ≠ 0 := by
    by_contra! hh
    exact hα (LinearMap.ext hh)
  obtain ⟨v, hv⟩ := hex
  have hs : character α v = -1 := by simp [character, sign, hv]
  have h := expect_translate (character α) v
  simp_rw [character_add, hs, ← Finset.mul_expect] at h
  linarith

lemma character_orthogonality (α β : Module.Dual F₂ W) :
    (𝔼 w, character α w * character β w) = if α = β then 1 else 0 := by
  simp_rw [← character_add_dual]
  simpa only [add_eq_zero_iff] using character_mean (α + β)

local instance f2DecidableEq : DecidableEq W := Classical.decEq W

local instance dualFintype : Fintype (Module.Dual F₂ W) :=
  Fintype.ofInjective (fun α : Module.Dual F₂ W => (α : W → F₂)) DFunLike.coe_injective

local instance f2DualDecidableEq : DecidableEq W := Classical.decEq W

lemma card_dual : Fintype.card (Module.Dual F₂ W) = Fintype.card W := by
  calc
    Fintype.card (Module.Dual F₂ W) =
        Fintype.card F₂ ^ Module.finrank F₂ (Module.Dual F₂ W) :=
      Module.card_eq_pow_finrank (K := F₂)
    _ = Fintype.card F₂ ^ Module.finrank F₂ W := by rw [Subspace.dual_finrank_eq]
    _ = Fintype.card W := (Module.card_eq_pow_finrank (K := F₂)).symm

lemma character_kernel (v w : W) :
    (∑ α : Module.Dual F₂ W, character α v * character α w) =
      if v = w then (Fintype.card W : ℝ) else 0 := by
  classical
  have he : (𝔼 α : Module.Dual F₂ W, character α (v+w)) =
      if v = w then 1 else 0 := by
    have h := character_mean ((Module.Dual.eval F₂ W) (v+w))
    have hz : (Module.Dual.eval F₂ W) (v+w) = 0 ↔ v = w := by
      rw [Module.eval_apply_eq_zero_iff, add_eq_zero_iff]
    simpa only [character, Module.Dual.eval_apply, hz] using h
  simp_rw [character_add] at he
  rw [Fintype.expect_eq_sum_div_card, card_dual] at he
  have hc : (Fintype.card W : ℝ) ≠ 0 := by positivity
  by_cases h : v = w
  · rw [ite_eq_left h] at he ⊢
    simpa using (div_eq_iff hc).mp he
  · rw [ite_eq_right h] at he ⊢
    simpa using (div_eq_iff hc).mp he

def coefficient (f : W → ℝ) (α : Module.Dual F₂ W) : ℝ :=
  𝔼 w, f w * character α w

lemma inversion (f : W → ℝ) (w : W) :
    (∑ α : Module.Dual F₂ W, coefficient f α * character α w) = f w := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have inner (v : W) :
      (∑ α : Module.Dual F₂ W, (f v * character α v) * character α w) =
      f v * (if v = w then (Fintype.card W : ℝ) else 0) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, character_kernel]
  simp_rw [inner]
  rw [Fintype.expect_eq_sum_div_card]
  simp

lemma parseval_inner (f g : W → ℝ) :
    (∑ α : Module.Dual F₂ W, coefficient f α * coefficient g α) =
      𝔼 w, f w * g w := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro w _
  have hi : (∑ α : Module.Dual F₂ W,
      (𝔼 v, f v * character α v) * (g w * character α w)) =
      g w * (∑ α : Module.Dual F₂ W, coefficient f α * character α w) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hi, inversion]
  ring

lemma parseval (f : W → ℝ) :
    (∑ α : Module.Dual F₂ W, coefficient f α ^ 2) = 𝔼 w, f w ^ 2 := by
  simpa only [sq] using parseval_inner f f

omit [Fintype W] in
@[simp] lemma add_add_cancel (v w : W) : v + (v + w) = w := by
  rw [← add_assoc, self_add, zero_add]

lemma coefficient_translate (f : W → ℝ) (α : Module.Dual F₂ W) (t : W) :
    coefficient (fun w => f (t+w)) α = character α t * coefficient f α := by
  unfold coefficient
  have ht := expect_translate (fun w => f w * character α (t+w)) t
  simp only [add_add_cancel] at ht
  rw [ht, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro w _
  rw [character_add]
  ring

def convolution (f g : W → ℝ) (t : W) : ℝ := 𝔼 w, f w * g (w+t)

lemma coefficient_convolution (f g : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (convolution f g) α = coefficient f α * coefficient g α := by
  unfold coefficient convolution
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  calc
    (𝔼 y, 𝔼 x, (f y * g (y+x)) * character α x) =
        𝔼 y, f y * coefficient (fun x => g (y+x)) α := by
      apply Finset.expect_congr rfl
      intro y _
      rw [coefficient, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 y, f y * (character α y * coefficient g α) := by
      simp_rw [coefficient_translate]
    _ = (𝔼 w, f w * character α w) * (𝔼 w, g w * character α w) := by
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro y _
      dsimp [coefficient]
      ring
    _ = 𝔼 w, f w * character α w * (𝔼 y, g y * character α y) := by
      rw [Finset.expect_mul]

lemma convolution_shifts (f g : W → ℝ) (r t : W) :
    (𝔼 s, f (r+s) * g (t+s)) = convolution f g (r+t) := by
  unfold convolution
  have hh : ∀ s : W, (r+s)+(r+t) = t+s := by
    intro s
    calc
      (r+s)+(r+t) = (r+r)+(t+s) := by abel
      _ = t+s := by rw [self_add, zero_add]
  have h := expect_translate (fun s => f s * g (s+(r+t))) r
  simpa only [hh] using h

lemma square_fourier (f₀₀ f₀₁ f₁₀ f₁₁ : W → ℝ) :
    (𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
      f₀₀ (r₀+s₀) * f₀₁ (r₀+s₁) * f₁₀ (r₁+s₀) * f₁₁ (r₁+s₁)) =
    ∑ α : Module.Dual F₂ W,
      coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α := by
  calc
    _ = 𝔼 r₀, 𝔼 r₁,
        (𝔼 s₀, f₀₀ (r₀+s₀) * f₁₀ (r₁+s₀)) *
        (𝔼 s₁, f₀₁ (r₀+s₁) * f₁₁ (r₁+s₁)) := by
      apply Finset.expect_congr rfl
      intro r₀ _
      apply Finset.expect_congr rfl
      intro r₁ _
      rw [Fintype.expect_mul_expect]
      apply Finset.expect_congr rfl
      intro s₀ _
      apply Finset.expect_congr rfl
      intro s₁ _
      ring
    _ = 𝔼 r₀, 𝔼 r₁, convolution f₀₀ f₁₀ (r₀+r₁) * convolution f₀₁ f₁₁ (r₀+r₁) := by
      simp_rw [convolution_shifts]
    _ = 𝔼 t, convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t := by
      trans 𝔼 r₀ : W, (𝔼 t, convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t)
      · apply Finset.expect_congr rfl
        intro r₀ _
        exact expect_translate (fun t => convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t) r₀
      · simp
    _ = ∑ α : Module.Dual F₂ W,
        coefficient (convolution f₀₀ f₁₀) α * coefficient (convolution f₀₁ f₁₁) α :=
      (parseval_inner _ _).symm
    _ = _ := by
      simp_rw [coefficient_convolution]
      apply Finset.sum_congr rfl
      intro α _
      ring

lemma square_bound (f₀₀ f₀₁ f₁₀ f₁₁ : W → ℝ) (ε H : ℝ)
    (hε : 0 ≤ ε)
    (h₀₀ : ∀ α, |coefficient f₀₀ α| ≤ ε)
    (h₀₁ : ∀ α, |coefficient f₀₁ α| ≤ ε)
    (h₁₀ : (𝔼 w, f₁₀ w ^ 2) ≤ H ^ 2)
    (h₁₁ : (𝔼 w, f₁₁ w ^ 2) ≤ H ^ 2) :
    |𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
      f₀₀ (r₀+s₀) * f₀₁ (r₀+s₁) * f₁₀ (r₁+s₀) * f₁₁ (r₁+s₁)| ≤ ε^2 * H^2 := by
  rw [square_fourier]
  have he₁₀ : (∑ α : Module.Dual F₂ W, |coefficient f₁₀ α| ^ 2) ≤ H^2 := by
    simpa only [sq_abs, parseval] using h₁₀
  have he₁₁ : (∑ α : Module.Dual F₂ W, |coefficient f₁₁ α| ^ 2) ≤ H^2 := by
    simpa only [sq_abs, parseval] using h₁₁
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun α : Module.Dual F₂ W => |coefficient f₁₀ α|)
    (fun α : Module.Dual F₂ W => |coefficient f₁₁ α|)
  have hprod : (∑ α : Module.Dual F₂ W, |coefficient f₁₀ α|^2) *
      (∑ α : Module.Dual F₂ W, |coefficient f₁₁ α|^2) ≤ H^2 * H^2 :=
    mul_le_mul he₁₀ he₁₁ (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hsum : (∑ α : Module.Dual F₂ W,
      |coefficient f₁₀ α| * |coefficient f₁₁ α|) ≤ H^2 := by
    nlinarith [sq_nonneg ((∑ α : Module.Dual F₂ W,
      |coefficient f₁₀ α| * |coefficient f₁₁ α|) - H^2)]
  calc
    _ ≤ ∑ α : Module.Dual F₂ W,
        |coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : Module.Dual F₂ W,
        ε^2 * (|coefficient f₁₀ α| * |coefficient f₁₁ α|) := by
      apply Finset.sum_le_sum
      intro α _
      rw [show coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α =
          (coefficient f₀₀ α * coefficient f₀₁ α) * (coefficient f₁₀ α * coefficient f₁₁ α) by ring,
        abs_mul, abs_mul, abs_mul, sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (h₀₀ α) (h₀₁ α) (abs_nonneg _) hε)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ε^2 * ∑ α : Module.Dual F₂ W, |coefficient f₁₀ α| * |coefficient f₁₁ α| := by
      rw [Finset.mul_sum]
    _ ≤ ε^2 * H^2 := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

end MinUncut.BinaryFourier

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory
abbrev F₂ := ZMod 2

variable {m n : ℕ}

abbrev Point (m n : ℕ) := Fin m → Fin n
abbrev Row (m n : ℕ) := Σ i : Fin m, ({j : Fin m // j ≠ i} → Fin n)

def face (x : Point m n) (i : Fin m) : {j : Fin m // j ≠ i} → Fin n := fun j => x j.1

def faceSum (m n : ℕ) : (Row m n → F₂) →ₗ[F₂] (Point m n → F₂) where
  toFun z x := ∑ i : Fin m, z ⟨i, face x i⟩
  map_add' z w := by funext x; simp [Finset.sum_add_distrib]
  map_smul' t z := by funext x; simp [Finset.mul_sum]

abbrev Code (m n : ℕ) := LinearMap.range (faceSum m n)

noncomputable instance codeFintype : Fintype (Code m n) := Fintype.ofFinite _
instance codeDecidableEq : DecidableEq (Code m n) := Classical.decEq _

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

abbrev Forms (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] :=
  A →ᵃ[F₂] F₂

noncomputable instance formsFintype [Fintype A] : Fintype (Forms A) := by
  classical
  exact Fintype.ofInjective (fun f : Forms A => (f : A → F₂)) AffineMap.coeFn_injective

abbrev FaceArray (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    (m n : ℕ) := Row m n → Forms A

def labelCode (B : FaceArray A m n) (a : A) : Code m n :=
  ⟨faceSum m n (fun r => B r a), ⟨(fun r => B r a), rfl⟩⟩

@[simp] lemma labelCode_apply (B : FaceArray A m n) (a : A) (x : Point m n) :
    (labelCode B a : Point m n → F₂) x = ∑ i : Fin m, B ⟨i, face x i⟩ a := rfl

structure FoldedProof (A : Type*) where
  answer : (A → Bool) → Bool
  folded : ∀ P, answer (fun a => !(P a)) = !(answer P)

def bitSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] lemma bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by cases b <;> norm_num [bitSign]
@[simp] lemma bitSign_abs (b : Bool) : |bitSign b| = 1 := by cases b <;> norm_num [bitSign]
@[simp] lemma bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by cases b <;> norm_num [bitSign]

noncomputable def query (u : Point m n → ℝ) (d : Code m n → ℝ) : Code m n → Bool :=
  fun z => decide (0 ≤ (Real.sqrt (n^m : ℕ))⁻¹ *
    (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + d z)

noncomputable def pullQuery (B : FaceArray A m n) (u : Point m n → ℝ)
    (d : Code m n → ℝ) : A → Bool := fun a => query u d (labelCode B a)

noncomputable def gauss (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

noncomputable def smooth (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    bitSign (f.answer (pullQuery B (c + σ • g) (η • l)))
      ∂gauss (Code m n) ∂gauss (Point m n)

noncomputable def gradient (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  Real.sqrt (n^m : ℕ) *
    deriv (fun t => smooth f B σ η (Function.update c x t)) (c x)

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.OuterSmoothness

lemma expect_pair {B C : Type*} [Fintype B] [Fintype C] (f : B × C → ℝ) :
    (𝔼 p, f p) = 𝔼 b, 𝔼 c, f (b,c) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

abbrev FixedSets (ι : Type*) [Fintype ι] (k : ℕ) := {H : Finset ι // H.card = k}

end MinUncut.OuterSmoothness

namespace MinUncut.BinaryFourier
variable {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
local instance densityFourierDecidableEq : DecidableEq W := Classical.decEq W
attribute [local instance] dualFintype

lemma coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → W → ℝ)
    (α : Module.Dual F₂ W) : coefficient (fun w => ∑ i ∈ s, f i w) α =
      ∑ i ∈ s, coefficient (f i) α := by
  simp only [coefficient, Finset.sum_mul]
  rw [Finset.expect_sum_comm]

lemma coefficient_character (α β : Module.Dual F₂ W) :
    coefficient (character α) β = if α = β then 1 else 0 := by
  by_cases h : α = β <;> simpa [coefficient, h] using character_orthogonality α β

lemma coefficient_scale (a : ℝ) (f : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (fun w => a * f w) α = a * coefficient f α := by
  simp only [coefficient, mul_assoc, Finset.mul_expect]

lemma coefficient_sub (f g : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (fun w => f w - g w) α = coefficient f α - coefficient g α := by
  simp only [coefficient, sub_mul, Finset.expect_sub_distrib]

lemma fourth_moment (f : W → ℝ) :
    (𝔼 a, 𝔼 b, 𝔼 c, f a * f b * f c * f (a+b+c)) =
      ∑ α : Module.Dual F₂ W, coefficient f α ^ 4 := by
  have hexp (a b c : W) : f a * f b * f c * f (a+b+c) =
      ∑ α : Module.Dual F₂ W, coefficient f α *
        ((f a * character α a) * (f b * character α b) * (f c * character α c)) := by
    rw [← inversion f (a+b+c), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [character_add, character_add]
    ring
  simp only [hexp, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [← Finset.mul_expect, ← Finset.expect_mul]
  rw [← Fintype.expect_mul_expect]
  change coefficient f α * (coefficient f α * coefficient f α * coefficient f α) = _
  ring

def largeSpectrum (f : W → ℝ) (u : ℝ) : Finset (Module.Dual F₂ W) :=
  Finset.univ.filter (fun α => u ≤ |coefficient f α|)

def largePart (f : W → ℝ) (u : ℝ) (w : W) : ℝ :=
  ∑ α ∈ largeSpectrum f u, coefficient f α * character α w

def remainder (f : W → ℝ) (u : ℝ) (w : W) : ℝ := f w - largePart f u w

lemma coefficient_largePart (f : W → ℝ) (u : ℝ) (β : Module.Dual F₂ W) :
    coefficient (largePart f u) β = if u ≤ |coefficient f β| then coefficient f β else 0 := by
  classical
  unfold largePart
  rw [coefficient_sum]
  simp_rw [coefficient_scale, coefficient_character]
  simp [largeSpectrum]

lemma coefficient_remainder (f : W → ℝ) (u : ℝ) (β : Module.Dual F₂ W) :
    coefficient (remainder f u) β = if |coefficient f β| < u then coefficient f β else 0 := by
  unfold remainder
  rw [coefficient_sub, coefficient_largePart]
  split_ifs <;> simp_all
  linarith

omit [Module F₂ W] in
lemma energy_le_of_bounded (f : W → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ w, |f w| ≤ M) : (𝔼 w, f w ^ 2) ≤ M^2 := by
  calc _ ≤ 𝔼 _w : W, M^2 := Finset.expect_le_expect (fun w _ => by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hf w))
       _ = _ := Fintype.expect_const _

lemma largeSpectrum_card (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) : (largeSpectrum f u).card ≤ M^2 / u^2 := by
  have he := energy_le_of_bounded f hM hf
  have hs : (largeSpectrum f u).card * u^2 ≤ ∑ α : Module.Dual F₂ W, coefficient f α ^ 2 := by
    calc _ = ∑ _α ∈ largeSpectrum f u, u^2 := by simp
         _ ≤ ∑ α ∈ largeSpectrum f u, coefficient f α ^ 2 := by
           apply Finset.sum_le_sum
           intro α hα
           have h := (Finset.mem_filter.mp hα).2
           nlinarith [sq_abs (coefficient f α)]
         _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  rw [parseval] at hs
  exact (le_div_iff₀ (sq_pos_of_pos hu)).mpr (hs.trans he)

lemma remainder_fourth_bound (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) :
    (∑ α : Module.Dual F₂ W, coefficient (remainder f u) α ^ 4) ≤ u^2 * M^2 := by
  have he := energy_le_of_bounded f hM hf
  calc _ ≤ ∑ α : Module.Dual F₂ W, u^2 * coefficient f α ^ 2 := by
         apply Finset.sum_le_sum
         intro α _
         rw [coefficient_remainder]
         split_ifs with hα
         · have hs : coefficient f α ^2 ≤ u^2 := by
             simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hu.le).mpr hα.le
           nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (coefficient f α))]
         · simp only [zero_pow (by omega : 4 ≠ 0)]
           exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
       _ = u^2 * (𝔼 w, f w^2) := by rw [← Finset.mul_sum, parseval]
       _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg u)

lemma remainder_abs_bound (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) (w : W) : |remainder f u w| ≤ M + M^2 / u := by
  have he := energy_le_of_bounded f hM hf
  have hs : (∑ α ∈ largeSpectrum f u, |coefficient f α|) ≤ M^2/u := by
    calc _ ≤ ∑ α ∈ largeSpectrum f u, coefficient f α ^2/u := by
           apply Finset.sum_le_sum
           intro α hα
           have h := (Finset.mem_filter.mp hα).2
           apply (le_div_iff₀ hu).mpr
           nlinarith [mul_nonneg (abs_nonneg (coefficient f α)) (sub_nonneg.mpr h),
             sq_abs (coefficient f α)]
         _ = (∑ α ∈ largeSpectrum f u, coefficient f α ^2)/u := by rw [Finset.sum_div]
         _ ≤ M^2/u := by
           apply div_le_div_of_nonneg_right _ hu.le
           exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)).trans
             ((parseval f).le.trans he)
  calc |remainder f u w| ≤ |f w| + |largePart f u w| := by
         simpa only [remainder, sub_zero, zero_sub, abs_neg] using abs_sub_le (f w) 0 (largePart f u w)
       _ ≤ M + ∑ α ∈ largeSpectrum f u, |coefficient f α| := by
         apply add_le_add (hf w)
         unfold largePart
         exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
       _ ≤ _ := add_le_add_right hs M

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]
local instance densityProjectedDecidableEq : DecidableEq V := Classical.decEq V

omit [Fintype V] in
lemma coefficient_projected_sum (S : Finset (Module.Dual F₂ V))
    (a : Module.Dual F₂ V → ℝ) (π : W →ₗ[F₂] V) (β : Module.Dual F₂ W) :
    coefficient (fun w => ∑ α ∈ S, a α * character α (π w)) β =
      ∑ α ∈ S, if α.comp π = β then a α else 0 := by
  classical
  rw [coefficient_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [coefficient_scale]
  change a α * coefficient (character (α.comp π)) β = _
  rw [coefficient_character]
  split_ifs <;> simp

lemma coefficient_largePart_pullback (f : V → ℝ) (u : ℝ) (π : W →ₗ[F₂] V)
    (β : Module.Dual F₂ W) :
    coefficient (fun w => largePart f u (π w)) β =
      ∑ α ∈ largeSpectrum f u, if α.comp π = β then coefficient f α else 0 :=
  coefficient_projected_sum _ _ _ _

lemma large_preimage_of_nonzero (f : V → ℝ) (u : ℝ) (π : W →ₗ[F₂] V)
    (β : Module.Dual F₂ W) (hb : coefficient (fun w => largePart f u (π w)) β ≠ 0) :
    ∃ α : Module.Dual F₂ V, u ≤ |coefficient f α| ∧ α.comp π = β := by
  classical
  by_contra hn
  push Not at hn
  apply hb
  rw [coefficient_largePart_pullback]
  apply Finset.sum_eq_zero
  intro α hα
  exact ite_eq_right (hn α (Finset.mem_filter.mp hα).2)

lemma extract_matched_odd (f : V → ℝ) (g : W → ℝ) (π : W →ₗ[F₂] V)
    (oneV : V) (oneW : W) (hπ : π oneW = oneV)
    (β : Module.Dual F₂ W) {u θ : ℝ} (hθ : 0 < θ)
    (hodd : β oneW = 1) (hβ : θ ≤ |coefficient g β|)
    (hclose : |coefficient g β - coefficient (fun w => f (π w)) β| < θ/4)
    (hrem : |coefficient (fun w => remainder f u (π w)) β| < θ/4) :
    ∃ α : Module.Dual F₂ V, u ≤ |coefficient f α| ∧ α.comp π = β ∧ α oneV = 1 := by
  have hnonzero : coefficient (fun w => largePart f u (π w)) β ≠ 0 := by
    intro hz
    have hr : coefficient (fun w => remainder f u (π w)) β =
        coefficient (fun w => f (π w)) β := by
      unfold remainder
      rw [coefficient_sub, hz, sub_zero]
    rw [hr] at hrem
    have ht := abs_add_le (coefficient g β - coefficient (fun w => f (π w)) β)
      (coefficient (fun w => f (π w)) β)
    rw [sub_add_cancel] at ht
    linarith
  obtain ⟨α, ha, hab⟩ := large_preimage_of_nonzero f u π β hnonzero
  refine ⟨α, ha, hab, ?_⟩
  have he := congrArg (fun γ : Module.Dual F₂ W => γ oneW) hab
  simpa only [LinearMap.comp_apply, hπ, hodd] using he

end MinUncut.BinaryFourier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EuclideanInvariantScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

def thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) : ℝ :=
  if f.answer (fun a => Function.update (query u (η • l)) z true (labelCode B a)) =
      f.answer (fun a => Function.update (query u (η • l)) z false (labelCode B a)) then 0 else 1

def thirdRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  𝔼 z : Code m n, ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n)

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FaceCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators

variable {m n : ℕ}

def faceCorrelation (v : Point m n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun z : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)|)

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
abbrev γ : Measure ℝ := gaussianReal 0 1

def he (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n)

def hePoly (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

@[simp] lemma hePoly_eval (n : ℕ) (x : ℝ) : (hePoly n).eval x = he n x := by
  simp [hePoly, he, aeval_def, eval_map]

@[simp] lemma hePoly_zero : hePoly 0 = 1 := by simp [hePoly]

lemma hePoly_succ (n : ℕ) : hePoly (n+1) = X * hePoly n - (hePoly n).derivative := by
  simp [hePoly, derivative_map]

@[simp] lemma he_zero (x : ℝ) : he 0 x = 1 := by simp [he]

def H (n : ℕ) (x : ℝ) : ℝ := he n x / Real.sqrt (n.factorial : ℝ)

section Product
variable {ι : Type*} [Fintype ι]
abbrev γpi (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi (fun _ => γ)

def psi (a : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, H (a i) (x i)

end Product

@[simp] lemma he_one (x : ℝ) : he 1 x = x := by
  rw [← hePoly_eval, show hePoly 1 = X by simp [hePoly_succ]]
  simp

variable {ι : Type*} [Fintype ι]

def score (ρ s : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∫ g, g i * Q (ρ • x+s • g) ∂γpi ι

lemma coordinate_integrable (i : ι) : Integrable (fun g : ι → ℝ => g i) (γpi ι) :=
  integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))

def coeff (f : (ι → ℝ) → ℝ) (a : ι → ℕ) : ℝ := ∫ x, psi a x * f x ∂γpi ι

def degree (a : ι → ℕ) : ℕ := ∑ i, a i

end MinUncut.GaussianHermite
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_Gradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι]

@[simp] lemma psi_zero (x : ι → ℝ) : psi 0 x = 1 := by
  simp [psi, H]

@[simp] lemma coeff_zero (f : (ι → ℝ) → ℝ) : coeff f 0 = ∫ x, f x ∂γpi ι := by
  simp [coeff]

def low [DecidableEq ι] (d : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.range (d+1))).filter (fun a => degree a ≤ d)

@[simp] lemma mem_low [DecidableEq ι] (d : ℕ) (a : ι → ℕ) :
    a ∈ low d ↔ degree a ≤ d := by
  simp only [low, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : a i ≤ degree a := Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
      (Finset.mem_univ i)
    omega

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

namespace MinUncut.RowNoise
open BinaryFourier
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def rowDensity (a : ℝ) (b c : W) : ℝ :=
  (1-a)*(if c=b then (Fintype.card W : ℝ) else 0) + a

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_MaskRowKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def maskRowKernel (active : Bool) (b c : W) : ℝ :=
  if active then rowDensity 0 b c-1 else 1

def maskKernel (S : Finset R) (B C : R → W) : ℝ :=
  ∏ r, maskRowKernel (decide (r ∈ S)) (B r) (C r)

def maskProject (S : Finset R) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  𝔼 C, maskKernel S B C * f C

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

abbrev Rest (r : R) := {t : R // t ≠ r} → W

def joinRow (r : R) (b : W) (D : Rest (W := W) r) : R → W :=
  (Equiv.funSplitAt r W).symm (b,D)

omit [Fintype R] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
@[simp] lemma joinRow_at (r : R) (b : W) (D : Rest (W := W) r) : joinRow r b D r = b := by
  simp [joinRow, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype R] [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
@[simp] lemma joinRow_other (r : R) (b : W) (D : Rest (W := W) r) (t : {t : R // t≠r}) :
    joinRow r b D t = D t := by
  simp [joinRow, Equiv.funSplitAt, Equiv.piSplitAt, t.property]

def rowCoefficient (r : R) (f : (R → W) → ℝ) (α : Module.Dual F₂ W)
    (D : Rest (W := W) r) : ℝ :=
  𝔼 b, f (joinRow r b D) * character α b

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_OddAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
local instance oddAtomDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def oddAtom (r : R) (one : W) (f : (R → W) → ℝ) (D : Rest (W := W) r) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun α : Module.Dual F₂ W =>
    if α one=1 then |rowCoefficient r f α D| else 0)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_HermiteComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [DecidableEq R] [Fintype W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def hermiteComponent (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) : ℝ := psi I c * GaussianHermite.coeff (u B) I

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_MaskHermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def maskHermite (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) : ℝ := maskProject S (fun D => hermiteComponent I u D c) B

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SelectedProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def selectedProject (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) (c : ι → ℝ) : ℝ :=
  ∑ j ∈ J, maskHermite j.1 j.2 u B c

end MinUncut.RowNoise
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SecondFailureIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

def rectangle (D s : ℕ) : Finset (Finset R × (ι → ℕ)) :=
  (Finset.univ.filter (fun S : Finset R => S.card≤D)).product (GaussianHermite.low s)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LowGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def lowGradient (D s : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  selectedProject (rectangle D s) (fun B c => gradient f B σ η c x) B c

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ArraySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def doubleMatch (i j : Fin m) (q x : Point m n) : Prop :=
  ∀ t : Fin m, t ≠ i → t ≠ j → x t = q t

def rowFill (q : Point m n) (r : Row m n) : Point m n :=
  fun t => if ht : t = r.1 then q t else r.2 ⟨t,ht⟩

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_Hermite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def hermiteSupport (I : Point m n → ℕ) : Finset (Point m n) := Finset.univ.filter (fun u => 0 < I u)

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Away
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open scoped BigOperators
open OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

abbrev Away (x : A) := {a : A // a ≠ x}

def pointedSet (x : A) {k : ℕ} (H : FixedSets (Away x) k) : Finset A :=
  insert x (H.val.map ⟨Subtype.val, Subtype.val_injective⟩)

lemma mem_pointedSet_self (x : A) {k : ℕ} (H : FixedSets (Away x) k) : x ∈ pointedSet x H := by
  simp [pointedSet]

lemma mem_pointedSet {x a : A} (h : a ≠ x) {k : ℕ} (H : FixedSets (Away x) k) :
    a ∈ pointedSet x H ↔ (⟨a,h⟩ : Away x) ∈ H.val := by
  simp only [pointedSet, Finset.mem_insert, h, false_or, Finset.mem_map]
  constructor
  · rintro ⟨b,hb,he⟩
    have : b=⟨a,h⟩ := Subtype.ext he
    simpa [this] using hb
  · intro ha
    exact ⟨⟨a,h⟩,ha,rfl⟩

lemma pointedSet_card (x : A) {k : ℕ} (H : FixedSets (Away x) k) :
    (pointedSet x H).card = k+1 := by
  have hx : x ∉ H.val.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro a _ h
    exact a.property h
  simp [pointedSet, hx, H.property]

abbrev PointedBox (x : ι → A) (k : ℕ) := ∀ i, FixedSets (Away (x i)) k

def InBox {x : ι → A} {k : ℕ} (H : PointedBox x k) (u : ι → A) : Prop :=
  ∀ i, u i ∈ pointedSet (x i) (H i)

def FaceInBox {x : ι → A} {k : ℕ} (H : PointedBox x k) (i : ι)
    (u : {j : ι // j ≠ i} → A) : Prop := ∀ j : {j : ι // j ≠ i}, u j ∈ pointedSet (x j.val) (H j.val)

abbrev Row (ι A : Type*) := Σ i : ι, ({j : ι // j ≠ i} → A)

def Removed {x : ι → A} {k : ℕ} (H : PointedBox x k)
    (P : Finset (ι → A)) (S : Finset (Row ι A)) : Prop :=
  (∃ u ∈ P, u ≠ x ∧ InBox H u) ∨
    (∃ r ∈ S, r.2 ≠ (fun j => x j.val) ∧ FaceInBox H r.1 r.2)

end MinUncut.Subbox
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

def zeroFree (F : Finset R) (B : R → W) : R → W := fun t => if t ∈ F then 0 else B t

def localSlice (J : Finset (Finset R × (ι → ℕ))) (u : (R → W) → (ι → ℝ) → ℝ)
    (F : Finset R) (r : R) (C : R → W) (c : ι → ℝ) (b : W) : ℝ :=
  selectedProject J u (zeroFree F C+Pi.single r b) c

end MinUncut.RowNoise
namespace MinUncut.Inner
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

abbrev PairClass (m : ℕ) := {p : Fin m × Fin m // p.1<p.2}

instance pairClassOrder : LinearOrder (PairClass m) :=
  LinearOrder.lift' (fun p : PairClass m => finProdFinEquiv p.val)
    (fun _ _ h => Subtype.ext (finProdFinEquiv.injective h))

def PairAdmissible (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n))
    (p : PairClass m) : Prop :=
  (∀ u, 0 < I u → face u p.val.1 ≠ face x p.val.1 ∧ face u p.val.2 ≠ face x p.val.2) ∧
  (∀ y, (⟨p.val.1,y⟩ : Row m n) ∈ S → doubleMatch p.val.1 p.val.2 x (rowFill x ⟨p.val.1,y⟩) → y=face x p.val.1) ∧
  (∀ y, (⟨p.val.2,y⟩ : Row m n) ∈ S → doubleMatch p.val.2 p.val.1 x (rowFill x ⟨p.val.2,y⟩) → y=face x p.val.2)

def admissibleClasses (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) :
    Finset (PairClass m) := Finset.univ.filter (PairAdmissible x I S)

def maskClass (x : Point m n) (I : Point m n → ℕ) (S : Finset (Row m n)) : Option (PairClass m) :=
  if 0 < I x then none else
    if h : (admissibleClasses x I S).Nonempty then some ((admissibleClasses x I S).min' h) else none

def classSelection (x : Point m n) (a : Option (PairClass m))
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :=
  J.filter (fun j => maskClass x j.2 j.1=a)

end MinUncut.Inner
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def freePairRows (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m) :
    Finset (Row m n) := Finset.univ.filter (fun r =>
      (r.1=p.val.1 ∨ r.1=p.val.2) ∧ Subbox.FaceInBox H r.1 r.2)

def retainedClass (x : Point m n) {k : ℕ} (H : Subbox.PointedBox x k)
    (a : Option (PairClass m)) (J : Finset (Finset (Row m n) × (Point m n → ℕ))) :=
  (classSelection x a J).filter (fun j => ¬Subbox.Removed H (hermiteSupport j.2) j.1)

def pairSlice (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (C : FaceArray A m n) (c : Point m n → ℝ) (b : Forms A) : ℝ :=
  localSlice (retainedClass x H (some p) J) (fun B c => gradient f B σ η c x)
    (freePairRows x H p) ⟨p.val.1,face x p.val.1⟩ C c b

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_Vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Box
variable {A : Type*} [Fintype A] [Nonempty A]

def vertex {m : ℕ} (b : Fin m → Bool) (x y : Fin m → A) : Fin m → A :=
  fun i => if b i then x i else y i

def moment {m : ℕ} (f : (Fin m → A) → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, ∏ b : Fin m → Bool, f (vertex b x y)

def correlation {m : ℕ} (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) : ℝ :=
  𝔼 x, f x * ∏ i, a i x

def Local {m : ℕ} (a : Fin m → (Fin m → A) → ℝ) : Prop :=
  ∀ i x z, a i (Function.update x i z) = a i x

omit [Nonempty A] in
lemma expect_cons {m : ℕ} (f : (Fin (m+1) → A) → ℝ) :
    (𝔼 x, f x) = 𝔼 z, 𝔼 x, f (Fin.cons z x) := by
  rw [← Finset.expect_product', Finset.univ_product_univ]
  exact Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (m+1) => A)).symm _ _ (fun x => congrArg f (Fin.cons_self_tail x).symm)

lemma prod_cons {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∏ b, f b) = ∏ z : Bool, ∏ b, f (Fin.cons z b) := by
  rw [← Finset.prod_product' ]
  rw [Finset.univ_product_univ]
  exact Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).symm _ _ (fun x => congrArg f (Fin.cons_self_tail x).symm)

omit [Fintype A] [Nonempty A] in
@[simp] lemma vertex_cons {m : ℕ} (b : Bool) (bs : Fin m → Bool)
    (x y : A) (xs ys : Fin m → A) :
    vertex (Fin.cons b bs) (Fin.cons x xs) (Fin.cons y ys) =
      Fin.cons (if b then x else y) (vertex bs xs ys) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [vertex]

omit [Nonempty A] in
lemma moment_succ {m : ℕ} (f : (Fin (m+1) → A) → ℝ) :
    moment f = 𝔼 z, 𝔼 w, moment (fun x => f (Fin.cons z x) * f (Fin.cons w x)) := by
  unfold moment
  rw [expect_cons]
  conv_lhs => arg 2; ext z; arg 2; ext x; rw [expect_cons]
  simp_rw [prod_cons, Fintype.prod_bool, vertex_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.prod_mul_distrib]
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_comm]

lemma expect_pow_two_pow {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) (m : ℕ) :
    (𝔼 t, f t)^(2^m) ≤ 𝔼 t, (f t)^(2^m) := by
  cases m with
  | zero => simp
  | succ m =>
      have he : Even (2^(m+1)) := ⟨2^m, by rw [pow_succ]; omega⟩
      have h := Real.pow_arith_mean_le_arith_mean_pow_of_even Finset.univ
        (fun _ : T => (Fintype.card T : ℝ)⁻¹) f (fun _ _ => by positivity)
        (by simp [Fintype.card_ne_zero]) he
      simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ, ← Finset.mul_sum,
        ← Finset.sum_mul, div_eq_mul_inv, mul_comm] using h

lemma expect_sq_le {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) :
    (𝔼 t, f t)^2 ≤ 𝔼 t, (f t)^2 := by
  simpa using expect_pow_two_pow f 1

omit [Fintype A] [Nonempty A] in
lemma face_zero {m : ℕ} (a : Fin (m+1) → (Fin (m+1) → A) → ℝ)
    (ha : Local a) (z w : A) (x : Fin m → A) :
    a 0 (Fin.cons z x) = a 0 (Fin.cons w x) := by
  simpa only [Fin.update_cons_zero] using ha 0 (Fin.cons w x) z

lemma first_step {m : ℕ} (f : (Fin (m+1) → A) → ℝ)
    (a : Fin (m+1) → (Fin (m+1) → A) → ℝ)
    (ha : Local a) (hb : ∀ i x, |a i x| ≤ 1) :
    (correlation f a)^2 ≤ 𝔼 z, 𝔼 w,
      correlation (fun x => f (Fin.cons z x)*f (Fin.cons w x))
        (fun i x => a i.succ (Fin.cons z x)*a i.succ (Fin.cons w x)) := by
  let z₀ := Classical.choice (inferInstance : Nonempty A)
  let g (x : Fin m → A) : ℝ := 𝔼 z, f (Fin.cons z x) * ∏ i : Fin m, a i.succ (Fin.cons z x)
  have hc : correlation f a = 𝔼 x, a 0 (Fin.cons z₀ x) * g x := by
    unfold correlation
    rw [expect_cons, Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro x _
    simp only [Fin.prod_univ_succ]
    simp_rw [face_zero a ha _ z₀ x]
    dsimp [g]
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro z _
    ring
  rw [hc]
  calc
    _ ≤ 𝔼 x, (a 0 (Fin.cons z₀ x)*g x)^2 := expect_sq_le _
    _ ≤ 𝔼 x, (g x)^2 := by
      apply Finset.expect_le_expect
      intro x _
      rw [mul_pow]
      have hs : (a 0 (Fin.cons z₀ x))^2 ≤ 1 := by
        nlinarith [sq_abs (a 0 (Fin.cons z₀ x)), hb 0 (Fin.cons z₀ x), abs_nonneg (a 0 (Fin.cons z₀ x))]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (g x))
    _ = _ := by
      dsimp [g, correlation]
      simp only [sq, Finset.expect_mul_expect]
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro z _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro w _
      apply Finset.expect_congr rfl
      intro x _
      rw [Finset.prod_mul_distrib]
      ring

theorem box_cs (m : ℕ) (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) (ha : Local a) (hb : ∀ i x, |a i x|≤1) :
    (correlation f a)^(2^m) ≤ moment f := by
  induction m with
  | zero =>
      have hf : ∀ x : Fin 0 → A, f x = f (fun i => Fin.elim0 i) :=
        fun x => congrArg f (Subsingleton.elim _ _)
      simp [correlation, moment, hf]
  | succ m ih =>
      let g := fun z w (x : Fin m → A) => f (Fin.cons z x)*f (Fin.cons w x)
      let b := fun z w (i : Fin m) (x : Fin m → A) =>
        a i.succ (Fin.cons z x)*a i.succ (Fin.cons w x)
      have h₁ := first_step f a ha hb
      have hlocal (z w : A) : Local (b z w) := by
        intro i x t
        dsimp [b]
        simp only [Fin.cons_update, ha i.succ]
      have hbound (z w : A) (i : Fin m) (x : Fin m → A) : |b z w i x|≤1 := by
        dsimp [b]
        rw [abs_mul]
        simpa using mul_le_mul (hb i.succ (Fin.cons z x)) (hb i.succ (Fin.cons w x))
          (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
      calc
        _ = ((correlation f a)^2)^(2^m) := by rw [← pow_mul, pow_succ]; congr 1; omega
        _ ≤ (𝔼 z, 𝔼 w, correlation (g z w) (b z w))^(2^m) :=
          pow_le_pow_left₀ (sq_nonneg _) h₁ _
        _ ≤ 𝔼 z, (𝔼 w, correlation (g z w) (b z w))^(2^m) := expect_pow_two_pow _ m
        _ ≤ 𝔼 z, 𝔼 w, (correlation (g z w) (b z w))^(2^m) :=
          Finset.expect_le_expect (fun z _ => expect_pow_two_pow _ m)
        _ ≤ 𝔼 z, 𝔼 w, moment (g z w) := by
          apply Finset.expect_le_expect
          intro z _
          apply Finset.expect_le_expect
          intro w _
          exact ih _ _ (hlocal z w) (hbound z w)
        _ = _ := (moment_succ f).symm

lemma abs_correlation_cs {m : ℕ} (hm : 0 < m) (f : (Fin m → A) → ℝ)
    (a : Fin m → (Fin m → A) → ℝ) (ha : Local a) (hb : ∀ i x, |a i x|≤1) :
    |correlation f a|^(2^m) ≤ moment f := by
  have he : Even (2^m) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact ⟨2^k, by rw [pow_succ]; omega⟩
  simpa only [he.pow_abs] using box_cs m f a ha hb
end MinUncut.Box

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FaceUpdateSelf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Slice
open BinaryFourier
variable {W : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]

def clip (A z : ℝ) : ℝ := max (-A) (min z A)

lemma clip_abs_le {A : ℝ} (hA : 0 ≤ A) (z : ℝ) : |clip A z| ≤ A := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

lemma clip_loss {A : ℝ} (hA : 0 < A) (z : ℝ) : |z-clip A z| ≤ z^2/A := by
  rw [le_div_iff₀ hA]
  unfold clip
  rcases le_total z A with hz | hz
  · rw [min_eq_left hz]
    rcases le_total (-A) z with ha | ha
    · rw [max_eq_right ha]; simpa using sq_nonneg z
    · rw [max_eq_left ha, abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (z+A), mul_nonneg (le_of_lt hA) (show 0 ≤ -z-A by linarith)]
  · rw [min_eq_right hz, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (z-A), mul_nonneg (le_of_lt hA) (show 0 ≤ z-A by linarith)]

local instance faceUpdateSelfSliceDualFintype : Fintype (Module.Dual F₂ W) :=
  BinaryFourier.dualFintype

def oddMax (one : W) (f : W → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun α : Module.Dual F₂ W =>
    if α one = 1 then |coefficient f α| else 0)

def processed (H γ A : ℝ) (one : W) (f : W → ℝ) (w : W) : ℝ :=
  if H < Real.sqrt (𝔼 b, (f b)^2) ∨ γ < oddMax one f then 0 else clip A (f w)

open BinaryFourier
end MinUncut.Slice

namespace MinUncut.Slice
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma clip_memLp {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : MemLp f 2 μ) :
    MemLp (fun x => clip A (f x)) 2 μ := by
  apply MemLp.of_bound
    ((aemeasurable_const.max (hf.aestronglyMeasurable.aemeasurable.min aemeasurable_const)).aestronglyMeasurable) A
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, clip] using clip_abs_le hA (f x))

lemma clip_integral_loss {f : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hf : MemLp f 2 μ) :
    (∫ x, |f x-clip A (f x)| ∂μ) ≤ (∫ x, (f x)^2 ∂μ)/A := by
  have hh : Integrable (fun x => |f x-clip A (f x)|) μ :=
    ((hf.sub (clip_memLp hA.le hf)).integrable (by norm_num)).abs
  calc
    _ ≤ ∫ x, (f x)^2/A ∂μ := integral_mono hh (hf.integrable_sq.div_const _) (fun x => clip_loss hA (f x))
    _ = _ := integral_div _ _

def centeredClip (μ : Measure Ω) (A : ℝ) (f : Ω → ℝ) (x : Ω) : ℝ :=
  clip A (f x) - ∫ y, clip A (f y) ∂μ

lemma centeredClip_loss {f : Ω → ℝ} {A : ℝ} (hA : 0 < A) (hf : MemLp f 2 μ)
    (hm : (∫ x, f x ∂μ) = 0) :
    (∫ x, |f x-centeredClip μ A f x| ∂μ) ≤ 2*(∫ x, (f x)^2 ∂μ)/A := by
  have hc := (clip_memLp hA.le hf).integrable (by norm_num)
  have hf' := hf.integrable (by norm_num)
  have he : |∫ x, clip A (f x) ∂μ| ≤ ∫ x, |f x-clip A (f x)| ∂μ := by
    have h := abs_integral_le_integral_abs (μ := μ) (f := fun x => f x-clip A (f x))
    rw [integral_sub hf' hc, hm, zero_sub, abs_neg] at h
    exact h
  have hl := clip_integral_loss hA hf
  have hi : Integrable (fun x => |f x-centeredClip μ A f x|) μ :=
    (hf'.sub (hc.sub (integrable_const _))).abs
  calc
    _ ≤ ∫ x, |f x-clip A (f x)| + |∫ y, clip A (f y) ∂μ| ∂μ := by
      refine integral_mono hi ((hf'.sub hc).abs.add (integrable_const _)) ?_
      intro x
      have hrewrite : f x - centeredClip μ A f x =
          (f x - clip A (f x)) + ∫ y, clip A (f y) ∂μ := by
        unfold centeredClip
        ring
      simpa only [hrewrite] using
        abs_add_le (f x - clip A (f x)) (∫ y, clip A (f y) ∂μ)
    _ = (∫ x, |f x-clip A (f x)| ∂μ) + |∫ y, clip A (f y) ∂μ| := by
      have hh : Integrable (fun x => |f x-clip A (f x)|) μ := (hf'.sub hc).abs
      rw [integral_add hh (integrable_const _)]; simp
    _ ≤ 2*(∫ x, (f x)^2 ∂μ)/A := by rw [mul_div_assoc]; linarith

end MinUncut.Slice

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CollisionIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Box
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma bounded_integrable {f : Ω → ℝ} {C : ℝ} (hf : AEStronglyMeasurable f μ)
    (hC : ∀ x, |f x|≤C) : Integrable f μ :=
  (MemLp.of_bound hf C (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x)) : MemLp f 2 μ).integrable (by norm_num)

lemma integral_pow_bound {f : Ω → ℝ} {C : ℝ} (hf : AEStronglyMeasurable f μ)
    (hC : ∀ x, |f x|≤C) (hpos : ∀ x, 0≤f x) (k : ℕ) :
    (∫ x, f x ∂μ)^k ≤ ∫ x, (f x)^k ∂μ := by
  apply (convexOn_pow k).map_integral_le (by fun_prop) isClosed_Ici
    (Eventually.of_forall hpos) (bounded_integrable hf hC)
  apply bounded_integrable (C := C^k) (hf.pow k)
  intro x
  simpa only [Function.comp_apply,Pi.pow_apply,abs_pow] using pow_le_pow_left₀ (abs_nonneg (f x)) (hC x) k

omit [IsProbabilityMeasure μ] in
lemma integral_expect {T : Type*} [Fintype T] (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    (∫ x, (𝔼 t, f t x) ∂μ) = 𝔼 t, ∫ x, f t x ∂μ := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun t _ => hf t)]
end MinUncut.Box

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SelectedProjectGaussianLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def gaussianSlice (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (H : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) (t : ℝ) : ℝ :=
  selectedProject (retainedClass x H none J) (fun B c => gradient f B σ η c x)
    B (Function.update C x t)

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EraseAway
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

def eraseAway (x : A) (Y : Finset A) : Finset (Away x) :=
  (Y.erase x).attach.map ⟨fun (a : {a : A // a∈Y.erase x}) => ⟨a.val,(Finset.mem_erase.mp a.property).1⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : Away x => z.val) h)⟩

omit [Fintype A] in
@[simp] lemma mem_eraseAway (x : A) (Y : Finset A) (a : Away x) :
    a∈eraseAway x Y ↔ a.val∈Y := by
  simp only [eraseAway,Finset.mem_map,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val hb
    rw [← he]
    exact (Finset.mem_erase.mp b.property).2
  · intro ha
    exact ⟨⟨a.val,Finset.mem_erase.mpr ⟨a.property,ha⟩⟩,rfl⟩

omit [Fintype A] in
lemma eraseAway_card (x : A) (Y : Finset A) (hx : x∈Y) :
    (eraseAway x Y).card=Y.card-1 := by simp [eraseAway,Finset.card_erase_of_mem hx]

def unpoint (x : A) {k : ℕ} (Y : FixedSets A (k+1)) (hx : x∈Y.val) : FixedSets (Away x) k :=
  ⟨eraseAway x Y.val,by rw [eraseAway_card x Y.val hx,Y.property]; omega⟩

@[simp] lemma pointed_unpoint (x : A) {k : ℕ} (Y : FixedSets A (k+1)) (hx : x∈Y.val) :
    pointedSet x (unpoint x Y hx)=Y.val := by
  ext a
  by_cases ha : a=x
  · subst a; simp [mem_pointedSet_self,hx]
  · rw [mem_pointedSet ha]
    exact mem_eraseAway x Y.val ⟨a,ha⟩

@[simp] lemma unpoint_pointed (x : A) {k : ℕ} (H : FixedSets (Away x) k) :
    unpoint x ⟨pointedSet x H,pointedSet_card x H⟩ (mem_pointedSet_self x H)=H := by
  apply Subtype.ext
  ext a
  change a∈eraseAway x (pointedSet x H) ↔ a∈H.val
  rw [mem_eraseAway,mem_pointedSet a.property]

abbrev UnpointedBox (ι A : Type*) [Fintype A] (k : ℕ) := ι → FixedSets A (k+1)
open OuterSmoothness
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def coordinateEnum {k : ℕ} (Y : UnpointedBox ι A k) (i : ι) :
    Fin (k+1) ≃ {a : A // a∈(Y i).val} :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,(Y i).property])

def pointEmbed {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) : ι → A :=
  fun i => (coordinateEnum Y i (u i)).val

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] in
lemma pointEmbed_mem {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) (i : ι) :
    pointEmbed Y u i ∈ (Y i).val := (coordinateEnum Y i (u i)).property

end MinUncut.Subbox

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def pointBox {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) :
    PointedBox (pointEmbed Y u) k :=
  fun i => unpoint (pointEmbed Y u i) (Y i) (pointEmbed_mem Y u i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma pointBox_set {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) (i : ι) :
    pointedSet (pointEmbed Y u i) (pointBox Y u i)=(Y i).val :=
  pointed_unpoint _ _ _
end MinUncut.Subbox

namespace MinUncut.Inner
open Subbox
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def faceEmbed {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) : {j : Fin m // j≠i} → Fin n :=
  fun j => (coordinateEnum Y j.val (v j)).val

lemma faceEmbed_injective {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m) :
    Function.Injective (faceEmbed Y i) := by
  intro u v h
  funext j
  apply (coordinateEnum Y j.val).injective
  apply Subtype.ext
  exact congrFun h j

@[simp] lemma faceEmbed_face {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (i : Fin m) (u : Point m (k+1)) : faceEmbed Y i (face u i)=face (pointEmbed Y u) i := rfl

def embedSingle {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (v : {j : Fin m // j≠i} → Fin (k+1)) : Row m n := ⟨i,faceEmbed Y i v⟩

lemma embedSingle_injective {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m) :
    Function.Injective (embedSingle Y i) := by
  intro u v h
  exact faceEmbed_injective Y i (sigma_mk_injective h)

def extendSingle {W : Type*} [Zero W] {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k)
    (i : Fin m) (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) : Row m n → W :=
  Function.extend (embedSingle Y i) B (fun _ => 0)

@[simp] lemma extendSingle_local {W : Type*} [Zero W] {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (i : Fin m)
    (B : ({j : Fin m // j≠i} → Fin (k+1)) → W) (u : Point m (k+1)) :
    extendSingle Y i B ⟨i,face (pointEmbed Y u) i⟩ = B (face u i) :=
  (embedSingle_injective Y i).extend_apply B (fun _ => 0) (face u i)

end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def pairProcessedOnBox (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) : ℝ :=
  Slice.processed H γ A₀ (AffineMap.const F₂ A 1)
    (pairSlice f σ η (pointEmbed Y u) (pointBox Y u) p J B c)
    (B ⟨p.val.1,face (pointEmbed Y u) p.val.1⟩+B ⟨p.val.2,face (pointEmbed Y u) p.val.2⟩)

end MinUncut.Inner
namespace MinUncut.BoxGaussian
open MeasureTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

abbrev Outside (e : κ → ι) := {i : ι // i∉Set.range e}

def indexEquiv (e : κ → ι) (he : Function.Injective e) : κ ⊕ Outside e ≃ ι :=
  ((Equiv.ofInjective e he).sumCongr (Equiv.refl (Outside e))).trans (Equiv.Set.sumCompl (Set.range e))

omit [Fintype ι] in
@[simp] lemma indexEquiv_left (e : κ → ι) (he : Function.Injective e) (j : κ) :
    indexEquiv e he (Sum.inl j)=e j := rfl
omit [Fintype ι] in
@[simp] lemma indexEquiv_right (e : κ → ι) (he : Function.Injective e) (j : Outside e) :
    indexEquiv e he (Sum.inr j)=j.val := rfl

omit [Fintype ι] in
lemma indexEquiv_symm_left (e : κ → ι) (he : Function.Injective e) (j : κ) :
    (indexEquiv e he).symm (e j)=Sum.inl j := by
  apply (indexEquiv e he).injective
  simp only [Equiv.apply_symm_apply,indexEquiv_left]

omit [Fintype ι] in
lemma indexEquiv_symm_right (e : κ → ι) (he : Function.Injective e) (j : Outside e) :
    (indexEquiv e he).symm j.val=Sum.inr j := by
  apply (indexEquiv e he).injective
  simp only [Equiv.apply_symm_apply,indexEquiv_right]

def joinEquiv (e : κ → ι) (he : Function.Injective e) :
    ((κ → ℝ) × (Outside e → ℝ)) ≃ᵐ (ι → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ Outside e => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) (indexEquiv e he))

def join (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) : ι → ℝ :=
  joinEquiv e he (C,D)

omit [Fintype ι] in
@[simp] lemma join_at (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) (j : κ) :
    join e he C D (e j)=C j := by
  simp [join,joinEquiv,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,indexEquiv_symm_left,MeasurableEquiv.coe_sumPiEquivProdPi_symm]

omit [Fintype ι] in
@[simp] lemma join_other (e : κ → ι) (he : Function.Injective e) (C : κ → ℝ) (D : Outside e → ℝ) (j : Outside e) :
    join e he C D j.val=D j := by
  simp [join,joinEquiv,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,indexEquiv_symm_right,MeasurableEquiv.coe_sumPiEquivProdPi_symm]

lemma join_preserves (μ : Measure ℝ) [SigmaFinite μ] (e : κ → ι) (he : Function.Injective e) :
    MeasurePreserving (joinEquiv e he)
      ((Measure.pi (fun _ : κ => μ)).prod (Measure.pi (fun _ : Outside e => μ)))
      (Measure.pi (fun _ : ι => μ)) :=
  (measurePreserving_piCongrLeft (fun _ : ι => μ) (indexEquiv e he)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ Outside e => μ))

lemma integral_split (μ : Measure ℝ) [SigmaFinite μ] (e : κ → ι) (he : Function.Injective e)
    (f : (ι → ℝ) → ℝ) (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ c, f c ∂Measure.pi (fun _ : ι => μ)) =
      ∫ D, ∫ C, f (join e he C D) ∂Measure.pi (fun _ : κ => μ) ∂Measure.pi (fun _ : Outside e => μ) := by
  have hp := join_preserves μ e he
  have hi := (hp.integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hf
  rw [← hp.integral_comp (joinEquiv e he).measurableEmbedding]
  exact integral_prod_symm _ hi
end MinUncut.BoxGaussian
namespace MinUncut.Box

lemma square_root_power {H ε : ℝ} (hH : 0≤H) (hε : 0≤ε) {m : ℕ} (hm : 2 ≤ m) :
    (Real.sqrt (H*ε))^(2^m)=(ε^2*H^2)^(2^(m-2)) := by
  have he : 2^m=4*2^(m-2) := by
    calc
      _ = 2^(2+(m-2)) := by congr; omega
      _ = _ := by rw [pow_add]; norm_num
  rw [he,pow_mul]
  have hh : (Real.sqrt (H*ε))^4=ε^2*H^2 := by
    calc
      _ = ((Real.sqrt (H*ε))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg hH hε)]; ring
  rw [hh]

lemma cube_power_to_bound {x A H ε d : ℝ} (hx : 0≤x) (hA : 0≤A)
    (hH : 0≤H) (hε : 0≤ε) (hd : 0≤d) {m : ℕ} (hm : 2 ≤ m)
    (h : x^(2^m)≤A^(2^m)*d+(ε^2*H^2)^(2^(m-2))) :
    x≤A*d^(((2^m:ℕ):ℝ)⁻¹)+Real.sqrt (H*ε) := by
  have hq : (2^m:ℕ)≠0 := by positivity
  apply (pow_le_pow_iff_left₀ hx (by positivity) hq).mp
  calc
    _ ≤ A^(2^m)*d+(ε^2*H^2)^(2^(m-2)) := h
    _ = (A*d^(((2^m:ℕ):ℝ)⁻¹))^(2^m)+(Real.sqrt (H*ε))^(2^m) := by
      rw [mul_pow A (d^(((2^m:ℕ):ℝ)⁻¹)) (2^m),Real.rpow_inv_natCast_pow hd hq,square_root_power hH hε hm]
    _ ≤ _ := pow_add_pow_le (by positivity) (by positivity) hq
end MinUncut.Box
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def zeroProcessedOnBox (f : FoldedProof A) (σ η : ℝ) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (u : Point m (k+1)) : ℝ :=
  Slice.centeredClip γ A₀ (gaussianSlice f σ η (pointEmbed Y u) (pointBox Y u) J B c)
    (c (pointEmbed Y u))

attribute [local irreducible] gaussianSlice Slice.centeredClip

attribute [local irreducible] pointEmbed coordinateEnum

end MinUncut.Inner
namespace MinUncut.BoxGaussian
open MeasureTheory ProbabilityTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
attribute [local instance] Classical.propDecidable

lemma integral_split_power_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : κ → ι) (he : Function.Injective e) (G : (ι → ℝ) → ℝ)
    (hG : Measurable G) {C L : ℝ} (hb : ∀ c, |G c|≤C)
    (hp : ∀ c, 0≤G c) (q : ℕ)
    (hlocal : ∀ D : Outside e → ℝ,
      (∫ c, G (join e he c D) ∂Measure.pi (fun _ : κ => μ))^q≤L) :
    (∫ c, G c ∂Measure.pi (fun _ : ι => μ))^q≤L := by
  let F := fun p : (Outside e → ℝ) × (κ → ℝ) => G (join e he p.2 p.1)
  have hF : Measurable F := hG.comp ((joinEquiv e he).measurable.comp (measurable_snd.prodMk measurable_fst))
  let Q := fun D : Outside e → ℝ => ∫ c, F (D,c) ∂Measure.pi (fun _ : κ => μ)
  have hQ : Measurable Q := hF.stronglyMeasurable.integral_prod_right.measurable
  have hQb D : |Q D|≤C := by
    calc
      _ ≤ ∫ c, |F (D,c)| ∂Measure.pi (fun _ : κ => μ) := abs_integral_le_integral_abs
      _ ≤ ∫ _c : κ → ℝ, C ∂Measure.pi (fun _ : κ => μ) := by
        apply integral_mono
        · exact (Box.bounded_integrable (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (fun c => hb _)).abs
        · exact integrable_const _
        · intro c; exact hb _
      _ = _ := by simp
  have hQp D : 0≤Q D := integral_nonneg (fun c => hp _)
  rw [integral_split μ e he G (Box.bounded_integrable hG.aestronglyMeasurable hb)]
  calc
    _ ≤ ∫ D, (Q D)^q ∂Measure.pi (fun _ : Outside e => μ) :=
      Box.integral_pow_bound hQ.aestronglyMeasurable hQb hQp q
    _ ≤ ∫ _D : Outside e → ℝ, L ∂Measure.pi (fun _ : Outside e => μ) := by
      apply integral_mono
      · apply Box.bounded_integrable (C := C^q) (hQ.aestronglyMeasurable.pow q)
        intro D
        simpa only [Pi.pow_apply,abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hQb D) q
      · exact integrable_const _
      · exact hlocal
    _ = _ := by simp
end MinUncut.BoxGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FreshCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery thirdFailure
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def thirdError (f : FoldedProof A) (σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, thirdRejection f B σ η c ∂gauss (Point m n)

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.BoxGaussian
open MeasureTheory ProbabilityTheory GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def singletonEmbed (x : ι) : Unit → ι := fun _ => x
omit [Fintype ι] [DecidableEq ι] in
lemma singletonEmbed_injective (x : ι) : Function.Injective (singletonEmbed x) := by
  intro a b _
  exact Subsingleton.elim a b

omit [Fintype ι] in
lemma update_join_singleton (x : ι) (C : Unit → ℝ) (D : Outside (singletonEmbed x) → ℝ) (t : ℝ) :
    Function.update (join (singletonEmbed x) (singletonEmbed_injective x) C D) x t =
      join (singletonEmbed x) (singletonEmbed_injective x) (fun _ => t) D := by
  funext y
  by_cases hy : y=x
  · subst y
    simpa only [Function.update_self, singletonEmbed] using
      (join_at (singletonEmbed x) (singletonEmbed_injective x) (fun _ => t) D Unit.unit).symm
  · rw [Function.update_of_ne hy]
    have hout : y∉Set.range (singletonEmbed x) := by
      rintro ⟨a,ha⟩
      exact hy ha.symm
    rw [join_other _ _ _ _ ⟨y,hout⟩,join_other _ _ _ _ ⟨y,hout⟩]

lemma integral_singleton (v : ℝ → ℝ) :
    (∫ C : Unit → ℝ, v (C Unit.unit) ∂γpi Unit) = ∫ t, v t ∂γ := by
  exact (measurePreserving_funUnique γ Unit).integral_comp
    (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding v

lemma centered_resample_memLp (x : ι) (u : (ι → ℝ) → ℝ) (hu : Measurable u)
    {A : ℝ} (hA : 0≤A) :
    MemLp (fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)) 2 (γpi ι) := by
  have hupdate : Measurable (fun p : (ι → ℝ) × ℝ => Function.update p.1 x p.2) := by
    apply Measurable.of_eval
    intro y
    by_cases hy : y=x
    · subst y
      simpa only [Function.update_self, singletonEmbed] using measurable_snd
    · simp only [Function.update_of_ne hy]
      exact (measurable_pi_apply y).comp measurable_fst
  have hm : Measurable (fun p : (ι → ℝ) × ℝ => Slice.clip A (u (Function.update p.1 x p.2))) :=
    (measurable_const.max ((hu.comp hupdate).min measurable_const))
  have hmean : Measurable (fun C => ∫ t, Slice.clip A (u (Function.update C x t)) ∂γ) :=
    hm.stronglyMeasurable.integral_prod_right.measurable
  have hd : Measurable (fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)) := by
    unfold Slice.centeredClip
    simp only [Function.update_eq_self]
    exact (measurable_const.max (hu.min measurable_const)).sub hmean
  apply MemLp.of_bound hd.aestronglyMeasurable (2*A)
  filter_upwards [] with C
  rw [Real.norm_eq_abs]
  unfold Slice.centeredClip
  exact (abs_sub _ _).trans (by
    have hc := Slice.clip_abs_le hA (u (Function.update C x (C x)))
    have hm : |∫ t, Slice.clip A (u (Function.update C x t)) ∂γ|≤A := by
      refine (abs_integral_le_integral_abs).trans ?_
      exact (integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
        (integrable_const A) (ae_of_all _ (fun t => Slice.clip_abs_le hA _))).trans_eq
          (by simp)
    linarith)

omit [DecidableEq ι] in
lemma integral_split_le {κ : Type*} [Fintype κ] (μ : Measure ℝ) [SigmaFinite μ]
    (e : κ → ι) (he : Function.Injective e) (u v : (ι → ℝ) → ℝ)
    (hu : Integrable u (Measure.pi (fun _ : ι => μ)))
    (hv : Integrable v (Measure.pi (fun _ : ι => μ))) {a : ℝ}
    (h : ∀ D : Outside e → ℝ,
      (∫ C : κ → ℝ, u (join e he C D) ∂Measure.pi (fun _ : κ => μ)) ≤
      a*(∫ C : κ → ℝ, v (join e he C D) ∂Measure.pi (fun _ : κ => μ))) :
    (∫ C, u C ∂Measure.pi (fun _ : ι => μ)) ≤ a*(∫ C, v C ∂Measure.pi (fun _ : ι => μ)) := by
  have hup := ((join_preserves μ e he).integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hu
  have hvp := ((join_preserves μ e he).integrable_comp_emb (joinEquiv e he).measurableEmbedding).mpr hv
  rw [integral_split μ e he u hu,integral_split μ e he v hv, ← integral_const_mul]
  exact integral_mono hup.integral_prod_right (hvp.integral_prod_right.const_mul a) h

attribute [local irreducible] Finset.univ Fintype.piFinset

lemma centered_resample_loss (x : ι) (u : (ι → ℝ) → ℝ) (hum : Measurable u)
    (hu : MemLp u 2 (γpi ι))
    (hv : ∀ C, MemLp (fun t => u (Function.update C x t)) 2 γ)
    (hz : ∀ C, (∫ t, u (Function.update C x t) ∂γ)=0)
    {A : ℝ} (hA : 0<A) :
    (∫ C, |u C-Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)| ∂γpi ι) ≤
      2*(∫ C, (u C)^2 ∂γpi ι)/A := by
  let e := singletonEmbed x
  let he := singletonEmbed_injective x
  let w := fun C => Slice.centeredClip γ A (fun t => u (Function.update C x t)) (C x)
  have hw : MemLp w 2 (γpi ι) := centered_resample_memLp x u hum hA.le
  have hl : Integrable (fun C => |u C-w C|) (γpi ι) := (hu.sub hw).integrable (by norm_num) |>.abs
  have hq : Integrable (fun C => (u C)^2) (γpi ι) := hu.integrable_sq
  have hs D : (∫ C : Unit → ℝ, |u (join e he C D)-w (join e he C D)| ∂γpi Unit) ≤
      2*(∫ C : Unit → ℝ, (u (join e he C D))^2 ∂γpi Unit)/A := by
    let C₀ := join e he (fun _ => 0) D
    let v := fun t => u (Function.update C₀ x t)
    have huC (C : Unit → ℝ) : u (join e he C D)=v (C Unit.unit) := by
      dsimp only [v,C₀,e,he]
      rw [update_join_singleton]

    have hwC (C : Unit → ℝ) : w (join e he C D)=Slice.centeredClip γ A v (C Unit.unit) := by
      dsimp only [w]
      have hh : (fun t => u (Function.update (join e he C D) x t))=v := by
        funext t
        dsimp only [v,C₀,e,he]
        rw [update_join_singleton,update_join_singleton]
      rw [hh]
      congr 1
      exact join_at e he C D Unit.unit
    simp_rw [huC,hwC]
    rw [integral_singleton (fun t => |v t-Slice.centeredClip γ A v t|),
      integral_singleton (fun t => (v t)^2)]
    exact Slice.centeredClip_loss hA (hv C₀) (hz C₀)
  change (∫ C, |u C-w C| ∂γpi ι) ≤ _
  rw [← div_mul_eq_mul_div]
  apply integral_split_le γ e he _ _ hl hq
  intro D
  simpa only [div_mul_eq_mul_div] using hs D
end MinUncut.BoxGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_AffineLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open BinaryFourier
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

def labelFrequency (a : A) : Module.Dual F₂ (Forms A) where
  toFun b := b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma labelFrequency_apply (a : A) (b : Forms A) : labelFrequency a b = b a := rfl
@[simp] lemma labelFrequency_odd (a : A) :
    labelFrequency a (AffineMap.const F₂ A 1) = 1 := rfl

def basedForm (a₀ : A) : Module.Dual F₂ V →ₗ[F₂] Forms A where
  toFun l := l.toAffineMap.comp (AffineEquiv.vaddConst F₂ a₀).symm.toAffineMap
  map_add' l k := by ext a; rfl
  map_smul' t l := by ext a; rfl

@[simp] lemma basedForm_apply (a₀ a : A) (l : Module.Dual F₂ V) :
    basedForm a₀ l a = l (a -ᵥ a₀) := rfl

lemma form_decomposition (a₀ : A) (b : Forms A) :
    b = basedForm a₀ b.linear + b a₀ • AffineMap.const F₂ A 1 := by
  ext a
  have h := b.map_vadd a₀ (a -ᵥ a₀)
  simpa only [vsub_vadd, vadd_eq_add, AffineMap.coe_add, AffineMap.coe_smul, Pi.add_apply, Pi.smul_apply,
    AffineMap.const_apply, smul_eq_mul, mul_one, basedForm_apply] using h

lemma labelFrequency_injective : Function.Injective (labelFrequency (A := A)) := by
  intro a a' h
  have hlin : (Module.Dual.eval F₂ V) (a -ᵥ a') = 0 := by
    ext l
    have hh := congrArg (fun α : Module.Dual F₂ (Forms A) => α (basedForm a' l)) h
    simpa using hh
  have hz : a -ᵥ a' = 0 := (Module.eval_apply_eq_zero_iff F₂ _).mp hlin
  exact vsub_eq_zero_iff_eq.mp hz

variable [Fintype A]

lemma oddFrequency_exists_label (α : Module.Dual F₂ (Forms A))
    (hα : α (AffineMap.const F₂ A 1) = 1) : ∃ a : A, labelFrequency a = α := by
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let : Fintype V := Fintype.ofEquiv A (AffineEquiv.vaddConst F₂ a₀).toEquiv.symm
  obtain ⟨v,hv⟩ := (Module.bijective_dual_eval F₂ V).2 (α.comp (basedForm a₀))
  refine ⟨v +ᵥ a₀, ?_⟩
  apply LinearMap.ext
  intro b
  have hb : α b = b.linear v + b a₀ := by
    conv_lhs => rw [form_decomposition a₀ b]
    rw [map_add, map_smul, hα]
    have hh := congrArg (fun β : Module.Dual F₂ (Module.Dual F₂ V) => β b.linear) hv
    change b.linear v = α (basedForm a₀ b.linear) at hh
    rw [← hh]
    simp
  simpa only [labelFrequency_apply, AffineMap.map_vadd, vadd_eq_add] using hb.symm

variable {V' A' : Type*} [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A']

def formPullback (π : A →ᵃ[F₂] A') : Forms A' →ₗ[F₂] Forms A where
  toFun b := b.comp π
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl

omit [Fintype A] in
@[simp] lemma formPullback_one (π : A →ᵃ[F₂] A') :
    formPullback π (AffineMap.const F₂ A' 1) = AffineMap.const F₂ A 1 := by ext a; rfl

omit [Fintype A] in
@[simp] lemma labelFrequency_pullback (π : A →ᵃ[F₂] A') (a : A) :
    (labelFrequency a).comp (formPullback π) = labelFrequency (π a) := rfl
end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_LocalDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]

def labelList (f : Forms A → ℝ) (u : ℝ) : Finset A :=
  Finset.univ.filter (fun a => u ≤ |coefficient f (labelFrequency a)|)

@[simp] lemma mem_labelList (f : Forms A → ℝ) (u : ℝ) (a : A) :
    a ∈ labelList f u ↔ u ≤ |coefficient f (labelFrequency a)| := by
  simp [labelList]

lemma coefficient_sq_le_mean (f : Forms A → ℝ) (α : Module.Dual F₂ (Forms A)) :
    coefficient f α ^2 ≤ 𝔼 a, f a ^2 := by
  rw [← parseval]
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ α)

theorem local_matching (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ)
    {u θ : ℝ} (hθ : 0<θ) (b : B)
    (hb : b ∈ labelList g θ)
    (hclose : (𝔼 z : Forms B, (g z-f (formPullback π z))^2) < (θ/4)^2)
    (hrem : |coefficient (fun z => remainder f u (formPullback π z))
      (labelFrequency b)| < θ/4) :
    ∃ a ∈ labelList f u, π a=b := by
  have hc := coefficient_sq_le_mean (fun z => g z-f (formPullback π z)) (labelFrequency b)
  rw [coefficient_sub] at hc
  have hcabs : |coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b)| < θ/4 := by
    have hs := hc.trans_lt hclose
    nlinarith [sq_abs (coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b)),
      abs_nonneg (coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b))]
  obtain ⟨α,ha,hα,hodd⟩ := extract_matched_odd f g (formPullback π)
    (AffineMap.const F₂ A 1) (AffineMap.const F₂ B 1) (formPullback_one π)
    (labelFrequency b) hθ (labelFrequency_odd b) ((mem_labelList g θ b).mp hb) hcabs hrem
  obtain ⟨a,rfl⟩ := oddFrequency_exists_label α hodd
  refine ⟨a,(mem_labelList f u a).mpr ha,?_⟩
  exact labelFrequency_injective hα

end MinUncut.Composition

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.CodeEffective
open Turing.ToPartrec
abbrev NCode := Nat.Partrec.Code

def embed : Code → NCode
  | .zero' => .zero
  | .succ => .succ
  | .tail => .left
  | .cons f g => .pair (embed f) (embed g)
  | .comp f g => .comp (embed f) (embed g)
  | .case f g => .prec (embed f) (embed g)
  | .fix f => .rfind' (embed f)

def retract : NCode → Code
  | .zero => .zero'
  | .succ => .succ
  | .left => .tail
  | .right => .tail
  | .pair f g => .cons (retract f) (retract g)
  | .comp f g => .comp (retract f) (retract g)
  | .prec f g => .case (retract f) (retract g)
  | .rfind' f => .fix (retract f)
lemma retract_embed (c : Code) : retract (embed c)=c := by
  induction c <;> simp_all [embed,retract]

def normalize : NCode → NCode := fun c=>embed (retract c)
lemma primrec_normalize : Primrec normalize := by
  have h := Nat.Partrec.Code.primrec_recOn (α:=NCode) (σ:=NCode) (c:=id) Primrec.id
    (z:=fun _=>Nat.Partrec.Code.zero) (Primrec.const _) (s:=fun _=>Nat.Partrec.Code.succ) (Primrec.const _)
    (l:=fun _=>Nat.Partrec.Code.left) (Primrec.const _) (r:=fun _=>Nat.Partrec.Code.left) (Primrec.const _)
    (pr:=fun _ _ _ x y=>Nat.Partrec.Code.pair x y)
    (Nat.Partrec.Code.primrec₂_pair.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (co:=fun _ _ _ x y=>Nat.Partrec.Code.comp x y)
    (Nat.Partrec.Code.primrec₂_comp.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc:=fun _ _ _ x y=>Nat.Partrec.Code.prec x y)
    (Nat.Partrec.Code.primrec₂_prec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (rf:=fun _ _ x=>Nat.Partrec.Code.rfind' x)
    (Nat.Partrec.Code.primrec_rfind'.comp (Primrec.snd.comp Primrec.snd))
  apply h.of_eq
  intro c
  induction c <;> simp_all [normalize,embed,retract]

instance instPrimcodableCode_solutions : Primcodable Code where
  __ := Encodable.ofLeftInverse embed retract retract_embed
  prim := by
    have h := (Primrec.succ.comp (Primrec.encode.comp
      (primrec_normalize.comp (Primrec.ofNat NCode))))
    apply (Primrec.nat_iff.mp h).of_eq
    intro n
    change Encodable.encode (embed (retract (Denumerable.ofNat NCode n))) + 1 =
      @Encodable.encode (Option Code) _ ((Encodable.decode (α:=NCode) n).bind (some ∘ retract))
    rw [Denumerable.decode_eq_ofNat]
    rfl

lemma primrec_embed : Primrec embed := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode

lemma primrec_retract : Primrec retract := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.comp primrec_normalize

lemma primrec_cons : Primrec₂ Code.cons := by
  change Primrec (fun p : Code × Code=>Code.cons p.1 p.2)
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_pair.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_comp : Primrec₂ Code.comp := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_comp.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_case : Primrec₂ Code.case := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_prec.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_fix : Primrec Code.fix := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec_rfind'.comp primrec_embed)).of_eq
      (by intro c; simp [retract,retract_embed])
lemma computable_cons : Computable₂ Code.cons := primrec_cons.to_comp
lemma computable_comp : Computable₂ Code.comp := primrec_comp.to_comp
end MinUncut.CodeEffective

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
inductive Expr where
  | const (n : ℕ)
  | reg (i : ℕ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | eq (a b : Expr)
  | le (a b : Expr)
  | at (a : Expr)
  | cond (e a b : Expr)

def Expr.eval : Expr → List ℕ → ℕ
  | .const n,_ => n
  | .reg i,v => (v.drop i).headI
  | .add a b,v => a.eval v+b.eval v
  | .sub a b,v => a.eval v-b.eval v
  | .mul a b,v => a.eval v*b.eval v
  | .eq a b,v => if a.eval v=b.eval v then 1 else 0
  | .le a b,v => if a.eval v≤b.eval v then 1 else 0
  | .at a,v => (v.drop (a.eval v)).headI
  | .cond e a b,v => if e.eval v=0 then a.eval v else b.eval v

end MinUncut.Costed

namespace MinUncut.Costed.Arena

abbrev Node := Fin 4 → ℕ
abbrev Heap := List Node

def words (h : Heap) : List ℕ := h.flatMap (fun n => List.ofFn n)

def read (h : Heap) (a : ℕ) (j : Fin 4) : ℕ :=
  if a=0 then 0 else ((h.drop (h.length-a)).headD (fun _=>0)) j

@[simp] lemma words_nil : words []=[] := rfl
@[simp] lemma words_cons (n : Node) (h : Heap) :
    words (n::h)=[n 0,n 1,n 2,n 3]++words h := by
  simp [words,List.ofFn_succ]

@[simp] lemma length_words (h : Heap) : (words h).length=4*h.length := by
  induction h with
  | nil => rfl
  | cons n h ih => simp only [words_cons,List.length_append,List.length_cons,List.length_nil,ih]; omega

@[simp] lemma read_null (h : Heap) (j : Fin 4) : read h 0 j=0 := by simp [read]

@[simp] lemma read_new (h : Heap) (n : Node) (j : Fin 4) :
    read (n::h) (h.length+1) j=n j := by simp [read]

def readExpr (pre len : ℕ) (addr : Expr) (field : Fin 4) : Expr :=
  .cond (.eq addr (.const 0))
    (.at (.add (.const (pre+field.val)) (.mul (.const 4) (.sub (.reg len) addr))))
    (.const 0)

open Turing.ToPartrec

def node (a b c d : ℕ) : Node := ![a,b,c,d]

@[simp] lemma node_zero (a b c d : ℕ) : node a b c d 0=a := rfl
@[simp] lemma node_one (a b c d : ℕ) : node a b c d 1=b := rfl
@[simp] lemma node_two (a b c d : ℕ) : node a b c d 2=c := rfl
@[simp] lemma node_three (a b c d : ℕ) : node a b c d 3=d := rfl

def codeCells : Code → ℕ → Heap
  | .zero',_ => [node 0 0 0 0]
  | .succ,_ => [node 1 0 0 0]
  | .tail,_ => [node 2 0 0 0]
  | .cons f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 3 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .comp f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 4 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .case f g,b =>
    let l := codeCells f b
    let r := codeCells g (b+l.length)
    node 5 (b+l.length) (b+l.length+r.length) 0::(r++l)
  | .fix f,b =>
    let l := codeCells f b
    node 6 (b+l.length) 0 0::l

structure State where
  mode : ℕ
  pc : ℕ
  env : ℕ
  kont : ℕ
  heap : Heap

def State.encode (s : State) : List ℕ :=
  [s.mode,s.pc,s.env,s.kont,s.heap.length]++words s.heap

abbrev r (i : ℕ) : Expr := .reg i
abbrev g (addr : Expr) (field : Fin 4) : Expr := readExpr 5 4 addr field
abbrev n : Expr := .reg 4

@[simp] lemma encode_head (s : State) : s.encode.headI=s.mode := rfl
@[simp] lemma encode_tail_head (s : State) : s.encode.tail.headI=s.pc := rfl
@[simp] lemma encode_reg0 (s : State) : (s.encode.drop 0).headI=s.mode := rfl
@[simp] lemma encode_reg1 (s : State) : (s.encode.drop 1).headI=s.pc := rfl
@[simp] lemma encode_reg2 (s : State) : (s.encode.drop 2).headI=s.env := rfl
@[simp] lemma encode_reg3 (s : State) : (s.encode.drop 3).headI=s.kont := rfl
@[simp] lemma encode_reg4 (s : State) : (s.encode.drop 4).headI=s.heap.length := rfl

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FourthTest
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {V A V' A' : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup V'] [Module F₂ V'] [AddTorsor V' A'] [Fintype A'] {m n : ℕ}

def comparisonFailure (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  if f.answer (pullQuery B (c+σ•p.1) (η•p.2)) =
    g.answer (pullQuery C (c+σ•p.1) (η•p.2)) then 0 else 1

def comparisonRejection (f : FoldedProof A) (g : FoldedProof A')
    (B : FaceArray A m n) (C : FaceArray A' m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ p, comparisonFailure f g B C σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n))

def pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n) : FaceArray A m n :=
  fun r => formPullback π (C r)

omit [Fintype A] [Fintype A'] in
@[simp] lemma labelCode_pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n) (a : A) :
    labelCode (pullbackFaces π C) a = labelCode C (π a) := rfl

omit [Fintype A] [Fintype A'] in
@[simp] lemma pullQuery_pullbackFaces (π : A →ᵃ[F₂] A') (C : FaceArray A' m n)
    (u : Point m n → ℝ) (d : Code m n → ℝ) :
    pullQuery (pullbackFaces π C) u d = (pullQuery C u d) ∘ π := by
  funext a
  unfold pullQuery
  rw [labelCode_pullbackFaces]
  rfl

def fourthError (π : A →ᵃ[F₂] A') (f : FoldedProof A) (g : FoldedProof A')
    (σ η : ℝ) : ℝ :=
  𝔼 C : FaceArray A' m n, ∫ c,
    comparisonRejection f g (pullbackFaces π C) C σ η c ∂gauss (Point m n)

end MinUncut.Inner

open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner RowNoise
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]

def listMatch (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) (u θ : ℝ) : Prop :=
  ∃ a ∈ labelList f u, ∃ b ∈ labelList g θ, π a=b

def rowDistance (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) : ℝ :=
  𝔼 z : Forms B, (g z-f (formPullback π z))^2

def restrictedFourth (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ) : ℝ :=
  ∑ β : Module.Dual F₂ (Forms B), coefficient (fun z => remainder f u (formPullback π z)) β ^4

omit [Fintype A] in
lemma rowDistance_nonneg (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ) :
    0 ≤ rowDistance π f g := Finset.expect_nonneg (fun _ _ => sq_nonneg _)

lemma restrictedFourth_nonneg (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ) :
    0 ≤ restrictedFourth π f u := Finset.sum_nonneg (fun _ _ => by positivity)

lemma coefficient_fourth_le (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (u : ℝ)
    (β : Module.Dual F₂ (Forms B)) :
    coefficient (fun z => remainder f u (formPullback π z)) β ^4 ≤ restrictedFourth π f u :=
  by
    unfold restrictedFourth
    exact Finset.single_le_sum (f := fun γ : Module.Dual F₂ (Forms B) =>
      coefficient (fun z => remainder f u (formPullback π z)) γ ^4)
      (fun _ _ => by positivity) (Finset.mem_univ β)

theorem atom_le_matching_charge (π : A →ᵃ[F₂] B) (f : Forms A → ℝ)
    (g : Forms B → ℝ) (u : ℝ) {θ : ℝ} (hθ : 0<θ) :
    (if (labelList g θ).Nonempty then (1 : ℝ) else 0) ≤
      (if listMatch π f g u θ then 1 else 0) +
      16/θ^2*rowDistance π f g + 256/θ^4*restrictedFourth π f u := by
  have hd := rowDistance_nonneg π f g
  have hr := restrictedFourth_nonneg π f u
  have hd0 : 0≤16/θ^2*rowDistance π f g := by positivity
  have hr0 : 0≤256/θ^4*restrictedFourth π f u := by positivity
  by_cases ha : (labelList g θ).Nonempty
  · rw [ite_eq_left ha]
    by_cases hm : listMatch π f g u θ
    · rw [ite_eq_left hm]; linarith
    rw [ite_eq_right hm,zero_add]
    obtain ⟨b,hb⟩ := ha
    by_cases hc : rowDistance π f g < (θ/4)^2
    · have hrem : θ/4 ≤ |coefficient (fun z => remainder f u (formPullback π z))
          (labelFrequency b)| := by
        by_contra hn
        obtain ⟨a,ha,hab⟩ := local_matching π f g hθ b hb hc (lt_of_not_ge hn)
        exact hm ⟨a,ha,b,hb,hab⟩
      have hpow := pow_le_pow_left₀ (by positivity : 0≤θ/4) hrem 4
      rw [pow_abs,abs_of_nonneg (by positivity)] at hpow
      have hfour := coefficient_fourth_le π f u (labelFrequency b)
      have hlow : θ^4 ≤ 256*restrictedFourth π f u := by nlinarith
      have hcharge : 1≤256/θ^4*restrictedFourth π f u := by
        rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hθ 4),one_mul]
        exact hlow
      linarith
    · have hlow : θ^2≤16*rowDistance π f g := by
        have hh := le_of_not_gt hc
        nlinarith
      have hcharge : 1≤16/θ^2*rowDistance π f g := by
        rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hθ 2),one_mul]
        exact hlow
      linarith
  · rw [ite_eq_right ha]
    have hm0 : (0 : ℝ) ≤ (if listMatch π f g u θ then 1 else 0) := by split_ifs <;> norm_num
    linarith

end MinUncut.Composition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_TripleKernel
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier OuterSmoothness
variable {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
attribute [local instance] BinaryFourier.dualFintype

local instance tripleKernelDecidableEq_rb4a3d0_1 : DecidableEq W := Classical.decEq W
def tripleKernel (f : W → ℝ) (v : W × W × W) : ℝ :=
  f v.1 * f v.2.1 * f v.2.2 * f (v.1+v.2.1+v.2.2)

lemma tripleKernel_mean (f : W → ℝ) :
    (𝔼 v : W × W × W, tripleKernel f v) =
      ∑ α : Module.Dual F₂ W, coefficient f α ^ 4 := by
  unfold tripleKernel
  rw [expect_pair]
  simp_rw [expect_pair]
  exact fourth_moment f

omit [Module F₂ W] [Fintype W] in
lemma tripleKernel_abs (f : W → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ w, |f w| ≤ M) (v : W × W × W) : |tripleKernel f v| ≤ M^4 := by
  simp only [tripleKernel, abs_mul]
  calc _ ≤ M * M * M * M := by
         gcongr <;> exact hf _
       _ = _ := by ring

end MinUncut.Composition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_AdaptiveKernel
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

abbrev TripleIndex (J : Type*) := Option (Option (Option J))

def tripleTupleEquiv {J A : Type*} :
    (TripleIndex J → A) ≃ ((J → A) × (A × A × A)) where
  toFun L := (fun j => L (some (some (some j))), L none,L (some none),L (some (some none)))
  invFun z
    | none => z.2.1
    | some none => z.2.2.1
    | some (some none) => z.2.2.2
    | some (some (some j)) => z.1 j
  left_inv L := by funext j; cases j with
    | none => rfl
    | some j => cases j with
      | none => rfl
      | some j => cases j <;> rfl
  right_inv _ := rfl

lemma TripleIndex.card (J : Type*) [Fintype J] :
    Fintype.card (TripleIndex J)=Fintype.card J+3 := by simp [TripleIndex]

variable {J V W : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Module F₂ V] [Fintype V]
  [AddCommGroup W] [Module F₂ W] [Fintype W]

def adaptiveKernel (f : (J → V) → V → ℝ) (u : ℝ) (L : TripleIndex J → V) : ℝ :=
  tripleKernel (remainder (f (tripleTupleEquiv L).1) u) (tripleTupleEquiv L).2

omit [Fintype J] [DecidableEq J] in
lemma adaptiveKernel_abs (f : (J → V) → V → ℝ) {M u : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) (L : TripleIndex J → V) :
    |adaptiveKernel f u L|≤(M+M^2/u)^4 :=
  tripleKernel_abs _ (by positivity) (remainder_abs_bound _ hM hu (hf _)) _

lemma adaptiveKernel_uniform (f : (J → V) → V → ℝ) {M u : ℝ}
    (hM : 0≤M) (hu : 0<u) (hf : ∀ D z, |f D z|≤M) :
    (𝔼 L : TripleIndex J → V, adaptiveKernel f u L)≤u^2*M^2 := by
  have he : (𝔼 L : TripleIndex J → V, adaptiveKernel f u L) =
      𝔼 z : (J → V) × (V × V × V), tripleKernel (remainder (f z.1) u) z.2 :=
    Fintype.expect_equiv tripleTupleEquiv _ _ (fun _ => rfl)
  rw [he,expect_pair]
  simp_rw [tripleKernel_mean]
  exact (Finset.expect_le_expect (fun D _ => remainder_fourth_bound (f D) hM hu (hf D))).trans_eq
    (Fintype.expect_const _)

omit [Fintype J] [DecidableEq J] [Fintype W] in
lemma adaptiveKernel_pullback (π : W →ₗ[F₂] V) (f : (J → V) → V → ℝ) (u : ℝ)
    (L : TripleIndex J → W) :
    adaptiveKernel f u (fun j => π (L j)) =
      tripleKernel (fun z => remainder (f (fun j => π ((tripleTupleEquiv L).1 j))) u (π z))
        (tripleTupleEquiv L).2 := by
  simp only [adaptiveKernel,tripleKernel,tripleTupleEquiv,Equiv.coe_fn_mk,map_add]

lemma adaptiveKernel_pullback_mean (π : W →ₗ[F₂] V) (f : (J → V) → V → ℝ) (u : ℝ) :
    (𝔼 L : TripleIndex J → W, adaptiveKernel f u (fun j => π (L j))) =
      𝔼 D : J → W, ∑ β : Module.Dual F₂ W,
        coefficient (fun z => remainder (f (fun j => π (D j))) u (π z)) β ^4 := by
  simp_rw [adaptiveKernel_pullback]
  have he := Fintype.expect_equiv (tripleTupleEquiv (J := J) (A := W))
    (fun L => tripleKernel (fun z => remainder (f (fun j => π ((tripleTupleEquiv L).1 j))) u (π z))
      (tripleTupleEquiv L).2)
    (fun z => tripleKernel (fun w => remainder (f (fun j => π (z.1 j))) u (π w)) z.2)
    (fun _ => rfl)
  rw [he,expect_pair]
  simp_rw [tripleKernel_mean]

end MinUncut.Composition

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.Average

lemma weighted_sqrt_mul_sqrt {T : Type*} [Fintype T] (w a b : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    (∑ t, w t * (Real.sqrt (a t) * Real.sqrt (b t))) ≤
      Real.sqrt (∑ t, w t*a t) * Real.sqrt (∑ t, w t*b t) := by
  have he t : w t * (Real.sqrt (a t) * Real.sqrt (b t)) =
      Real.sqrt (w t*a t) * Real.sqrt (w t*b t) := by
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (a t) * Real.sqrt (b t)) := by rw [Real.sq_sqrt (hw t)]
      _ = _ := by ring
  simp_rw [he]
  exact Real.sum_sqrt_mul_sqrt_le _ (fun t => mul_nonneg (hw t) (ha t))
    (fun t => mul_nonneg (hw t) (hb t))

lemma weighted_sqrt {T : Type*} [Fintype T] (w a : T → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t=1) (ha : ∀ t, 0 ≤ a t) :
    (∑ t, w t * Real.sqrt (a t)) ≤ Real.sqrt (∑ t, w t*a t) := by
  simpa only [Real.sqrt_one, mul_one, hw1] using
    weighted_sqrt_mul_sqrt w a (fun _ => 1) hw ha (fun _ => by norm_num)

lemma expect_sqrt_mul_sqrt {T : Type*} [Fintype T] (a b : T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    (𝔼 t, Real.sqrt (a t)*Real.sqrt (b t)) ≤
      Real.sqrt (𝔼 t, a t)*Real.sqrt (𝔼 t, b t) := by
  have h := weighted_sqrt_mul_sqrt (fun _ : T => (Fintype.card T:ℝ)⁻¹) a b
    (fun _ => by positivity) ha hb
  simpa only [← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv,
    mul_comm (Fintype.card T:ℝ)⁻¹, ← Finset.sum_mul] using h
end MinUncut.Average

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def classField (f : FoldedProof A) (σ η : ℝ)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (a : Option (PairClass m))
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  selectedProject (classSelection x a J) (fun B c => gradient f B σ η c x) B c

end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def pairProcessed (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) (H γ A₀ : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) : ℝ :=
  Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x Y p J B c)
    (B ⟨p.val.1,face x p.val.1⟩+B ⟨p.val.2,face x p.val.2⟩)

attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
end MinUncut.Inner

open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators
variable {m n : ℕ}

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass pairSlice pairProcessed Slice.processed
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def pairAtomMean (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, Slice.oddMax (AffineMap.const F₂ A 1)
      (pairSlice f σ η x Y p J B c) ∂γpi (Point m n)

end MinUncut.Inner

open scoped BigOperators

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient oddAtom
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] {m n : ℕ}

def rowAtom (f : FoldedProof A) (σ η : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) : ℝ :=
  oddAtom ⟨i,face x i⟩ (AffineMap.const F₂ A 1) (fun B => gradient f B σ η c x) D

def rowAtomIndicator (f : FoldedProof A) (σ η θ : ℝ) (x : Point m n) (i : Fin m)
    (D : Rest (W := AffineMap F₂ A F₂) (⟨i,face x i⟩ : Row m n)) (c : Point m n → ℝ) : ℝ :=
  if θ ≤ rowAtom f σ η x i D c then 1 else 0

def rowEventProbability (f : FoldedProof A) (σ η θ : ℝ) (x : Point m n) (i : Fin m) : ℝ :=
  𝔼 D, ∫ c, rowAtomIndicator f σ η θ x i D c ∂γpi (Point m n)

def atomProbability (f : FoldedProof A) (σ η θ : ℝ) : ℝ :=
  𝔼 x : Point m n, 𝔼 i : Fin m, rowEventProbability f σ η θ x i

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineTableSplit

open _root_.Turing


abbrev Tape := Fin 5

end MinUncutGames.Foundations.Complexity.MachineTableSplit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeContinuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena
open Turing.ToPartrec

open Turing.ToPartrec

structure OutputState where
  ptr : ℕ
  heap : Heap
  acc : List ℕ

def OutputState.encode (s : OutputState) : List ℕ :=
  [s.ptr,s.heap.length,s.acc.length]++s.acc++2::words s.heap

@[simp] lemma out_encode_reg0 (s : OutputState) : (r 0).eval s.encode=s.ptr := rfl
@[simp] lemma out_encode_reg1 (s : OutputState) : (r 1).eval s.encode=s.heap.length := rfl

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_HeapInitializationMath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.Arena
open Turing.ToPartrec

def rebasePointer (d a : ℕ) : ℕ := if a=0 then 0 else d+a
def rebaseNode (d : ℕ) (n : Node) : Node :=
  node (n 0) (rebasePointer d (n 1)) (rebasePointer d (n 2)) (n 3)

lemma codeCells_length_eq (c : Code) (a b : ℕ) :
    (codeCells c a).length=(codeCells c b).length := by
  induction c generalizing a b with
  | zero' | succ | tail => rfl
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    simp only [codeCells,List.length_cons,List.length_append]
    rw [ih a b, ih']
  | fix f ih => simp only [codeCells,List.length_cons,ih a b]

lemma codeCells_pos (c : Code) (b : ℕ) : 0<(codeCells c b).length := by
  cases c <;> simp [codeCells]

lemma codeCells_rebase (c : Code) (b d : ℕ) :
    codeCells c (b+d)=(codeCells c b).map (rebaseNode d) := by
  induction c generalizing b with
  | zero' | succ | tail => simp [codeCells,rebaseNode,rebasePointer]
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    have hf := codeCells_pos f b
    have hg := codeCells_pos g (b+(codeCells f b).length)
    have he := codeCells_length_eq f (b+d) b
    simp only [codeCells,List.map_cons,List.map_append]
    rw [he,show b+d+(codeCells f b).length=(b+(codeCells f b).length)+d by omega]
    rw [codeCells_length_eq g ((b+(codeCells f b).length)+d) (b+(codeCells f b).length),
      ih,ih']
    congr 1
    simp only [rebaseNode,node_zero,node_one,node_two,node_three,rebasePointer]
    erw [ite_eq_right (by omega : b+(codeCells f b).length≠0),
      ite_eq_right (by omega : b+(codeCells f b).length+(codeCells g (b+(codeCells f b).length)).length≠0)]
    congr 1 <;> omega
  | fix f ih =>
    have hf:=codeCells_pos f b
    simp only [codeCells,List.map_cons,ih]
    congr 1
    simp only [rebaseNode,node_zero,node_one,node_two,node_three,rebasePointer]
    erw [ite_eq_right (by omega : b+(codeCells f b).length≠0)]
    congr 1
    simp only [List.length_map]
    omega

end MinUncut.Costed.Arena

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_CodeFoldComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.CodeEffective
open Turing.ToPartrec
variable {σ : Type*} [Primcodable σ]
def fold (z s t : σ) (b3 b4 b5 : σ → σ → σ) (f6 : σ → σ) : Code → σ
  | .zero' => z
  | .succ => s
  | .tail => t
  | .cons f g => b3 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .comp f g => b4 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .case f g => b5 (fold z s t b3 b4 b5 f6 f) (fold z s t b3 b4 b5 f6 g)
  | .fix f => f6 (fold z s t b3 b4 b5 f6 f)
lemma primrec_fold (z s t : σ) {b3 b4 b5 : σ → σ → σ} {f6 : σ → σ}
    (h3 : Primrec₂ b3) (h4 : Primrec₂ b4) (h5 : Primrec₂ b5) (h6 : Primrec f6) :
    Primrec (fold z s t b3 b4 b5 f6) := by
  have h := Nat.Partrec.Code.primrec_recOn (α:=Code) (σ:=σ) primrec_embed
    (z:=fun _=>z) (Primrec.const _) (s:=fun _=>s) (Primrec.const _)
    (l:=fun _=>t) (Primrec.const _) (r:=fun _=>t) (Primrec.const _)
    (pr:=fun _ _ _ x y=>b3 x y)
    (h3.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (co:=fun _ _ _ x y=>b4 x y)
    (h4.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc:=fun _ _ _ x y=>b5 x y)
    (h5.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (rf:=fun _ _ x=>f6 x) (h6.comp (Primrec.snd.comp Primrec.snd))
  apply h.of_eq
  intro c
  induction c <;> simp_all [fold,embed]
end MinUncut.CodeEffective

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_CodeLayoutComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.CodeEffective.Layout
open Turing.ToPartrec MinUncut.Costed.Arena
abbrev Cell := ℕ × ℕ × ℕ × ℕ
def shift (b : ℕ) (x : Cell) : Cell :=
  (x.1,rebasePointer b x.2.1,rebasePointer b x.2.2.1,x.2.2.2)
lemma p_pointer : Primrec₂ rebasePointer :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)
lemma p_shift : Primrec₂ shift :=
  (Primrec.fst.comp Primrec.snd).pair
    ((p_pointer.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      ((p_pointer.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
def binary (tag : ℕ) (l r : List Cell) : List Cell :=
  (tag,l.length,l.length+r.length,0)::(r.map (shift l.length)++l)
def unary (l : List Cell) : List Cell := (6,l.length,0,0)::l
lemma p_binary (tag : ℕ) : Primrec₂ (binary tag) := by
  have hl : Primrec (fun p : List Cell × List Cell=>p.1.length) := Primrec.list_length.comp Primrec.fst
  have hr : Primrec (fun p : List Cell × List Cell=>p.2.length) := Primrec.list_length.comp Primrec.snd
  have hm : Primrec (fun p : List Cell × List Cell=>p.2.map (shift p.1.length)) :=
    Primrec.list_map Primrec.snd (p_shift.comp (hl.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp
    ((Primrec.const tag).pair (hl.pair ((Primrec.nat_add.comp hl hr).pair (Primrec.const 0))))
    (Primrec.list_append.comp hm Primrec.fst)
lemma p_unary : Primrec unary :=
  Primrec.list_cons.comp
    ((Primrec.const 6).pair (Primrec.list_length.pair ((Primrec.const 0).pair (Primrec.const 0)))) Primrec.id

def cells : Code → List Cell := fold [(0,0,0,0)] [(1,0,0,0)] [(2,0,0,0)] (binary 3) (binary 4) (binary 5) unary
lemma p_cells : Primrec cells := primrec_fold _ _ _ (p_binary 3) (p_binary 4) (p_binary 5) p_unary

def pack (n : Node) : Cell := (n 0,n 1,n 2,n 3)
lemma pack_rebase (d : ℕ) (h : Heap) :
    (h.map (rebaseNode d)).map pack=(h.map pack).map (shift d) := by
  simp only [List.map_map]
  rfl
lemma cells_eq (c : Code) : cells c=(codeCells c 0).map pack := by
  induction c with
  | zero' | succ | tail => rfl
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    have hg:=codeCells_rebase g 0 (codeCells f 0).length
    simp only [Nat.zero_add] at hg
    change binary _ (cells f) (cells g)=_
    rw [binary,ih,ih']
    simp only [codeCells,Nat.zero_add,List.length_map,hg,List.map_cons,List.map_append,
      pack_rebase,pack,node_zero,node_one,node_two,node_three]
  | fix f ih =>
    change unary (cells f)=_
    rw [unary,ih]
    simp only [codeCells,Nat.zero_add,List.length_map,List.map_cons,pack,node_zero,node_one,node_two,node_three]

def flattenCell (x : Cell) : List ℕ := [x.1,x.2.1,x.2.2.1,x.2.2.2]
lemma p_flattenCell : Primrec flattenCell :=
  Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const []))))
lemma p_words : Primrec (fun c=>words (codeCells c 0)) := by
  have hh : Primrec (fun c=>(cells c).flatMap flattenCell) :=
    Primrec.list_flatMap p_cells (p_flattenCell.comp Primrec.snd).to₂
  exact hh.of_eq (by intro c; simp only [cells_eq,List.flatMap_map,words]; congr 1)
lemma p_count : Primrec (fun c=>(codeCells c 0).length) :=
  (Primrec.list_length.comp p_cells).of_eq (by intro c; simp only [cells_eq,List.length_map])
lemma c_prefix : Computable (fun c=>(codeCells c 0).length::words (codeCells c 0)) :=
  (Primrec.list_cons.comp p_count p_words).to_comp
end MinUncut.CodeEffective.Layout

end

end OAI
end


