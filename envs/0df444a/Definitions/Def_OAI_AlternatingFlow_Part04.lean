-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part04
-- name    : OAI_AlternatingFlow_Part04
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:31:46.302978+00:00
-- url     : https://prove2.me/theorems/230fdad2-8976-4d8c-be6b-798ab0fe28b8
-- title:
--   Alternating-flow construction, part 4 of 11 (port of OpenAI's formalization): derivative bounds and rapid decay
-- statement:
--   Part 4 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains derivative bounds and rapid decay.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `DerivativeBounds` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/DerivativeBounds.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 4 of 11: derivative bounds and rapid decay.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: DerivativeBounds.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part03

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DerivativeBounds.lean =====
namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Bounds
noncomputable section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def BoundedJets (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ r f x‖ ≤ C

def ScaledJets (s : ℕ → ℝ) (f : ℕ → E → F) : Prop :=
  (∀ n, ContDiff ℝ ∞ (f n)) ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ n x, ‖iteratedFDeriv ℝ r (f n) x‖ ≤ C * s n ^ r

lemma compact_bounded (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    BoundedJets f := by
  refine ⟨hf, fun r => ?_⟩
  obtain ⟨B, hB⟩ := ((hc.iteratedFDeriv r).isCompact_range
    (hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top))).exists_bound_of_continuousOn
      continuous_id.continuousOn
  exact ⟨max 0 B, le_max_left _ _, fun x => (hB _ ⟨x, rfl⟩).trans (le_max_right _ _)⟩

lemma ScaledJets.congr {s : ℕ → ℝ} {f g : ℕ → E → F} (hf : ScaledJets s f)
    (he : ∀ n x, f n x = g n x) : ScaledJets s g := by
  have h : f = g := funext (fun n => funext (he n))
  rwa [← h]

lemma ScaledJets.const {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (a : ℕ → F)
    (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ B) :
    ScaledJets s (fun n (_ : E) => a n) := by
  refine ⟨fun _ => contDiff_const, fun r => ⟨B, hB, fun n x => ?_⟩⟩
  rcases r with _ | r
  · simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using ha n
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]
    exact mul_nonneg hB (pow_nonneg (hs n) _)

lemma ScaledJets.fixed {s : ℕ → ℝ} (hs : ∀ n, 1 ≤ s n) {f : E → F}
    (hf : BoundedJets f) : ScaledJets s (fun _ => f) := by
  refine ⟨fun _ => hf.1, fun r => ?_⟩
  obtain ⟨C, hC, h⟩ := hf.2 r
  exact ⟨C, hC, fun n x => (h x).trans (le_mul_of_one_le_right hC (one_le_pow₀ (hs n)))⟩

lemma ScaledJets.add {s : ℕ → ℝ} {f g : ℕ → E → F}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x + g n x) := by
  refine ⟨fun n => (hf.1 n).add (hg.1 n), fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
    (hg.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  exact (norm_add_le _ _).trans (by linarith [hfa n x, hgb n x])

lemma ScaledJets.sub {s : ℕ → ℝ} {f g : ℕ → E → F}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x - g n x) := by
  refine ⟨fun n => (hf.1 n).sub (hg.1 n), fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
    (hg.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  exact (norm_sub_le _ _).trans (by linarith [hfa n x, hgb n x])

lemma ScaledJets.smul {s : ℕ → ℝ} (_hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, |a n| ≤ B) :
    ScaledJets s (fun n x => a n • f n x) := by
  refine ⟨fun n => contDiff_const.smul (hf.1 n), fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨B * C, mul_nonneg hB hC, fun n x => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (hf.1 n |>.of_le (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt), norm_smul,
    Real.norm_eq_abs]
  calc
    |a n| * ‖iteratedFDeriv ℝ r (f n) x‖ ≤ B * (C * s n ^ r) := by
      gcongr
      exact ha n
      exact hc n x
    _ = _ := by ring

lemma ScaledJets.mul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f g : ℕ → E → ℝ}
    (hf : ScaledJets s f) (hg : ScaledJets s g) :
    ScaledJets s (fun n x => f n x * g n x) := by
  classical
  refine ⟨fun n => (hf.1 n).mul (hg.1 n), fun r => ?_⟩
  choose A hA hfa using hf.2
  choose B hB hgb using hg.2
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)), fun n x => ?_⟩
  apply (norm_iteratedFDeriv_mul_le (hf.1 n) (hg.1 n) x (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω))).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (A i * s n ^ i) * (B (r - i) * s n ^ (r - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA i) (pow_nonneg (hs n) _))
      · exact hfa i n x
      · exact hgb (r - i) n x
    _ = C * s n ^ r := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
      rw [show (r.choose i : ℝ) * (A i * s n ^ i) * (B (r - i) * s n ^ (r - i)) =
        ((r.choose i : ℝ) * A i * B (r - i)) * (s n ^ i * s n ^ (r - i)) by ring,
        ← pow_add, Nat.add_sub_of_le hir]

lemma ScaledJets.sum {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {ι : Type*}
    (I : Finset ι) (f : ι → ℕ → E → F) (hf : ∀ i ∈ I, ScaledJets s (f i)) :
    ScaledJets s (fun n x => ∑ i ∈ I, f i n x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using ScaledJets.const hs (fun _ => (0 : F)) 0 le_rfl (by simp)
  | @insert a I ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma ScaledJets.ite {s : ℕ → ℝ} {f g : ℕ → E → F} (hs : ∀ n, 0 ≤ s n)
    (hf : ScaledJets s f) (hg : ScaledJets s g) (p : ℕ → Prop) [DecidablePred p] :
    ScaledJets s (fun n => if p n then f n else g n) := by
  refine ⟨fun n => by dsimp only; split_ifs <;> [exact hf.1 n; exact hg.1 n], fun r => ?_⟩
  obtain ⟨A, hA, hfa⟩ := hf.2 r
  obtain ⟨B, hB, hgb⟩ := hg.2 r
  refine ⟨max A B, le_trans hA (le_max_left _ _), fun n x => ?_⟩
  dsimp only
  split_ifs
  · exact (hfa n x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hs n) _))
  · exact (hgb n x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hs n) _))

lemma ScaledJets.comp {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) {g : F → G} (hg : BoundedJets g) :
    ScaledJets s (fun n => g ∘ f n) := by
  classical
  refine ⟨fun n => hg.1.comp (hf.1 n), fun r => ?_⟩
  choose A hA hfa using hf.2
  choose B hB hgb using hg.2
  let D : ℝ := 1 + ∑ i ∈ Finset.range (r + 1), A i
  let C : ℝ := ∑ i ∈ Finset.range (r + 1), B i
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hA i))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hB i)
  refine ⟨r.factorial * C * D ^ r, by positivity, fun n x => ?_⟩
  have h := norm_iteratedFDeriv_comp_le hg.1 (hf.1 n) (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω)) x
    (C := C) (D := D * s n) ?_ ?_
  · simpa only [mul_pow, mul_assoc] using h
  · intro i hi
    exact (hgb i (f n x)).trans (Finset.single_le_sum (fun i _ => hB i)
      (Finset.mem_range.mpr (by omega)))
  · intro i hi hir
    have hai : A i ≤ D := by
      have := Finset.single_le_sum (s := Finset.range (r + 1)) (f := A)
        (fun i _ => hA i) (Finset.mem_range.mpr (by omega : i < r + 1))
      dsimp [D]; linarith
    have hai' : A i ≤ D ^ i := hai.trans (le_self_pow₀ hD (by omega))
    calc
      ‖iteratedFDeriv ℝ i (f n) x‖ ≤ A i * s n ^ i := hfa i n x
      _ ≤ D ^ i * s n ^ i := mul_le_mul_of_nonneg_right hai' (pow_nonneg (hs n) _)
      _ = (D * s n) ^ i := (mul_pow _ _ _).symm

lemma norm_comp_linear (f : E → F) (hf : ContDiff ℝ ∞ f) (L : G →L[ℝ] E)
    (r : ℕ) (x : G) :
    ‖iteratedFDeriv ℝ r (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ r f (L x)‖ * ‖L‖ ^ r := by
  rw [L.iteratedFDeriv_comp_right hf x (WithTop.coe_le_coe.mpr le_top)]
  simpa using (iteratedFDeriv ℝ r f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

lemma ScaledJets.comp_linear {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → F}
    (hf : ScaledJets s f) (L : ℕ → G →L[ℝ] E) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ n, ‖L n‖ ≤ B) : ScaledJets s (fun n => f n ∘ L n) := by
  refine ⟨fun n => (hf.1 n).comp (L n).contDiff, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨C * B ^ r, by positivity, fun n x => ?_⟩
  apply (norm_comp_linear (f n) (hf.1 n) (L n) r x).trans
  calc
    _ ≤ (C * s n ^ r) * B ^ r := by
      gcongr
      · exact mul_nonneg hC (pow_nonneg (hs n) _)
      · exact hc n _
      · exact hL n
    _ = _ := by ring

lemma BoundedJets.comp_scaled_linear {s : ℕ → ℝ} (_hs : ∀ n, 0 ≤ s n) {f : E → F}
    (hf : BoundedJets f) (L : ℕ → G →L[ℝ] E) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ n, ‖L n‖ ≤ B * s n) : ScaledJets s (fun n => f ∘ L n) := by
  refine ⟨fun n => hf.1.comp (L n).contDiff, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := hf.2 r
  refine ⟨C * B ^ r, by positivity, fun n x => ?_⟩
  apply (norm_comp_linear f hf.1 (L n) r x).trans
  calc
    _ ≤ C * (B * s n) ^ r := by gcongr; exact hc _; exact hL n
    _ = _ := by ring

lemma ScaledJets.constant {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (a : F) :
    ScaledJets s (fun _ (_ : E) => a) :=
  ScaledJets.const hs (fun _ => a) ‖a‖ (norm_nonneg _) (fun _ => le_rfl)

lemma ScaledJets.cmul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (ha : ∀ n, |a n| ≤ B) :
    ScaledJets s (fun n x => a n * f n x) := hf.smul hs a B hB ha

lemma ScaledJets.const_mul {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℝ) : ScaledJets s (fun n x => a * f n x) :=
  hf.cmul hs (fun _ => a) |a| (abs_nonneg _) (fun _ => le_rfl)

lemma ScaledJets.div_const {s : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) {f : ℕ → E → ℝ}
    (hf : ScaledJets s f) (a : ℝ) : ScaledJets s (fun n x => f n x / a) :=
  (hf.const_mul hs a⁻¹).congr (fun _ _ => by simp [div_eq_mul_inv, mul_comm])

lemma decoder_bounded (b : ℕ) (hb : 2 ≤ b) : BoundedJets (Profiles.decoder b) := by
  refine ⟨Profiles.decoder_smooth b hb, fun r => ?_⟩
  obtain ⟨C, hC, hc⟩ := Profiles.decoder_derivatives_bounded b hb r
  exact ⟨C, hC, fun x => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] using hc x⟩

lemma selector_bounded (b a : ℕ) (hb : 0 < b) : BoundedJets (Profiles.selector b a) := by
  apply compact_bounded _ (Profiles.selector_smooth b a)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := (2 * (a : ℝ) - 1 / 4) / b) (b := (2 * (a : ℝ) + 5 / 4) / b))
    isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  obtain ⟨h₁, h₂⟩ := Profiles.selector_support_bound b a x hx
  exact ⟨(div_le_iff₀ hb').mpr (by nlinarith), (le_div_iff₀ hb').mpr (by nlinarith)⟩

def readScale (M : Machine) (N n : ℕ) : ℝ :=
  (M.base : ℝ) ^ (Scales.s N n + 1 + Scales.K N n)

lemma readScale_ge_one (M : Machine) (N n : ℕ) : 1 ≤ readScale M N n :=
  one_le_pow₀ (by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base))

lemma readScale_nonneg (M : Machine) (N n : ℕ) : 0 ≤ readScale M N n :=
  le_trans zero_le_one (readScale_ge_one M N n)

lemma inverse_power_bound (M : Machine) (k : ℕ) : |((M.base : ℝ) ^ k)⁻¹| ≤ 1 := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  rw [abs_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hb)

lemma scaled_decoder (M : Machine) (N : ℕ) (k : ℕ → ℕ)
    (hk : ∀ n, k n ≤ Scales.s N n + 1 + Scales.K N n) :
    ScaledJets (readScale M N) (fun n D => Profiles.decoder M.base ((M.base : ℝ) ^ k n * D)) := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  refine (decoder_bounded M.base (by have := M.base_ge_four; omega)).comp_scaled_linear
    (readScale_nonneg M N) (fun n => (M.base : ℝ) ^ k n • ContinuousLinearMap.id ℝ ℝ)
    1 zero_le_one ?_
  intro n
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hb) _),
    ContinuousLinearMap.norm_id, mul_one, one_mul, readScale] using pow_le_pow_right₀ hb (hk n)

lemma readC_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readC M N) := by
  exact scaled_decoder M N (Scales.s N) (fun _ => by omega)

lemma readB_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readB M N) := by
  exact scaled_decoder M N (fun n => Scales.s N n + 1 + Scales.K N n) (fun _ => le_rfl)

lemma readA_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.readA M N) := by
  exact (scaled_decoder M N (fun n => Scales.s N n + 1) (fun _ => by omega)).sub
    ((readB_scaled M N).cmul (readScale_nonneg M N) _ 1 zero_le_one
      (fun n => inverse_power_bound M _))

lemma updateLeft_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.updateLeft M.base a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  unfold LocalRule.updateLeft
  split_ifs
  · exact ((readA_scaled M N).const_mul (readScale_nonneg M N) _).sub
      (ScaledJets.constant (readScale_nonneg M N) _)
  · exact readA_scaled M N
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add (readA_scaled M N)).div_const
      (readScale_nonneg M N) _

lemma updateRight_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.updateRight M.base a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  have hR := ((readB_scaled M N).const_mul (readScale_nonneg M N) (M.base : ℝ)).sub
    (ScaledJets.constant (readScale_nonneg M N) (2 * (a : ℝ)))
  unfold LocalRule.updateRight
  dsimp only
  split_ifs
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add
      (((ScaledJets.constant (readScale_nonneg M N) _).add hR).div_const
        (readScale_nonneg M N) _)).div_const (readScale_nonneg M N) _
  · exact ((ScaledJets.constant (readScale_nonneg M N) _).add hR).div_const
      (readScale_nonneg M N) _
  · exact hR

lemma branchNumerator_scaled (M : Machine) (N a l : ℕ) (r : Rule) :
    ScaledJets (readScale M N) (fun n D => LocalRule.branchNumerator M.base
      (Scales.K N (n + 1)) a l r (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  exact ((ScaledJets.constant (readScale_nonneg M N) _).add (updateLeft_scaled M N a l r)).add
    ((updateRight_scaled M N a l r).cmul (readScale_nonneg M N) _ 1 zero_le_one
      (fun n => inverse_power_bound M _))

lemma branch_scaled (M : Machine) (N q a : ℕ) :
    ScaledJets (readScale M N) (fun n D =>
      LocalRule.branch M N n q a (LocalRule.readA M N n D) (LocalRule.readB M N n D)) := by
  classical
  unfold LocalRule.branch
  dsimp only
  split_ifs
  · exact ScaledJets.sum (readScale_nonneg M N) _ _ (fun l _ =>
      ((readA_scaled M N).comp (readScale_nonneg M N)
        (selector_bounded M.base l (by have := M.base_ge_four; omega))).mul
        (readScale_nonneg M N) (branchNumerator_scaled M N a l _))
  · exact branchNumerator_scaled M N a 0 _

def writeCore (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  (1 / (M.base : ℝ)) *
    ∑ q ∈ Finset.range (M.states + 1), ∑ a ∈ Finset.range M.alphabet,
      Profiles.selector M.base q (LocalRule.readC M N n D) *
        Profiles.selector M.base a (LocalRule.readB M N n D) *
          LocalRule.branch M N n q a (LocalRule.readA M N n D) (LocalRule.readB M N n D)

lemma writeCore_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (writeCore M N) := by
  classical
  apply ScaledJets.const_mul (readScale_nonneg M N)
  apply ScaledJets.sum (readScale_nonneg M N)
  intro q _
  apply ScaledJets.sum (readScale_nonneg M N)
  intro a _
  exact (((readC_scaled M N).comp (readScale_nonneg M N)
    (selector_bounded M.base q (by have := M.base_ge_four; omega))).mul (readScale_nonneg M N)
    ((readB_scaled M N).comp (readScale_nonneg M N)
      (selector_bounded M.base a (by have := M.base_ge_four; omega)))).mul (readScale_nonneg M N)
        (branch_scaled M N q a)

lemma write_factor (M : Machine) (N n : ℕ) (D : ℝ) :
    LocalRule.write M N n D = Scales.ε M.base N (n + 1) * writeCore M N n D := by
  unfold LocalRule.write writeCore
  ring

lemma haltWeight_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (LocalRule.haltWeight M N) := by
  classical
  apply ScaledJets.sum (readScale_nonneg M N)
  intro q _
  split_ifs
  · exact (readC_scaled M N).comp (readScale_nonneg M N)
      (selector_bounded M.base q (by have := M.base_ge_four; omega))
  · exact ScaledJets.constant (readScale_nonneg M N) _

lemma ScaledJets.finite_family {s : ℕ → ℝ} (hs : ∀ n, 1 ≤ s n) {ι : Type*} [Fintype ι]
    (f : ι → E → F) (hf : ∀ i, BoundedJets (f i)) (idx : ℕ → ι) :
    ScaledJets s (fun n => f (idx n)) := by
  classical
  refine ⟨fun n => (hf (idx n)).1, fun r => ?_⟩
  choose C hC hc using fun i => (hf i).2 r
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun n x => ?_⟩
  exact ((hc (idx n) x).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))).trans
    (le_mul_of_one_le_right (Finset.sum_nonneg (fun i _ => hC i)) (one_le_pow₀ (hs n)))

lemma norm_postcomp_linear (f : E → F) (hf : ContDiff ℝ ∞ f) (L : F →L[ℝ] G)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (L ∘ f) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ r f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
  exact L.norm_compContinuousMultilinearMap_le _

lemma norm_directional_iterated (f : E → F) (hf : ContDiff ℝ ∞ f) (v : E)
    (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (fun x => fderiv ℝ f x v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
  apply (norm_postcomp_linear _ (hf.fderiv_right (by simp))
    (ContinuousLinearMap.apply ℝ F v) r x).trans
  rw [norm_iteratedFDeriv_fderiv]
  gcongr
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun L => by
    simpa only [ContinuousLinearMap.apply_apply, mul_comm] using L.le_opNorm v)

lemma norm_e (i : Fin 3) : ‖e i‖ = 1 := by simp [e]

lemma norm_iterated_curl (i j : Fin 3) (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ r (Spatial.curl i j f) x‖ ≤ 2 * ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
  have h (i j : Fin 3) :
      ‖iteratedFDeriv ℝ r (fun x => Spatial.d j f x • e i) x‖ ≤
        ‖iteratedFDeriv ℝ (r + 1) f x‖ := by
    apply (norm_postcomp_linear _ (Spatial.d_smooth j f hf)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)) r x).trans
    have hn : ‖(ContinuousLinearMap.id ℝ ℝ).smulRight (e i)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun a => by simp [norm_smul, norm_e])
    calc
      _ ≤ 1 * (1 * ‖iteratedFDeriv ℝ (r + 1) f x‖) := by
        gcongr
        change ‖iteratedFDeriv ℝ r (fun x : Space => fderiv ℝ f x (e j)) x‖ ≤ _
        simpa only [norm_e] using norm_directional_iterated f hf (e j) r x
      _ = _ := by ring
  have hi (i j : Fin 3) : ContDiff ℝ ∞ (fun x => Spatial.d j f x • e i) :=
    (Spatial.d_smooth j f hf).smul contDiff_const
  unfold Spatial.curl
  rw [fun_iteratedFDeriv_sub_apply
    ((hi i j).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((hi j i).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  exact (norm_sub_le _ _).trans (by linarith [h i j, h j i])

lemma cutoff_coordinate_bounded (i : Fin 3) :
    BoundedJets (fun x : Space => Spatial.cutoff x * x i) := by
  apply compact_bounded _ (Spatial.cutoff_smooth.mul (Spatial.coord_smooth i))
  exact Spatial.box_compact.of_isClosed_subset isClosed_closure
    (tsupport_mul_subset_left.trans Spatial.cutoff_support)

lemma scaled_coord_comp (M : Machine) (N : ℕ) {f : ℕ → ℝ → ℝ}
    (hf : ScaledJets (readScale M N) f) (idx : ℕ → Fin 3) :
    ScaledJets (readScale M N) (fun n (x : Space) => f n (x (idx n))) := by
  apply hf.comp_linear (readScale_nonneg M N)
    (fun n => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (idx n)) 1 zero_le_one
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, PiLp.proj_apply] using PiLp.norm_apply_le x (idx n)

def fixedPotential (n : ℕ) (x : Space) : ℝ :=
  -(Spatial.cutoff x * x (Construction.receiverIndex n))

def corePotential (M : Machine) (N n : ℕ) (x : Space) : ℝ :=
  (Spatial.cutoff x * x 0) * writeCore M N n (x (Construction.donorIndex n)) -
    (Spatial.cutoff x * x (Construction.receiverIndex n)) *
      (2 * LocalRule.haltWeight M N n (x (Construction.donorIndex n)))

lemma fixedPotential_scaled : ScaledJets (fun _ => 1) fixedPotential := by
  have h := ScaledJets.finite_family (fun _ => le_rfl : ∀ _ : ℕ, (1 : ℝ) ≤ 1)
    (fun i (x : Space) => Spatial.cutoff x * x i) cutoff_coordinate_bounded
    Construction.receiverIndex
  exact (h.const_mul (fun _ => zero_le_one) (-1)).congr (fun _ _ => by simp [fixedPotential])

lemma corePotential_scaled (M : Machine) (N : ℕ) :
    ScaledJets (readScale M N) (corePotential M N) := by
  have h (idx : ℕ → Fin 3) := ScaledJets.finite_family (readScale_ge_one M N)
    (fun i (x : Space) => Spatial.cutoff x * x i) cutoff_coordinate_bounded idx
  exact ((h (fun _ => 0)).mul (readScale_nonneg M N)
    (scaled_coord_comp M N (writeCore_scaled M N) Construction.donorIndex)).sub
      ((h Construction.receiverIndex).mul (readScale_nonneg M N)
        ((scaled_coord_comp M N (haltWeight_scaled M N) Construction.donorIndex).const_mul
          (readScale_nonneg M N) 2))

lemma potential_decomposition (M : Machine) (N n : ℕ) (x : Space) :
    Spatial.cutoff x * Spatial.shearPotential (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 (LocalRule.write M N n) (LocalRule.signal M N n) x =
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) * fixedPotential n x +
      Scales.ε M.base N (n + 1) * corePotential M N n x := by
  unfold Spatial.shearPotential LocalRule.signal fixedPotential corePotential
  rw [write_factor]
  ring

lemma potential_bound (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (fun x => Spatial.cutoff x *
      Spatial.shearPotential (Construction.donorIndex n) (Construction.receiverIndex n) 0
        (LocalRule.write M N n) (LocalRule.signal M N n) x) x‖ ≤
        C * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ r) := by
  obtain ⟨A, hA, ha⟩ := fixedPotential_scaled.2 r
  obtain ⟨B, hB, hb⟩ := (corePotential_scaled M N).2 r
  refine ⟨A + B, add_nonneg hA hB, fun n x => ?_⟩
  have hε : 0 ≤ Scales.ε M.base N (n + 1) := Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)
  have hε' : Scales.ε M.base N (n + 1) ≤ Scales.ε M.base N n :=
    (Scales.ε_strictAnti M.base N (by have := M.base_ge_four; omega)).antitone (by omega)
  have h₁ := fixedPotential_scaled.1 n
  have h₂ := (corePotential_scaled M N).1 n
  simp_rw [potential_decomposition]
  change ‖iteratedFDeriv ℝ r (fun x =>
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • fixedPotential n x +
      Scales.ε M.base N (n + 1) • corePotential M N n x) x‖ ≤ _
  have hs₁ : ContDiff ℝ ∞ (fun x =>
      (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • fixedPotential n x) := h₁.const_smul _
  have hs₂ : ContDiff ℝ ∞ (fun x =>
      Scales.ε M.base N (n + 1) • corePotential M N n x) := h₂.const_smul _
  rw [fun_iteratedFDeriv_add_apply
    (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hs₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply' (h₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (h₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hε'), abs_of_nonneg hε]
  have haa : ‖iteratedFDeriv ℝ r (fixedPotential n) x‖ ≤ A := by simpa using ha n x
  have hbb := hb n x
  have hscale := pow_nonneg (readScale_nonneg M N n) r
  calc
    _ ≤ Scales.ε M.base N n * A +
      Scales.ε M.base N (n + 1) * (B * readScale M N n ^ r) := by
      exact add_le_add
        (mul_le_mul (by linarith) haa (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_left hbb hε)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ Scales.ε M.base N n by linarith) hB,
      mul_nonneg hA (mul_nonneg hε hscale)]

theorem slot_estimate (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤
      C * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1)) := by
  obtain ⟨C, hC, hc⟩ := potential_bound M N (r + 1)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun n x => ?_⟩
  have h := norm_iterated_curl (Construction.receiverIndex n) 0 _
    (Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 _ _
      (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n))) r x
  exact h.trans (by nlinarith [hc n x])

lemma uniform_read_cost (M : Machine) (N r : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
    Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) ≤ D * Scales.ε M.base N n := by
  classical
  let q (n : ℕ) := Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) / Scales.ε M.base N n
  have hε (n : ℕ) : 0 < Scales.ε M.base N n :=
    Scales.ε_pos _ _ _ (by have := M.base_ge_four; omega)
  have hq (n : ℕ) : 0 ≤ q n := div_nonneg
    (mul_nonneg (hε _).le (pow_nonneg (readScale_nonneg M N n) _)) (hε _).le
  let D := 1 + ∑ n ∈ Finset.range r, q n
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hq n))
  refine ⟨D, zero_le_one.trans hD, fun n => ?_⟩
  by_cases hn : n < r
  · apply (div_le_iff₀ (hε n)).mp
    exact (Finset.single_le_sum (fun n _ => hq n) (Finset.mem_range.mpr hn)).trans
      (by dsimp [D]; linarith)
  · have h := Scales.derivative_cost_bound M.base N r n (by have := M.base_ge_four; omega)
      (by omega)
    have he : readScale M N n ^ (r + 1) =
        (M.base : ℝ) ^ ((r + 1) * (Scales.s N n + 1 + Scales.K N n)) := by
      rw [readScale, ← pow_mul, Nat.mul_comm]
    rw [he]
    exact h.trans (le_mul_of_one_le_left (hε n).le hD)

theorem slot_decay (M : Machine) (N r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤ C * Scales.ε M.base N n := by
  obtain ⟨C, hC, hc⟩ := slot_estimate M N r
  obtain ⟨D, hD, hd⟩ := uniform_read_cost M N r
  refine ⟨C * (1 + D), by positivity, fun n x => (hc n x).trans ?_⟩
  have := mul_le_mul_of_nonneg_left (hd n) hC
  nlinarith

def amplitude (M : Machine) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Scales.ε M.base N n

lemma amplitude_nonneg (M : Machine) (N n : ℕ) : 0 ≤ amplitude M N n := by
  cases n with
  | zero => exact zero_le_one
  | succ n => exact Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)

lemma weighted_amplitude_summable (M : Machine) (N J : ℕ) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ J * amplitude M N n) := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (amplitude_nonneg M N _)) _
    ((Scales.summable_weighted_ε M.base N J (by have := M.base_ge_four; omega)).mul_left ((2 : ℝ) ^ J))
  intro n
  simp only [amplitude, Nat.cast_add, Nat.cast_one]
  calc
    (1 + ((n : ℝ) + 1)) ^ J * Scales.ε M.base N n ≤
        (2 * (1 + (n : ℝ))) ^ J * Scales.ε M.base N n := by
      apply mul_le_mul_of_nonneg_right _ (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega))
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [mul_pow]; ring

lemma piece_decay (M : Machine) (w : List ℕ) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
    ‖iteratedFDeriv ℝ r (Construction.piece M w n) x‖ ≤ C * amplitude M w.length n := by
  have hload := compact_bounded (Construction.loading M w) (Construction.loading_smooth M w)
    (Spatial.box_compact.of_isClosed_subset isClosed_closure (Construction.piece_support M w 0))
  obtain ⟨A, hA, ha⟩ := hload.2 r
  obtain ⟨B, hB, hb⟩ := slot_decay M w.length r
  refine ⟨max A B, hA.trans (le_max_left _ _), fun n x => ?_⟩
  cases n with
  | zero =>
    change ‖iteratedFDeriv ℝ r (Construction.loading M w) x‖ ≤ max A B * 1
    simpa only [mul_one] using (ha x).trans (le_max_left A B)
  | succ n => exact (hb n x).trans (mul_le_mul_of_nonneg_right (le_max_right A B)
      (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)))

lemma pulse_bounded : BoundedJets Profiles.pulse := by
  apply compact_bounded _ Profiles.pulse_smooth
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ℝ)) (b := 1)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro t ht
  exact ⟨le_of_not_gt (fun h => ht (Profiles.pulse_zero_left t h.le)),
    le_of_not_gt (fun h => ht (Profiles.pulse_zero_right t h.le))⟩

def pulsePiece (M : Machine) (w : List ℕ) (n : ℕ) (z : ℝ × Space) : Space :=
  Profiles.pulse (z.1 - n) • Construction.piece M w n z.2

lemma pulsePiece_smooth (M : Machine) (w : List ℕ) (n : ℕ) :
    ContDiff ℝ ∞ (pulsePiece M w n) :=
  (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const)).fun_smul
    ((Construction.piece_smooth M w n).comp contDiff_snd)

lemma pulsePiece_decay (M : Machine) (w : List ℕ) (r : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n z,
    ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ ≤ C * amplitude M w.length n := by
  classical
  choose A hA ha using pulse_bounded.2
  choose B hB hb using piece_decay M w
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)),
    fun n z => ?_⟩
  have hp (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Profiles.pulse (z.1 - n)) z‖ ≤ A i := by
    apply (norm_comp_linear (fun t => Profiles.pulse (t - n))
      (Profiles.pulse_smooth.comp (contDiff_id.sub contDiff_const)) (ContinuousLinearMap.fst ℝ ℝ Space)
      i z).trans
    rw [iteratedFDeriv_comp_sub]
    have h₁ := ha i (z.1 - n)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (hA i)
  have hw (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Construction.piece M w n z.2) z‖ ≤
        B i * amplitude M w.length n := by
    apply (norm_comp_linear (Construction.piece M w n) (Construction.piece_smooth M w n)
      (ContinuousLinearMap.snd ℝ ℝ Space) i z).trans
    have h₁ := hb i n z.2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (hB i) (amplitude_nonneg M w.length n))
  apply (norm_iteratedFDeriv_smul_le
    (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const))
    ((Construction.piece_smooth M w n).comp contDiff_snd) z (WithTop.coe_le_coe.mpr le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * (B (r - i) * amplitude M w.length n) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hw (r - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
      exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    _ = C * amplitude M w.length n := by simp only [C, Finset.sum_mul, mul_assoc]

def RapidJets (f : ℝ × Space → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ J r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z, 0 ≤ z.1 → (1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r f z‖ ≤ C

lemma box_norm (x : Space) (hx : x ∈ Spatial.box) : ‖x‖ ≤ 9 := by
  have hi (i : Fin 3) : ‖x.ofLp i‖ ^ 2 ≤ 9 := by
    have := hx i
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (x i)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [← PiLp.norm_sq_eq_of_L2] at hsum
  norm_num at hsum
  nlinarith [norm_nonneg x]

lemma pulsePiece_support (M : Machine) (w : List ℕ) (n : ℕ) :
    tsupport (pulsePiece M w n) ⊆ Set.Icc (n : ℝ) (n + 1) ×ˢ Spatial.box := by
  apply closure_minimal _ (isClosed_Icc.prod Spatial.isClosed_box)
  intro z hz
  have h₁ : Profiles.pulse (z.1 - n) ≠ 0 := fun h => hz (by simp [pulsePiece, h])
  have h₂ : Construction.piece M w n z.2 ≠ 0 := fun h => hz (by simp [pulsePiece, h])
  refine ⟨⟨?_, ?_⟩, Construction.piece_support M w n (subset_closure h₂)⟩
  · exact le_of_not_gt (fun h => h₁ (Profiles.pulse_zero_left _ (by linarith)))
  · exact le_of_not_gt (fun h => h₁ (Profiles.pulse_zero_right _ (by linarith)))

lemma pulsePiece_weighted (M : Machine) (w : List ℕ) (J r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, 0 ≤ z.1 →
      (1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ ≤
        C * (1 + (n : ℝ)) ^ J * amplitude M w.length n := by
  obtain ⟨C, hC, hc⟩ := pulsePiece_decay M w r
  refine ⟨11 ^ J * C, by positivity, fun n z ht => ?_⟩
  by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ r (pulsePiece M w n))
  · have hsupport := pulsePiece_support M w n (tsupport_iteratedFDeriv_subset r hz)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hw : (1 + z.1 + ‖z.2‖) ^ J ≤ (11 * (1 + (n : ℝ))) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith [hsupport.1.2, box_norm z.2 hsupport.2]) _
    calc
      _ ≤ (11 * (1 + (n : ℝ))) ^ J * (C * amplitude M w.length n) :=
        mul_le_mul hw (hc n z) (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) (by positivity))
      (amplitude_nonneg M w.length n)

theorem velocity_rapidJets (M : Machine) (w : List ℕ) :
    RapidJets (Function.uncurry (Construction.velocity M w)) := by
  classical
  refine ⟨Construction.velocity_smooth M w, fun J r => ?_⟩
  obtain ⟨C, hC, hc⟩ := pulsePiece_weighted M w J r
  let a : ℕ → ℝ := fun n => C * ((1 + (n : ℝ)) ^ J * amplitude M w.length n)
  have has : Summable a := (weighted_amplitude_summable M w.length J).mul_left C
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg hC
    (mul_nonneg (by positivity) (amplitude_nonneg M w.length n))
  refine ⟨∑' n, a n, tsum_nonneg ha, fun z ht => ?_⟩
  obtain ⟨N, hN⟩ := TimeGlue.locally_eq_sum Profiles.pulse Profiles.pulse_zero_left
    (Construction.piece M w) z
  change Function.uncurry (Construction.velocity M w) =ᶠ[𝓝 z]
    (fun z => ∑ n ∈ Finset.range N, pulsePiece M w n z) at hN
  rw [(hN.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ => (pulsePiece_smooth M w n).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * ∑ n ∈ Finset.range N,
        ‖iteratedFDeriv ℝ r (pulsePiece M w n) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ∑ n ∈ Finset.range N, a n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n _
      simpa only [a, mul_assoc] using hc n z ht
    _ ≤ _ := has.sum_le_tsum _ (fun n _ => ha n)

lemma RapidJets.congr {f g : ℝ × Space → F} (hf : RapidJets f) (he : ∀ z, f z = g z) :
    RapidJets g := by rwa [← funext he]

lemma RapidJets.add {f g : ℝ × Space → F} (hf : RapidJets f) (hg : RapidJets g) :
    RapidJets (fun z => f z + g z) := by
  refine ⟨hf.1.add hg.1, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J r
  obtain ⟨B, hB, hb⟩ := hg.2 J r
  refine ⟨A + B, add_nonneg hA hB, fun z hz => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hf.1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hg.1.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J *
        (‖iteratedFDeriv ℝ r f z‖ + ‖iteratedFDeriv ℝ r g z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ A + B := by rw [mul_add]; exact add_le_add (ha z hz) (hb z hz)

lemma RapidJets.linear {f : ℝ × Space → F} (hf : RapidJets f) (L : F →L[ℝ] G) :
    RapidJets (L ∘ f) := by
  refine ⟨L.contDiff.comp hf.1, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J r
  refine ⟨‖L‖ * A, by positivity, fun z hz => ?_⟩
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * (‖L‖ * ‖iteratedFDeriv ℝ r f z‖) :=
      mul_le_mul_of_nonneg_left (norm_postcomp_linear f hf.1 L r z) (by positivity)
    _ = ‖L‖ * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ r f z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _)

lemma RapidJets.const_smul {f : ℝ × Space → F} (hf : RapidJets f) (a : ℝ) :
    RapidJets (fun z => a • f z) := hf.linear (a • ContinuousLinearMap.id ℝ F)

lemma RapidJets.sub {f g : ℝ × Space → F} (hf : RapidJets f) (hg : RapidJets g) :
    RapidJets (fun z => f z - g z) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.const_smul (-1))

lemma RapidJets.zero : RapidJets (fun _ : ℝ × Space => (0 : F)) := by
  refine ⟨contDiff_const, fun J r => ⟨0, le_rfl, fun z _ => ?_⟩⟩
  simp

lemma RapidJets.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × Space → F)
    (hf : ∀ i ∈ s, RapidJets (f i)) : RapidJets (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RapidJets.zero : RapidJets (fun _ => (0 : F)))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma RapidJets.directional {f : ℝ × Space → F} (hf : RapidJets f) (v : ℝ × Space) :
    RapidJets (fun z => fderiv ℝ f z v) := by
  refine ⟨(hf.1.fderiv_right (by simp)).clm_apply contDiff_const, fun J r => ?_⟩
  obtain ⟨A, hA, ha⟩ := hf.2 J (r + 1)
  refine ⟨‖v‖ * A, by positivity, fun z hz => ?_⟩
  calc
    _ ≤ (1 + z.1 + ‖z.2‖) ^ J * (‖v‖ * ‖iteratedFDeriv ℝ (r + 1) f z‖) :=
      mul_le_mul_of_nonneg_left (norm_directional_iterated f hf.1 v r z) (by positivity)
    _ = ‖v‖ * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ (r + 1) f z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ha z hz) (norm_nonneg _)

lemma dx_eq_full_directional (F : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Fin 3) (z : ℝ × Space) :
    dx i F z.1 z.2 = fderiv ℝ (Function.uncurry F) z (0, e i) := by
  have h₁ : HasFDerivAt (fun x : Space => (z.1, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hh := (hf.differentiable (by simp) (z.1,z.2)).hasFDerivAt.comp z.2 h₁
  have he := hh.fderiv
  change fderiv ℝ (F z.1) z.2 = _ at he
  rw [dx, he]
  simp

lemma fullDt_eq_full_directional (F : Field E) (hf : ContDiff ℝ ∞ (Function.uncurry F))
    (z : ℝ × Space) :
    Analytic.fullDt F z.1 z.2 = fderiv ℝ (Function.uncurry F) z (1, 0) := by
  have h₁ : HasFDerivAt (fun t : ℝ => (t, z.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] Space)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hh := (hf.differentiable (by simp) (z.1,z.2)).hasFDerivAt.comp z.1 h₁
  have he := hh.fderiv
  change fderiv ℝ (fun t => F t z.2) z.1 = _ at he
  rw [Analytic.fullDt, he]
  simp

lemma RapidJets.dx {f : Field F} (hf : RapidJets (Function.uncurry f)) (i : Fin 3) :
    RapidJets (Function.uncurry (dx i f)) :=
  (hf.directional (0, e i)).congr (fun z => (dx_eq_full_directional f hf.1 i z).symm)

lemma RapidJets.fullDt {f : Field F} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (Analytic.fullDt f)) :=
  (hf.directional (1, 0)).congr (fun z => (fullDt_eq_full_directional f hf.1 z).symm)

lemma RapidJets.smul {f : ℝ × Space → ℝ} {g : ℝ × Space → F}
    (hf : RapidJets f) (hg : RapidJets g) : RapidJets (fun z => f z • g z) := by
  classical
  refine ⟨hf.1.fun_smul hg.1, fun J r => ?_⟩
  choose A hA ha using hf.2 J
  choose B hB hb using hg.2 0
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * A i * B (r - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _)),
    fun z hz => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hf.1 hg.1 z
    (WithTop.coe_le_coe.mpr le_top)) (pow_nonneg (by positivity) J)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = (r.choose i : ℝ) * ((1 + z.1 + ‖z.2‖) ^ J * ‖iteratedFDeriv ℝ i f z‖) *
        ‖iteratedFDeriv ℝ (r - i) g z‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (ha i z hz) (Nat.cast_nonneg _))
      (by simpa using hb (r - i) z hz) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hA i))

lemma advection_eq_sum (u : Velocity) (t : ℝ) (x : Space) :
    advection u t x = ∑ i : Fin 3, (u t x i) • dx i u t x := by
  have he (v : Space) : v = ∑ i : Fin 3, v i • e i := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  conv_lhs => unfold advection; rw [he (u t x)]
  simp only [map_sum, map_smul, dx]

lemma RapidJets.advection {f : Velocity} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (advection f)) := by
  have h : ∀ i : Fin 3, RapidJets (fun z : ℝ × Space => f z.1 z.2 i • AlternatingNS.dx i f z.1 z.2) :=
    fun i => (hf.linear (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i)).smul (hf.dx i)
  exact (RapidJets.sum Finset.univ _ (fun i _ => h i)).congr
    (fun z => (advection_eq_sum f z.1 z.2).symm)

lemma RapidJets.laplacian {f : Velocity} (hf : RapidJets (Function.uncurry f)) :
    RapidJets (Function.uncurry (laplacian f)) :=
  RapidJets.sum Finset.univ _ (fun i _ => (hf.dx i).dx i)

lemma RapidJets.fullResidual {f : Velocity} (hf : RapidJets (Function.uncurry f)) (ν : ℝ) :
    RapidJets (fun z : ℝ × Space => Analytic.fullDt f z.1 z.2 + AlternatingNS.advection f z.1 z.2 -
      ν • AlternatingNS.laplacian f z.1 z.2) :=
  (hf.fullDt.add hf.advection).sub (hf.laplacian.const_smul ν)

def HalfEq (f g : Field F) : Prop := ∀ t, 0 ≤ t → ∀ x, f t x = g t x

lemma HalfEq.dx {f g : Field F} (h : HalfEq f g) (i : Fin 3) : HalfEq (dx i f) (dx i g) := by
  intro t ht x
  have he : f t = g t := funext (h t ht)
  simp only [AlternatingNS.dx, he]

lemma HalfEq.dt {f g : Field F} (h : HalfEq f g) : HalfEq (dt f) (dt g) := by
  intro t ht x
  exact congrArg (fun L : ℝ →L[ℝ] F => L 1)
    (fderivWithin_congr (fun u hu => h u hu x) (h t ht x))

lemma HalfEq.spatial {f g : Field F} (h : HalfEq f g) (α : MultiIndex) :
    HalfEq (spatial α f) (spatial α g) := by
  have hi (i : Fin 3) (n : ℕ) {u v : Field F} (hv : HalfEq u v) :
      HalfEq ((AlternatingNS.dx i)^[n] u) ((AlternatingNS.dx i)^[n] v) := by
    induction n with
    | zero => exact hv
    | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using ih.dx i
  exact hi 0 (α 0) (hi 1 (α 1) (hi 2 (α 2) h))

lemma HalfEq.mixed {f g : Field F} (h : HalfEq f g) (l : ℕ) (α : MultiIndex) :
    HalfEq (mixed l α f) (mixed l α g) := by
  induction l with
  | zero => exact h.spatial α
  | succ l ih => simpa only [AlternatingNS.mixed, Function.iterate_succ_apply'] using ih.dt

lemma RapidJets.spatial {f : Field F} (hf : RapidJets (Function.uncurry f)) (α : MultiIndex) :
    RapidJets (Function.uncurry (spatial α f)) := by
  have hi (i : Fin 3) (n : ℕ) {u : Field F} (hu : RapidJets (Function.uncurry u)) :
      RapidJets (Function.uncurry ((AlternatingNS.dx i)^[n] u)) := by
    induction n with
    | zero => exact hu
    | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.dx i
  exact hi 0 (α 0) (hi 1 (α 1) (hi 2 (α 2) hf))

lemma fullDt_iterate {f : Field F} (hf : RapidJets (Function.uncurry f)) (l : ℕ) :
    RapidJets (Function.uncurry (Analytic.fullDt^[l] f)) ∧
      HalfEq (dt^[l] f) (Analytic.fullDt^[l] f) := by
  induction l with
  | zero => exact ⟨hf, fun _ _ _ => rfl⟩
  | succ l ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨ih.1.fullDt, fun t ht x => ?_⟩
    exact (ih.2.dt t ht x).trans (Analytic.dt_eq_full _ ih.1.1 t ht x)

lemma RapidJets.rapid {f : Velocity} (hf : RapidJets (Function.uncurry f)) : Rapid f := by
  intro J l α
  obtain ⟨hG, he⟩ := fullDt_iterate (hf.spatial α) l
  obtain ⟨C, hC, hc⟩ := hG.2 J 0
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [show mixed l α f t x = (Analytic.fullDt^[l] (AlternatingNS.spatial α f)) t x from he t ht x]
  simpa only [norm_iteratedFDeriv_zero, Function.uncurry] using hc (t, x) ht

lemma Rapid.congr_half {f g : Velocity} (hf : Rapid f) (h : HalfEq f g) : Rapid g := by
  intro J l α
  obtain ⟨C, hC, hc⟩ := hf J l α
  refine ⟨C, hC, fun t ht x => ?_⟩
  rw [← h.mixed l α t ht x]
  exact hc t ht x

theorem velocity_rapid (M : Machine) (w : List ℕ) : Rapid (Construction.velocity M w) :=
  (velocity_rapidJets M w).rapid

theorem force_rapid (ν : ℝ) (M : Machine) (w : List ℕ) : Rapid (Construction.force ν M w) := by
  have hf := velocity_rapidJets M w
  have hR : Rapid (fun t x => Analytic.fullDt (Construction.velocity M w) t x +
      advection (Construction.velocity M w) t x - ν • laplacian (Construction.velocity M w) t x) :=
    RapidJets.rapid (f := fun t x => Analytic.fullDt (Construction.velocity M w) t x +
      advection (Construction.velocity M w) t x - ν • laplacian (Construction.velocity M w) t x)
      (hf.fullResidual ν)
  apply Rapid.congr_half hR
  intro t ht x
  simp only [Construction.force, residual]
  rw [Analytic.dt_eq_full _ hf.1 t ht x]

end
end Bounds
end AlternatingNS

end OAI


