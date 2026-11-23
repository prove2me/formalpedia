-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:14.287411+00:00
-- url     : https://prove2.me/theorems/7c3e16f4-0171-489b-9a69-92f942e9faa8
-- title:
--   Continuous Seminorm Diff SLe
-- statement:
--   Definitions and structural lemmas for Continuous Seminorm Diff SLe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSeminormDiffSLe.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
section Decay
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def diffFun (f : SchwartzMap V ℂ) (y : V) : V → ℂ := fun x => f (x + y) * conj (f x)
theorem contDiff_translate (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f (x + y)) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)
theorem contDiff_conj (f : SchwartzMap V ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => conj (f x)) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)
theorem contDiff_diffFun (f : SchwartzMap V ℂ) (y : V) :
    ContDiff ℝ (⊤ : ℕ∞) (diffFun f y) :=
  (contDiff_translate f y).mul (contDiff_conj f)
theorem norm_iteratedFDeriv_conj (f : SchwartzMap V ℂ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => conj (f x)) x‖ = ‖iteratedFDeriv ℝ i f x‖ :=
  Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) f x i
theorem peetre (x y : V) : 1 + ‖y‖ ≤ (1 + ‖x + y‖) * (1 + ‖x‖) := by
  have h : ‖y‖ ≤ ‖x + y‖ + ‖x‖ := by
    have := norm_sub_le (x + y) x
    simpa using this
  nlinarith [norm_nonneg (x + y), norm_nonneg x, mul_nonneg (norm_nonneg (x + y)) (norm_nonneg x)]
theorem diffFun_bound (f : SchwartzMap V ℂ) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : V,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K ≤ C := by
  set M : ℝ := 2 ^ (K + k) *
    ((Finset.Iic (K + k, n)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hM
  have hM0 : 0 ≤ M := by
    rw [hM]; exact mul_nonneg (by positivity) (apply_nonneg _ _)
  have hA : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ (K + k) * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + k, n)) le_rfl hi f z
  have hB : ∀ i, i ≤ n → ∀ z : V, (1 + ‖z‖) ^ K * ‖iteratedFDeriv ℝ i f z‖ ≤ M := by
    intro i hi z
    refine le_trans ?_ (hA i hi z)
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (Nat.le_add_right _ _)) (norm_nonneg _)
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M), by positivity, fun x y => ?_⟩
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (contDiff_translate f y) (contDiff_conj f) x (n := n) (by exact_mod_cast le_top)
  have hw : ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k) := by
    have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have h2 : (1 + ‖y‖) ^ K ≤ ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K :=
      pow_le_pow_left₀ (by positivity) (peetre x y) _
    calc ‖x‖ ^ k * (1 + ‖y‖) ^ K ≤ (1 + ‖x‖) ^ k * ((1 + ‖x + y‖) * (1 + ‖x‖)) ^ K := by
          gcongr
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hw0 : 0 ≤ ‖x‖ ^ k * (1 + ‖y‖) ^ K := by positivity
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ * (1 + ‖y‖) ^ K
      = (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ‖iteratedFDeriv ℝ n (diffFun f y) x‖ := by ring
    _ ≤ (‖x‖ ^ k * (1 + ‖y‖) ^ K) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => f (x + y)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun x => conj (f x)) x‖ :=
        mul_le_mul_of_nonneg_left hL hw0
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((‖x‖ ^ k * (1 + ‖y‖) ^ K) *
          (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_conj, iteratedFDeriv_comp_add_right]
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * M) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc _ ≤ ((1 + ‖x + y‖) ^ K * (1 + ‖x‖) ^ (K + k)) *
              (‖iteratedFDeriv ℝ i f (x + y)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) :=
              mul_le_mul_of_nonneg_right hw (by positivity)
          _ = ((1 + ‖x + y‖) ^ K * ‖iteratedFDeriv ℝ i f (x + y)‖) *
              ((1 + ‖x‖) ^ (K + k) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
          _ ≤ M * M := mul_le_mul (hB i hi' _) (hA _ (Nat.sub_le _ _) _)
              (by positivity) hM0
def diffS (f : SchwartzMap V ℂ) (y : V) : SchwartzMap V ℂ where
  toFun := diffFun f y
  smooth' := contDiff_diffFun f y
  decay' := by
    intro k n
    obtain ⟨C, -, hC⟩ := diffFun_bound f k n 0
    exact ⟨C, fun x => by simpa using hC x y⟩
end Decay
section Fourier
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ))
end Fourier
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl


