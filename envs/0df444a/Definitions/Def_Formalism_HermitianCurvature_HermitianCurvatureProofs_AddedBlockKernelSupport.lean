-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:20.995045+00:00
-- url     : https://prove2.me/theorems/8b814721-b63f-4406-8bb9-bef8d75617b5
-- title:
--   Added Block Kernel Support
-- statement:
--   Definitions and structural lemmas for Added Block Kernel Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AddedBlockKernelSupport.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x7
section Supp
variable {K : Type} [CommRing K] (R : Subring K)
end Supp
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Ones
variable {K : Type} [CommRing K] (R : Subring K)
def cos1 (w : Point K) : Cos R w := (Quotient.mk _ 1, QuotientGroup.mk 1)
end Ones
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Padic
variable (p : ℕ) [hp : Fact p.Prime]
def InS (r : ℚ) : Prop := ∃ (k : ℕ) (b : ℤ), (p : ℚ) ^ k * r = b
theorem inS_add {r s : ℚ} (hr : InS p r) (hs : InS p s) : InS p (r + s) := by
  obtain ⟨k, a, hk⟩ := hr
  obtain ⟨l, b, hl⟩ := hs
  refine ⟨k + l, p ^ l * a + p ^ k * b, ?_⟩
  push_cast
  rw [← hk, ← hl]
  ring
theorem inS_neg {r : ℚ} (hr : InS p r) : InS p (-r) := by
  obtain ⟨k, b, hk⟩ := hr
  refine ⟨k, -b, ?_⟩
  push_cast
  rw [← hk]
  ring
theorem inS_int {r : ℚ} (hr : InS p r) (hn : ‖(r : ℚ_[p])‖ ≤ 1) : ∃ z : ℤ, r = z := by
  obtain ⟨k, b, hk⟩ := hr
  have e : ((b : ℤ) : ℚ_[p]) = (p : ℚ_[p]) ^ k * (r : ℚ_[p]) := by
    have h := congrArg (fun q : ℚ => (q : ℚ_[p])) hk
    push_cast at h
    exact h.symm
  have hb : ‖((b : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
    rw [e, norm_mul, Padic.norm_p_pow]
    exact mul_le_of_le_one_right (by positivity) hn
  obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd b k).1 hb
  refine ⟨c, ?_⟩
  have hp0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  apply mul_left_cancel₀ hp0
  rw [hk, hc]
  push_cast
  ring
theorem exists_approx (x : ℚ_[p]) : ∃ r : ℚ, InS p r ∧ ‖x - (r : ℚ_[p])‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  have hpm : ‖(p : ℚ_[p]) ^ m * x‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow, _root_.zpow_neg, zpow_natCast, inv_mul_le_iff₀ (by positivity),
      mul_one]
    exact hm.le
  let y : ℤ_[p] := ⟨(p : ℚ_[p]) ^ m * x, hpm⟩
  have hy : ‖y - ((y.appr m : ℕ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 (PadicInt.appr_spec m y)
  have hp0 : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hq : (p : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine ⟨((y.appr m : ℕ) : ℚ) / (p : ℚ) ^ m, ⟨m, (y.appr m : ℕ), ?_⟩, ?_⟩
  · rw [Int.cast_natCast]
    field_simp
  · have e : x - ((((y.appr m : ℕ) : ℚ) / (p : ℚ) ^ m : ℚ) : ℚ_[p])
        = ((p : ℚ_[p]) ^ m)⁻¹ * ((p : ℚ_[p]) ^ m * x - ((y.appr m : ℕ) : ℚ_[p])) := by
      push_cast
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul, div_eq_inv_mul]
    have hy' : ‖(p : ℚ_[p]) ^ m * x - ((y.appr m : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
      rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hy
    rw [e, norm_mul, norm_inv, Padic.norm_p_pow]
    calc ((p : ℝ) ^ (-(m : ℤ)))⁻¹ * ‖(p : ℚ_[p]) ^ m * x - ((y.appr m : ℕ) : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (-(m : ℤ)))⁻¹ * (p : ℝ) ^ (-(m : ℤ)) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
noncomputable def fr (x : ℚ_[p]) : ℚ := (exists_approx p x).choose
theorem fr_inS (x : ℚ_[p]) : InS p (fr p x) := (exists_approx p x).choose_spec.1
theorem fr_norm (x : ℚ_[p]) : ‖x - (fr p x : ℚ_[p])‖ ≤ 1 := (exists_approx p x).choose_spec.2
theorem exp_int (z : ℤ) (w : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * (w + z)) = Complex.exp (2 * Real.pi * Complex.I * w) := by
  rw [mul_add, Complex.exp_add]
  have h : Complex.exp (2 * Real.pi * Complex.I * z) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨z, by ring⟩
  rw [h, mul_one]
noncomputable def stdChar : AddChar ℚ_[p] ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * ((fr p x : ℚ) : ℂ))
  map_zero_eq_one' := by
    have h := fr_norm p 0
    rw [zero_sub, norm_neg] at h
    obtain ⟨z, hz⟩ := inS_int p (fr_inS p 0) h
    rw [hz, Complex.exp_eq_one_iff]
    exact ⟨z, by push_cast; ring⟩
  map_add_eq_mul' x y := by
    have hS : InS p (fr p (x + y) + (-(fr p x) + -(fr p y))) :=
      inS_add p (fr_inS p _) (inS_add p (inS_neg p (fr_inS p x)) (inS_neg p (fr_inS p y)))
    have hn : ‖((fr p (x + y) + (-(fr p x) + -(fr p y)) : ℚ) : ℚ_[p])‖ ≤ 1 := by
      have e : ((fr p (x + y) + (-(fr p x) + -(fr p y)) : ℚ) : ℚ_[p])
          = (-(x + y - (fr p (x + y) : ℚ_[p])) + (x - (fr p x : ℚ_[p]))) + (y - (fr p y : ℚ_[p])) := by
        push_cast; ring
      rw [e]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (fr_norm p y))
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (fr_norm p x))
      rw [norm_neg]; exact fr_norm p _
    obtain ⟨z, hz⟩ := inS_int p hS hn
    have e : ((fr p (x + y) : ℚ) : ℂ) = (((fr p x : ℚ) : ℂ) + ((fr p y : ℚ) : ℂ)) + (z : ℂ) := by
      have : fr p (x + y) = fr p x + fr p y + z := by linarith
      rw [this]; push_cast; ring
    rw [e, exp_int, mul_add, Complex.exp_add]
end Padic
end Formalism.FourierDecayAlt.P.A5x7


