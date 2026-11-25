-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
-- name    : GroundTheory_LocalFields_LocalFourierPadic
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:22:11.463813+00:00
-- url     : https://prove2.me/theorems/fa7f4f7b-e2a4-59bc-890a-a4b194a5606c
-- title:
--   Local Fourier Padic
-- statement:
--   Definitions and structural lemmas for Local Fourier Padic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
section DifferentNorm
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
end DifferentNorm
namespace Padic
variable (p : ℕ) [hp : Fact p.Prime]
theorem mem_integer_iff_norm_le_one (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation ℚ_[p]), ← Valuation.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := _root_.Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]
def padicIntRingEquivInteger : ℤ_[p] ≃+* 𝒪[ℚ_[p]] where
  toFun x := ⟨x, (mem_integer_iff_norm_le_one p x).mpr x.2⟩
  invFun y := ⟨y, (mem_integer_iff_norm_le_one p y).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
theorem fourierChar_intCast (n : ℤ) : Real.fourierChar (n : ℝ) = 1 := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  exact ⟨n, by ring⟩
theorem exists_int_of_norm_le_one {N : ℤ} {j : ℕ}
    (h : ‖(N : ℚ_[p]) / (p : ℚ_[p]) ^ j‖ ≤ 1) : ∃ n : ℤ, (N : ℚ) / (p : ℚ) ^ j = n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [norm_div, norm_pow, _root_.Padic.norm_p, div_le_one (pow_pos (inv_pos.mpr hp0) j)] at h
  have h' : ‖(N : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨n, hn⟩ := (_root_.Padic.norm_int_le_pow_iff_dvd N j).mp h'
  refine ⟨n, ?_⟩
  have : (p : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [hn, div_eq_iff this]
  push_cast
  ring
theorem exists_norm_sub_le_one (x : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 := by
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    refine ⟨x.valuation.natAbs, ?_⟩
    rw [norm_mul, norm_pow, _root_.Padic.norm_p, _root_.Padic.norm_eq_zpow_neg_valuation hx,
      inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
    omega
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k ⟨_, hk⟩)
  refine ⟨PadicInt.appr ⟨_, hk⟩ k, k, ?_⟩
  have hz' : (z : ℚ_[p]) * (p : ℚ_[p]) ^ k =
      (p : ℚ_[p]) ^ k * x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) := by
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] at this
    exact this
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ hpp
  have e : x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) / (p : ℚ_[p]) ^ k = (z : ℚ_[p]) := by
    have h2 : (x - (PadicInt.appr ⟨_, hk⟩ k : ℚ_[p]) / (p : ℚ_[p]) ^ k) * (p : ℚ_[p]) ^ k =
        (z : ℚ_[p]) * (p : ℚ_[p]) ^ k := by
      rw [sub_mul, div_mul_cancel₀ _ hpk, hz']
      ring
    exact mul_right_cancel₀ hpk h2
  push_cast
  rw [e]
  exact z.2
theorem fourierChar_eq_of_norm_sub_le_one {m m' : ℤ} {k k' : ℕ}
    (h : ‖(m : ℚ_[p]) / (p : ℚ_[p]) ^ k - (m' : ℚ_[p]) / (p : ℚ_[p]) ^ k'‖ ≤ 1) :
    Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) =
      Real.fourierChar (((m' : ℚ) / (p : ℚ) ^ k' : ℚ) : ℝ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : (m : ℚ_[p]) / (p : ℚ_[p]) ^ k - (m' : ℚ_[p]) / (p : ℚ_[p]) ^ k' =
      ((m * (p : ℤ) ^ k' - m' * (p : ℤ) ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + k') := by
    push_cast
    field_simp
    ring
  rw [e] at h
  obtain ⟨n, hn⟩ := exists_int_of_norm_le_one p h
  have e' : (m : ℚ) / (p : ℚ) ^ k = (m' : ℚ) / (p : ℚ) ^ k' + n := by
    rw [← hn]
    push_cast
    field_simp
    ring
  rw [e', Rat.cast_add, Rat.cast_intCast, AddChar.map_add_eq_mul, fourierChar_intCast, mul_one]
def fracRep (x : ℚ_[p]) : ℚ :=
  ((Classical.choose (exists_norm_sub_le_one p x) : ℤ) : ℚ) /
    (p : ℚ) ^ Classical.choose (Classical.choose_spec (exists_norm_sub_le_one p x))
theorem fracRep_spec (x : ℚ_[p]) : ∃ (m : ℤ) (k : ℕ), fracRep p x = (m : ℚ) / (p : ℚ) ^ k ∧
    ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1 :=
  ⟨_, _, rfl, Classical.choose_spec (Classical.choose_spec (exists_norm_sub_le_one p x))⟩
def stdCharFun (x : ℚ_[p]) : Circle := Real.fourierChar (fracRep p x : ℝ)
theorem stdCharFun_eq (x : ℚ_[p]) (m : ℤ) (k : ℕ)
    (h : ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) :
    stdCharFun p x = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) := by
  obtain ⟨m₀, k₀, e₀, h₀⟩ := fracRep_spec p x
  rw [stdCharFun, e₀]
  apply fourierChar_eq_of_norm_sub_le_one
  calc ‖(m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀ - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖
      = ‖(x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k) + -(x - (m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀)‖ := by
        congr 1
        ring
    _ ≤ max ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ‖-(x - (m₀ : ℚ_[p]) / (p : ℚ_[p]) ^ k₀)‖ :=
        _root_.Padic.nonarchimedean _ _
    _ ≤ 1 := max_le h (by rwa [norm_neg])
def stdChar : AddChar ℚ_[p] Circle where
  toFun := stdCharFun p
  map_zero_eq_one' := by
    rw [stdCharFun_eq p 0 0 0 (by simp)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨mx, kx, ex, hx⟩ := fracRep_spec p x
    obtain ⟨my, ky, ey, hy⟩ := fracRep_spec p y
    have hpp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hxy : ‖(x + y) - ((mx * (p : ℤ) ^ ky + my * (p : ℤ) ^ kx : ℤ) : ℚ_[p]) /
        (p : ℚ_[p]) ^ (kx + ky)‖ ≤ 1 := by
      have e : (x + y) - ((mx * (p : ℤ) ^ ky + my * (p : ℤ) ^ kx : ℤ) : ℚ_[p]) /
          (p : ℚ_[p]) ^ (kx + ky) = (x - (mx : ℚ_[p]) / (p : ℚ_[p]) ^ kx) +
            (y - (my : ℚ_[p]) / (p : ℚ_[p]) ^ ky) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (_root_.Padic.nonarchimedean _ _).trans (max_le hx hy)
    rw [stdCharFun_eq p _ _ _ hxy, stdCharFun_eq p _ _ _ hx, stdCharFun_eq p _ _ _ hy,
      ← AddChar.map_add_eq_mul, ← Rat.cast_add]
    congr 2
    push_cast
    field_simp
    ring
section Extension
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
def stdCharOf : AddChar K Circle := traceChar K (stdChar p)
variable [MeasurableSpace K] [BorelSpace K]
end Extension
end Padic
end GroundTheory.LocalField


