-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:31.837978+00:00
-- url     : https://prove2.me/theorems/64b0b685-50c6-4f81-be7e-5fc302bd99db
-- title:
--   Sqrt Neg Disc Mem Coeff Field
-- statement:
--   Definitions and structural lemmas for Sqrt Neg Disc Mem Coeff Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/SqrtNegDiscMemCoeffField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField in

theorem _root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n) n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  exact Complex.isPrimitiveRoot_exp n hn.ne'
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

lemma _root_.GlobalTheory.HostModel.zeta_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n * m) ^ m = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.zeta_mem_coeff_of_dvd {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) {a : ℕ} (h : a ∣ l.M') : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta a ∈ c.F := by
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (_root_.GlobalTheory.LevelExist.M'_pos l) h
  rw [hk]
  exact pow_mem c.zeta_mem k
theorem zeta_M_mem_coeff {l : Level H} (c : Coeff l) : zeta l.M ∈ c.F :=
  zeta_mem_coeff_of_dvd c (Nat.dvd_lcm_left l.M l.A)
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.zeta_A_mem_coeff {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta l.A ∈ c.F :=
  _root_.GlobalTheory.HostModel.zeta_mem_coeff_of_dvd c (by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M'; exact Nat.dvd_lcm_right _ _)
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} in

theorem _root_.GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) : H.rt0 ∈ c.F := by
  apply c.le
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA
  exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
def coeff (l : Level H) : Coeff l := LevelExist.minCoeff l
example : zeta 4 = Complex.I := by
  unfold zeta
  rw [show (2 * Real.pi * Complex.I / (4 : ℕ) : ℂ) = Real.pi / 2 * Complex.I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I
example : zeta 6 ^ 3 = -1 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, zeta_mul_pow two_pos three_pos]
  exact (isPrimitiveRoot_zeta two_pos).eq_neg_one_of_two_right
example (l : Level H) : (coeff l).F ≠ ⊥ := by
  intro h
  have hm := sqrtNegDisc_mem_coeffField (coeff l)
  rw [h, IntermediateField.mem_bot] at hm
  obtain ⟨q, hq⟩ := hm
  have h2 := H.sqrt_neg_disc_sq
  rw [← hq] at h2
  have h3 : q ^ 2 = -(H.d : ℚ) := by
    apply (algebraMap ℚ ℂ).injective
    simpa using h2
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg q]
example (l : Level H) : (coeff l).F ≠ ⊤ := by
  intro h
  haveI := (coeff l).fin
  have hc : Countable (coeff l).F := (Module.finBasis ℚ (coeff l).F).equivFun.injective.countable
  rw [h] at hc
  haveI : Countable ℂ := (IntermediateField.topEquiv (F := ℚ) (E := ℂ)).symm.injective.countable
  exact not_countable (Complex.ofReal_injective.countable)
example (H : Host E) : zeta (H.d + 4) ∈ (coeff (level H 5 (by norm_num))).F ∧
    zeta 5 ∈ (coeff (level H 5 (by norm_num))).F :=
  ⟨zeta_M_mem_coeff _, zeta_A_mem_coeff _⟩
end GlobalTheory.HostModel


