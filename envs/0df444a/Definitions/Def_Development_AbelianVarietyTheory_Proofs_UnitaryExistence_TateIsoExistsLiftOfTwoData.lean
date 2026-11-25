-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TateIsoExistsLiftOfTwoData
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TateIsoExistsLiftOfTwoData
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:40.061159+00:00
-- url     : https://prove2.me/theorems/ba8cad3b-f7d8-549f-810d-a8b5d5f0d5e3
-- title:
--   Tate Iso Exists Lift Of Two Data
-- statement:
--   Definitions and structural lemmas for Tate Iso Exists Lift Of Two Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TateIsoExistsLiftOfTwoData.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
end
noncomputable def expNegUnit (n : ℕ) : ℂˣ :=
  (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n)) (Complex.exp_ne_zero _))⁻¹
theorem expNegUnit_zpow_val (n : ℕ) (j : ℤ) :
    ((expNegUnit n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expNegUnit, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg,
    ← Complex.exp_int_mul]
  congr 1
  ring
theorem expNegUnit_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expNegUnit n) n :=
  (IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')).inv
theorem expNegUnit_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expNegUnit (n * m) ^ m = expNegUnit n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [← zpow_natCast, expNegUnit_zpow_val, ← zpow_one (expNegUnit n), expNegUnit_zpow_val]
  congr 1
  push_cast
  field_simp
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) {i : Fin U.n}
  {P : (U.Di i).La →+ (Fin g → ℂ)}
theorem familyUnif_ex_nsmul (hP : IsPeriod (U.Di i) ty P) (n : ℕ) (z : Fin g → ℂ) :
    U.ex i P ((n : ℂ) • z) = U.ex i P z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (U.ex_ker i P hP 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, U.ex_add i P hP, ih, pow_succ]
noncomputable def familyUnifTateIso (hP : IsPeriod (U.Di i) ty P) :
    TateIso (U.Di i) ℂ (Over.mk (U.u i P) ⟶ Xo.univ.t.G) (fun a x => x ≫ Xo.univ.t.act.act a)
      (fun n x x' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := U.ex i P ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add, smul_add, U.ex_add i P hP]
  lin n c a := by
    rw [← U.ex_lin i P hP]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, hP.1]
    ring
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [U.ex_ker i P hP]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := U.ex_onto i P hP x
      rw [← familyUnif_ex_nsmul U hP, U.ex_ker i P hP] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      rw [← familyUnif_ex_nsmul U hP, smul_inv_smul₀ hn', U.ex_ker i P hP]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← familyUnif_ex_nsmul U hP, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := U.ex_weil i P hP n a b _ hn (expNegUnit_zpow_val n _)
end
end GlobalTheory


