-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:35:07.955816+00:00
-- url     : https://prove2.me/theorems/540b7565-36b2-4f30-bcda-587a76736fe7
-- title:
--   Logarithmic Residue
-- statement:
--   Definitions and structural lemmas for Logarithmic Residue, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Local/LogarithmicResidue.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
namespace Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
noncomputable def logarithmicDifferentialMonoidHom :
    Fˣ →* Multiplicative (Differential k F) where
  toFun f := Multiplicative.ofAdd
    (logarithmicDifferential (k := k) (F := F) (f : F))
  map_one' := by
    simp only [logarithmicDifferential, Units.val_one, inv_one, one_smul]
    rw [← map_one (algebraMap k F), differential_algebraMap]
    rfl
  map_mul' f g := by
    exact congrArg Multiplicative.ofAdd
      (logarithmicDifferential_mul (k := k) (F := F) (f : F) (g : F)
        f.ne_zero g.ne_zero)
theorem logarithmicDifferential_zpow (f : Fˣ) (n : ℤ) :
    logarithmicDifferential (k := k) (F := F) ((f ^ n : Fˣ) : F) =
      n • logarithmicDifferential (k := k) (F := F) (f : F) := by
  have h := (logarithmicDifferentialMonoidHom (k := k) (F := F)).map_zpow f n
  exact h
theorem localParameterPower_valuation (P : GlobalPlace k F) (n : ℤ) :
    P.valuation (localParameterPower P n) = WithZero.exp (-n) := by
  rw [localParameterPower, Units.val_zpow_eq_zpow_val, map_zpow₀,
    localParameterUnit, Units.val_mk0, localParameter, P.valuation_uniformizer,
    ← WithZero.exp_zsmul]
  congr 1
  simp
theorem exists_unit_mul_localParameterPower_eq
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    ∃ u : P.valuationRingˣ,
      (u : F) * localParameterPower P (P.order f) = f := by
  let t : F := localParameterPower P (P.order f)
  have ht : t ≠ 0 := by
    exact Units.ne_zero _
  have hvaluation :
      P.valuation f = P.valuation t := by
    calc
      P.valuation f = WithZero.exp (WithZero.log (P.valuation f)) :=
        (WithZero.exp_log ((P.valuation).ne_zero_iff.mpr hf)).symm
      _ = WithZero.exp (-P.order f) := by simp [GlobalPlace.order]
      _ = P.valuation t :=
        (localParameterPower_valuation (k := k) (F := F) P (P.order f)).symm
  let q : Fˣ := Units.mk0 (f * t⁻¹) (mul_ne_zero hf (inv_ne_zero ht))
  have hqvaluation : P.valuation (q : F) = 1 := by
    change P.valuation (f * t⁻¹) = 1
    rw [map_mul, map_inv₀, hvaluation, mul_inv_cancel₀]
    exact (P.valuation).ne_zero_iff.mpr ht
  have hqmem : q ∈ P.valuationRing.unitGroup :=
    (Valuation.mem_unitGroup_iff F P.valuation q).mpr hqvaluation
  let u : P.valuationRingˣ := P.valuationRing.unitGroupMulEquiv ⟨q, hqmem⟩
  refine ⟨u, ?_⟩
  change (q : F) * t = f
  simp only [q, Units.val_mk0]
  field_simp [ht]
theorem logarithmicDifferential_eq_unit_add_order_smul
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    ∃ u : P.valuationRingˣ,
      logarithmicDifferential (k := k) (F := F) f =
        logarithmicDifferential (k := k) (F := F) (u : F) +
          P.order f • logarithmicDifferential (k := k) (F := F)
            (P.uniformizerInValuationRing : F) := by
  obtain ⟨u, hu⟩ := exists_unit_mul_localParameterPower_eq
    (k := k) (F := F) P f hf
  refine ⟨u, ?_⟩
  have hu_ne : (u : F) ≠ 0 := by
    intro hzero
    apply u.ne_zero
    apply Subtype.ext
    exact hzero
  have ht_ne : localParameterPower P (P.order f) ≠ 0 := Units.ne_zero _
  calc
    logarithmicDifferential (k := k) (F := F) f =
        logarithmicDifferential (k := k) (F := F)
          ((u : F) * localParameterPower P (P.order f)) := by rw [hu]
    _ = logarithmicDifferential (k := k) (F := F) (u : F) +
          logarithmicDifferential (k := k) (F := F)
            (localParameterPower P (P.order f)) :=
      logarithmicDifferential_mul (k := k) (F := F) _ _ hu_ne ht_ne
    _ = logarithmicDifferential (k := k) (F := F) (u : F) +
          P.order f • logarithmicDifferential (k := k) (F := F)
            (P.uniformizerInValuationRing : F) := by
      congr 1
      exact logarithmicDifferential_zpow (k := k) (F := F)
        (localParameterUnit P) (P.order f)
theorem logarithmicDifferential_mem_simplePoleDifferentialLattice
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    logarithmicDifferential (k := k) (F := F) f ∈
      simplePoleDifferentialLattice P := by
  obtain ⟨u, hu⟩ := logarithmicDifferential_eq_unit_add_order_smul
    (k := k) (F := F) P f hf
  rw [hu]
  exact (simplePoleDifferentialLattice P).add_mem
    (localDifferentialLattice_le_simplePoleDifferentialLattice
      (k := k) (F := F) P
      (logarithmicDifferential_mem_localDifferentialLattice_of_unit
        (k := k) (F := F) P u))
    (AddSubgroup.zsmul_mem (simplePoleDifferentialLattice P).toAddSubgroup
      (uniformizerLogDifferential (k := k) (F := F) P).property (P.order f))
noncomputable def logarithmicDifferentialAtSimplePole
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleDifferentialLattice P :=
  ⟨logarithmicDifferential (k := k) (F := F) f,
    logarithmicDifferential_mem_simplePoleDifferentialLattice
      (k := k) (F := F) P f hf⟩
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


