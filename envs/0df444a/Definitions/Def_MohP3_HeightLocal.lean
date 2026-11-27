-- Prove2me | Definitions.Def_MohP3_HeightLocal
-- name    : MohP3_HeightLocal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:29:02.158189+00:00
-- url     : https://prove2.me/theorems/da92ed2d-8062-4dbf-abb4-b959e7640fde
-- title:
--   Height Local
-- statement:
--   Definitions and structural lemmas for Height Local, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPowerSeries
namespace MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
def bb : Fin 3 → MvPowerSeries (Fin 2) k :=
  ![X 0, (X 1)^4, (X 1)^5]
omit [CharZero k] in
lemma hasSubst_bb : MvPowerSeries.HasSubst (bb k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s <;> simp [bb]
def sigmaS : Sk k →ₐ[k] MvPowerSeries (Fin 2) k :=
  MvPowerSeries.substAlgHom (hasSubst_bb k)
omit [CharZero k] in
@[simp] lemma sigmaS_xs : sigmaS k (xs k) = X 0 := by
  rw [sigmaS, xs, MvPowerSeries.substAlgHom_X]; simp [bb]
omit [CharZero k] in
@[simp] lemma sigmaS_ys : sigmaS k (ys k) = (X 1 : MvPowerSeries (Fin 2) k)^4 := by
  rw [sigmaS, ys, MvPowerSeries.substAlgHom_X]; simp [bb]
omit [CharZero k] in
@[simp] lemma sigmaS_zs : sigmaS k (zs k) = (X 1 : MvPowerSeries (Fin 2) k)^5 := by
  rw [sigmaS, zs, MvPowerSeries.substAlgHom_X]; simp [bb]
def cc : Fin 2 → PowerSeries k :=
  ![PowerSeries.X^6 + PowerSeries.X^31, PowerSeries.X^2]
omit [CharZero k] in
lemma hasSubst_cc : MvPowerSeries.HasSubst (cc k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    PowerSeries.constantCoeff_X
  fin_cases s <;> simp [cc, hX]
def tauS : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPowerSeries.substAlgHom (hasSubst_cc k)
def Psurfk : Ideal (Sk k) := RingHom.ker (sigmaS k)
instance : IsDomain (MvPowerSeries (Fin 2) k) := NoZeroDivisors.to_isDomain _
def chiS : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPowerSeries.substAlgHom (a := ![PowerSeries.X, PowerSeries.X])
    (by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro s
      have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
        PowerSeries.constantCoeff_X
      fin_cases s <;> simpa using hX)
end MohP3.FormalLocal


