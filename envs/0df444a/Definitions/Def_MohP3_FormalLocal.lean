-- Prove2me | Definitions.Def_MohP3_FormalLocal
-- name    : MohP3_FormalLocal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:53:06.641326+00:00
-- url     : https://prove2.me/theorems/5eb1573e-7389-431f-9192-fced437b9cb7
-- title:
--   Formal Local
-- statement:
--   Definitions and structural lemmas for Formal Local, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean

module
public import Definitions.Def_MohP3_Generic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPowerSeries
namespace MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
abbrev Sk := MvPowerSeries (Fin 3) k
def xs : Sk k := X 0
def ys : Sk k := X 1
def zs : Sk k := X 2
def Pk : Ideal (Sk k) := Gen.P (xs k) (ys k) (zs k)
def Qk : Ideal (Sk k) := Gen.Q (xs k) (ys k) (zs k)
def aa : Fin 3 → PowerSeries k :=
  ![PowerSeries.X^6 + PowerSeries.X^31, PowerSeries.X^8, PowerSeries.X^10]
omit [CharZero k] in
lemma hasSubst_aa : MvPowerSeries.HasSubst (aa k) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries k) = 0 :=
    PowerSeries.constantCoeff_X
  fin_cases s <;> simp [aa, hX]
def psi : Sk k →ₐ[k] PowerSeries k := MvPowerSeries.substAlgHom (hasSubst_aa k)
omit [CharZero k] in
@[simp] lemma psi_xs : psi k (xs k) = PowerSeries.X^6 + PowerSeries.X^31 := by
  rw [psi, xs, MvPowerSeries.substAlgHom_X]; simp [aa]
omit [CharZero k] in
@[simp] lemma psi_ys : psi k (ys k) = PowerSeries.X^8 := by
  rw [psi, ys, MvPowerSeries.substAlgHom_X]; simp [aa]
omit [CharZero k] in
@[simp] lemma psi_zs : psi k (zs k) = PowerSeries.X^10 := by
  rw [psi, zs, MvPowerSeries.substAlgHom_X]; simp [aa]
omit [CharZero k] in
lemma hasSubst_ys : PowerSeries.HasSubst (ys k) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (by simp [ys])
def iotaS : PowerSeries k →ₐ[k] Sk k := PowerSeries.substAlgHom (hasSubst_ys k)
def exp8 : PowerSeries k →ₐ[k] PowerSeries k := PowerSeries.expand 8 (by norm_num)
def hhS : Fin 8 → Sk k :=
  ![1, xs k, zs k, (xs k)^2, xs k * zs k - (ys k)^2, (xs k)^3 - ys k * zs k,
    (zs k)^2 - ys k * (xs k)^2, (xs k)^2 * zs k - (ys k)^2 * xs k - (ys k)^9]
def vvS : Fin 8 → PowerSeries k :=
  ![1,
    PowerSeries.X^6*(1+PowerSeries.X^25),
    PowerSeries.X^10,
    PowerSeries.X^12*(1+2*PowerSeries.X^25+PowerSeries.X^50),
    PowerSeries.X^41,
    PowerSeries.X^43*(3+3*PowerSeries.X^25+PowerSeries.X^50),
    PowerSeries.X^45*(-2-PowerSeries.X^25),
    PowerSeries.X^47]
def ooS : Fin 8 → ℕ := ![0, 6, 10, 12, 41, 43, 45, 47]
def Generation : Prop :=
  ∀ F : Sk k, ∃ p : Fin 8 → PowerSeries k, F - ∑ i, iotaS k (p i) * hhS k i ∈ Pk k
end MohP3.FormalLocal


