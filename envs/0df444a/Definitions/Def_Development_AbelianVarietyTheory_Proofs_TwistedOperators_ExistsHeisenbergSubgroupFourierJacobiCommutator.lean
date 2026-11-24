-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:02.092714+00:00
-- url     : https://prove2.me/theorems/0bd7539c-1df8-4fab-a8f6-eebbc7d734d6
-- title:
--   Exists Heisenberg Subgroup Fourier Jacobi Commutator
-- statement:
--   Definitions and structural lemmas for Exists Heisenberg Subgroup Fourier Jacobi Commutator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsHeisenbergSubgroupFourierJacobiCommutator.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colM_mul_rowM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup
section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
def zM (c p : ℕ) (t : k) : Matrix (Fin c) (Fin c) k :=
  Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0
def hM (c p : ℕ) (u β : n → k) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 (ExchangeSupport.colM c (p + 1) β) (ExchangeSupport.rowM c p u) (1 + zM c p t)
theorem zM_add (s t : k) : zM c p (s + t) = zM c p s + zM c p t := by
  ext l i
  simp only [zM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp
theorem zM_zero : zM c p (0 : k) = 0 := by
  ext l i
  simp [zM]
theorem zM_mul (s t : k) : zM c p s * zM c p t = 0 := by
  ext l i
  simp only [Matrix.mul_apply, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp
omit [Fintype n] [DecidableEq n] in
theorem col_mul_zM (β : n → k) (t : k) : ExchangeSupport.colM c (p + 1) β * zM c p t = 0 := by
  ext r i
  simp only [Matrix.mul_apply, ExchangeSupport.colM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp
omit [Fintype n] [DecidableEq n] in
theorem zM_mul_row (u : n → k) (t : k) : zM c p t * ExchangeSupport.rowM c p u = 0 := by
  ext l s
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp
omit [DecidableEq n] in
theorem row_mul_col (u β : n → k) :
    ExchangeSupport.rowM c p u * ExchangeSupport.colM c (p + 1) β = zM c p (u ⬝ᵥ β) := by
  ext l i
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, ExchangeSupport.colM, zM, Matrix.of_apply]
  by_cases hl : l.val + 1 = p <;> by_cases hi : i.val + 1 = p + 1 <;> simp [hl, hi, dotProduct]
omit [Fintype n] [DecidableEq n] in
theorem row_add (u w : n → k) : ExchangeSupport.rowM c p (u + w) =
    ExchangeSupport.rowM c p u + ExchangeSupport.rowM c p w := by
  ext l s
  simp only [ExchangeSupport.rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp
omit [Fintype n] [DecidableEq n] in
theorem col_add (u w : n → k) : ExchangeSupport.colM c p (u + w) =
    ExchangeSupport.colM c p u + ExchangeSupport.colM c p w := by
  ext r i
  simp only [ExchangeSupport.colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp
omit [Fintype n] [DecidableEq n] in
theorem row_zero : ExchangeSupport.rowM c p (0 : n → k) = 0 := by
  ext l s
  simp [ExchangeSupport.rowM]
omit [Fintype n] [DecidableEq n] in
theorem col_zero : ExchangeSupport.colM c p (0 : n → k) = 0 := by
  ext r i
  simp [ExchangeSupport.colM]
theorem hM_mul (u β u' β' : n → k) (t t' : k) :
    hM c p u β t * hM c p u' β' t' = hM c p (u + u') (β + β') (t + t' + u ⬝ᵥ β') := by
  simp only [hM, Matrix.fromBlocks_multiply]
  congr 1
  · rw [ExchangeSupport.colM_mul_rowM, Matrix.one_mul, add_zero]
  · rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, col_mul_zM, add_zero, col_add]
    abel
  · rw [Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, zM_mul_row, add_zero, row_add]
  · rw [row_mul_col]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, zM_mul, zM_add]
    abel
omit [Fintype n] in
theorem hM_zero : hM c p (0 : n → k) 0 0 = 1 := by
  rw [hM, row_zero, col_zero, zM_zero, add_zero, Matrix.fromBlocks_one]
def Heisenberg₂ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | ∃ (u β : n → k) (t : k), g.val = hM c p u β t}
  one_mem' := ⟨0, 0, 0, hM_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨u, β, t, hg⟩ ⟨u', β', t', hh⟩
    exact ⟨_, _, _, by rw [Units.val_mul, hg, hh, hM_mul]⟩
  inv_mem' := by
    rintro g ⟨u, β, t, hg⟩
    refine ⟨-u, -β, u ⬝ᵥ β - t, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, hM_mul, ← hM_zero (p := p)]
    simp
end
end GlobalTheory.RootEx.HeisenbergSubgroup


