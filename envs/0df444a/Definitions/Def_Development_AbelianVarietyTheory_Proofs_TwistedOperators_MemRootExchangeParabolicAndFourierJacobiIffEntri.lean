-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:23.506075+00:00
-- url     : https://prove2.me/theorems/57f734a2-c515-409d-a847-f0bfe4198298
-- title:
--   Mem Root Exchange Parabolic And Fourier Jacobi Iff Entri
-- statement:
--   Definitions and structural lemmas for Mem Root Exchange Parabolic And Fourier Jacobi Iff Entri, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemRootExchangeParabolicAndFourierJacobiIffEntri.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
namespace GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def Par (L : ℕ) (b : Fin c → ℕ) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r →
    M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
omit [Fintype n] in
theorem Par.blockTri {L : ℕ} {b : Fin c → ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M) :
    M.BlockTriangular (Sum.elim (fun _ => L) b) := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact lt_irrefl _ hrs
  rw [h r s _ hrs.le, Matrix.one_apply_ne hne]
  rcases r with r | r <;> rcases s with s | s <;> simp_all
theorem Par.mul_left {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hr : r.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M * M') r s = M' r s := by
  have : (M * M') r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b t) (Sum.elim (fun _ => L) b r) with ht | ht
    · rw [h r t (Or.inl hr) ht]
    · rw [h' (lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul]
theorem Par.mul_right {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hs : s.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M' * M) r s = M' r s := by
  have : (M' * M) r s = (M' * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b s) (Sum.elim (fun _ => L) b t) with ht | ht
    · rw [h t s (Or.inr hs) ht]
    · rw [h' (lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [this, Matrix.mul_one]
theorem Par.blockTri_inv {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (h : Par L b g.val) :
    (g⁻¹).val.BlockTriangular (Sum.elim (fun _ => L) b) := by
  letI : Invertible g.val := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri
def parGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) (b : Fin c → ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Par L b g.val}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh r s hor hrs
    rw [Units.val_mul]
    rcases hor with hr | hs
    · rw [Par.mul_left hg (Par.blockTri hh) hr hrs, hh r s (Or.inl hr) hrs]
    · rw [Par.mul_right hh (Par.blockTri hg) hs hrs, hg r s (Or.inr hs) hrs]
  inv_mem' := by
    intro g hg r s hor hrs
    rcases hor with hr | hs
    · rw [← Par.mul_left hg (Par.blockTri_inv hg) hr hrs, Units.mul_inv]
    · rw [← Par.mul_right hg (Par.blockTri_inv hg) hs hrs, Units.inv_mul]
end GlobalTheory.RootEx.ParabolicEntries


