-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:28.172163+00:00
-- url     : https://prove2.me/theorems/e9c33a98-3c04-49a1-99be-af04067fe4f8
-- title:
--   Char Eq One Of Op ENe Zero
-- statement:
--   Definitions and structural lemmas for Char Eq One Of Op ENe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
namespace GlobalTheory.RootEx.Supp
section Bounds
variable {k : Type} [Field k] [ValuativeRel k]
def Bd {ι κ : Type} (γ : ValueGroupWithZero k) (x : Matrix ι κ k) : Prop := ∀ r s, valuation k (x r s) ≤ γ
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Bounds
section Levi
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
def diagPart (lv : ι → ℕ) (b : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if lv r = lv s then b r s else 0
theorem mul_diagPart_apply {lv : ι → ℕ} {b b' : Matrix ι ι k} (hb : b.BlockTriangular lv)
    (hb' : b'.BlockTriangular lv) {r s : ι} (h : lv s ≤ lv r) :
    (b * diagPart lv b') r s = (b * b') r s := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [diagPart, Matrix.of_apply]
  split_ifs with h1
  · rfl
  · rcases lt_or_gt_of_ne h1 with h2 | h2
    · rw [hb (h2.trans_le h)]; simp
    · rw [hb' h2]
theorem diagPart_mul {lv : ι → ℕ} {b b' : Matrix ι ι k} (hb : b.BlockTriangular lv)
    (hb' : b'.BlockTriangular lv) (h1 : b * b' = 1) : diagPart lv b * diagPart lv b' = 1 := by
  ext r s
  by_cases h : lv r = lv s
  · rw [← h1, ← mul_diagPart_apply hb hb' h.ge, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [diagPart, Matrix.of_apply]
    by_cases h2 : lv t = lv s
    · simp [h, h2]
    · simp [h2]
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e])), Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [diagPart, Matrix.of_apply]
    by_cases h2 : lv t = lv s
    · simp [h, h2]
    · simp [h2]
theorem inv_blockTriangular {lv : ι → ℕ} {b : GL ι k} (hb : b.val.BlockTriangular lv) :
    (b⁻¹).val.BlockTriangular lv := by
  rw [Matrix.coe_units_inv]
  letI := b.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hb
def levi (lv : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular lv) : GL ι k :=
  ⟨diagPart lv b.val, diagPart lv (b⁻¹).val, diagPart_mul hb (inv_blockTriangular hb) b.mul_inv,
    diagPart_mul (inv_blockTriangular hb) hb b.inv_mul⟩
end Levi
end GlobalTheory.RootEx.Supp
namespace GlobalTheory.RootEx
open Supp
end GlobalTheory.RootEx


