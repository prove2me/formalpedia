-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:37.437858+00:00
-- url     : https://prove2.me/theorems/77fb4858-b012-4b38-9d15-a2f1f3ebcb17
-- title:
--   Unitriangular Map Induction
-- statement:
--   Definitions and structural lemmas for Unitriangular Map Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitriangularMapInduction.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
namespace GlobalTheory.UnipChange
section Shear
variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]
end Shear
section Linear
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]
end Linear
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
section Algebra
variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}
variable (k b) in

def filt (t : ℕ) : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ∀ i j, ¬ b i + t ≤ b j → X i j = 0}
  add_mem' := by
    intro X Y hX hY i j h
    simp [hX i j h, hY i j h]
  zero_mem' := by intro i j _; rfl
  smul_mem' := by
    intro c X hX i j h
    simp [hX i j h]
theorem mul_mem_filt {s t : ℕ} {X Y : Matrix (Fin r) (Fin r) k} (hX : X ∈ filt k b s)
    (hY : Y ∈ filt k b t) : X * Y ∈ filt k b (s + t) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : b i + s ≤ b l
  · rw [hY l j (by omega), mul_zero]
  · rw [hX i l hl, zero_mul]
theorem mem_filt_zero {X : Matrix (Fin r) (Fin r) k} (h : X.BlockTriangular b) : X ∈ filt k b 0 :=
  fun _ _ hij => h (by omega)
theorem mem_filt_one {X : Matrix (Fin r) (Fin r) k} (h : X ∈ lieRadical k b) : X ∈ filt k b 1 :=
  fun i j hij => h i j (by omega)
theorem pow_mem_filt {X : Matrix (Fin r) (Fin r) k} (h : X ∈ filt k b 1) (n : ℕ) :
    X ^ n ∈ filt k b n := by
  induction n with
  | zero => rw [pow_zero]; exact mem_filt_zero Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact mul_mem_filt ih h
theorem pow_eq_zero {X : Matrix (Fin r) (Fin r) k} (h : X ∈ filt k b 1) :
    X ^ (Finset.univ.sup b + 1) = 0 := by
  ext i j
  refine pow_mem_filt h _ i j ?_
  have := Finset.le_sup (f := b) (Finset.mem_univ j)
  omega
def unip (X : lieRadical k b) : radical k b :=
  ⟨⟨1 + X, ∑ i ∈ Finset.range (Finset.univ.sup b + 1), (-(X : Matrix (Fin r) (Fin r) k)) ^ i,
    by
      rw [← sub_neg_eq_add, mul_neg_geom_sum, pow_eq_zero (neg_mem (mem_filt_one X.2)), sub_zero],
    by
      rw [← sub_neg_eq_add, geom_sum_mul_neg, pow_eq_zero (neg_mem (mem_filt_one X.2)), sub_zero]⟩,
    by
      show (1 + X : Matrix (Fin r) (Fin r) k) - 1 ∈ lieRadical k b
      simp⟩
def lg (n : radical k b) : lieRadical k b :=
  ⟨((n : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) - 1, n.2⟩
theorem lg_unip (X : lieRadical k b) : lg (unip X) = X := by
  apply Subtype.ext
  simp [lg, unip]
theorem unip_lg (n : radical k b) : unip (lg n) = n := by
  apply Subtype.ext
  apply Units.ext
  simp [lg, unip]
abbrev Pos (b : Fin r → ℕ) : Type := {p : Fin r × Fin r // b p.1 < b p.2}
variable (k b) in

def coord : lieRadical k b ≃ₗ[k] (Pos b → k) where
  toFun X p := (X : Matrix (Fin r) (Fin r) k) p.1.1 p.1.2
  invFun x := ⟨Matrix.of fun i j => if h : b i < b j then x ⟨(i, j), h⟩ else 0, fun i j h => by simp [h]⟩
  map_add' X Y := rfl
  map_smul' c X := rfl
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : b i < b j
    · simp [h]
    · simp [h, X.2 i j h]
  right_inv x := by
    funext p
    simp [p.2]
end Algebra
section Top
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}
theorem continuous_lg_val :
    Continuous fun n : radical k b => (lg n : Matrix (Fin r) (Fin r) k) :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
theorem continuous_coord_symm_val :
    Continuous fun x : Pos b → k => ((coord k b).symm x : Matrix (Fin r) (Fin r) k) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun x : Pos b → k => if h : b i < b j then x ⟨(i, j), h⟩ else 0
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
variable (k b) in

def chart : (Pos b → k) ≃ₜ radical k b where
  toFun x := unip ((coord k b).symm x)
  invFun n := coord k b (lg n)
  left_inv x := by simp [lg_unip]
  right_inv n := by simp [unip_lg]
  continuous_toFun := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact continuous_const.add continuous_coord_symm_val
    · show Continuous fun x : Pos b → k => ∑ i ∈ Finset.range (Finset.univ.sup b + 1),
        (-((coord k b).symm x : Matrix (Fin r) (Fin r) k)) ^ i
      exact continuous_finset_sum _ fun i _ => (continuous_coord_symm_val (k := k) (b := b)).neg.pow i
  continuous_invFun := continuous_pi fun p => continuous_lg_val.matrix_elem _ _
end Top
end GlobalTheory.UnipChange


