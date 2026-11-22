-- Prove2me | Definitions.Def_Csg_ConcurrentCoBuchiExample
-- name    : Csg_ConcurrentCoBuchiExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:54:05.603947+00:00
-- url     : https://prove2.me/theorems/6e0be65e-47d1-4ef5-b627-4df8d6ebcc92
-- title:
--   Concurrent Co Buchi Example
-- statement:
--   Definitions and structural lemmas for Concurrent Co Buchi Example, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ConcurrentCoBuchiExample.lean

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit true
namespace Csg
inductive CBState
  | t1
  | t2
  | t3
  | t4
  | t5
  deriving DecidableEq, Inhabited
instance : Fintype CBState where
  elems := {CBState.t1, .t2, .t3, .t4, .t5}
  complete := by intro s; cases s <;> decide
inductive RowMove
  | b
  | d
  deriving DecidableEq, Inhabited
instance : Fintype RowMove where
  elems := {RowMove.b, .d}
  complete := by intro a; cases a <;> decide
inductive ColMove
  | c
  | d
  deriving DecidableEq, Inhabited
instance : Fintype ColMove where
  elems := {ColMove.c, .d}
  complete := by intro a; cases a <;> decide
noncomputable def cbCoin (x y : CBState) (_hxy : x ≠ y) : PMF CBState :=
  PMF.uniformOfFinset {x, y} ⟨x, by simp⟩
noncomputable def cbK : CBState → RowMove → ColMove → PMF CBState
  | .t1, _, _ => PMF.pure .t1
  | .t2, .b, _ => PMF.pure .t2
  | .t2, .d, _ => cbCoin .t1 .t3 (by decide)
  | .t3, _, .c => PMF.pure .t3
  | .t3, _, .d => cbCoin .t2 .t4 (by decide)
  | .t4, _, _ => PMF.pure .t5
  | .t5, _, _ => PMF.pure .t4
noncomputable def cbR : CBState → RowMove → ColMove → ℝ := fun _ _ _ => 0
noncomputable def cbCSG : CSG CBState RowMove ColMove where
  K := cbK
  r := cbR
theorem cbCSG_r (s : CBState) (a1 : RowMove) (a2 : ColMove) : cbCSG.r s a1 a2 = 0 := rfl
theorem cbR_zero : ∀ s a1 a2, cbCSG.r s a1 a2 = 0 := cbCSG_r
def cbU : CBState → Prop := fun s => s = .t1 ∨ s = .t2 ∨ s = .t4
instance : DecidablePred cbU := fun s => by unfold cbU; infer_instance
def pointRow (m : RowMove) : RowMove → ℝ := fun m' => if m' = m then 1 else 0
def pointCol (m : ColMove) : ColMove → ℝ := fun m' => if m' = m then 1 else 0
noncomputable def cbVStarVal : CBState → ℝ
  | .t1 => 1
  | .t2 => 2 / 3
  | .t3 => 1 / 3
  | .t4 => 0
  | .t5 => 0
theorem cbVStarVal_mem (s : CBState) : cbVStarVal s ∈ Set.Icc (0 : ℝ) 1 := by
  cases s <;> constructor <;> norm_num [cbVStarVal]
noncomputable def cbVStar : CBState → Set.Icc (0 : ℝ) 1 := fun s =>
  ⟨cbVStarVal s, cbVStarVal_mem s⟩
noncomputable def cbGClosedVal (b : CBState → ℝ) : CBState → ℝ
  | .t1 => 1
  | .t2 => (1 + max (b .t3) ((b .t2 + b .t4) / 2)) / 2
  | .t3 => max (b .t3) ((b .t2 + b .t4) / 2)
  | .t4 => b .t4
  | .t5 => b .t4
theorem cbGClosedVal_mem (b : CBState → Set.Icc (0 : ℝ) 1) (s : CBState) :
    cbGClosedVal (fun s' => (b s' : ℝ)) s ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 := (b .t2).2; have h3 := (b .t3).2; have h4 := (b .t4).2
  simp only [Set.mem_Icc] at h2 h3 h4
  have hmax_nonneg : (0 : ℝ) ≤ max ((b .t3 : ℝ)) (((b .t2 : ℝ) + b .t4) / 2) :=
    le_trans h3.1 (le_max_left _ _)
  have hmax_le_one : max ((b .t3 : ℝ)) (((b .t2 : ℝ) + b .t4) / 2) ≤ 1 :=
    max_le h3.2 (by linarith [h2.2, h4.2])
  cases s with
  | t1 => unfold cbGClosedVal; constructor <;> norm_num
  | t2 =>
      unfold cbGClosedVal
      constructor
      · linarith [hmax_nonneg]
      · linarith [hmax_le_one]
  | t3 => unfold cbGClosedVal; exact ⟨hmax_nonneg, hmax_le_one⟩
  | t4 => unfold cbGClosedVal; exact h4
  | t5 => unfold cbGClosedVal; exact h4
noncomputable def cbGClosed (b : CBState → Set.Icc (0 : ℝ) 1) : CBState → Set.Icc (0 : ℝ) 1 :=
  fun s => ⟨cbGClosedVal (fun s' => (b s' : ℝ)) s, cbGClosedVal_mem b s⟩
end Csg


