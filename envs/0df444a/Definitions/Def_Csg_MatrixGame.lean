-- Prove2me | Definitions.Def_Csg_MatrixGame
-- name    : Csg_MatrixGame
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:36:59.052328+00:00
-- url     : https://prove2.me/theorems/08385611-a7c7-4b69-80ae-9ad250c40296
-- title:
--   Matrix Game
-- statement:
--   Definitions and structural lemmas for Matrix Game, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
set_option autoImplicit true
namespace Csg
structure MatrixGame (I J : Type*) [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J] where
  /-- The payoff matrix: `A i j` is paid by the row player to the column player. -/
  A : I → J → ℝ
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
namespace MatrixGame
variable (G : MatrixGame I J)
noncomputable def payoff (x : I → ℝ) (y : J → ℝ) : ℝ := ∑ i, ∑ j, x i * G.A i j * y j
theorem payoff_eq_sum_mul (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ i, x i * ∑ j, G.A i j * y j := by
  unfold payoff
  congr 1
  funext i
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring
theorem payoff_eq_sum_mul' (x : I → ℝ) (y : J → ℝ) :
    G.payoff x y = ∑ j, (∑ i, x i * G.A i j) * y j := by
  unfold payoff
  rw [Finset.sum_comm]
  congr 1
  funext j
  rw [Finset.sum_mul]
theorem payoff_smul_add_smul_left (p₁ p₂ : I → ℝ) (q : J → ℝ) (a b : ℝ) :
    G.payoff (a • p₁ + b • p₂) q = a * G.payoff p₁ q + b * G.payoff p₂ q := by
  simp only [payoff_eq_sum_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext i
  ring
theorem payoff_smul_add_smul_right (p : I → ℝ) (q₁ q₂ : J → ℝ) (a b : ℝ) :
    G.payoff p (a • q₁ + b • q₂) = a * G.payoff p q₁ + b * G.payoff p q₂ := by
  simp only [payoff_eq_sum_mul', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  funext j
  ring
theorem continuous_payoff_left (y : J → ℝ) :
    Continuous (fun x : I → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
theorem continuous_payoff_right (x : I → ℝ) :
    Continuous (fun y : J → ℝ => G.payoff x y) := by
  simp only [payoff_eq_sum_mul']
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
theorem convexOn_payoff_left (y : J → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ I) (fun x => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ I, ?_⟩
  intro p _ p' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_left p p' y a b).le
theorem concaveOn_payoff_right (x : I → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ J) (fun y => G.payoff x y) := by
  refine ⟨convex_stdSimplex ℝ J, ?_⟩
  intro q _ q' _ a b _ _ _
  simp only [smul_eq_mul]
  exact (G.payoff_smul_add_smul_right x q q' a b).ge
theorem exists_optimal_strategies :
    ∃ p ∈ stdSimplex ℝ I, ∃ q ∈ stdSimplex ℝ J,
      (∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q) ∧
      (∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) := by
  obtain ⟨p, hp, q, hq, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      (X := stdSimplex ℝ I) (Y := stdSimplex ℝ J) (f := G.payoff)
      (ne_X := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary I)⟩)
      (cX := convex_stdSimplex ℝ I) (kX := isCompact_stdSimplex ℝ I)
      (hfy := fun y _ => (G.continuous_payoff_left y).continuousOn.lowerSemicontinuousOn)
      (hfy' := fun y _ => G.convexOn_payoff_left y |>.quasiconvexOn)
      (cY := convex_stdSimplex ℝ J)
      (ne_Y := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary J)⟩)
      (kY := isCompact_stdSimplex ℝ J)
      (hfx := fun x _ => (G.continuous_payoff_right x).continuousOn.upperSemicontinuousOn)
      (hfx' := fun x _ => G.concaveOn_payoff_right x |>.quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' => hsaddle p' hp' q hq, fun q' hq' => hsaddle p hp q' hq'⟩
noncomputable def optimalRow : I → ℝ := G.exists_optimal_strategies.choose
noncomputable def optimalCol : J → ℝ := G.exists_optimal_strategies.choose_spec.2.choose
noncomputable def value : ℝ := G.payoff G.optimalRow G.optimalCol
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
noncomputable def relabelRow (e : I' ≃ I) : MatrixGame I' J where
  A i' j := G.A (e i') j
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
noncomputable def relabelCol (e : J' ≃ J) : MatrixGame I J' where
  A i j' := G.A i (e j')
def rowLPFeasible (G : MatrixGame I J) : Set ℝ :=
  {t : ℝ | ∃ p ∈ stdSimplex ℝ I, ∀ j, (∑ i, p i * G.A i j) ≤ t}
def colLPFeasible (G : MatrixGame I J) : Set ℝ :=
  {t : ℝ | ∃ q ∈ stdSimplex ℝ J, ∀ i, t ≤ (∑ j, G.A i j * q j)}
end MatrixGame
end Csg


