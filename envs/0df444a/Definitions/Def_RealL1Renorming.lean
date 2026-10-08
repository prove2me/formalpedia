-- Prove2me | Definitions.Def_RealL1Renorming
-- name    : RealL1Renorming
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.60679+00:00
-- url     : https://prove2.me/theorems/856cb1ff-3b79-438e-b360-1ad755e02440
-- statement:
--   The block defines a bounded-approximation-property predicate and a statement about renorming real ℓ¹. HasBAP(X,Λ), for a real normed space X, says that for every compact set C ⊆ X and every ε>0 there is a continuous linear operator T:X→X whose range is a finitely generated (finite-dimensional) real subspace, with operator norm ‖T‖ ≤ Λ, and a number η<ε such that ‖Tu−u‖ ≤ η for every u in C. blockBound(p) is the real number 300p²+150p+5. RealL1 is the space of real sequences indexed by the natural numbers that are absolutely summable, with its usual ℓ¹ norm and real normed-space structure. RealL1RenormingStatement is a defined proposition, not an established theorem: for every natural number p ≥ 1 there exists an additive group norm N on RealL1 such that N(r·c)=|r|·N(c) for all real r and c, and (1/2)‖c‖ ≤ N(c) ≤ blockBound(p)·‖c‖ for all c, where ‖·‖ is the ℓ¹ norm. Moreover, taking N as the norm while keeping the same addition and scalar multiplication, there is a real normed-space structure whose underlying module is the original one, in which RealL1 is complete, has the bounded approximation property with constant 2·blockBound(p), and fails it with constant p. When p=1, it additionally fails the bounded approximation property with constant 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RealL1Renorming.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RealL1Renorming.lean; bytes 131..1674
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.RingTheory.Finiteness.Defs

namespace OAI

noncomputable section

/-!
# Quantitative renorming of real ℓ¹ with fixed vector-space operations
-/

open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

def HasBAP (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (Λ : ℝ) : Prop :=
  ∀ C : Set X, IsCompact C → ∀ ε : ℝ, 0 < ε →
    ∃ T : X →L[ℝ] X, Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧
      ‖T‖ ≤ Λ ∧ ∃ η : ℝ, η < ε ∧ ∀ u ∈ C, ‖T u - u‖ ≤ η

def blockBound (p : ℕ) : ℝ := 300 * (p : ℝ)^2 + 150 * (p : ℝ) + 5

open scoped BigOperators ENNReal

def RealL1 : Type := lp (fun _ : ℕ => ℝ) (1 : ENNReal)

noncomputable instance : NormedAddCommGroup RealL1 :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

noncomputable instance : NormedSpace ℝ RealL1 :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

def RealL1RenormingStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∃ N : AddGroupNorm RealL1,
    (∀ (r : ℝ) (c : RealL1), N (r • c) = |r| * N c) ∧
    (∀ c : RealL1, (1 / 2 : ℝ) * ‖c‖ ≤ N c ∧ N c ≤ blockBound p * ‖c‖) ∧
    (let m : Module ℝ RealL1 := inferInstance
     letI : NormedAddCommGroup RealL1 := N.toNormedAddCommGroup
     ∃ s : NormedSpace ℝ RealL1, s.toModule = m ∧
       letI := s
       CompleteSpace RealL1 ∧
       HasBAP RealL1 (2 * blockBound p) ∧ ¬ HasBAP RealL1 (p : ℝ) ∧
         (p = 1 → ¬ HasBAP RealL1 1))



end DiscreteFree
end
end OAI


