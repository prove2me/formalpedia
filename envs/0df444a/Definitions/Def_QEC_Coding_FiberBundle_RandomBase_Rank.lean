-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
-- name    : QEC_Coding_FiberBundle_RandomBase_Rank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:27:22.184906+00:00
-- url     : https://prove2.me/theorems/e2e11f83-8e09-42cc-8980-e66a2b8b80b6
-- title:
--   Rank
-- statement:
--   Definitions and structural lemmas for Rank, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Rank.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
abbrev ColumnSample (r : Nat) := Fin (3 * r) → Bool
abbrev GroupedSample (r : Nat) := Fin (4 * r) → ColumnSample r
def sampleEquivGrouped (r : Nat) : Sample r ≃ GroupedSample r where
  toFun sample b a := sample (a, b)
  invFun grouped edge := grouped edge.2 edge.1
  left_inv sample := by
    funext edge
    rfl
  right_inv grouped := by
    funext b a
    rfl
noncomputable def columnDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (ColumnSample r) :=
  independentProduct fun _ =>
    PMF.bernoulli
      (incidenceProbability (4 * r) Delta)
      (incidenceProbability_le_one hDelta)
noncomputable def groupedDistribution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    PMF (GroupedSample r) :=
  independentProduct fun _ => columnDistribution r Delta hDelta
def rowSupport {r : Nat} (coeff : Fin (3 * r) → ZMod 2) :
    Finset (Fin (3 * r)) :=
  Finset.univ.filter fun a => coeff a ≠ 0
def subsetRowCombination {r : Nat}
    (sample : Sample r) (A : Finset (Fin (3 * r))) :
    Fin (4 * r) → ZMod 2 :=
  fun b => ∑ a ∈ A, boundary sample a b
def ColumnParityZero {r : Nat}
    (A : Finset (Fin (3 * r))) (column : ColumnSample r) : Prop :=
  (∑ a ∈ A, cond (column a) (1 : ZMod 2) 0) = 0
instance instDecidablePredColumnParityZero
    {r : Nat} (A : Finset (Fin (3 * r))) :
    DecidablePred (ColumnParityZero A) := by
  intro column
  unfold ColumnParityZero
  infer_instance
def paritySign (x : ZMod 2) : Real :=
  if x = 0 then 1 else -1
def signedBit (b : Bool) : Real :=
  cond b (-1) 1
noncomputable def parityZeroIndicator {r : Nat}
    (A : Finset (Fin (3 * r))) (column : ColumnSample r) : Real :=
  by
    classical
    exact if ColumnParityZero A column then 1 else 0
noncomputable instance instDecidablePredHasFullRowRank (r : Nat) :
    DecidablePred (@HasFullRowRank r) :=
  Classical.decPred _
end QEC.Coding.FiberBundle.RandomBase


