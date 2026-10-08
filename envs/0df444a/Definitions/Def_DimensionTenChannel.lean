-- Prove2me | Definitions.Def_DimensionTenChannel
-- name    : DimensionTenChannel
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.698883+00:00
-- url     : https://prove2.me/theorems/21f310ad-ed65-487b-bfa5-fe2daf1d054e
-- statement:
--   For finite index sets n and m, Mat(n) is the space of square complex matrices indexed by n, and Map(n,m) consists of complex-linear maps from Mat(n) to Mat(m). The amplification of a map F to matrices indexed by k × n applies F to each n-by-n block: its entry at ((a,u),(b,v)) is F(X[(a,·),(b,·)]) at (u,v). Complete positivity means that every such amplification, for every finite auxiliary index set k, sends positive semidefinite matrices to positive semidefinite matrices. Transposition defines a complex-linear map, and F has the PPT property precisely when both F and its composition with output transposition are completely positive. Trace preservation means trace(F(X)) = trace(X) for every X. A matrix on n × m is separable if it is a finite sum of Kronecker products Aᵢ ⊗ Bᵢ with both factors positive semidefinite; no trace normalization is required, and the empty sum is allowed. A map is entanglement breaking if it is completely positive and every amplification sends every positive semidefinite input to a separable output. Trace preservation is a separate condition, not part of the definitions of PPT or entanglement breaking; none of these definitions restricts the dimension to ten.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DimensionTenChannel.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DimensionTenChannel.lean; bytes 16..1223
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion

abbrev Mat (n : Type) := Matrix n n ℂ
abbrev Map (n m : Type) := Mat n →ₗ[ℂ] Mat m

variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

def amplify (F : Map n m) {k : Type} (X : Mat (k × n)) : Mat (k × m) :=
  fun a b => F (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

def CP (F : Map n m) : Prop :=
  ∀ (k : Type) [Fintype k] (X : Mat (k × n)), X.PosSemidef → (amplify F X).PosSemidef

def transposeMap : Map n n where
  toFun := Matrix.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def PPT (F : Map n m) : Prop := CP F ∧ CP (transposeMap.comp F)

def TracePreserving (F : Map n m) : Prop := ∀ X, Matrix.trace (F X) = Matrix.trace X

def Separable (Z : Mat (n × m)) : Prop :=
  ∃ (r : ℕ) (A : Fin r → Mat n) (B : Fin r → Mat m),
    (∀ i, (A i).PosSemidef) ∧ (∀ i, (B i).PosSemidef) ∧
    Z = ∑ i, A i ⊗ₖ B i

def EntanglementBreaking (F : Map n m) : Prop :=
  CP F ∧ ∀ (k : Type) [Fintype k] (X : Mat (k × n)),
    X.PosSemidef → Separable (amplify F X)

end ChannelCompletion

namespace DimensionTen



end DimensionTen
end
end OAI


