-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
-- name    : QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:29:40.75839+00:00
-- url     : https://prove2.me/theorems/2ac2bfe5-5c95-4066-9577-7cdabc38ec27
-- title:
--   Small Set Expansion Square
-- statement:
--   Definitions and structural lemmas for Small Set Expansion Square, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionSquare.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Mathlib.Data.Nat.Log
set_option autoImplicit false
namespace QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
def IsSymmetric (M : WeightedGraph V) : Prop :=
  ∀ v u, M v u = M u v
def IsRegular [Fintype V] (M : WeightedGraph V) (degree : Nat) : Prop :=
  ∀ v, ∑ u, M v u = degree
def HasExpanderMixingBound [Fintype V]
    (M : WeightedGraph V) (degree : Nat) (spectral : ℝ) : Prop :=
  ∀ S T : Finset V,
    (Fintype.card V : ℝ) * crossCount M S T ≤
      degree * (S.card : ℝ) * T.card +
        spectral * Fintype.card V *
          Real.sqrt ((S.card : ℝ) * T.card)
noncomputable def adjacencyPairing [Fintype V]
    (M : WeightedGraph V) (f g : V → ℝ) : ℝ :=
  ∑ v, f v * ∑ u, (M v u : ℝ) * g u
noncomputable def weightedNeighborSum [Fintype V]
    (M : WeightedGraph V) (g : V → ℝ) (v : V) : ℝ :=
  ∑ u, (M v u : ℝ) * g u
def HasMeanZeroBilinearBound [Fintype V]
    (M : WeightedGraph V) (spectral : ℝ) : Prop :=
  ∀ f g : V → ℝ,
    (∑ v, f v) = 0 →
    (∑ v, g v) = 0 →
      |adjacencyPairing M f g| ≤
        spectral * Real.sqrt ((∑ v, (f v) ^ 2) * ∑ v, (g v) ^ 2)
noncomputable def vertexIndicator [DecidableEq V]
    (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then 1 else 0
noncomputable def centeredVertexIndicator [Fintype V] [DecidableEq V]
    (S : Finset V) (v : V) : ℝ :=
  Fintype.card V * vertexIndicator S v - S.card
def incomingCount (M : WeightedGraph V) (S : Finset V) (x : V) : Nat :=
  ∑ v ∈ S, M v x
def outgoingCount (M : WeightedGraph V) (T : Finset V) (x : V) : Nat :=
  ∑ u ∈ T, M x u
def intermediateSupport [Fintype V] [DecidableEq V]
    (M : WeightedGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun x => incomingCount M S x ≠ 0
end QEC.Coding.SmallSetExpansion


