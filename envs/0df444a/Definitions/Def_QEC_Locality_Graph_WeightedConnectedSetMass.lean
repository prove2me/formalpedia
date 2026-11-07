-- Prove2me | Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
-- name    : QEC_Locality_Graph_WeightedConnectedSetMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:15:09.179645+00:00
-- url     : https://prove2.me/theorems/7127a8cf-08cd-4d31-81f4-6422600f4925
-- title:
--   Weighted Connected Set Mass
-- statement:
--   Definitions and structural lemmas for Weighted Connected Set Mass, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/Graph/WeightedConnectedSetMass.lean

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
noncomputable section
namespace QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
def alpha (Delta : ℕ) : ℝ := (Delta+1 : ℝ)^2
def rootedMass (G : SimpleGraph V) (r : V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ rooted G r m, ∏ v ∈ K, a v
def anchoredMass (G : SimpleGraph V) (R : Finset V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ anchored G R m, ∏ v ∈ K, a v
def occupiedMass (G : SimpleGraph V) (R B : Finset V) (m : ℕ) (a : V → ℝ) : ℝ :=
  ∑ K ∈ anchored G R m, ∏ v ∈ K \ B, a v
def interval (f : ℕ → ℝ) (L U : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (U+1-max 1 L), f (max 1 L+j)
def geometric (q : ℝ) (l n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q^(l+j)
def structuralEnvelope (A b : ℝ) (c L U : ℕ) : ℝ :=
  (∑ m ∈ (Finset.range (U+1-max 1 L)).filter (fun j => max 1 L+j≤c),
      b*A^(max 1 L+m)) +
    (∑ m ∈ (Finset.range (U+1-max 1 L)).filter (fun j => c < max 1 L+j),
      A^c*(A*b)^(max 1 L+m-c))
end QEC.Locality.WeightedConnectedSetMass


