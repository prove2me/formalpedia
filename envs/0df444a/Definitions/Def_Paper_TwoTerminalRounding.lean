-- Prove2me | Definitions.Def_Paper_TwoTerminalRounding
-- name    : Paper_TwoTerminalRounding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:52:00.544419+00:00
-- url     : https://prove2.me/theorems/60077947-8812-44a9-b776-c099e8334d00
-- title:
--   Two Terminal Rounding
-- statement:
--   Definitions and structural lemmas for Two Terminal Rounding, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean

import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def twoTerminalFactor (H : Hypergraph) (R : Finset ℕ) : ℝ :=
  min (8 + 4 * Real.log ((H.induce R).independenceNumber : ℝ)) (6 * (H.degeneracy : ℝ))
def TwoTerminalRounding : Prop :=
  ∀ (H : Hypergraph) (A B : Finset ℕ) (x : ℕ → ℝ),
    A ⊆ H.vertices → B ⊆ H.vertices → H.FractionalSeparator A B x →
    ∃ S ⊆ H.vertices.filter (fun v => x v ≠ 0), H.IntegralSeparator A B S ∧
      H.setCoverCost S ≤ H.twoTerminalFactor (H.vertices.filter (fun v => x v ≠ 0)) * H.coverCost x
def levelSeparator (H : Hypergraph) (x d : ℕ → ℝ) (r : ℝ) : Finset ℕ :=
  H.vertices.filter fun v => x v ≠ 0 ∧ d v - x v ≤ r ∧ r ≤ d v
end Paper.Hypergraph


