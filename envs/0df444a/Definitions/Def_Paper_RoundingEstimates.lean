-- Prove2me | Definitions.Def_Paper_RoundingEstimates
-- name    : Paper_RoundingEstimates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:50:06.078983+00:00
-- url     : https://prove2.me/theorems/d63f8881-7fe1-4d9a-82ed-5da2f5d91181
-- title:
--   Rounding Estimates
-- statement:
--   Definitions and structural lemmas for Rounding Estimates, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingEstimates.lean

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def edgeVolume (H : Hypergraph) (γ : ℕ → ℝ) (Q : Finset ℕ) : ℝ :=
  ∑ e ∈ H.edges.filter (fun e => ¬ Disjoint (H.edge e) Q), γ e
def roundingBall (H : Hypergraph) (x : ℕ → ℝ) (Q : Finset ℕ)
    (c : ℕ) (r : ℝ) : Finset ℕ :=
  (H.vertices ∩ Q).filter fun v => (H.induce Q).vertexDistance x c v ≤ r
def roundingThreshold (H : Hypergraph) (x : ℕ → ℝ) (a : ℝ) : Finset ℕ :=
  H.vertices.filter fun v => a ≤ x v
def restrictDemand (x : ℕ → ℝ) (P : Finset ℕ) (v : ℕ) : ℝ :=
  if v ∈ P then x v else 0
end Paper.Hypergraph


