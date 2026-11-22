-- Prove2me | Definitions.Def_Paper_RoundingCutoff
-- name    : Paper_RoundingCutoff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:57.98095+00:00
-- url     : https://prove2.me/theorems/353a0205-0a36-47c9-b506-d3a012a350dd
-- title:
--   Rounding Cutoff
-- statement:
--   Definitions and structural lemmas for Rounding Cutoff, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
structure CutoffPiece (H : Hypergraph) (γ x : ℕ → ℝ) (Q : Finset ℕ)
    (volumeBound costFactor : ℝ) where
  piece : Finset ℕ
  separator : Finset ℕ
  nonempty : piece.Nonempty
  piece_subset : piece ⊆ Q
  separator_subset : separator ⊆ Q
  disjoint : Disjoint piece separator
  support : separator ⊆ H.vertices.filter (fun v => x v ≠ 0)
  separated : ∀ e ∈ H.edges, Disjoint (H.edge e) piece ∨
    Disjoint (H.edge e) (Q \ (piece ∪ separator))
  volume_le : H.edgeVolume γ piece ≤ volumeBound
  cost_le : H.setCoverCost separator ≤ costFactor * H.coverCost (restrictDemand x piece)
end Paper.Hypergraph


