-- Prove2me | Definitions.Def_Paper_RoundingSeparation
-- name    : Paper_RoundingSeparation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:27.758888+00:00
-- url     : https://prove2.me/theorems/a6dcbb95-0508-47c5-98d1-eb0c9f019f82
-- title:
--   Rounding Separation
-- statement:
--   Definitions and structural lemmas for Rounding Separation, from lnz's pinned Width comparison for sparse-incidence homomorphisms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean

import Definitions.Def_Paper_RoundingPaths
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
namespace Paper.Hypergraph
def IntegralSeparator (H : Hypergraph) (A B S : Finset ℕ) : Prop :=
  S ⊆ H.vertices ∧ ∀ a ∈ A \ S, ∀ b ∈ B \ S,
    ¬ (H.induce (H.vertices \ S)).primal.Reachable a b
def separatorRegion (H : Hypergraph) (A S : Finset ℕ) : Finset ℕ :=
  (H.vertices \ S).filter fun v => ∃ a ∈ A \ S,
    (H.induce (H.vertices \ S)).primal.Reachable a v
end Paper.Hypergraph


