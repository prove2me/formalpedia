-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:10:57.113953+00:00
-- url     : https://prove2.me/theorems/e5585e2b-d4e7-4afb-80ec-21d0f95a42ee
-- title:
--   Graph
-- statement:
--   Definitions and structural lemmas for Graph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Graph.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def vertexEquiv (P : TannerSquarePresentation) :
    RXCoarseGraining.RXVertex P.X P.Q P.Z ≃ Vertex P where
  toFun
    | .inl x => .x x
    | .inr (.inl q) => .q q
    | .inr (.inr z) => .z z
  invFun
    | .x x => .inl x
    | .q q => .inr (.inl q)
    | .z z => .inr (.inr z)
  left_inv := by intro v; rcases v with x | (q | z) <;> rfl
  right_inv := by intro v; cases v <;> rfl
noncomputable def rxLevel (P : TannerSquarePresentation) :
    LevelGraph (RXCoarseGraining.RXVertex P.X P.Q P.Z) where
  skeleton :=
    { adjacent := fun u v => (tannerSkeleton P).adjacent (vertexEquiv P u) (vertexEquiv P v)
      symmetric := fun _ _ h => (tannerSkeleton P).symmetric h
      loopless := fun u => (tannerSkeleton P).loopless (vertexEquiv P u) }
  kind := fun v => vertexKind P (vertexEquiv P v)
  skeletonDecidable := fun u v => tannerAdjacentDecidable P (vertexEquiv P u) (vertexEquiv P v)
noncomputable def topCenter (P : TannerSquarePresentation) (S : OddScale) :
    RX2 P S → RXCoarseGraining.RXVertex P.X P.Q P.Z :=
  fun p => (vertexEquiv P).symm (rxSyndromeOwner P S p)
end QEC.Coding.BDL26RXDecoderAdapter


