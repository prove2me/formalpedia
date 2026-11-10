-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:59:36.352039+00:00
-- url     : https://prove2.me/theorems/be0b3b65-d3b3-4672-807f-19656ede87ea
-- title:
--   Local Counts
-- statement:
--   Definitions and structural lemmas for Local Counts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/LocalCounts.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def incidentTriangles (P : TannerSquarePresentation) (v : Vertex P) :
    Finset (Triangle P) := by
  classical
  exact Finset.univ.filter (fun a => v ∈ triangleSupport P a)
noncomputable def localPool (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) : Finset (Triangle P) := by
  classical
  exact Finset.univ.filter (fun b => dist (oldAnchor P J a) (oldAnchor P J b) ≤ K)
end QEC.Coding.BDL26RandomPerturbation


