-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:33:11.010608+00:00
-- url     : https://prove2.me/theorems/4942db71-4707-4767-bc18-d4ee6224e55a
-- title:
--   Keyed Geometric Counts
-- statement:
--   Definitions and structural lemmas for Keyed Geometric Counts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
set_option autoImplicit false
namespace QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
noncomputable def keyEventsAtTriangle (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) : Finset (KeyEvent P key hk J K) := by
  classical
  exact Finset.univ.filter (fun e => a ∈ e.val)
noncomputable def keyEventsAtVertex (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) : Finset (KeyEvent P key hk J K) := by
  classical
  exact Finset.univ.filter (fun e => v ∈ keySupport P key hk J K e)
end QEC.Coding.BDL26KeyedGeometric


