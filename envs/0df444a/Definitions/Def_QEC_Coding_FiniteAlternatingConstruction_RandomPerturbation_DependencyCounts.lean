-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:02:41.930056+00:00
-- url     : https://prove2.me/theorems/5cffb975-1893-46e6-a025-53e6fdeaf113
-- title:
--   Dependency Counts
-- statement:
--   Definitions and structural lemmas for Dependency Counts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/DependencyCounts.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
noncomputable def eventsAtTriangle (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (a : Triangle P) : Finset (Event P J K) := by
  classical
  exact Finset.univ.filter (fun e => a ∈ e.val)
noncomputable def eventsAtVertex (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) : Finset (Event P J K) := by
  classical
  exact Finset.univ.filter (fun e => v ∈ eventSupport P J K e)
end QEC.Coding.BDL26RandomPerturbation


