-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:08.134006+00:00
-- url     : https://prove2.me/theorems/87081215-ec53-468b-8fb5-4c788a748bb4
-- title:
--   Fibre Representation Smooth
-- statement:
--   Definitions and structural lemmas for Fibre Representation Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FibreRepresentationSmooth.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
namespace GlobalTheory.CompanionTheory.ThetaGLLen
section Smooth
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
end Smooth
end GlobalTheory.CompanionTheory.ThetaGLLen
namespace GlobalTheory.CompanionTheory.ThetaGLLen
end GlobalTheory.CompanionTheory.ThetaGLLen


