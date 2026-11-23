-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:54.667418+00:00
-- url     : https://prove2.me/theorems/ca3376ce-7b1d-494b-a399-f457faccb3a9
-- title:
--   Smooth Spreads Out
-- statement:
--   Definitions and structural lemmas for Smooth Spreads Out, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
namespace GlobalTheory.CompanionTheory.SmoothSpread
section Witness
variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]
end Witness
section Spread
variable {R₀ R B : Type} [CommRing R₀] [CommRing R] [CommRing B] [Algebra R₀ R] [Algebra R₀ B]
end Spread
section Schemes
end Schemes
end GlobalTheory.CompanionTheory.SmoothSpread


