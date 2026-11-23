-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:21.340803+00:00
-- url     : https://prove2.me/theorems/74443d8f-afde-4a70-9828-101157aef101
-- title:
--   Exists Prime Dimension LEOne Avoiding
-- statement:
--   Definitions and structural lemmas for Exists Prime Dimension LEOne Avoiding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.LineThrough
noncomputable def lineMap {d : ℕ} (a c : Fin d → ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => C (a i) + C (c i - a i) * X
end GlobalTheory.LineThrough


