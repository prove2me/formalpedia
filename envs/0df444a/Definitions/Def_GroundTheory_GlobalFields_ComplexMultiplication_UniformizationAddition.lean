-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:05:39.213174+00:00
-- url     : https://prove2.me/theorems/5f084318-605f-518e-81c3-b18836077cc2
-- title:
--   Uniformization Addition
-- statement:
--   Definitions and structural lemmas for Uniformization Addition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {L : PeriodPair}
variable (L) in

def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)
variable (L) in

def addDefect (w z : ℂ) : ℂ :=
  ℘[L] (z + w) + ℘[L] z + ℘[L] w - chordSlope L z w ^ 2 / 4
variable (L) in

def tangentSlope (w : ℂ) : ℂ := (6 * ℘[L] w ^ 2 - L.g₂ / 2) / ℘'[L] w
end Elliptic
end GroundTheory.Global


