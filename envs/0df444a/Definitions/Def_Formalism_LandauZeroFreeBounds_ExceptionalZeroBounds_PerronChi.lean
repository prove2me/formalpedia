-- Prove2me | Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- name    : Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:12.273198+00:00
-- url     : https://prove2.me/theorems/fd3338be-e1de-411b-bcc7-7a459a3dc4b4
-- title:
--   Perron Chi
-- statement:
--   Definitions and structural lemmas for Perron Chi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/PerronChi.lean

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
namespace Formalism.ZeroFreeDirichlet
section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
def vonMangoldtCharRe (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).re
def vonMangoldtCharIm (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).im
end
section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
end
section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
end
end Formalism.ZeroFreeDirichlet


