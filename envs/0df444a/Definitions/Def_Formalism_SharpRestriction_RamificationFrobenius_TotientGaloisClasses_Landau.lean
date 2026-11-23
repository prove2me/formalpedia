-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:29.33454+00:00
-- url     : https://prove2.me/theorems/a633fdc6-69fd-4736-adc7-96c693c0b954
-- title:
--   Landau
-- statement:
--   Definitions and structural lemmas for Landau, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Formalism.HC.Landau
open Formalism ArithmeticFunction
def AP (P : ℂ → ℂ) (a b : ℂ) (s : ℂ) : ℂ := deriv P s - (a + b * s) * P s
def PhiP (P : ℂ → ℂ) (a b : ℂ) (C θ : ℝ) (s : ℂ) : ℂ := dslope (AP P a b) 1 s / (s * P s) + C / (s - θ)
section Family
open DirichletCharacter
variable {N : ℕ} [NeZero N]
end Family
end Formalism.HC.Landau
end


