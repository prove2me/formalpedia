-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:47.389909+00:00
-- url     : https://prove2.me/theorems/68f13a50-d911-456a-904c-35aa93d2c570
-- title:
--   Integral Exp Int
-- statement:
--   Definitions and structural lemmas for Integral Exp Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/IntegralExpInt.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
abbrev mu1 : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))
abbrev muT (G : ℕ) : Measure (Fin G → ℝ) := Measure.pi (fun _ : Fin G => mu1)
end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures


