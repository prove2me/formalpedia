-- Prove2me | Definitions.Def_keyholeLineIntegral
-- name    : keyholeLineIntegral
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-09-16T12:43:41.187701+00:00
-- url     : https://prove2.me/theorems/47a217d9-ba21-4147-ba10-e11374334d44
-- title:
--   Complex line integral along a parametrized keyhole path
-- statement:
--   We define the complex line integral of a function along a real-parameterized path and the resulting full and component integrals for the assembled keyhole contour. These definitions provide the concrete objects used in the contour-boundary and arc-limit lemmas.
-- source:
--   Standard parametrized complex line integral for piecewise-C1 contours.

import Mathlib
import Definitions.Def_keyholeBoundaryPath
import Definitions.Def_keyholeInnerArc
import Definitions.Def_keyholeOuterArc
import Definitions.Def_keyholeUpperBank
import Definitions.Def_keyholeLowerBank

open scoped Interval

noncomputable def keyholeLineIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (u v : ℝ) : ℂ :=
  ∫ t in u..v, F (γ t) * deriv γ t

noncomputable def keyholeBoundaryIntegral (F : ℂ → ℂ) (a₀ a₁ r R : ℝ) : ℂ :=
  keyholeLineIntegral F (keyholeBoundaryPath a₀ a₁ r R) 0 1

noncomputable def keyholeUpperBankIntegral (F : ℂ → ℂ) (a₀ a₁ : ℝ) : ℂ :=
  keyholeLineIntegral F (fun t => keyholeUpperBank (a₀ + t * (a₁ - a₀))) 0 1

noncomputable def keyholeLowerBankIntegral (F : ℂ → ℂ) (a₀ a₁ : ℝ) : ℂ :=
  keyholeLineIntegral F (fun t => keyholeLowerBank (a₁ + t * (a₀ - a₁))) 0 1

noncomputable def keyholeInnerArcIntegral (F : ℂ → ℂ) (r : ℝ) : ℂ :=
  keyholeLineIntegral F (keyholeInnerArc r) 0 1

noncomputable def keyholeOuterArcIntegral (F : ℂ → ℂ) (R : ℝ) : ℂ :=
  keyholeLineIntegral F (keyholeOuterArc R) 0 1


