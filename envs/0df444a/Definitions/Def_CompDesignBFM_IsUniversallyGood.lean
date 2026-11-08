-- Prove2me | Definitions.Def_CompDesignBFM_IsUniversallyGood
-- name    : CompDesignBFM_IsUniversallyGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:07.794614+00:00
-- url     : https://prove2.me/theorems/72141e0b-5347-4fa5-a2c6-1f33e4638d71
-- title:
--   Universally truthful, ex post IR and budget-feasible mechanism
-- statement:
--   A randomized mechanism is **universally truthful**, and individually rational and budget feasible **ex post**, if every component of the mixture is truthful, individually rational, pays only selected agents nonnegative amounts, and is budget feasible.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_CompDesignBFM_RandMechanism
import Definitions.Def_CompDesignBFM_IsGood

namespace CompDesignBFM

/-- Universal truthfulness with ex post individual rationality and budget feasibility
(Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3: "every realized deterministic mechanism has the corresponding property"):
every component of the mixture has all four properties. -/
def IsUniversallyGood {n : ℕ} (B : ℝ) (R : RandMechanism n) : Prop :=
  ∀ j, IsGood B (R.mech j)

end CompDesignBFM


