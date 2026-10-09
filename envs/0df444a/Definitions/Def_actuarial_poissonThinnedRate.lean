-- Prove2me | Definitions.Def_actuarial_poissonThinnedRate
-- name    : actuarial_poissonThinnedRate
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:52:13.957177+00:00
-- url     : https://prove2.me/theorems/654cc8b1-c625-4fe8-a13c-408443fb5709
-- title:
--   Thinned Poisson rate
-- statement:
--   Each original arrival is independently selected with probability selection. The selected-event intensity is the original intensity multiplied by the selection fraction, with the complementary intensity obtained by replacing selection with one minus that fraction.
--
--   **Mathematical statement**
--
--   $$
--   \lambda_{\rm selected}=\lambda p
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), ch 21 sections 21.8-21.9, library PDF pages 411-413; Poisson count thinning and splitting, plus actuarial claim-type superposition. See also SCMA469 Actuarial Statistics chapter 5 https://pairote-sat.github.io/SCMA469/poisson-processes.html

import Mathlib

namespace ActuarialValuation

noncomputable def poissonThinnedRate (rate selection : ℝ) : ℝ :=
  rate * selection

end ActuarialValuation


