-- Prove2me | Definitions.Def_OAIQ024S014
-- name    : OAIQ024S014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:22:04.897952+00:00
-- url     : https://prove2.me/theorems/4481b7c4-7e14-48e7-a643-6abf323b3622
-- title:
--   Definitions bundle OAIQ024S014 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K8.blocks`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K8`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K8.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39` and `OAI.SKRatio.Certificate.Data.J4K8.checks`; the proofs of `OAI.SKRatio.Certificate.Data.J4K8.check_12`, `OAI.SKRatio.Certificate.Data.J4K8.check_13`, `OAI.SKRatio.Certificate.Data.J4K8.check_14`, `OAI.SKRatio.Certificate.Data.J4K8.check_15`, `OAI.SKRatio.Certificate.Data.J4K8.check_16`, `OAI.SKRatio.Certificate.Data.J4K8.check_17`, `OAI.SKRatio.Certificate.Data.J4K8.check_18`, `OAI.SKRatio.Certificate.Data.J4K8.check_19`, `OAI.SKRatio.Certificate.Data.J4K8.check_20`, `OAI.SKRatio.Certificate.Data.J4K8.check_21`, `OAI.SKRatio.Certificate.Data.J4K8.check_22`, `OAI.SKRatio.Certificate.Data.J4K8.check_23`, `OAI.SKRatio.Certificate.Data.J4K8.check_24`, `OAI.SKRatio.Certificate.Data.J4K8.check_25`, `OAI.SKRatio.Certificate.Data.J4K8.check_26`, `OAI.SKRatio.Certificate.Data.J4K8.check_27`, `OAI.SKRatio.Certificate.Data.J4K8.check_28`, `OAI.SKRatio.Certificate.Data.J4K8.check_29`, `OAI.SKRatio.Certificate.Data.J4K8.check_30`, `OAI.SKRatio.Certificate.Data.J4K8.check_31`, `OAI.SKRatio.Certificate.Data.J4K8.check_32`, `OAI.SKRatio.Certificate.Data.J4K8.check_33`, `OAI.SKRatio.Certificate.Data.J4K8.check_34`, `OAI.SKRatio.Certificate.Data.J4K8.check_35`, `OAI.SKRatio.Certificate.Data.J4K8.check_36`, `OAI.SKRatio.Certificate.Data.J4K8.check_37`, `OAI.SKRatio.Certificate.Data.J4K8.check_38`, `OAI.SKRatio.Certificate.Data.J4K8.check_39`, `OAI.SKRatio.Certificate.Data.J4K8.checks` and `OAI.SKRatio.Certificate.endpointK_zero_bound`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K8

def blocks : ℕ → Box
  | 0 => ⟨-1/1000000,1/1000000⟩
  | 1 => ⟨-1/1000000,1/1000000⟩
  | 2 => ⟨-1/1000000,1/1000000⟩
  | 3 => ⟨-1/1000000,1/1000000⟩
  | 4 => ⟨-1/1000000,1/1000000⟩
  | 5 => ⟨-1/1000000,1/1000000⟩
  | 6 => ⟨-1/1000000,1/1000000⟩
  | 7 => ⟨-1/1000000,1/1000000⟩
  | 8 => ⟨-1/1000000,1/1000000⟩
  | 9 => ⟨-1/1000000,1/1000000⟩
  | 10 => ⟨0,1/1000000⟩
  | 11 => ⟨7/1000000,1/125000⟩
  | 12 => ⟨29/500000,3/50000⟩
  | 13 => ⟨389/1000000,49/125000⟩
  | 14 => ⟨2153/1000000,541/250000⟩
  | 15 => ⟨9853/1000000,309/31250⟩
  | 16 => ⟨29/800,18163/500000⟩
  | 17 => ⟨20263/200000,25349/250000⟩
  | 18 => ⟨19983/100000,199907/1000000⟩
  | 19 => ⟨262289/1000000,3281/12500⟩
  | 20 => ⟨227819/1000000,113967/500000⟩
  | 21 => ⟨68903/500000,13787/100000⟩
  | 22 => ⟨1563/25000,62609/1000000⟩
  | 23 => ⟨4523/200000,1417/62500⟩
  | 24 => ⟨6737/1000000,6763/1000000⟩
  | 25 => ⟨333/200000,67/40000⟩
  | 26 => ⟨339/1000000,343/1000000⟩
  | 27 => ⟨7/125000,29/500000⟩
  | 28 => ⟨7/1000000,1/125000⟩
  | 29 => ⟨0,1/500000⟩
  | 30 => ⟨-1/1000000,1/1000000⟩
  | 31 => ⟨-1/1000000,1/1000000⟩
  | 32 => ⟨-1/1000000,1/1000000⟩
  | 33 => ⟨-1/1000000,1/1000000⟩
  | 34 => ⟨-1/1000000,1/1000000⟩
  | 35 => ⟨-1/1000000,1/1000000⟩
  | 36 => ⟨-1/1000000,1/1000000⟩
  | 37 => ⟨-1/1000000,1/1000000⟩
  | 38 => ⟨-1/1000000,1/1000000⟩
  | 39 => ⟨-1/1000000,1/1000000⟩
  | _ => Box.rat 0

end SKRatio.Certificate.Data.J4K8

end

end OAI
end


