-- Prove2me | Definitions.Def_OAIQ024S015
-- name    : OAIQ024S015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:22:26.081987+00:00
-- url     : https://prove2.me/theorems/32d8dcb7-e798-4eb0-8d16-1bba3aaf5448
-- title:
--   Definitions bundle OAIQ024S015 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.SKRatio.Certificate.Data.J4K9.blocks`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: [`SKRatio_Certificates_ScalarDataJ4K9`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKRatio/Certificates/ScalarDataJ4K9.lean).
--
--   **Imports.** It imports the bundle `OAIQ024S000` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39` and `OAI.SKRatio.Certificate.Data.J4K9.checks`; the proofs of `OAI.SKRatio.Certificate.Data.J4K9.check_12`, `OAI.SKRatio.Certificate.Data.J4K9.check_13`, `OAI.SKRatio.Certificate.Data.J4K9.check_14`, `OAI.SKRatio.Certificate.Data.J4K9.check_15`, `OAI.SKRatio.Certificate.Data.J4K9.check_16`, `OAI.SKRatio.Certificate.Data.J4K9.check_17`, `OAI.SKRatio.Certificate.Data.J4K9.check_18`, `OAI.SKRatio.Certificate.Data.J4K9.check_19`, `OAI.SKRatio.Certificate.Data.J4K9.check_20`, `OAI.SKRatio.Certificate.Data.J4K9.check_21`, `OAI.SKRatio.Certificate.Data.J4K9.check_22`, `OAI.SKRatio.Certificate.Data.J4K9.check_23`, `OAI.SKRatio.Certificate.Data.J4K9.check_24`, `OAI.SKRatio.Certificate.Data.J4K9.check_25`, `OAI.SKRatio.Certificate.Data.J4K9.check_26`, `OAI.SKRatio.Certificate.Data.J4K9.check_27`, `OAI.SKRatio.Certificate.Data.J4K9.check_28`, `OAI.SKRatio.Certificate.Data.J4K9.check_29`, `OAI.SKRatio.Certificate.Data.J4K9.check_30`, `OAI.SKRatio.Certificate.Data.J4K9.check_31`, `OAI.SKRatio.Certificate.Data.J4K9.check_32`, `OAI.SKRatio.Certificate.Data.J4K9.check_33`, `OAI.SKRatio.Certificate.Data.J4K9.check_34`, `OAI.SKRatio.Certificate.Data.J4K9.check_35`, `OAI.SKRatio.Certificate.Data.J4K9.check_36`, `OAI.SKRatio.Certificate.Data.J4K9.check_37`, `OAI.SKRatio.Certificate.Data.J4K9.check_38`, `OAI.SKRatio.Certificate.Data.J4K9.check_39`, `OAI.SKRatio.Certificate.Data.J4K9.checks` and `OAI.SKRatio.Certificate.endpointK_one_bound`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ024S000

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K9

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
  | 10 => ⟨-1/1000000,1/1000000⟩
  | 11 => ⟨-1/1000000,1/1000000⟩
  | 12 => ⟨0,1/500000⟩
  | 13 => ⟨7/500000,1/62500⟩
  | 14 => ⟨77/500000,39/250000⟩
  | 15 => ⟨1171/1000000,1179/1000000⟩
  | 16 => ⟨1/160,98/15625⟩
  | 17 => ⟨4437/200000,22213/1000000⟩
  | 18 => ⟨49053/1000000,1227/25000⟩
  | 19 => ⟨64197/1000000,64259/1000000⟩
  | 20 => ⟨24739/500000,49507/1000000⟩
  | 21 => ⟨2931/125000,587/25000⟩
  | 22 => ⟨7299/1000000,3663/500000⟩
  | 23 => ⟨1583/1000000,399/250000⟩
  | 24 => ⟨249/1000000,127/500000⟩
  | 25 => ⟨29/1000000,31/1000000⟩
  | 26 => ⟨1/500000,3/1000000⟩
  | 27 => ⟨-1/1000000,1/1000000⟩
  | 28 => ⟨-1/1000000,1/1000000⟩
  | 29 => ⟨-1/1000000,1/1000000⟩
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

end SKRatio.Certificate.Data.J4K9

end

end OAI
end


