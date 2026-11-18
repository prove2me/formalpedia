-- Prove2me | Definitions.Def_OAIQ368Chrom010
-- name    : OAIQ368Chrom010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:47.595022+00:00
-- url     : https://prove2.me/theorems/41dd90e8-b1a0-44ba-bb10-21aa005ca748
-- title:
--   Definitions bundle OAIQ368Chrom010 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 2 definitions and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.incomingTransportTraceAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.incomingTransportTraceRing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Walls_IncomingTransportTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/IncomingTransportTrace.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe` and `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingTransportTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
variable [Module ℚ A]
@[simp] lemma log_one : FormalLog.log (1 : PowerSeries A)=0 := by
  ext n
  simp [FormalLog.log]
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance incomingTransportTraceRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance incomingTransportTraceAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


