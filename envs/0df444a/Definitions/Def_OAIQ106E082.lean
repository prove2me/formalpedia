-- Prove2me | Definitions.Def_OAIQ106E082
-- name    : OAIQ106E082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T19:26:31.607839+00:00
-- url     : https://prove2.me/theorems/63038e72-1bba-4334-b48d-0b9c2bd8beec
-- title:
--   Definitions bundle OAIQ106E082 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.codeChunk66`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`MutuallyUnbiased_MixedSemantics_Nodes66`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedSemantics/Nodes66.lean).
--
--   **Imports.** It imports the bundles `OAIQ106E002`, `OAIQ106E079` and `OAIQ106E081` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106E085`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E079
import Definitions.Def_OAIQ106E081

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def codeChunk66 : Array Code := #[⟨5, 3, 3, node4224, node4224Labels⟩, ⟨4, 3, 3, node4225, node4225Labels⟩, ⟨4, 3, 3, node4226, node4226Labels⟩, ⟨4, 3, 3, node4227, node4227Labels⟩, ⟨4, 3, 3, node4228, node4228Labels⟩, ⟨4, 3, 3, node4229, node4229Labels⟩, ⟨6, 3, 3, node4230, node4230Labels⟩, ⟨5, 3, 3, node4231, node4231Labels⟩, ⟨6, 3, 3, node4232, node4232Labels⟩, ⟨5, 3, 3, node4233, node4233Labels⟩, ⟨5, 3, 3, node4234, node4234Labels⟩, ⟨4, 3, 3, node4235, node4235Labels⟩, ⟨6, 3, 3, node4236, node4236Labels⟩, ⟨5, 3, 3, node4237, node4237Labels⟩, ⟨5, 3, 3, node4238, node4238Labels⟩, ⟨5, 3, 3, node4239, node4239Labels⟩, ⟨4, 3, 3, node4240, node4240Labels⟩, ⟨4, 3, 3, node4241, node4241Labels⟩, ⟨4, 3, 3, node4242, node4242Labels⟩, ⟨4, 3, 3, node4243, node4243Labels⟩, ⟨6, 3, 3, node4244, node4244Labels⟩, ⟨6, 3, 3, node4245, node4245Labels⟩, ⟨6, 3, 3, node4246, node4246Labels⟩, ⟨5, 3, 3, node4247, node4247Labels⟩, ⟨6, 3, 3, node4248, node4248Labels⟩, ⟨6, 3, 3, node4249, node4249Labels⟩, ⟨6, 3, 3, node4250, node4250Labels⟩, ⟨5, 3, 3, node4251, node4251Labels⟩, ⟨6, 3, 3, node4252, node4252Labels⟩, ⟨5, 3, 3, node4253, node4253Labels⟩, ⟨5, 3, 3, node4254, node4254Labels⟩, ⟨5, 3, 3, node4255, node4255Labels⟩, ⟨5, 3, 3, node4256, node4256Labels⟩, ⟨4, 3, 3, node4257, node4257Labels⟩, ⟨6, 3, 3, node4258, node4258Labels⟩, ⟨5, 3, 3, node4259, node4259Labels⟩, ⟨5, 3, 3, node4260, node4260Labels⟩, ⟨5, 3, 3, node4261, node4261Labels⟩, ⟨4, 3, 3, node4262, node4262Labels⟩, ⟨6, 3, 3, node4263, node4263Labels⟩, ⟨5, 3, 3, node4264, node4264Labels⟩, ⟨5, 3, 3, node4265, node4265Labels⟩, ⟨4, 3, 3, node4266, node4266Labels⟩, ⟨5, 3, 3, node4267, node4267Labels⟩, ⟨5, 3, 3, node4268, node4268Labels⟩, ⟨4, 3, 3, node4269, node4269Labels⟩, ⟨4, 3, 3, node4270, node4270Labels⟩, ⟨4, 3, 3, node4271, node4271Labels⟩, ⟨4, 3, 3, node4272, node4272Labels⟩, ⟨4, 3, 3, node4273, node4273Labels⟩, ⟨3, 3, 3, node4274, node4274Labels⟩, ⟨5, 3, 3, node4275, node4275Labels⟩, ⟨4, 3, 3, node4276, node4276Labels⟩, ⟨4, 3, 3, node4277, node4277Labels⟩, ⟨4, 3, 3, node4278, node4278Labels⟩, ⟨4, 3, 3, node4279, node4279Labels⟩, ⟨3, 3, 3, node4280, node4280Labels⟩, ⟨4, 3, 3, node4281, node4281Labels⟩, ⟨3, 3, 3, node4282, node4282Labels⟩, ⟨4, 3, 3, node4283, node4283Labels⟩, ⟨3, 3, 3, node4284, node4284Labels⟩, ⟨3, 3, 3, node4285, node4285Labels⟩, ⟨6, 3, 3, node4286, node4286Labels⟩, ⟨6, 3, 3, node4287, node4287Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end


