-- Prove2me | Definitions.Def_OAIQ098E006
-- name    : OAIQ098E006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T04:53:29.513909+00:00
-- url     : https://prove2.me/theorems/5020f635-2f43-49e2-b576-fab8ac3029ca
-- title:
--   Definitions bundle OAIQ098E006 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.eNode`, `OAI.SharpPlanar.Numerical.exteriorIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Indices`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E007` and `OAIQ098E125`; the statement `OAI.SharpPlanar.Numerical.exteriorIndex_injective_e`; the proof of `OAI.SharpPlanar.Numerical.exteriorIndex_injective_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E000

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

open scoped BigOperators
def eNode : Fin 48 → Node := ![⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩,⟨43,by norm_num [residues]⟩,⟨45,by norm_num [residues]⟩,⟨48,by norm_num [residues]⟩,⟨49,by norm_num [residues]⟩,⟨51,by norm_num [residues]⟩,⟨52,by norm_num [residues]⟩,⟨55,by norm_num [residues]⟩,⟨57,by norm_num [residues]⟩,⟨60,by norm_num [residues]⟩,⟨61,by norm_num [residues]⟩,⟨63,by norm_num [residues]⟩,⟨64,by norm_num [residues]⟩,⟨67,by norm_num [residues]⟩,⟨69,by norm_num [residues]⟩,⟨72,by norm_num [residues]⟩,⟨73,by norm_num [residues]⟩,⟨75,by norm_num [residues]⟩,⟨76,by norm_num [residues]⟩,⟨79,by norm_num [residues]⟩,⟨81,by norm_num [residues]⟩,⟨84,by norm_num [residues]⟩,⟨85,by norm_num [residues]⟩,⟨87,by norm_num [residues]⟩,⟨88,by norm_num [residues]⟩,⟨91,by norm_num [residues]⟩,⟨93,by norm_num [residues]⟩,⟨96,by norm_num [residues]⟩,⟨97,by norm_num [residues]⟩,⟨99,by norm_num [residues]⟩,⟨100,by norm_num [residues]⟩]
def exteriorIndex (i : Fin 48 × Fin 2) : Node × Bool := (eNode i.1,decide (i.2.val=1))
end SharpPlanar.Numerical

end OAI
end


