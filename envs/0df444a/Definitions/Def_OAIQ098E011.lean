-- Prove2me | Definitions.Def_OAIQ098E011
-- name    : OAIQ098E011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T04:53:33.194305+00:00
-- url     : https://prove2.me/theorems/05b30818-56d8-438d-b749-5bd25de64eca
-- title:
--   Definitions bundle OAIQ098E011 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 definitions. The definitions and types are `OAI.SharpPlanar.Numerical.lDeriv`, `OAI.SharpPlanar.Numerical.lNode`, `OAI.SharpPlanar.Numerical.lowExteriorIndex`, `OAI.SharpPlanar.Numerical.node12`, `OAI.SharpPlanar.Numerical.node13`, `OAI.SharpPlanar.Numerical.node15`, `OAI.SharpPlanar.Numerical.node16`, `OAI.SharpPlanar.Numerical.node7`, `OAI.SharpPlanar.Numerical.node9`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Indices`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E054`, `OAIQ098E059` and `OAIQ098E111`; the statement `OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_e`; the proof of `OAI.SharpPlanar.Numerical.lowExteriorIndex_injective_e`.
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

def node7 : Node := ⟨7,by norm_num [residues]⟩
def node9 : Node := ⟨9,by norm_num [residues]⟩
def node12 : Node := ⟨12,by norm_num [residues]⟩
def node13 : Node := ⟨13,by norm_num [residues]⟩
def node15 : Node := ⟨15,by norm_num [residues]⟩
def node16 : Node := ⟨16,by norm_num [residues]⟩
def lNode : Fin 12 → Node := ![node7,node9,node12,node13,node15,node16,node7,node9,node12,node13,node15,node16]
def lDeriv : Fin 12 → Bool := ![false,false,false,false,false,false,true,true,true,true,true,true]
open scoped BigOperators
def lowExteriorIndex (i : Fin 12) : Node × Bool := (lNode i,lDeriv i)
end SharpPlanar.Numerical

end OAI
end


