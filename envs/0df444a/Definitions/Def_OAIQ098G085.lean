-- Prove2me | Definitions.Def_OAIQ098G085
-- name    : OAIQ098G085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T19:02:23.964085+00:00
-- url     : https://prove2.me/theorems/8b397b9a-1bf2-42fc-b91e-6f05ce0708db
-- title:
--   Definitions bundle OAIQ098G085 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 4 definitions. The definitions and types are `OAI.SharpPlanar.IntegerCompact.nodeLookup`, `OAI.SharpPlanar.IntegerCompact.partialBox`, `OAI.SharpPlanar.IntegerCompact.rootLookup`, `OAI.SharpPlanar.IntegerCompact.rootRows`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Fejer`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Fejer.lean).
--
--   **Imports.** It imports the bundles `OAIQ098G065`, `OAIQ098G081`, `OAIQ098G082` and `OAIQ098G084` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098G086`; the proofs of `OAI.SharpPlanar.IntegerGrid.gridRows_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row0_9_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row1_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_7_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_8_contains_g`, `OAI.SharpPlanar.IntegerGrid.row2_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_10_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_11_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row3_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_15_contains_g`, `OAI.SharpPlanar.IntegerGrid.row4_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_13_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_14_contains_g`, `OAI.SharpPlanar.IntegerGrid.row5_15_contains_g` and `OAI.SharpPlanar.IntegerGrid.row5_contains_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G065
import Definitions.Def_OAIQ098G081
import Definitions.Def_OAIQ098G082
import Definitions.Def_OAIQ098G084

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
def rootRows : Fin 32 → Fin 32 → CBox := ![roots0,roots1,roots2,roots3,roots4,roots5,roots6,roots7,roots8,roots9,roots10,roots11,roots12,roots13,roots14,roots15,roots16,roots17,roots18,roots19,roots20,roots21,roots22,roots23,roots24,roots25,roots26,roots27,roots28,roots29,roots30,roots31]
def rootLookup (n : ℕ) : CBox :=
  rootRows ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

def partialBox (v : ℕ) : ℕ → RBox
  | 0 => ⟨0,0⟩
  | N+1 => (partialBox v N).add ((rootLookup (2*(N+1)*(2*v+1))).re.scale 1
      (4*((N+1:ℕ):ℤ)^2-1))

def nodeLookup (n : Fin 256) : RBox := (rootLookup (2*n.val+1)).re
end SharpPlanar.IntegerCompact


end OAI
end


