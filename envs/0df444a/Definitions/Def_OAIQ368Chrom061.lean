-- Prove2me | Definitions.Def_OAIQ368Chrom061
-- name    : OAIQ368Chrom061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:36:54.378451+00:00
-- url     : https://prove2.me/theorems/1ba1aa65-549f-4d47-9b82-f8e1475f5889
-- title:
--   Definitions bundle OAIQ368Chrom061 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.ElementaryPositivity.TriangularDynamics.triangularCommutativityAddGroup`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinearSectionAddGroup`, `OAI.ElementaryPositivity.TriangularDynamics.triangularLinearSectionRing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Walls_TriangularCommutativity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean), [`Chromatic_Walls_TriangularLinearSection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearSection.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom058` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom058

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLinearSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularLinearSectionRing : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)

local instance triangularLinearSectionAddCommGroup_ra3851c_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularLinearSectionAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularCommutativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}
local instance triangularCommutativityRing_ra3851c_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularCommutativityAddCommGroup_ra3851c_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularCommutativityAddGroup : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end


