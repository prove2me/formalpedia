-- Prove2me | Definitions.Def_OAIQ259US008
-- name    : OAIQ259US008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:09:49.395197+00:00
-- url     : https://prove2.me/theorems/0b7c271f-4ac1-44e5-98b2-f407efa1a4b3
-- title:
--   Definitions bundle OAIQ259US008 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 301 declarations of OpenAI's Lean: 301 definitions. The definitions and types are `OAI.UniversalTensorSquare.degreeP112`, `OAI.UniversalTensorSquare.degreeP116`, `OAI.UniversalTensorSquare.degreeP118`, `OAI.UniversalTensorSquare.degreeP12`, `OAI.UniversalTensorSquare.degreeP14`, `OAI.UniversalTensorSquare.degreeP151`, `OAI.UniversalTensorSquare.degreeP16`, `OAI.UniversalTensorSquare.degreeP17`, `OAI.UniversalTensorSquare.degreeP18`, `OAI.UniversalTensorSquare.degreeP19`, `OAI.UniversalTensorSquare.degreeP20`, `OAI.UniversalTensorSquare.degreeP22`, `OAI.UniversalTensorSquare.degreeP23`, `OAI.UniversalTensorSquare.degreeP24`, `OAI.UniversalTensorSquare.degreeP25`, `OAI.UniversalTensorSquare.degreeP26`, `OAI.UniversalTensorSquare.degreeP27`, `OAI.UniversalTensorSquare.degreeP29`, `OAI.UniversalTensorSquare.degreeP30`, `OAI.UniversalTensorSquare.degreeP31`, `OAI.UniversalTensorSquare.degreeP32`, `OAI.UniversalTensorSquare.degreeP33`, `OAI.UniversalTensorSquare.degreeP34`, `OAI.UniversalTensorSquare.degreeP35`, `OAI.UniversalTensorSquare.degreeP37`, `OAI.UniversalTensorSquare.degreeP38`, `OAI.UniversalTensorSquare.degreeP40`, `OAI.UniversalTensorSquare.degreeP42`, `OAI.UniversalTensorSquare.degreeP47`, `OAI.UniversalTensorSquare.degreeP48`, `OAI.UniversalTensorSquare.degreeQs116`, `OAI.UniversalTensorSquare.degreeRegion89_1`, `OAI.UniversalTensorSquare.degreeRegion89_2`, `OAI.UniversalTensorSquare.degreeRegion89_3`, `OAI.UniversalTensorSquare.degreeTree116`, `OAI.UniversalTensorSquare.degreeTree116_0`, `OAI.UniversalTensorSquare.degreeTree118`, `OAI.UniversalTensorSquare.degreeTree118_0`, `OAI.UniversalTensorSquare.degreeTree14`, `OAI.UniversalTensorSquare.degreeTree14_0` and 261 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `UniversalSquare_Finite_DegreePlans116`, `UniversalSquare_Finite_DegreePlans118`, `UniversalSquare_Finite_DegreePlans14`, `UniversalSquare_Finite_DegreePlans16`, `UniversalSquare_Finite_DegreePlans18`, `UniversalSquare_Finite_DegreePlans19`, `UniversalSquare_Finite_DegreePlans20`, `UniversalSquare_Finite_DegreePlans22`, `UniversalSquare_Finite_DegreePlans24`, `UniversalSquare_Finite_DegreePlans26`, `UniversalSquare_Finite_DegreePlans31`, `UniversalSquare_Finite_DegreePlans35`, `UniversalSquare_Finite_DegreePlans37`, `UniversalSquare_Finite_DegreeRegionData89`, `UniversalSquare_Finite_DegreeTreeData116`, `UniversalSquare_Finite_DegreeTreeData118`, `UniversalSquare_Finite_DegreeTreeData14`, `UniversalSquare_Finite_DegreeTreeData16`, `UniversalSquare_Finite_DegreeTreeData18`, `UniversalSquare_Finite_DegreeTreeData19`, `UniversalSquare_Finite_DegreeTreeData20`, `UniversalSquare_Finite_DegreeTreeData22`, `UniversalSquare_Finite_DegreeTreeData24`, `UniversalSquare_Finite_DegreeTreeData26`, `UniversalSquare_Finite_DegreeTreeData31`, `UniversalSquare_Finite_DegreeTreeData35`, `UniversalSquare_Finite_DegreeTreeData37`, `UniversalSquare_Finite_DegreeTreeData39`, `UniversalSquare_Finite_NumericalDegree112`, `UniversalSquare_Finite_NumericalDegree12`, `UniversalSquare_Finite_NumericalDegree151`, `UniversalSquare_Finite_NumericalDegree17`, `UniversalSquare_Finite_NumericalDegree23`, `UniversalSquare_Finite_NumericalDegree25`, `UniversalSquare_Finite_NumericalDegree27`, `UniversalSquare_Finite_NumericalDegree29`, `UniversalSquare_Finite_NumericalDegree30`, `UniversalSquare_Finite_NumericalDegree32`, `UniversalSquare_Finite_NumericalDegree33`, `UniversalSquare_Finite_NumericalDegree34`, `UniversalSquare_Finite_NumericalDegree38`, `UniversalSquare_Finite_NumericalDegree40`, `UniversalSquare_Finite_NumericalDegree42`, `UniversalSquare_Finite_NumericalDegree47`, `UniversalSquare_Finite_NumericalDegree48`.
--
--   **Imports.** It imports the bundles `OAIQ259US001` and `OAIQ259US002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ259US021`; the statements `OAI.UniversalTensorSquare.degreeCheck116`, `OAI.UniversalTensorSquare.degreeCheck118`, `OAI.UniversalTensorSquare.degreeCheck151`, `OAI.UniversalTensorSquare.degreeCheck151_2_0`, `OAI.UniversalTensorSquare.degreeCheck151_2_1`, `OAI.UniversalTensorSquare.degreeCheck151_2_2`, `OAI.UniversalTensorSquare.degreeCheck151_2_3`, `OAI.UniversalTensorSquare.degreeCheck151_2_4`, `OAI.UniversalTensorSquare.degreeCheck151_3_0`, `OAI.UniversalTensorSquare.degreeCheck151_3_1`, `OAI.UniversalTensorSquare.degreeCheck151_3_2`, `OAI.UniversalTensorSquare.degreeCheck151_3_3`, `OAI.UniversalTensorSquare.degreeCheck151_3_4`, `OAI.UniversalTensorSquare.degreeCheck151_4_0`, `OAI.UniversalTensorSquare.degreeCheck151_4_1`, `OAI.UniversalTensorSquare.degreeCheck151_4_2`, `OAI.UniversalTensorSquare.degreeCheck151_4_3`, `OAI.UniversalTensorSquare.degreeCheck151_4_4`, `OAI.UniversalTensorSquare.degreeCheck24`, `OAI.UniversalTensorSquare.degreeCheck31`, `OAI.UniversalTensorSquare.degreeCheck33`, `OAI.UniversalTensorSquare.degreeCheck35`, `OAI.UniversalTensorSquare.degreeCheck37`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31`, `OAI.UniversalTensorSquare.degreeTree20_13All`, `OAI.UniversalTensorSquare.degreeTree20_2All`, `OAI.UniversalTensorSquare.degreeTree20_3All`, `OAI.UniversalTensorSquare.degreeTree20_4All`, `OAI.UniversalTensorSquare.degreeTree20_6All`, `OAI.UniversalTensorSquare.degreeTree20_8All`, `OAI.UniversalTensorSquare.degreeTree20_9All`, `OAI.UniversalTensorSquare.degreeTree22_10All`, `OAI.UniversalTensorSquare.degreeTree22_12All`, `OAI.UniversalTensorSquare.degreeTree22_1All`, `OAI.UniversalTensorSquare.degreeTree22_4All`, `OAI.UniversalTensorSquare.degreeTree22_5All`, `OAI.UniversalTensorSquare.degreeTree22_6All`, `OAI.UniversalTensorSquare.degreeTree22_8All`, `OAI.UniversalTensorSquare.degreeTree22_9All`, `OAI.UniversalTensorSquare.degreeTree24_11All`, `OAI.UniversalTensorSquare.degreeTree24_12All`, `OAI.UniversalTensorSquare.degreeTree24_14All`, `OAI.UniversalTensorSquare.degreeTree24_17All`, `OAI.UniversalTensorSquare.degreeTree24_19All`, `OAI.UniversalTensorSquare.degreeTree24_1All`, `OAI.UniversalTensorSquare.degreeTree24_21All`, `OAI.UniversalTensorSquare.degreeTree24_22All`, `OAI.UniversalTensorSquare.degreeTree24_23All`, `OAI.UniversalTensorSquare.degreeTree24_27All`, `OAI.UniversalTensorSquare.degreeTree24_2All`, `OAI.UniversalTensorSquare.degreeTree24_3All`, `OAI.UniversalTensorSquare.degreeTree24_5All`, `OAI.UniversalTensorSquare.degreeTree24_8All`, `OAI.UniversalTensorSquare.degreeTree26_0All`, `OAI.UniversalTensorSquare.degreeTree26_10All`, `OAI.UniversalTensorSquare.degreeTree26_11All`, `OAI.UniversalTensorSquare.degreeTree26_13All`, `OAI.UniversalTensorSquare.degreeTree26_14All`, `OAI.UniversalTensorSquare.degreeTree26_15All`, `OAI.UniversalTensorSquare.degreeTree26_18All`, `OAI.UniversalTensorSquare.degreeTree26_19All`, `OAI.UniversalTensorSquare.degreeTree26_20All`, `OAI.UniversalTensorSquare.degreeTree26_21All`, `OAI.UniversalTensorSquare.degreeTree26_24All`, `OAI.UniversalTensorSquare.degreeTree26_26All`, `OAI.UniversalTensorSquare.degreeTree26_27All`, `OAI.UniversalTensorSquare.degreeTree26_28All`, `OAI.UniversalTensorSquare.degreeTree26_32All`, `OAI.UniversalTensorSquare.degreeTree26_33All`, `OAI.UniversalTensorSquare.degreeTree26_34All`, `OAI.UniversalTensorSquare.degreeTree26_35All`, `OAI.UniversalTensorSquare.degreeTree26_37All`, `OAI.UniversalTensorSquare.degreeTree26_38All`, `OAI.UniversalTensorSquare.degreeTree26_39All`, `OAI.UniversalTensorSquare.degreeTree26_41All`, `OAI.UniversalTensorSquare.degreeTree26_42All`, `OAI.UniversalTensorSquare.degreeTree26_44All`, `OAI.UniversalTensorSquare.degreeTree26_46All`, `OAI.UniversalTensorSquare.degreeTree26_47All`, `OAI.UniversalTensorSquare.degreeTree26_50All`, `OAI.UniversalTensorSquare.degreeTree26_53All`, `OAI.UniversalTensorSquare.degreeTree26_56All`, `OAI.UniversalTensorSquare.degreeTree26_57All`, `OAI.UniversalTensorSquare.degreeTree26_58All`, `OAI.UniversalTensorSquare.degreeTree26_5All`, `OAI.UniversalTensorSquare.degreeTree26_60All`, `OAI.UniversalTensorSquare.degreeTree26_61All`, `OAI.UniversalTensorSquare.degreeTree26_6All`, `OAI.UniversalTensorSquare.degreeTree26_7All`, `OAI.UniversalTensorSquare.degreeTree26_9All`, `OAI.UniversalTensorSquare.degreeTree31_0All`, `OAI.UniversalTensorSquare.degreeTree31_1All`, `OAI.UniversalTensorSquare.degreeTree31_2All`, `OAI.UniversalTensorSquare.degreeTree35_0All`, `OAI.UniversalTensorSquare.degreeTree35_10All`, `OAI.UniversalTensorSquare.degreeTree35_12All`, `OAI.UniversalTensorSquare.degreeTree35_14All`, `OAI.UniversalTensorSquare.degreeTree35_16All`, `OAI.UniversalTensorSquare.degreeTree35_18All`, `OAI.UniversalTensorSquare.degreeTree35_19All`, `OAI.UniversalTensorSquare.degreeTree35_1All`, `OAI.UniversalTensorSquare.degreeTree35_21All`, `OAI.UniversalTensorSquare.degreeTree35_22All`, `OAI.UniversalTensorSquare.degreeTree35_23All`, `OAI.UniversalTensorSquare.degreeTree35_4All`, `OAI.UniversalTensorSquare.degreeTree35_5All`, `OAI.UniversalTensorSquare.degreeTree35_7All`, `OAI.UniversalTensorSquare.degreeTree35_8All`, `OAI.UniversalTensorSquare.degreeTree39_0All`, `OAI.UniversalTensorSquare.degreeTree39_100All`, `OAI.UniversalTensorSquare.degreeTree39_102All`, `OAI.UniversalTensorSquare.degreeTree39_103All`, `OAI.UniversalTensorSquare.degreeTree39_104All`, `OAI.UniversalTensorSquare.degreeTree39_106All`, `OAI.UniversalTensorSquare.degreeTree39_109All`, `OAI.UniversalTensorSquare.degreeTree39_10All`, `OAI.UniversalTensorSquare.degreeTree39_110All`, `OAI.UniversalTensorSquare.degreeTree39_112All`, `OAI.UniversalTensorSquare.degreeTree39_114All`, `OAI.UniversalTensorSquare.degreeTree39_117All`, `OAI.UniversalTensorSquare.degreeTree39_119All`, `OAI.UniversalTensorSquare.degreeTree39_11All`, `OAI.UniversalTensorSquare.degreeTree39_122All`, `OAI.UniversalTensorSquare.degreeTree39_123All`, `OAI.UniversalTensorSquare.degreeTree39_124All`, `OAI.UniversalTensorSquare.degreeTree39_13All`, `OAI.UniversalTensorSquare.degreeTree39_14All`, `OAI.UniversalTensorSquare.degreeTree39_15All`, `OAI.UniversalTensorSquare.degreeTree39_16All`, `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree39_18All`, `OAI.UniversalTensorSquare.degreeTree39_19All`, `OAI.UniversalTensorSquare.degreeTree39_1All`, `OAI.UniversalTensorSquare.degreeTree39_23All`, `OAI.UniversalTensorSquare.degreeTree39_24All`, `OAI.UniversalTensorSquare.degreeTree39_25All`, `OAI.UniversalTensorSquare.degreeTree39_27All`, `OAI.UniversalTensorSquare.degreeTree39_29All`, `OAI.UniversalTensorSquare.degreeTree39_2All`, `OAI.UniversalTensorSquare.degreeTree39_30All`, `OAI.UniversalTensorSquare.degreeTree39_31All`, `OAI.UniversalTensorSquare.degreeTree39_3All`, `OAI.UniversalTensorSquare.degreeTree39_4All`, `OAI.UniversalTensorSquare.degreeTree39_63All`, `OAI.UniversalTensorSquare.degreeTree39_65All`, `OAI.UniversalTensorSquare.degreeTree39_66All`, `OAI.UniversalTensorSquare.degreeTree39_67All`, `OAI.UniversalTensorSquare.degreeTree39_72All`, `OAI.UniversalTensorSquare.degreeTree39_73All`, `OAI.UniversalTensorSquare.degreeTree39_74All`, `OAI.UniversalTensorSquare.degreeTree39_77All`, `OAI.UniversalTensorSquare.degreeTree39_80All`, `OAI.UniversalTensorSquare.degreeTree39_81All`, `OAI.UniversalTensorSquare.degreeTree39_83All`, `OAI.UniversalTensorSquare.degreeTree39_84All`, `OAI.UniversalTensorSquare.degreeTree39_86All`, `OAI.UniversalTensorSquare.degreeTree39_87All`, `OAI.UniversalTensorSquare.degreeTree39_88All`, `OAI.UniversalTensorSquare.degreeTree39_89All`, `OAI.UniversalTensorSquare.degreeTree39_90All`, `OAI.UniversalTensorSquare.degreeTree39_92All`, `OAI.UniversalTensorSquare.degreeTree39_93All`, `OAI.UniversalTensorSquare.degreeTree39_94All`, `OAI.UniversalTensorSquare.degreeTree39_95All`, `OAI.UniversalTensorSquare.degreeTree39_99All`, `OAI.UniversalTensorSquare.degreeTree39_9All`, `OAI.UniversalTensorSquare.degreeTreeAll116`, `OAI.UniversalTensorSquare.degreeTreeAll16`, `OAI.UniversalTensorSquare.degreeTreeAll18`, `OAI.UniversalTensorSquare.degreeTreeAll22`, `OAI.UniversalTensorSquare.degreeTreeAll37`, `OAI.UniversalTensorSquare.degreeUnionBranch31_36`, `OAI.UniversalTensorSquare.degreeUnionBranch31_64`, `OAI.UniversalTensorSquare.degreeUnionBranch31_8`, `OAI.UniversalTensorSquare.degreeUnionBranch35_101`, `OAI.UniversalTensorSquare.degreeUnionBranch35_102`, `OAI.UniversalTensorSquare.degreeUnionBranch35_107`, `OAI.UniversalTensorSquare.degreeUnionBranch35_114`, `OAI.UniversalTensorSquare.degreeUnionBranch35_122`, `OAI.UniversalTensorSquare.degreeUnionBranch35_13`, `OAI.UniversalTensorSquare.degreeUnionBranch35_145`, `OAI.UniversalTensorSquare.degreeUnionBranch35_20`, `OAI.UniversalTensorSquare.degreeUnionBranch35_42`, `OAI.UniversalTensorSquare.degreeUnionBranch35_52`, `OAI.UniversalTensorSquare.degreeUnionBranch35_57`, `OAI.UniversalTensorSquare.degreeUnionBranch35_63`, `OAI.UniversalTensorSquare.degreeUnionBranch35_70`, `OAI.UniversalTensorSquare.degreeUnionBranch35_8`, `OAI.UniversalTensorSquare.degreeUnionCheck26` and `OAI.UniversalTensorSquare.degreeUnionCheck35`; the proofs of `OAI.UniversalTensorSquare.degreeCheck116`, `OAI.UniversalTensorSquare.degreeCheck118`, `OAI.UniversalTensorSquare.degreeCheck151`, `OAI.UniversalTensorSquare.degreeCheck151_2_0`, `OAI.UniversalTensorSquare.degreeCheck151_2_1`, `OAI.UniversalTensorSquare.degreeCheck151_2_2`, `OAI.UniversalTensorSquare.degreeCheck151_2_3`, `OAI.UniversalTensorSquare.degreeCheck151_2_4`, `OAI.UniversalTensorSquare.degreeCheck151_3_0`, `OAI.UniversalTensorSquare.degreeCheck151_3_1`, `OAI.UniversalTensorSquare.degreeCheck151_3_2`, `OAI.UniversalTensorSquare.degreeCheck151_3_3`, `OAI.UniversalTensorSquare.degreeCheck151_3_4`, `OAI.UniversalTensorSquare.degreeCheck151_4_0`, `OAI.UniversalTensorSquare.degreeCheck151_4_1`, `OAI.UniversalTensorSquare.degreeCheck151_4_2`, `OAI.UniversalTensorSquare.degreeCheck151_4_3`, `OAI.UniversalTensorSquare.degreeCheck151_4_4`, `OAI.UniversalTensorSquare.degreeCheck24`, `OAI.UniversalTensorSquare.degreeCheck31`, `OAI.UniversalTensorSquare.degreeCheck33`, `OAI.UniversalTensorSquare.degreeCheck35`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31`, `OAI.UniversalTensorSquare.degreeTree39_117All`, `OAI.UniversalTensorSquare.degreeTree39_11All`, `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree39_30All`, `OAI.UniversalTensorSquare.degreeTree39_84All`, `OAI.UniversalTensorSquare.degreeUnionBranch31_36`, `OAI.UniversalTensorSquare.degreeUnionBranch31_64`, `OAI.UniversalTensorSquare.degreeUnionBranch31_8`, `OAI.UniversalTensorSquare.degreeUnionBranch35_101`, `OAI.UniversalTensorSquare.degreeUnionBranch35_102`, `OAI.UniversalTensorSquare.degreeUnionBranch35_107`, `OAI.UniversalTensorSquare.degreeUnionBranch35_114`, `OAI.UniversalTensorSquare.degreeUnionBranch35_122`, `OAI.UniversalTensorSquare.degreeUnionBranch35_13`, `OAI.UniversalTensorSquare.degreeUnionBranch35_145`, `OAI.UniversalTensorSquare.degreeUnionBranch35_20`, `OAI.UniversalTensorSquare.degreeUnionBranch35_42`, `OAI.UniversalTensorSquare.degreeUnionBranch35_52`, `OAI.UniversalTensorSquare.degreeUnionBranch35_57`, `OAI.UniversalTensorSquare.degreeUnionBranch35_63`, `OAI.UniversalTensorSquare.degreeUnionBranch35_70`, `OAI.UniversalTensorSquare.degreeUnionBranch35_8`, `OAI.UniversalTensorSquare.degreeUnionCheck26`, `OAI.UniversalTensorSquare.degreeUnionCheck35`, `OAI.UniversalTensorSquare.degree_pos151`, `OAI.UniversalTensorSquare.degree_pos32`, `OAI.UniversalTensorSquare.degree_pos33`, `OAI.UniversalTensorSquare.degree_pos34` and `OAI.UniversalTensorSquare.degree_pos48`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US002

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree116_0 : RowTree := (.node [11,11,11,11,11,11,11,11,10,9,9] (.node [11,11,11,11,11,11,11,10,10,10,9] (.node [11,11,11,11,11,11,10,10,10,10,10] .empty .empty) .empty) (.node [11,11,11,11,11,11,11,11,10,10,8] .empty .empty))

def degreeTree116 : RowTree := degreeTree116_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeQs116 : List (List ℕ) := [degreeRows116_1]

abbrev degreeP116 := TreeResidual 12 19 degreeQs116 degreeTree116

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree118_0 : RowTree := (.node [11,11,11,11,11,11,11,11,11,10,9] (.node [11,11,11,11,11,11,11,11,10,10,10] .empty .empty) .empty)

def degreeTree118 : RowTree := degreeTree118_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP118 := TreeResidual 12 20 degreeQs118 degreeTree118

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree14_0 : RowTree := (.node [7,2,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1] .empty .empty) .empty)

def degreeTree14 : RowTree := degreeTree14_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP14 := TreeResidual 4 2 degreeQs14 degreeTree14

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree16_0 : RowTree := (.node [6,4,1,1,1,1,1,1] (.node [6,3,1,1,1,1,1,1,1] (.node [6,2,2,2,1,1,1,1] (.node [6,2,1,1,1,1,1,1,1,1] (.node [6,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,1,1,1,1,1,1] .empty .empty)) (.node [6,2,2,2,2,2] (.node [6,2,2,2,2,1,1] .empty .empty) .empty)) (.node [6,3,2,2,2,1] (.node [6,3,2,2,1,1,1] (.node [6,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [6,3,3,2,1,1] (.node [6,3,3,1,1,1,1] .empty .empty) .empty))) (.node [7,2,2,1,1,1,1,1] (.node [6,5,1,1,1,1,1] (.node [6,4,2,2,1,1] (.node [6,4,2,1,1,1,1] .empty .empty) .empty) (.node [7,2,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [7,3,2,1,1,1,1] (.node [7,3,1,1,1,1,1,1] (.node [7,2,2,2,1,1,1] .empty .empty) .empty) (.node [8,2,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree16 : RowTree := degreeTree16_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP16 := TreeResidual 4 3 degreeQs16 degreeTree16

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree18_0 : RowTree := (.node [7,4,1,1,1,1,1,1,1] (.node [7,3,1,1,1,1,1,1,1,1] (.node [7,2,2,2,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,1] (.node [7,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [7,3,2,2,2,1,1] (.node [7,3,2,2,1,1,1,1] (.node [7,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,3,3,2,1,1,1] (.node [7,3,3,1,1,1,1,1] .empty .empty) .empty))) (.node [8,2,2,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1] (.node [7,4,2,2,1,1,1] (.node [7,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,1,1,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [8,3,2,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1] (.node [8,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [9,2,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree18 : RowTree := degreeTree18_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP18 := TreeResidual 4 4 degreeQs18 degreeTree18

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree19_0 : RowTree := (.node [8,3,2,2,1,1,1,1] (.node [8,2,2,2,2,1,1,1] .empty .empty) (.node [8,3,3,1,1,1,1,1] .empty .empty))

def degreeTree19 : RowTree := degreeTree19_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP19 := TreeResidual 5 2 degreeQs19 degreeTree19

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree20_0 : RowTree := (.node [6,2,2,2,2,1,1,1,1,1,1] (.node [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [5,5,4,3,3] (.node [5,4,4,4,3] (.node [4,4,4,4,4] .empty .empty) .empty) (.node [5,5,4,4,2] .empty .empty)) (.node [6,2,2,1,1,1,1,1,1,1,1,1,1] (.node [6,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [6,3,1,1,1,1,1,1,1,1,1,1,1] (.node [6,2,2,2,2,2,2,1,1] (.node [6,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [6,2,2,2,2,2,2,2] .empty .empty)) (.node [6,3,2,2,1,1,1,1,1,1,1] (.node [6,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,3,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree20_1 : RowTree := (.node [6,3,3,3,2,2,1] (.node [6,3,3,2,2,2,1,1] (.node [6,3,3,2,1,1,1,1,1,1] (.node [6,3,3,1,1,1,1,1,1,1,1] (.node [6,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [6,3,3,2,2,1,1,1,1] .empty .empty)) (.node [6,3,3,3,1,1,1,1,1] (.node [6,3,3,2,2,2,2] .empty .empty) (.node [6,3,3,3,2,1,1,1] .empty .empty))) (.node [6,4,2,1,1,1,1,1,1,1,1] (.node [6,3,3,3,3,2] (.node [6,3,3,3,3,1,1] .empty .empty) (.node [6,4,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,4,2,2,2,1,1,1,1] (.node [6,4,2,2,1,1,1,1,1,1] .empty .empty) (.node [6,4,2,2,2,2,1,1] .empty .empty))))

def degreeTree20_2 : RowTree := (.node [6,3,2,2,2,2,1,1,1] degreeTree20_0 degreeTree20_1)

def degreeTree20_3 : RowTree := (.node [6,4,4,1,1,1,1,1,1] (.node [6,4,3,3,1,1,1,1] (.node [6,4,3,2,2,1,1,1] (.node [6,4,3,2,1,1,1,1,1] (.node [6,4,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [6,4,3,2,2,2,1] .empty .empty)) (.node [6,4,3,3,2,2] (.node [6,4,3,3,2,1,1] .empty .empty) (.node [6,4,3,3,3,1] .empty .empty))) (.node [6,4,4,3,1,1,1] (.node [6,4,4,2,2,1,1] (.node [6,4,4,2,1,1,1,1] .empty .empty) (.node [6,4,4,2,2,2] .empty .empty)) (.node [6,4,4,4,1,1] (.node [6,4,4,3,2,1] .empty .empty) (.node [6,5,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_4 : RowTree := (.node [6,5,3,3,1,1,1] (.node [6,5,3,1,1,1,1,1,1] (.node [6,5,2,2,2,1,1,1] (.node [6,5,2,2,1,1,1,1,1] .empty .empty) (.node [6,5,2,2,2,2,1] .empty .empty)) (.node [6,5,3,2,2,1,1] (.node [6,5,3,2,1,1,1,1] .empty .empty) (.node [6,5,3,2,2,2] .empty .empty))) (.node [6,5,5,1,1,1,1] (.node [6,5,4,1,1,1,1,1] (.node [6,5,3,3,2,1] .empty .empty) (.node [6,5,4,2,1,1,1] .empty .empty)) (.node [6,6,2,1,1,1,1,1,1] (.node [6,6,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,6,2,2,1,1,1,1] .empty .empty))))

def degreeTree20_5 : RowTree := (.node [6,5,2,1,1,1,1,1,1,1] degreeTree20_3 degreeTree20_4)

def degreeTree20_6 : RowTree := (.node [6,4,2,2,2,2,2] degreeTree20_2 degreeTree20_5)

def degreeTree20_7 : RowTree := (.node [7,2,2,2,2,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,6,3,2,1,1,1] (.node [6,6,3,1,1,1,1,1] (.node [6,6,2,2,2,2] .empty .empty) .empty) (.node [6,6,4,1,1,1,1] .empty .empty)) (.node [7,2,2,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [7,3,2,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,2,1] (.node [7,2,2,2,2,2,1,1,1] .empty .empty) (.node [7,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,2,2,2,1,1,1,1] (.node [7,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,2,2,1,1] .empty .empty))))

def degreeTree20_8 : RowTree := (.node [7,4,2,1,1,1,1,1,1,1] (.node [7,3,3,2,2,2,1] (.node [7,3,3,2,1,1,1,1,1] (.node [7,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,2,2,1,1,1] .empty .empty)) (.node [7,3,3,3,2,1,1] (.node [7,3,3,3,1,1,1,1] .empty .empty) (.node [7,4,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,4,3,1,1,1,1,1,1] (.node [7,4,2,2,2,1,1,1] (.node [7,4,2,2,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,2,1] .empty .empty)) (.node [7,4,3,2,2,1,1] (.node [7,4,3,2,1,1,1,1] .empty .empty) (.node [7,4,3,3,1,1,1] .empty .empty))))

def degreeTree20_9 : RowTree := (.node [7,3,2,2,2,2,2] degreeTree20_7 degreeTree20_8)

def degreeTree20_10 : RowTree := (.node [8,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,5,3,1,1,1,1,1] (.node [7,5,2,2,1,1,1,1] (.node [7,5,2,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,5,2,2,2,1,1] .empty .empty)) (.node [7,6,2,1,1,1,1,1] (.node [7,6,1,1,1,1,1,1,1] .empty .empty) (.node [7,7,1,1,1,1,1,1] .empty .empty))) (.node [8,2,2,2,2,1,1,1,1] (.node [8,2,2,1,1,1,1,1,1,1,1] (.node [8,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [8,3,1,1,1,1,1,1,1,1,1] (.node [8,2,2,2,2,2,1,1] .empty .empty) (.node [8,3,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_11 : RowTree := (.node [9,1,1,1,1,1,1,1,1,1,1,1] (.node [8,4,1,1,1,1,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1] (.node [8,3,2,2,2,1,1,1] .empty .empty) (.node [8,3,3,2,1,1,1,1] .empty .empty)) (.node [8,4,2,2,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1] .empty .empty) (.node [8,5,1,1,1,1,1,1,1] .empty .empty))) (.node [9,3,1,1,1,1,1,1,1,1] (.node [9,2,2,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,1,1,1,1,1,1,1,1,1,1] (.node [9,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,2,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_12 : RowTree := (.node [8,3,2,2,1,1,1,1,1] degreeTree20_10 degreeTree20_11)

def degreeTree20_13 : RowTree := (.node [7,4,4,1,1,1,1,1] degreeTree20_9 degreeTree20_12)

def degreeTree20_14 : RowTree := (.node [6,6,2,2,2,1,1] degreeTree20_6 degreeTree20_13)

def degreeTree20 : RowTree := degreeTree20_14

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP20 := TreeResidual 4 5 degreeQs20 degreeTree20

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree22_0 : RowTree := (.node [7,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,1,1,1,1,1,1,1] (.node [7,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,2,1,1,1] (.node [7,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,2,2,2,2,1] .empty .empty))) (.node [7,3,2,2,2,2,2,1,1] (.node [7,3,2,2,2,1,1,1,1,1,1] (.node [7,3,2,2,1,1,1,1,1,1,1,1] (.node [7,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,3,2,2,2,2,1,1,1,1] .empty .empty)) (.node [7,3,3,1,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,2,2,2] .empty .empty) (.node [7,3,3,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_1 : RowTree := (.node [7,4,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,2,2,1,1] (.node [7,3,3,3,1,1,1,1,1,1] (.node [7,3,3,2,2,2,2,1] (.node [7,3,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [7,3,3,3,2,1,1,1,1] .empty .empty)) (.node [7,3,3,3,3,1,1,1] (.node [7,3,3,3,2,2,2] .empty .empty) (.node [7,3,3,3,3,2,1] .empty .empty))) (.node [7,4,2,2,2,2,1,1,1] (.node [7,4,2,2,1,1,1,1,1,1,1] (.node [7,4,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,3,1,1,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,1] .empty .empty) (.node [7,4,3,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_2 : RowTree := (.node [7,3,3,2,2,1,1,1,1,1] degreeTree22_0 degreeTree22_1)

def degreeTree22_3 : RowTree := (.node [7,4,4,2,2,1,1,1] (.node [7,4,3,3,2,2,1] (.node [7,4,3,3,1,1,1,1,1] (.node [7,4,3,2,2,2,2] (.node [7,4,3,2,2,2,1,1] .empty .empty) .empty) (.node [7,4,3,3,2,1,1,1] .empty .empty)) (.node [7,4,4,1,1,1,1,1,1,1] (.node [7,4,3,3,3,1,1] .empty .empty) (.node [7,4,4,2,1,1,1,1,1] .empty .empty))) (.node [7,4,4,4,1,1,1] (.node [7,4,4,3,1,1,1,1] (.node [7,4,4,2,2,2,1] .empty .empty) (.node [7,4,4,3,2,1,1] .empty .empty)) (.node [7,5,2,1,1,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_4 : RowTree := (.node [7,5,4,1,1,1,1,1,1] (.node [7,5,3,2,2,1,1,1] (.node [7,5,3,1,1,1,1,1,1,1] (.node [7,5,2,2,2,2,2] (.node [7,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [7,5,3,2,1,1,1,1,1] .empty .empty)) (.node [7,5,3,3,1,1,1,1] (.node [7,5,3,2,2,2,1] .empty .empty) (.node [7,5,3,3,2,1,1] .empty .empty))) (.node [7,6,2,1,1,1,1,1,1,1] (.node [7,5,5,1,1,1,1,1] (.node [7,5,4,2,1,1,1,1] .empty .empty) (.node [7,6,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,6,2,2,2,1,1,1] (.node [7,6,2,2,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,2,2,1] .empty .empty))))

def degreeTree22_5 : RowTree := (.node [7,5,2,2,2,1,1,1,1] degreeTree22_3 degreeTree22_4)

def degreeTree22_6 : RowTree := (.node [7,4,3,2,2,1,1,1,1] degreeTree22_2 degreeTree22_5)

def degreeTree22_7 : RowTree := (.node [8,2,2,1,1,1,1,1,1,1,1,1,1] (.node [7,7,2,2,1,1,1,1] (.node [7,7,1,1,1,1,1,1,1,1] (.node [7,6,4,1,1,1,1,1] (.node [7,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [7,7,2,1,1,1,1,1,1] .empty .empty)) (.node [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,7,3,1,1,1,1,1] .empty .empty) (.node [8,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [8,2,2,2,2,2,2,2] (.node [8,2,2,2,2,2,1,1,1,1] (.node [8,2,2,2,2,1,1,1,1,1,1] (.node [8,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,2,2,2,2,2,1,1] .empty .empty)) (.node [8,3,2,1,1,1,1,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,2,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_8 : RowTree := (.node [8,4,1,1,1,1,1,1,1,1,1,1] (.node [8,3,3,2,2,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1,1,1] (.node [8,3,2,2,2,2,2,1] (.node [8,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [8,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [8,3,3,3,1,1,1,1,1] (.node [8,3,3,2,2,2,1,1] .empty .empty) (.node [8,3,3,3,2,1,1,1] .empty .empty))) (.node [8,4,2,2,2,2,1,1] (.node [8,4,2,2,1,1,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,2,2,2,1,1,1,1] .empty .empty)) (.node [8,4,3,2,1,1,1,1,1] (.node [8,4,3,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,2,2,1,1,1] .empty .empty))))

def degreeTree22_9 : RowTree := (.node [8,3,2,2,2,1,1,1,1,1] degreeTree22_7 degreeTree22_8)

def degreeTree22_10 : RowTree := (.node [8,7,1,1,1,1,1,1,1] (.node [8,5,2,2,2,1,1,1] (.node [8,5,2,1,1,1,1,1,1,1] (.node [8,5,1,1,1,1,1,1,1,1,1] (.node [8,4,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,5,2,2,1,1,1,1,1] .empty .empty)) (.node [8,6,1,1,1,1,1,1,1,1] (.node [8,5,3,1,1,1,1,1,1] .empty .empty) (.node [8,6,2,1,1,1,1,1,1] .empty .empty))) (.node [9,2,2,2,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [9,2,2,2,2,2,1,1,1] (.node [9,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [9,3,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_11 : RowTree := (.node [10,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,4,1,1,1,1,1,1,1,1,1] (.node [9,3,3,1,1,1,1,1,1,1] (.node [9,3,2,2,2,1,1,1,1] (.node [9,3,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,3,3,2,1,1,1,1,1] .empty .empty)) (.node [9,4,2,2,1,1,1,1,1] (.node [9,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,5,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,3,1,1,1,1,1,1,1,1,1] (.node [10,2,2,1,1,1,1,1,1,1,1] (.node [10,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [11,1,1,1,1,1,1,1,1,1,1,1] (.node [10,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [11,2,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_12 : RowTree := (.node [9,3,2,1,1,1,1,1,1,1,1] degreeTree22_10 degreeTree22_11)

def degreeTree22_13 : RowTree := (.node [8,4,3,3,1,1,1,1] degreeTree22_9 degreeTree22_12)

def degreeTree22_14 : RowTree := (.node [7,6,3,1,1,1,1,1,1] degreeTree22_6 degreeTree22_13)

def degreeTree22 : RowTree := degreeTree22_14

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP22 := TreeResidual 4 6 degreeQs22 degreeTree22

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree24_0 : RowTree := (.node [5,5,4,4,3,2,1] (.node [5,4,4,4,3,2,2] (.node [4,4,4,4,4,3,1] (.node [4,4,4,4,3,3,2] (.node [4,4,4,3,3,3,3] .empty .empty) (.node [4,4,4,4,4,2,2] .empty .empty)) (.node [5,4,3,3,3,3,3] (.node [4,4,4,4,4,4] .empty .empty) (.node [5,4,4,3,3,3,2] .empty .empty))) (.node [5,5,3,3,3,3,2] (.node [5,4,4,4,4,2,1] (.node [5,4,4,4,3,3,1] .empty .empty) (.node [5,4,4,4,4,3] .empty .empty)) (.node [5,5,4,3,3,3,1] (.node [5,5,4,3,3,2,2] .empty .empty) (.node [5,5,4,4,2,2,2] .empty .empty)))) (.node [5,5,5,4,3,1,1] (.node [5,5,5,3,2,2,2] (.node [5,5,4,4,4,1,1] (.node [5,5,4,4,3,3] .empty .empty) (.node [5,5,4,4,4,2] .empty .empty)) (.node [5,5,5,3,3,3] (.node [5,5,5,3,3,2,1] .empty .empty) (.node [5,5,5,4,2,2,1] .empty .empty))) (.node [5,5,5,5,2,2] (.node [5,5,5,4,4,1] (.node [5,5,5,4,3,2] .empty .empty) (.node [5,5,5,5,2,1,1] .empty .empty)) (.node [5,5,5,5,4] (.node [5,5,5,5,3,1] .empty .empty) .empty))))

def degreeTree24_1 : RowTree := (.node [6,3,2,2,2,2,2,2,1,1,1] (.node [6,2,2,2,2,2,2,2,2,1,1] (.node [6,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,2,2,2,2,2,2,1,1,1,1,1,1] (.node [6,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,3,2,2,2,2,1,1,1,1,1,1,1] (.node [6,3,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,3,2,2,2,2,2,1,1,1,1,1] .empty .empty)))) (.node [6,3,3,2,2,2,2,2,2] (.node [6,3,3,2,2,1,1,1,1,1,1,1,1] (.node [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,3,2,2,2,2,2,2,2,1] .empty .empty) (.node [6,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,3,3,2,2,2,2,1,1,1,1] (.node [6,3,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [6,3,3,2,2,2,2,2,1,1] .empty .empty))) (.node [6,3,3,3,2,2,2,1,1,1] (.node [6,3,3,3,2,1,1,1,1,1,1,1] (.node [6,3,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,3,3,3,2,2,1,1,1,1,1] .empty .empty)) (.node [6,3,3,3,3,1,1,1,1,1,1] (.node [6,3,3,3,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree24_2 : RowTree := (.node [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree24_0 degreeTree24_1)

def degreeTree24_3 : RowTree := (.node [6,4,3,2,2,1,1,1,1,1,1,1] (.node [6,4,2,2,1,1,1,1,1,1,1,1,1,1] (.node [6,3,3,3,3,3,2,1] (.node [6,3,3,3,3,2,2,2] (.node [6,3,3,3,3,2,2,1,1] .empty .empty) (.node [6,3,3,3,3,3,1,1,1] .empty .empty)) (.node [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,3,3,3,3,3,3] .empty .empty) (.node [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [6,4,2,2,2,2,2,2,1,1] (.node [6,4,2,2,2,2,1,1,1,1,1,1] (.node [6,4,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,4,2,2,2,2,2,1,1,1,1] .empty .empty)) (.node [6,4,3,1,1,1,1,1,1,1,1,1,1,1] (.node [6,4,2,2,2,2,2,2,2] .empty .empty) (.node [6,4,3,2,1,1,1,1,1,1,1,1,1] .empty .empty)))) (.node [6,4,3,3,2,2,2,2] (.node [6,4,3,3,1,1,1,1,1,1,1,1] (.node [6,4,3,2,2,2,2,1,1,1] (.node [6,4,3,2,2,2,1,1,1,1,1] .empty .empty) (.node [6,4,3,2,2,2,2,2,1] .empty .empty)) (.node [6,4,3,3,2,2,1,1,1,1] (.node [6,4,3,3,2,1,1,1,1,1,1] .empty .empty) (.node [6,4,3,3,2,2,2,1,1] .empty .empty))) (.node [6,4,3,3,3,3,1,1] (.node [6,4,3,3,3,2,1,1,1] (.node [6,4,3,3,3,1,1,1,1,1] .empty .empty) (.node [6,4,3,3,3,2,2,1] .empty .empty)) (.node [6,4,4,1,1,1,1,1,1,1,1,1,1] (.node [6,4,3,3,3,3,2] .empty .empty) .empty))))

def degreeTree24_4 : RowTree := (.node [6,4,4,4,2,2,1,1] (.node [6,4,4,3,2,2,2,1] (.node [6,4,4,2,2,2,2,2] (.node [6,4,4,2,2,2,1,1,1,1] (.node [6,4,4,2,2,1,1,1,1,1,1] .empty .empty) (.node [6,4,4,2,2,2,2,1,1] .empty .empty)) (.node [6,4,4,3,2,1,1,1,1,1] (.node [6,4,4,3,1,1,1,1,1,1,1] .empty .empty) (.node [6,4,4,3,2,2,1,1,1] .empty .empty))) (.node [6,4,4,3,3,3,1] (.node [6,4,4,3,3,2,1,1] (.node [6,4,4,3,3,1,1,1,1] .empty .empty) (.node [6,4,4,3,3,2,2] .empty .empty)) (.node [6,4,4,4,2,1,1,1,1] (.node [6,4,4,4,1,1,1,1,1,1] .empty .empty) .empty))) (.node [6,5,2,1,1,1,1,1,1,1,1,1,1,1] (.node [6,4,4,4,3,3] (.node [6,4,4,4,3,1,1,1] (.node [6,4,4,4,2,2,2] .empty .empty) (.node [6,4,4,4,3,2,1] .empty .empty)) (.node [6,4,4,4,4,2] (.node [6,4,4,4,4,1,1] .empty .empty) (.node [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [6,5,2,2,2,2,2,1,1,1] (.node [6,5,2,2,2,1,1,1,1,1,1,1] (.node [6,5,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,5,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [6,5,3,1,1,1,1,1,1,1,1,1,1] (.node [6,5,2,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree24_5 : RowTree := (.node [6,4,4,2,1,1,1,1,1,1,1,1] degreeTree24_3 degreeTree24_4)

def degreeTree24_6 : RowTree := (.node [6,3,3,3,3,2,1,1,1,1] degreeTree24_2 degreeTree24_5)

def degreeTree24_7 : RowTree := (.node [6,5,4,2,2,2,1,1,1] (.node [6,5,3,3,2,2,2,1] (.node [6,5,3,2,2,2,2,2] (.node [6,5,3,2,2,2,1,1,1,1] (.node [6,5,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [6,5,3,2,2,2,2,1,1] .empty .empty)) (.node [6,5,3,3,2,1,1,1,1,1] (.node [6,5,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [6,5,3,3,2,2,1,1,1] .empty .empty))) (.node [6,5,3,3,3,3,1] (.node [6,5,3,3,3,2,1,1] (.node [6,5,3,3,3,1,1,1,1] .empty .empty) (.node [6,5,3,3,3,2,2] .empty .empty)) (.node [6,5,4,2,1,1,1,1,1,1,1] (.node [6,5,4,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,5,4,2,2,1,1,1,1,1] .empty .empty)))) (.node [6,5,4,3,3,3] (.node [6,5,4,3,2,2,1,1] (.node [6,5,4,3,1,1,1,1,1,1] (.node [6,5,4,2,2,2,2,1] .empty .empty) (.node [6,5,4,3,2,1,1,1,1] .empty .empty)) (.node [6,5,4,3,3,1,1,1] (.node [6,5,4,3,2,2,2] .empty .empty) (.node [6,5,4,3,3,2,1] .empty .empty))) (.node [6,5,4,4,3,1,1] (.node [6,5,4,4,2,1,1,1] (.node [6,5,4,4,1,1,1,1,1] .empty .empty) (.node [6,5,4,4,2,2,1] .empty .empty)) (.node [6,5,4,4,4,1] (.node [6,5,4,4,3,2] .empty .empty) .empty))))

def degreeTree24_8 : RowTree := (.node [6,6,2,1,1,1,1,1,1,1,1,1,1] (.node [6,5,5,3,3,1,1] (.node [6,5,5,2,2,2,2] (.node [6,5,5,2,2,1,1,1,1] (.node [6,5,5,2,1,1,1,1,1,1] .empty .empty) (.node [6,5,5,2,2,2,1,1] .empty .empty)) (.node [6,5,5,3,2,1,1,1] (.node [6,5,5,3,1,1,1,1,1] .empty .empty) (.node [6,5,5,3,2,2,1] .empty .empty))) (.node [6,5,5,4,2,2] (.node [6,5,5,4,1,1,1,1] (.node [6,5,5,3,3,2] .empty .empty) (.node [6,5,5,4,2,1,1] .empty .empty)) (.node [6,5,5,5,1,1,1] (.node [6,5,5,4,3,1] .empty .empty) (.node [6,6,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)))) (.node [6,6,3,2,2,1,1,1,1,1] (.node [6,6,2,2,2,2,2,1,1] (.node [6,6,2,2,2,1,1,1,1,1,1] (.node [6,6,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,6,2,2,2,2,1,1,1,1] .empty .empty)) (.node [6,6,3,1,1,1,1,1,1,1,1,1] (.node [6,6,2,2,2,2,2,2] .empty .empty) (.node [6,6,3,2,1,1,1,1,1,1,1] .empty .empty))) (.node [6,6,3,3,2,1,1,1,1] (.node [6,6,3,2,2,2,2,1] (.node [6,6,3,2,2,2,1,1,1] .empty .empty) (.node [6,6,3,3,1,1,1,1,1,1] .empty .empty)) (.node [6,6,3,3,2,2,2] (.node [6,6,3,3,2,2,1,1] .empty .empty) .empty))))

def degreeTree24_9 : RowTree := (.node [6,5,5,1,1,1,1,1,1,1,1] degreeTree24_7 degreeTree24_8)

def degreeTree24_10 : RowTree := (.node [6,6,5,1,1,1,1,1,1,1] (.node [6,6,4,3,1,1,1,1,1] (.node [6,6,4,2,1,1,1,1,1,1] (.node [6,6,3,3,3,3] (.node [6,6,3,3,3,2,1] .empty .empty) (.node [6,6,4,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,6,4,2,2,2,1,1] (.node [6,6,4,2,2,1,1,1,1] .empty .empty) (.node [6,6,4,2,2,2,2] .empty .empty))) (.node [6,6,4,3,3,2] (.node [6,6,4,3,2,2,1] (.node [6,6,4,3,2,1,1,1] .empty .empty) (.node [6,6,4,3,3,1,1] .empty .empty)) (.node [6,6,4,4,2,1,1] (.node [6,6,4,4,1,1,1,1] .empty .empty) (.node [6,6,4,4,2,2] .empty .empty)))) (.node [6,6,6,2,1,1,1,1] (.node [6,6,5,3,1,1,1,1] (.node [6,6,5,2,2,1,1,1] (.node [6,6,5,2,1,1,1,1,1] .empty .empty) (.node [6,6,5,2,2,2,1] .empty .empty)) (.node [6,6,5,4,1,1,1] (.node [6,6,5,3,2,1,1] .empty .empty) (.node [6,6,6,1,1,1,1,1,1] .empty .empty))) (.node [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,6,6,3,1,1,1] (.node [6,6,6,2,2,1,1] .empty .empty) (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_11 : RowTree := (.node [7,3,3,2,2,1,1,1,1,1,1,1] (.node [7,3,2,2,2,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,2,2,2,1] (.node [7,2,2,2,2,2,2,1,1,1,1,1] (.node [7,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,3,2,2,2,2,2,2,2] (.node [7,3,2,2,2,2,2,1,1,1,1] (.node [7,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,2,2,2,2,1,1] .empty .empty)) (.node [7,3,3,2,1,1,1,1,1,1,1,1,1] (.node [7,3,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [7,3,3,3,2,2,2,2] (.node [7,3,3,3,1,1,1,1,1,1,1,1] (.node [7,3,3,2,2,2,2,1,1,1] (.node [7,3,3,2,2,2,1,1,1,1,1] .empty .empty) (.node [7,3,3,2,2,2,2,2,1] .empty .empty)) (.node [7,3,3,3,2,2,1,1,1,1] (.node [7,3,3,3,2,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,3,2,2,2,1,1] .empty .empty))) (.node [7,3,3,3,3,3,1,1] (.node [7,3,3,3,3,2,1,1,1] (.node [7,3,3,3,3,1,1,1,1,1] .empty .empty) (.node [7,3,3,3,3,2,2,1] .empty .empty)) (.node [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,3,3,2] .empty .empty) .empty))))

def degreeTree24_12 : RowTree := (.node [7,2,2,2,2,1,1,1,1,1,1,1,1,1] degreeTree24_10 degreeTree24_11)

def degreeTree24_13 : RowTree := (.node [6,6,3,3,3,1,1,1] degreeTree24_9 degreeTree24_12)

def degreeTree24_14 : RowTree := (.node [6,5,3,2,1,1,1,1,1,1,1,1] degreeTree24_6 degreeTree24_13)

def degreeTree24_15 : RowTree := (.node [7,4,3,3,3,1,1,1,1] (.node [7,4,3,2,2,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,1,1,1] (.node [7,4,2,2,2,1,1,1,1,1,1,1] (.node [7,4,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,3,1,1,1,1,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,2,1] .empty .empty) (.node [7,4,3,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,4,3,3,1,1,1,1,1,1,1] (.node [7,4,3,2,2,2,2,1,1] (.node [7,4,3,2,2,2,1,1,1,1] .empty .empty) (.node [7,4,3,2,2,2,2,2] .empty .empty)) (.node [7,4,3,3,2,2,1,1,1] (.node [7,4,3,3,2,1,1,1,1,1] .empty .empty) (.node [7,4,3,3,2,2,2,1] .empty .empty)))) (.node [7,4,4,2,2,2,2,1] (.node [7,4,4,1,1,1,1,1,1,1,1,1] (.node [7,4,3,3,3,2,2] (.node [7,4,3,3,3,2,1,1] .empty .empty) (.node [7,4,3,3,3,3,1] .empty .empty)) (.node [7,4,4,2,2,1,1,1,1,1] (.node [7,4,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,4,2,2,2,1,1,1] .empty .empty))) (.node [7,4,4,3,2,2,2] (.node [7,4,4,3,2,1,1,1,1] (.node [7,4,4,3,1,1,1,1,1,1] .empty .empty) (.node [7,4,4,3,2,2,1,1] .empty .empty)) (.node [7,4,4,3,3,2,1] (.node [7,4,4,3,3,1,1,1] .empty .empty) .empty))))

def degreeTree24_16 : RowTree := (.node [7,5,3,3,1,1,1,1,1,1] (.node [7,5,2,2,2,2,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,4,4,4,2,2,1] (.node [7,4,4,4,2,1,1,1] .empty .empty) (.node [7,4,4,4,3,1,1] .empty .empty)) (.node [7,5,2,2,1,1,1,1,1,1,1,1] (.node [7,5,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [7,5,3,2,1,1,1,1,1,1,1] (.node [7,5,2,2,2,2,2,2] (.node [7,5,2,2,2,2,2,1,1] .empty .empty) (.node [7,5,3,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,5,3,2,2,2,1,1,1] (.node [7,5,3,2,2,1,1,1,1,1] .empty .empty) (.node [7,5,3,2,2,2,2,1] .empty .empty)))) (.node [7,5,4,2,2,1,1,1,1] (.node [7,5,3,3,3,1,1,1] (.node [7,5,3,3,2,2,1,1] (.node [7,5,3,3,2,1,1,1,1] .empty .empty) (.node [7,5,3,3,2,2,2] .empty .empty)) (.node [7,5,4,1,1,1,1,1,1,1,1] (.node [7,5,3,3,3,2,1] .empty .empty) (.node [7,5,4,2,1,1,1,1,1,1] .empty .empty))) (.node [7,5,4,3,2,1,1,1] (.node [7,5,4,2,2,2,2] (.node [7,5,4,2,2,2,1,1] .empty .empty) (.node [7,5,4,3,1,1,1,1,1] .empty .empty)) (.node [7,5,4,3,3,1,1] (.node [7,5,4,3,2,2,1] .empty .empty) .empty))))

def degreeTree24_17 : RowTree := (.node [7,4,4,4,1,1,1,1,1] degreeTree24_15 degreeTree24_16)

def degreeTree24_18 : RowTree := (.node [7,6,3,2,2,2,1,1] (.node [7,6,2,1,1,1,1,1,1,1,1,1] (.node [7,5,5,2,2,1,1,1] (.node [7,5,5,1,1,1,1,1,1,1] (.node [7,5,4,4,2,1,1] .empty .empty) (.node [7,5,5,2,1,1,1,1,1] .empty .empty)) (.node [7,5,5,3,1,1,1,1] (.node [7,5,5,2,2,2,1] .empty .empty) (.node [7,6,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,6,2,2,2,2,2,1] (.node [7,6,2,2,2,1,1,1,1,1] (.node [7,6,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,2,2,1,1,1] .empty .empty)) (.node [7,6,3,2,1,1,1,1,1,1] (.node [7,6,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,3,2,2,1,1,1,1] .empty .empty)))) (.node [7,6,4,3,1,1,1,1] (.node [7,6,3,3,2,2,1] (.node [7,6,3,3,1,1,1,1,1] (.node [7,6,3,2,2,2,2] .empty .empty) (.node [7,6,3,3,2,1,1,1] .empty .empty)) (.node [7,6,4,2,1,1,1,1,1] (.node [7,6,4,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,4,2,2,1,1,1] .empty .empty))) (.node [7,7,1,1,1,1,1,1,1,1,1,1] (.node [7,6,5,2,1,1,1,1] (.node [7,6,5,1,1,1,1,1,1] .empty .empty) (.node [7,6,6,1,1,1,1,1] .empty .empty)) (.node [7,7,2,2,1,1,1,1,1,1] (.node [7,7,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_19 : RowTree := (.node [8,2,2,2,2,2,1,1,1,1,1,1] (.node [7,7,4,2,1,1,1,1] (.node [7,7,3,2,1,1,1,1,1] (.node [7,7,2,2,2,2,2] (.node [7,7,2,2,2,2,1,1] .empty .empty) (.node [7,7,3,1,1,1,1,1,1,1] .empty .empty)) (.node [7,7,3,3,1,1,1,1] (.node [7,7,3,2,2,1,1,1] .empty .empty) (.node [7,7,4,1,1,1,1,1,1] .empty .empty))) (.node [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,7,5,1,1,1,1,1] .empty .empty) (.node [8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,2,2,2,2,1,1,1,1,1,1,1,1] (.node [8,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [8,3,2,2,2,2,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,2,2,2,2,2,2,2,1,1] (.node [8,2,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [8,2,2,2,2,2,2,2,2] .empty .empty)) (.node [8,3,2,2,1,1,1,1,1,1,1,1,1] (.node [8,3,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,2,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [8,3,3,2,1,1,1,1,1,1,1,1] (.node [8,3,2,2,2,2,2,2,1] (.node [8,3,2,2,2,2,2,1,1,1] .empty .empty) (.node [8,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,3,3,2,2,2,1,1,1,1] (.node [8,3,3,2,2,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_20 : RowTree := (.node [7,7,2,2,2,1,1,1,1] degreeTree24_18 degreeTree24_19)

def degreeTree24_21 : RowTree := (.node [7,5,4,4,1,1,1,1] degreeTree24_17 degreeTree24_20)

def degreeTree24_22 : RowTree := (.node [8,4,3,2,1,1,1,1,1,1,1] (.node [8,4,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,3,3,2,2,1,1,1] (.node [8,3,3,3,1,1,1,1,1,1,1] (.node [8,3,3,2,2,2,2,2] .empty .empty) (.node [8,3,3,3,2,1,1,1,1,1] .empty .empty)) (.node [8,3,3,3,3,1,1,1,1] (.node [8,3,3,3,2,2,2,1] .empty .empty) (.node [8,3,3,3,3,2,1,1] .empty .empty))) (.node [8,4,2,2,2,2,1,1,1,1] (.node [8,4,2,2,1,1,1,1,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [8,4,2,2,2,2,2,2] (.node [8,4,2,2,2,2,2,1,1] .empty .empty) (.node [8,4,3,1,1,1,1,1,1,1,1,1] .empty .empty)))) (.node [8,4,4,1,1,1,1,1,1,1,1] (.node [8,4,3,3,1,1,1,1,1,1] (.node [8,4,3,2,2,2,1,1,1] (.node [8,4,3,2,2,1,1,1,1,1] .empty .empty) (.node [8,4,3,2,2,2,2,1] .empty .empty)) (.node [8,4,3,3,2,2,1,1] (.node [8,4,3,3,2,1,1,1,1] .empty .empty) (.node [8,4,3,3,3,1,1,1] .empty .empty))) (.node [8,4,4,3,1,1,1,1,1] (.node [8,4,4,2,2,1,1,1,1] (.node [8,4,4,2,1,1,1,1,1,1] .empty .empty) (.node [8,4,4,2,2,2,1,1] .empty .empty)) (.node [8,4,4,4,1,1,1,1] (.node [8,4,4,3,2,1,1,1] .empty .empty) .empty))))

def degreeTree24_23 : RowTree := (.node [8,6,1,1,1,1,1,1,1,1,1,1] (.node [8,5,3,2,2,1,1,1,1] (.node [8,5,2,2,2,2,1,1,1] (.node [8,5,2,2,1,1,1,1,1,1,1] (.node [8,5,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,2,2,2,1,1,1,1,1] .empty .empty)) (.node [8,5,3,1,1,1,1,1,1,1,1] (.node [8,5,2,2,2,2,2,1] .empty .empty) (.node [8,5,3,2,1,1,1,1,1,1] .empty .empty))) (.node [8,5,4,1,1,1,1,1,1,1] (.node [8,5,3,3,1,1,1,1,1] (.node [8,5,3,2,2,2,1,1] .empty .empty) (.node [8,5,3,3,2,1,1,1] .empty .empty)) (.node [8,5,5,1,1,1,1,1,1] (.node [8,5,4,2,1,1,1,1,1] .empty .empty) .empty))) (.node [8,7,1,1,1,1,1,1,1,1,1] (.node [8,6,2,2,2,2,1,1] (.node [8,6,2,2,1,1,1,1,1,1] (.node [8,6,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,6,2,2,2,1,1,1,1] .empty .empty)) (.node [8,6,3,2,1,1,1,1,1] (.node [8,6,3,1,1,1,1,1,1,1] .empty .empty) (.node [8,6,4,1,1,1,1,1,1] .empty .empty))) (.node [8,8,1,1,1,1,1,1,1,1] (.node [8,7,2,2,1,1,1,1,1] (.node [8,7,2,1,1,1,1,1,1,1] .empty .empty) (.node [8,7,3,1,1,1,1,1,1] .empty .empty)) (.node [9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,8,2,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_24 : RowTree := (.node [8,5,1,1,1,1,1,1,1,1,1,1,1] degreeTree24_22 degreeTree24_23)

def degreeTree24_25 : RowTree := (.node [9,3,3,2,2,2,1,1,1] (.node [9,3,2,1,1,1,1,1,1,1,1,1,1] (.node [9,2,2,2,2,2,1,1,1,1,1] (.node [9,2,2,2,1,1,1,1,1,1,1,1,1] (.node [9,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [9,2,2,2,2,2,2,2,1] (.node [9,2,2,2,2,2,2,1,1,1] .empty .empty) (.node [9,3,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,3,2,2,2,2,2,1,1] (.node [9,3,2,2,2,1,1,1,1,1,1] (.node [9,3,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,2,2,2,2,1,1,1,1] .empty .empty)) (.node [9,3,3,2,1,1,1,1,1,1,1] (.node [9,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,3,2,2,1,1,1,1,1] .empty .empty)))) (.node [9,4,3,1,1,1,1,1,1,1,1] (.node [9,4,2,1,1,1,1,1,1,1,1,1] (.node [9,3,3,3,2,1,1,1,1] (.node [9,3,3,3,1,1,1,1,1,1] .empty .empty) (.node [9,4,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [9,4,2,2,2,1,1,1,1,1] (.node [9,4,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,4,2,2,2,2,1,1,1] .empty .empty))) (.node [9,4,4,1,1,1,1,1,1,1] (.node [9,4,3,2,2,1,1,1,1] (.node [9,4,3,2,1,1,1,1,1,1] .empty .empty) (.node [9,4,3,3,1,1,1,1,1] .empty .empty)) (.node [9,5,2,1,1,1,1,1,1,1,1] (.node [9,5,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_26 : RowTree := (.node [10,3,2,2,2,1,1,1,1,1] (.node [10,2,2,1,1,1,1,1,1,1,1,1,1] (.node [9,6,2,1,1,1,1,1,1,1] (.node [9,5,3,1,1,1,1,1,1,1] (.node [9,5,2,2,2,1,1,1,1] .empty .empty) (.node [9,6,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,7,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,2,2,2,2,1,1,1,1,1,1] (.node [10,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,3,2,2,1,1,1,1,1,1,1] (.node [10,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [11,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,4,2,1,1,1,1,1,1,1,1] (.node [10,3,3,2,1,1,1,1,1,1] (.node [10,3,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,1,1,1,1,1,1,1,1,1] (.node [10,4,2,2,1,1,1,1,1,1] .empty .empty) (.node [11,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [11,3,2,1,1,1,1,1,1,1,1] (.node [11,2,2,2,1,1,1,1,1,1,1] (.node [11,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [11,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [12,2,1,1,1,1,1,1,1,1,1,1] (.node [12,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree24_27 : RowTree := (.node [9,5,2,2,1,1,1,1,1,1] degreeTree24_25 degreeTree24_26)

def degreeTree24_28 : RowTree := (.node [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree24_24 degreeTree24_27)

def degreeTree24_29 : RowTree := (.node [8,3,3,2,2,2,2,1,1] degreeTree24_21 degreeTree24_28)

def degreeTree24_30 : RowTree := (.node [7,4,2,1,1,1,1,1,1,1,1,1,1,1] degreeTree24_14 degreeTree24_29)

def degreeTree24 : RowTree := degreeTree24_30

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP24 := TreeResidual 4 7 degreeQs24 degreeTree24

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree26_0 : RowTree := (.node [7,2,2,2,2,2,2,2,2,1,1,1] (.node [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,2,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,2,2,2,2,1,1,1,1,1] .empty .empty))) (.node [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,2,2,2,2,1] .empty .empty) (.node [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,2,2,2,2,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,2,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_1 : RowTree := (.node [7,3,3,2,2,2,2,2,2,1] (.node [7,3,3,2,2,1,1,1,1,1,1,1,1,1] (.node [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,2,2,2,2,2] (.node [7,3,2,2,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,3,2,2,2,2,1,1,1,1,1] (.node [7,3,3,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,2,2,2,2,2,1,1,1] .empty .empty))) (.node [7,3,3,3,2,2,2,1,1,1,1] (.node [7,3,3,3,2,1,1,1,1,1,1,1,1] (.node [7,3,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,3,2,2,1,1,1,1,1,1] .empty .empty)) (.node [7,3,3,3,2,2,2,2,2] (.node [7,3,3,3,2,2,2,2,1,1] .empty .empty) (.node [7,3,3,3,3,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_2 : RowTree := (.node [7,3,2,2,2,2,2,2,1,1,1,1] degreeTree26_0 degreeTree26_1)

def degreeTree26_3 : RowTree := (.node [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,3,3,2,2] (.node [7,3,3,3,3,3,1,1,1,1] (.node [7,3,3,3,3,2,2,2,1] (.node [7,3,3,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [7,3,3,3,3,3,2,1,1] .empty .empty)) (.node [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,3,3,3,1] .empty .empty) (.node [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,4,2,2,2,2,2,2,1,1,1] (.node [7,4,2,2,2,2,1,1,1,1,1,1,1] (.node [7,4,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,2,2,1] .empty .empty) (.node [7,4,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_4 : RowTree := (.node [7,4,3,3,2,2,2,1,1,1] (.node [7,4,3,2,2,2,2,2,2] (.node [7,4,3,2,2,2,2,1,1,1,1] (.node [7,4,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,4,3,2,2,2,2,2,1,1] .empty .empty)) (.node [7,4,3,3,2,1,1,1,1,1,1,1] (.node [7,4,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,3,3,2,2,1,1,1,1,1] .empty .empty))) (.node [7,4,3,3,3,2,2,1,1] (.node [7,4,3,3,3,1,1,1,1,1,1] (.node [7,4,3,3,2,2,2,2,1] .empty .empty) (.node [7,4,3,3,3,2,1,1,1,1] .empty .empty)) (.node [7,4,3,3,3,3,1,1,1] (.node [7,4,3,3,3,2,2,2] .empty .empty) (.node [7,4,3,3,3,3,2,1] .empty .empty))))

def degreeTree26_5 : RowTree := (.node [7,4,3,2,2,1,1,1,1,1,1,1,1] degreeTree26_3 degreeTree26_4)

def degreeTree26_6 : RowTree := (.node [7,3,3,3,3,2,1,1,1,1,1] degreeTree26_2 degreeTree26_5)

def degreeTree26_7 : RowTree := (.node [7,4,4,3,2,2,1,1,1,1] (.node [7,4,4,2,2,2,2,1,1,1] (.node [7,4,4,2,2,1,1,1,1,1,1,1] (.node [7,4,4,2,1,1,1,1,1,1,1,1,1] (.node [7,4,4,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,4,4,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,4,3,1,1,1,1,1,1,1,1] (.node [7,4,4,2,2,2,2,2,1] .empty .empty) (.node [7,4,4,3,2,1,1,1,1,1,1] .empty .empty))) (.node [7,4,4,3,3,2,1,1,1] (.node [7,4,4,3,2,2,2,2] (.node [7,4,4,3,2,2,2,1,1] .empty .empty) (.node [7,4,4,3,3,1,1,1,1,1] .empty .empty)) (.node [7,4,4,3,3,3,1,1] (.node [7,4,4,3,3,2,2,1] .empty .empty) (.node [7,4,4,3,3,3,2] .empty .empty))))

def degreeTree26_8 : RowTree := (.node [7,4,4,4,4,1,1,1] (.node [7,4,4,4,3,1,1,1,1] (.node [7,4,4,4,2,2,1,1,1] (.node [7,4,4,4,2,1,1,1,1,1] .empty .empty) (.node [7,4,4,4,2,2,2,1] .empty .empty)) (.node [7,4,4,4,3,2,2] (.node [7,4,4,4,3,2,1,1] .empty .empty) (.node [7,4,4,4,3,3,1] .empty .empty))) (.node [7,5,2,2,1,1,1,1,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,4,4,4,4,2,1] .empty .empty) (.node [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,5,2,2,2,2,1,1,1,1,1,1] (.node [7,5,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,2,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_9 : RowTree := (.node [7,4,4,4,1,1,1,1,1,1,1] degreeTree26_7 degreeTree26_8)

def degreeTree26_10 : RowTree := (.node [7,5,3,3,2,1,1,1,1,1,1] (.node [7,5,3,2,2,2,1,1,1,1,1] (.node [7,5,3,2,1,1,1,1,1,1,1,1,1] (.node [7,5,3,1,1,1,1,1,1,1,1,1,1,1] (.node [7,5,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [7,5,3,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [7,5,3,2,2,2,2,2,1] (.node [7,5,3,2,2,2,2,1,1,1] .empty .empty) (.node [7,5,3,3,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,5,3,3,3,1,1,1,1,1] (.node [7,5,3,3,2,2,2,1,1] (.node [7,5,3,3,2,2,1,1,1,1] .empty .empty) (.node [7,5,3,3,2,2,2,2] .empty .empty)) (.node [7,5,3,3,3,2,2,1] (.node [7,5,3,3,3,2,1,1,1] .empty .empty) (.node [7,5,3,3,3,3,1,1] .empty .empty))))

def degreeTree26_11 : RowTree := (.node [7,5,4,3,2,1,1,1,1,1] (.node [7,5,4,2,2,2,1,1,1,1] (.node [7,5,4,2,1,1,1,1,1,1,1,1] (.node [7,5,4,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,4,2,2,1,1,1,1,1,1] .empty .empty)) (.node [7,5,4,2,2,2,2,2] (.node [7,5,4,2,2,2,2,1,1] .empty .empty) (.node [7,5,4,3,1,1,1,1,1,1,1] .empty .empty))) (.node [7,5,4,3,3,2,1,1] (.node [7,5,4,3,2,2,2,1] (.node [7,5,4,3,2,2,1,1,1] .empty .empty) (.node [7,5,4,3,3,1,1,1,1] .empty .empty)) (.node [7,5,4,3,3,3,1] (.node [7,5,4,3,3,2,2] .empty .empty) (.node [7,5,4,4,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_12 : RowTree := (.node [7,5,3,3,3,3,2] degreeTree26_10 degreeTree26_11)

def degreeTree26_13 : RowTree := (.node [7,5,2,2,2,2,2,2,1,1] degreeTree26_9 degreeTree26_12)

def degreeTree26_14 : RowTree := (.node [7,4,3,3,3,3,3] degreeTree26_6 degreeTree26_13)

def degreeTree26_15 : RowTree := (.node [7,5,5,2,2,2,1,1,1] (.node [7,5,4,4,4,1,1] (.node [7,5,4,4,3,1,1,1] (.node [7,5,4,4,2,2,2] (.node [7,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [7,5,4,4,3,2,1] .empty .empty)) (.node [7,5,5,2,1,1,1,1,1,1,1] (.node [7,5,5,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,5,2,2,1,1,1,1,1] .empty .empty))) (.node [7,5,5,3,2,2,1,1] (.node [7,5,5,3,1,1,1,1,1,1] (.node [7,5,5,2,2,2,2,1] .empty .empty) (.node [7,5,5,3,2,1,1,1,1] .empty .empty)) (.node [7,5,5,3,3,1,1,1] (.node [7,5,5,3,2,2,2] .empty .empty) (.node [7,5,5,3,3,2,1] .empty .empty))))

def degreeTree26_16 : RowTree := (.node [7,6,2,2,2,1,1,1,1,1,1,1] (.node [7,5,5,5,1,1,1,1] (.node [7,5,5,4,2,2,1] (.node [7,5,5,4,2,1,1,1] .empty .empty) (.node [7,5,5,4,3,1,1] .empty .empty)) (.node [7,6,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,6,3,1,1,1,1,1,1,1,1,1,1] (.node [7,6,2,2,2,2,2,1,1,1] (.node [7,6,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,2,2,2,2,1] .empty .empty)) (.node [7,6,3,2,2,1,1,1,1,1,1] (.node [7,6,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,3,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_17 : RowTree := (.node [7,5,5,4,1,1,1,1,1] degreeTree26_15 degreeTree26_16)

def degreeTree26_18 : RowTree := (.node [7,6,3,3,3,3,1] (.node [7,6,3,3,2,2,2,1] (.node [7,6,3,3,2,1,1,1,1,1] (.node [7,6,3,3,1,1,1,1,1,1,1] (.node [7,6,3,2,2,2,2,2] .empty .empty) .empty) (.node [7,6,3,3,2,2,1,1,1] .empty .empty)) (.node [7,6,3,3,3,2,1,1] (.node [7,6,3,3,3,1,1,1,1] .empty .empty) (.node [7,6,3,3,3,2,2] .empty .empty))) (.node [7,6,4,2,2,2,1,1,1] (.node [7,6,4,2,1,1,1,1,1,1,1] (.node [7,6,4,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,4,2,2,1,1,1,1,1] .empty .empty)) (.node [7,6,4,3,1,1,1,1,1,1] (.node [7,6,4,2,2,2,2,1] .empty .empty) (.node [7,6,4,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_19 : RowTree := (.node [7,6,5,2,1,1,1,1,1,1] (.node [7,6,4,4,1,1,1,1,1] (.node [7,6,4,3,3,1,1,1] (.node [7,6,4,3,2,2,2] .empty .empty) (.node [7,6,4,3,3,2,1] .empty .empty)) (.node [7,6,4,4,2,2,1] (.node [7,6,4,4,2,1,1,1] .empty .empty) (.node [7,6,5,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,6,5,3,1,1,1,1,1] (.node [7,6,5,2,2,2,1,1] (.node [7,6,5,2,2,1,1,1,1] .empty .empty) (.node [7,6,5,2,2,2,2] .empty .empty)) (.node [7,6,5,4,1,1,1,1] (.node [7,6,5,3,2,1,1,1] .empty .empty) (.node [7,6,6,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_20 : RowTree := (.node [7,6,4,3,2,2,1,1] degreeTree26_18 degreeTree26_19)

def degreeTree26_21 : RowTree := (.node [7,6,3,2,2,2,2,1,1] degreeTree26_17 degreeTree26_20)

def degreeTree26_22 : RowTree := (.node [7,7,2,2,2,2,2,2] (.node [7,7,2,2,1,1,1,1,1,1,1,1] (.node [7,7,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,6,6,3,1,1,1,1] (.node [7,6,6,2,2,1,1,1] .empty .empty) .empty) (.node [7,7,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,7,2,2,2,2,1,1,1,1] (.node [7,7,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,7,2,2,2,2,2,1,1] .empty .empty))) (.node [7,7,3,2,2,2,1,1,1] (.node [7,7,3,2,1,1,1,1,1,1,1] (.node [7,7,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,7,3,2,2,1,1,1,1,1] .empty .empty)) (.node [7,7,3,3,1,1,1,1,1,1] (.node [7,7,3,2,2,2,2,1] .empty .empty) (.node [7,7,3,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_23 : RowTree := (.node [7,7,4,3,2,1,1,1] (.node [7,7,4,2,1,1,1,1,1,1] (.node [7,7,3,3,3,1,1,1] (.node [7,7,3,3,2,2,2] .empty .empty) (.node [7,7,4,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,7,4,2,2,2,1,1] (.node [7,7,4,2,2,1,1,1,1] .empty .empty) (.node [7,7,4,3,1,1,1,1,1] .empty .empty))) (.node [7,7,5,2,2,1,1,1] (.node [7,7,5,1,1,1,1,1,1,1] (.node [7,7,4,4,1,1,1,1] .empty .empty) (.node [7,7,5,2,1,1,1,1,1] .empty .empty)) (.node [7,7,6,1,1,1,1,1,1] (.node [7,7,5,3,1,1,1,1] .empty .empty) (.node [7,7,6,2,1,1,1,1] .empty .empty))))

def degreeTree26_24 : RowTree := (.node [7,7,3,3,2,2,1,1] degreeTree26_22 degreeTree26_23)

def degreeTree26_25 : RowTree := (.node [8,2,2,2,2,2,2,2,2,1,1] (.node [8,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,2,2,2,2,2,2,1,1,1,1,1,1] (.node [8,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,3,2,2,2,2,1,1,1,1,1,1,1] (.node [8,3,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,2,2,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_26 : RowTree := (.node [8,3,3,2,2,2,2,2,2] (.node [8,3,3,2,2,1,1,1,1,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,2,2,2,2,2,2,2,1] .empty .empty) (.node [8,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,3,3,2,2,2,2,1,1,1,1] (.node [8,3,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [8,3,3,2,2,2,2,2,1,1] .empty .empty))) (.node [8,3,3,3,2,2,2,1,1,1] (.node [8,3,3,3,2,1,1,1,1,1,1,1] (.node [8,3,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,3,3,2,2,1,1,1,1,1] .empty .empty)) (.node [8,3,3,3,3,1,1,1,1,1,1] (.node [8,3,3,3,2,2,2,2,1] .empty .empty) (.node [8,3,3,3,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_27 : RowTree := (.node [8,3,2,2,2,2,2,2,1,1,1] degreeTree26_25 degreeTree26_26)

def degreeTree26_28 : RowTree := (.node [7,7,7,1,1,1,1,1] degreeTree26_24 degreeTree26_27)

def degreeTree26_29 : RowTree := (.node [7,6,6,2,1,1,1,1,1] degreeTree26_21 degreeTree26_28)

def degreeTree26_30 : RowTree := (.node [7,5,4,4,2,1,1,1,1] degreeTree26_14 degreeTree26_29)

def degreeTree26_31 : RowTree := (.node [8,4,2,2,2,2,2,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,3,3,3,3,2,1] (.node [8,3,3,3,3,3,1,1,1] (.node [8,3,3,3,3,2,2,2] .empty .empty) .empty) (.node [8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,2,2,2,1,1,1,1,1,1,1,1] (.node [8,4,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,2,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [8,4,3,2,1,1,1,1,1,1,1,1,1] (.node [8,4,2,2,2,2,2,2,2] (.node [8,4,2,2,2,2,2,2,1,1] .empty .empty) (.node [8,4,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,3,2,2,2,1,1,1,1,1] (.node [8,4,3,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_32 : RowTree := (.node [8,4,3,3,3,2,2,1] (.node [8,4,3,3,2,2,2,1,1] (.node [8,4,3,3,2,1,1,1,1,1,1] (.node [8,4,3,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,3,2,2,1,1,1,1] .empty .empty)) (.node [8,4,3,3,3,1,1,1,1,1] (.node [8,4,3,3,2,2,2,2] .empty .empty) (.node [8,4,3,3,3,2,1,1,1] .empty .empty))) (.node [8,4,4,2,2,1,1,1,1,1,1] (.node [8,4,4,1,1,1,1,1,1,1,1,1,1] (.node [8,4,3,3,3,3,1,1] .empty .empty) (.node [8,4,4,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,4,2,2,2,2,1,1] (.node [8,4,4,2,2,2,1,1,1,1] .empty .empty) (.node [8,4,4,2,2,2,2,2] .empty .empty))))

def degreeTree26_33 : RowTree := (.node [8,4,3,2,2,2,2,2,1] degreeTree26_31 degreeTree26_32)

def degreeTree26_34 : RowTree := (.node [8,4,4,4,3,1,1,1] (.node [8,4,4,3,3,2,1,1] (.node [8,4,4,3,2,2,2,1] (.node [8,4,4,3,2,2,1,1,1] (.node [8,4,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,4,4,3,3,1,1,1,1] .empty .empty)) (.node [8,4,4,4,2,1,1,1,1] (.node [8,4,4,4,1,1,1,1,1,1] .empty .empty) (.node [8,4,4,4,2,2,1,1] .empty .empty))) (.node [8,5,2,2,2,1,1,1,1,1,1,1] (.node [8,5,2,1,1,1,1,1,1,1,1,1,1,1] (.node [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,5,2,2,2,2,2,1,1,1] (.node [8,5,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [8,5,2,2,2,2,2,2,1] .empty .empty))))

def degreeTree26_35 : RowTree := (.node [8,5,3,3,2,2,1,1,1] (.node [8,5,3,2,2,2,2,1,1] (.node [8,5,3,2,2,1,1,1,1,1,1] (.node [8,5,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,3,2,2,2,1,1,1,1] .empty .empty)) (.node [8,5,3,3,1,1,1,1,1,1,1] (.node [8,5,3,2,2,2,2,2] .empty .empty) (.node [8,5,3,3,2,1,1,1,1,1] .empty .empty))) (.node [8,5,4,1,1,1,1,1,1,1,1,1] (.node [8,5,3,3,3,1,1,1,1] (.node [8,5,3,3,2,2,2,1] .empty .empty) (.node [8,5,3,3,3,2,1,1] .empty .empty)) (.node [8,5,4,2,2,1,1,1,1,1] (.node [8,5,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,4,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_36 : RowTree := (.node [8,5,3,1,1,1,1,1,1,1,1,1,1] degreeTree26_34 degreeTree26_35)

def degreeTree26_37 : RowTree := (.node [8,4,4,3,1,1,1,1,1,1,1] degreeTree26_33 degreeTree26_36)

def degreeTree26_38 : RowTree := (.node [8,5,5,2,2,1,1,1,1] (.node [8,5,4,4,1,1,1,1,1] (.node [8,5,4,3,2,2,1,1] (.node [8,5,4,3,2,1,1,1,1] (.node [8,5,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,5,4,3,3,1,1,1] .empty .empty)) (.node [8,5,5,1,1,1,1,1,1,1,1] (.node [8,5,4,4,2,1,1,1] .empty .empty) (.node [8,5,5,2,1,1,1,1,1,1] .empty .empty))) (.node [8,6,2,1,1,1,1,1,1,1,1,1,1] (.node [8,5,5,3,1,1,1,1,1] (.node [8,5,5,2,2,2,1,1] .empty .empty) (.node [8,6,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,6,2,2,2,1,1,1,1,1,1] (.node [8,6,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,6,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_39 : RowTree := (.node [8,6,3,3,2,1,1,1,1] (.node [8,6,3,2,2,1,1,1,1,1] (.node [8,6,3,1,1,1,1,1,1,1,1,1] (.node [8,6,2,2,2,2,2,2] .empty .empty) (.node [8,6,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [8,6,3,2,2,2,2,1] (.node [8,6,3,2,2,2,1,1,1] .empty .empty) (.node [8,6,3,3,1,1,1,1,1,1] .empty .empty))) (.node [8,6,4,2,2,1,1,1,1] (.node [8,6,4,1,1,1,1,1,1,1,1] (.node [8,6,3,3,2,2,1,1] .empty .empty) (.node [8,6,4,2,1,1,1,1,1,1] .empty .empty)) (.node [8,6,5,1,1,1,1,1,1,1] (.node [8,6,4,3,1,1,1,1,1] .empty .empty) (.node [8,6,5,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_40 : RowTree := (.node [8,6,2,2,2,2,2,1,1] degreeTree26_38 degreeTree26_39)

def degreeTree26_41 : RowTree := (.node [8,7,3,2,2,1,1,1,1] (.node [8,7,2,2,2,2,1,1,1] (.node [8,7,2,2,1,1,1,1,1,1,1] (.node [8,7,2,1,1,1,1,1,1,1,1,1] (.node [8,7,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,7,2,2,2,1,1,1,1,1] .empty .empty)) (.node [8,7,3,1,1,1,1,1,1,1,1] (.node [8,7,2,2,2,2,2,1] .empty .empty) (.node [8,7,3,2,1,1,1,1,1,1] .empty .empty))) (.node [8,7,5,1,1,1,1,1,1] (.node [8,7,4,1,1,1,1,1,1,1] (.node [8,7,3,3,1,1,1,1,1] .empty .empty) (.node [8,7,4,2,1,1,1,1,1] .empty .empty)) (.node [8,8,2,1,1,1,1,1,1,1,1] (.node [8,8,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,8,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_42 : RowTree := (.node [9,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,8,3,2,1,1,1,1,1] (.node [8,8,3,1,1,1,1,1,1,1] .empty .empty) (.node [8,8,4,1,1,1,1,1,1] .empty .empty)) (.node [9,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,2,2,2,2,2,2,2,2,1] (.node [9,2,2,2,2,2,2,1,1,1,1,1] (.node [9,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [9,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_43 : RowTree := (.node [8,8,2,2,2,1,1,1,1] degreeTree26_41 degreeTree26_42)

def degreeTree26_44 : RowTree := (.node [8,6,6,1,1,1,1,1,1] degreeTree26_40 degreeTree26_43)

def degreeTree26_45 : RowTree := (.node [8,5,4,2,2,2,2,1] degreeTree26_37 degreeTree26_44)

def degreeTree26_46 : RowTree := (.node [9,3,3,2,2,2,2,1,1,1] (.node [9,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [9,3,2,2,2,2,2,2,1,1] (.node [9,3,2,2,2,2,2,1,1,1,1] (.node [9,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,3,2,2,2,2,2,2,2] .empty .empty)) (.node [9,3,3,2,2,1,1,1,1,1,1,1] (.node [9,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,3,2,2,2,1,1,1,1,1] .empty .empty))) (.node [9,3,3,3,2,2,1,1,1,1] (.node [9,3,3,3,1,1,1,1,1,1,1,1] (.node [9,3,3,2,2,2,2,2,1] .empty .empty) (.node [9,3,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [9,3,3,3,3,1,1,1,1,1] (.node [9,3,3,3,2,2,2,1,1] .empty .empty) (.node [9,3,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree26_47 : RowTree := (.node [9,4,3,2,1,1,1,1,1,1,1,1] (.node [9,4,2,2,2,2,1,1,1,1,1] (.node [9,4,2,2,1,1,1,1,1,1,1,1,1] (.node [9,4,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,4,2,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [9,4,2,2,2,2,2,2,1] (.node [9,4,2,2,2,2,2,1,1,1] .empty .empty) (.node [9,4,3,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,4,3,3,1,1,1,1,1,1,1] (.node [9,4,3,2,2,2,1,1,1,1] (.node [9,4,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [9,4,3,2,2,2,2,1,1] .empty .empty)) (.node [9,4,3,3,2,2,1,1,1] (.node [9,4,3,3,2,1,1,1,1,1] .empty .empty) (.node [9,4,3,3,3,1,1,1,1] .empty .empty))))

def degreeTree26_48 : RowTree := (.node [9,4,1,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree26_46 degreeTree26_47)

def degreeTree26_49 : RowTree := (.node [9,5,2,2,1,1,1,1,1,1,1,1] (.node [9,4,4,3,2,1,1,1,1] (.node [9,4,4,2,2,2,1,1,1] (.node [9,4,4,2,2,1,1,1,1,1] (.node [9,4,4,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,4,4,3,1,1,1,1,1,1] .empty .empty)) (.node [9,5,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,4,4,4,1,1,1,1,1] .empty .empty) (.node [9,5,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,5,3,1,1,1,1,1,1,1,1,1] (.node [9,5,2,2,2,2,1,1,1,1] (.node [9,5,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [9,5,2,2,2,2,2,1,1] .empty .empty)) (.node [9,5,3,2,2,1,1,1,1,1] (.node [9,5,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,5,3,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_50 : RowTree := (.node [9,6,2,2,2,1,1,1,1,1] (.node [9,5,5,1,1,1,1,1,1,1] (.node [9,5,4,1,1,1,1,1,1,1,1] (.node [9,5,3,3,2,1,1,1,1] .empty .empty) (.node [9,5,4,2,1,1,1,1,1,1] .empty .empty)) (.node [9,6,2,1,1,1,1,1,1,1,1,1] (.node [9,6,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,6,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [9,6,4,1,1,1,1,1,1,1] (.node [9,6,3,1,1,1,1,1,1,1,1] (.node [9,6,2,2,2,2,1,1,1] .empty .empty) (.node [9,6,3,2,1,1,1,1,1,1] .empty .empty)) (.node [9,7,2,1,1,1,1,1,1,1,1] (.node [9,7,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,7,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_51 : RowTree := (.node [9,5,3,3,1,1,1,1,1,1] degreeTree26_49 degreeTree26_50)

def degreeTree26_52 : RowTree := (.node [9,4,4,1,1,1,1,1,1,1,1,1] degreeTree26_48 degreeTree26_51)

def degreeTree26_53 : RowTree := (.node [10,2,2,2,2,2,1,1,1,1,1,1] (.node [10,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,9,1,1,1,1,1,1,1,1] (.node [9,8,2,1,1,1,1,1,1,1] (.node [9,8,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,3,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,2,2,2,2,2,2,2,1,1] (.node [10,2,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,3,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,3,2,2,2,1,1,1,1,1,1,1] (.node [10,3,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,2,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_54 : RowTree := (.node [10,4,2,1,1,1,1,1,1,1,1,1,1] (.node [10,3,3,2,2,2,1,1,1,1] (.node [10,3,3,2,1,1,1,1,1,1,1,1] (.node [10,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,2,2,1,1,1,1,1,1] .empty .empty)) (.node [10,3,3,3,2,1,1,1,1,1] (.node [10,3,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,4,3,1,1,1,1,1,1,1,1,1] (.node [10,4,2,2,2,1,1,1,1,1,1] (.node [10,4,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,4,3,2,2,1,1,1,1,1] (.node [10,4,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_55 : RowTree := (.node [10,3,2,2,2,2,2,1,1,1] degreeTree26_53 degreeTree26_54)

def degreeTree26_56 : RowTree := (.node [11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,1,1,1,1,1,1,1,1] (.node [10,5,2,2,1,1,1,1,1,1,1] (.node [10,5,2,1,1,1,1,1,1,1,1,1] (.node [10,5,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,5,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,6,2,1,1,1,1,1,1,1,1] (.node [10,6,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [11,2,2,2,2,1,1,1,1,1,1,1] (.node [11,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [11,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [11,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [11,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [11,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [11,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_57 : RowTree := (.node [12,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [11,4,1,1,1,1,1,1,1,1,1,1,1] (.node [11,3,3,1,1,1,1,1,1,1,1,1] (.node [11,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [11,3,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [11,4,2,2,1,1,1,1,1,1,1] (.node [11,4,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [11,5,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [12,3,1,1,1,1,1,1,1,1,1,1,1] (.node [12,2,2,1,1,1,1,1,1,1,1,1,1] (.node [12,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [12,2,2,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [13,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [12,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [13,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_58 : RowTree := (.node [11,3,2,2,1,1,1,1,1,1,1,1] degreeTree26_56 degreeTree26_57)

def degreeTree26_59 : RowTree := (.node [10,4,4,1,1,1,1,1,1,1,1] degreeTree26_55 degreeTree26_58)

def degreeTree26_60 : RowTree := (.node [9,7,3,1,1,1,1,1,1,1] degreeTree26_52 degreeTree26_59)

def degreeTree26_61 : RowTree := (.node [9,3,2,2,2,1,1,1,1,1,1,1,1] degreeTree26_45 degreeTree26_60)

def degreeTree26_62 : RowTree := (.node [8,3,3,3,3,2,2,1,1] degreeTree26_30 degreeTree26_61)

def degreeTree26 : RowTree := degreeTree26_62

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP26 := TreeResidual 4 8 degreeQs26 degreeTree26

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree31_0 : RowTree := (.node [10,3,3,3,2,2,2,2,2,2] (.node [9,9,3,2,2,2,1,1,1,1] (.node [9,8,6,2,1,1,1,1,1,1] (.node [8,8,8,1,1,1,1,1,1,1] (.node [8,8,7,2,1,1,1,1,1,1] .empty .empty) (.node [9,7,7,2,1,1,1,1,1,1] .empty .empty)) (.node [9,9,2,2,2,2,2,1,1,1] (.node [9,8,7,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [9,9,4,3,1,1,1,1,1,1] (.node [9,9,4,2,2,1,1,1,1,1] (.node [9,9,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [9,9,6,1,1,1,1,1,1,1] (.node [9,9,5,2,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,4,3,3,3,2,2,2,1,1] (.node [10,3,3,3,3,3,3,1,1,1] (.node [10,3,3,3,3,3,2,2,1,1] (.node [10,3,3,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [10,4,3,3,2,2,2,2,2,1] (.node [10,4,3,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [10,4,4,3,2,2,2,2,1,1] (.node [10,4,4,2,2,2,2,2,2,1] (.node [10,4,3,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [10,4,4,3,3,3,1,1,1,1] (.node [10,4,4,3,3,2,2,1,1,1] .empty .empty) .empty))))

def degreeTree31_1 : RowTree := (.node [10,5,4,4,3,1,1,1,1,1] (.node [10,5,3,3,3,2,2,1,1,1] (.node [10,5,2,2,2,2,2,2,2,2] (.node [10,4,4,4,4,1,1,1,1,1] (.node [10,4,4,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [10,5,3,3,2,2,2,2,1,1] (.node [10,5,3,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [10,5,4,3,2,2,2,1,1,1] (.node [10,5,4,2,2,2,2,2,1,1] (.node [10,5,3,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [10,5,4,4,2,2,1,1,1,1] (.node [10,5,4,3,3,2,1,1,1,1] .empty .empty) .empty))) (.node [10,6,3,3,2,2,2,1,1,1] (.node [10,5,5,3,3,1,1,1,1,1] (.node [10,5,5,3,2,2,1,1,1,1] (.node [10,5,5,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [10,6,3,2,2,2,2,2,1,1] (.node [10,6,2,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [10,6,4,3,2,2,1,1,1,1] (.node [10,6,4,2,2,2,2,1,1,1] (.node [10,6,3,3,3,2,1,1,1,1] .empty .empty) .empty) (.node [10,7,3,2,2,2,2,1,1,1] (.node [10,7,2,2,2,2,2,2,1,1] .empty .empty) .empty))))

def degreeTree31_2 : RowTree := (.node [10,4,4,4,2,2,2,1,1,1] degreeTree31_0 degreeTree31_1)

def degreeTree31 : RowTree := degreeTree31_2

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP31 := TreeResidual 6 5 degreeQs31 degreeTree31

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree35_0 : RowTree := (.node [8,8,7,4,3,1,1,1,1,1] (.node [8,8,7,2,2,2,2,2,2] (.node [8,8,6,6,2,1,1,1,1,1] (.node [8,7,7,7,1,1,1,1,1,1] (.node [8,7,7,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,8,7,2,2,2,2,2,1,1] .empty .empty)) (.node [8,8,7,3,3,2,1,1,1,1] (.node [8,8,7,3,2,2,2,1,1,1] .empty .empty) (.node [8,8,7,4,2,2,1,1,1,1] .empty .empty))) (.node [8,8,8,3,2,2,1,1,1,1] (.node [8,8,7,6,1,1,1,1,1,1] (.node [8,8,7,5,2,1,1,1,1,1] .empty .empty) (.node [8,8,8,2,2,2,2,1,1,1] .empty .empty)) (.node [8,8,8,4,2,1,1,1,1,1] (.node [8,8,8,3,3,1,1,1,1,1] .empty .empty) (.node [8,8,8,5,1,1,1,1,1,1] .empty .empty))))

def degreeTree35_1 : RowTree := (.node [9,7,7,6,1,1,1,1,1,1] (.node [9,7,7,3,3,2,1,1,1,1] (.node [9,7,7,2,2,2,2,2,2] (.node [9,7,7,2,2,2,2,2,1,1] .empty .empty) (.node [9,7,7,3,2,2,2,1,1,1] .empty .empty)) (.node [9,7,7,4,3,1,1,1,1,1] (.node [9,7,7,4,2,2,1,1,1,1] .empty .empty) (.node [9,7,7,5,2,1,1,1,1,1] .empty .empty))) (.node [9,8,6,3,3,2,1,1,1,1] (.node [9,8,6,2,2,2,2,2,2] (.node [9,8,6,2,2,2,2,2,1,1] .empty .empty) (.node [9,8,6,3,2,2,2,1,1,1] .empty .empty)) (.node [9,8,6,4,3,1,1,1,1,1] (.node [9,8,6,4,2,2,1,1,1,1] .empty .empty) (.node [9,8,6,5,2,1,1,1,1,1] .empty .empty))))

def degreeTree35_2 : RowTree := (.node [9,7,6,6,2,1,1,1,1,1] degreeTree35_0 degreeTree35_1)

def degreeTree35_3 : RowTree := (.node [9,9,3,2,2,2,2,2,2,2] (.node [9,8,7,5,1,1,1,1,1,1] (.node [9,8,7,3,3,1,1,1,1,1] (.node [9,8,7,3,2,2,1,1,1,1] (.node [9,8,7,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [9,8,7,4,2,1,1,1,1,1] .empty .empty)) (.node [9,8,8,3,2,1,1,1,1,1] (.node [9,8,8,2,2,2,1,1,1,1] .empty .empty) (.node [9,8,8,4,1,1,1,1,1,1] .empty .empty))) (.node [9,9,3,3,3,3,2,1,1,1] (.node [9,9,3,3,3,2,2,2,1,1] (.node [9,9,3,3,2,2,2,2,2,1] .empty .empty) (.node [9,9,3,3,3,2,2,2,2] .empty .empty)) (.node [9,9,4,3,2,2,2,2,1,1] (.node [9,9,4,2,2,2,2,2,2,1] .empty .empty) (.node [9,9,4,3,2,2,2,2,2] .empty .empty))))

def degreeTree35_4 : RowTree := (.node [9,9,5,4,2,2,1,1,1,1] (.node [9,9,4,4,4,1,1,1,1,1] (.node [9,9,4,4,2,2,2,1,1,1] (.node [9,9,4,3,3,3,1,1,1,1] .empty .empty) (.node [9,9,4,4,3,2,1,1,1,1] .empty .empty)) (.node [9,9,5,3,2,2,2,1,1,1] (.node [9,9,5,2,2,2,2,2,1,1] .empty .empty) (.node [9,9,5,3,3,2,1,1,1,1] .empty .empty))) (.node [9,9,6,3,2,2,1,1,1,1] (.node [9,9,5,5,2,1,1,1,1,1] (.node [9,9,5,4,3,1,1,1,1,1] .empty .empty) (.node [9,9,6,2,2,2,2,1,1,1] .empty .empty)) (.node [9,9,6,4,2,1,1,1,1,1] (.node [9,9,6,3,3,1,1,1,1,1] .empty .empty) (.node [9,9,6,5,1,1,1,1,1,1] .empty .empty))))

def degreeTree35_5 : RowTree := (.node [9,9,4,3,3,2,2,1,1,1] degreeTree35_3 degreeTree35_4)

def degreeTree35_6 : RowTree := (.node [9,8,6,6,1,1,1,1,1,1] degreeTree35_2 degreeTree35_5)

def degreeTree35_7 : RowTree := (.node [10,3,2,2,2,2,2,2,2,2,2,2,1,1] (.node [9,9,9,2,1,1,1,1,1,1] (.node [9,9,8,2,2,1,1,1,1,1] (.node [9,9,7,4,1,1,1,1,1,1] (.node [9,9,7,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [9,9,8,3,1,1,1,1,1,1] .empty .empty)) (.node [10,2,2,2,2,2,2,2,2,2,2,2,2,1] (.node [10,2,2,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,3,2,2,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [10,3,3,2,2,2,2,2,2,2,2,2,1] (.node [10,3,3,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,3,2,2,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [10,3,3,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,3,3,3,2,2,2,2,2,2,1,1,1,1] (.node [10,3,3,3,2,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,2,2,2,2,2,2,2,1,1] .empty .empty))))

def degreeTree35_8 : RowTree := (.node [10,3,3,3,3,3,2,2,2,2,1,1] (.node [10,3,3,3,3,2,2,2,2,2,2,1] (.node [10,3,3,3,3,2,2,2,2,1,1,1,1,1] (.node [10,3,3,3,3,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,3,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,3,3,3,3,3,2,2,1,1,1,1,1,1] (.node [10,3,3,3,3,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,3,3,2,2,2,1,1,1,1] .empty .empty))) (.node [10,3,3,3,3,3,3,2,2,1,1,1] (.node [10,3,3,3,3,3,3,1,1,1,1,1,1,1] (.node [10,3,3,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,3,3,3,3,3,3,2,1,1,1,1,1] .empty .empty)) (.node [10,3,3,3,3,3,3,3,1,1,1,1] (.node [10,3,3,3,3,3,3,2,2,2,1] .empty .empty) (.node [10,3,3,3,3,3,3,3,2,1,1] .empty .empty))))

def degreeTree35_9 : RowTree := (.node [10,3,3,3,2,2,2,2,2,2,2,2] degreeTree35_7 degreeTree35_8)

def degreeTree35_10 : RowTree := (.node [10,4,3,3,3,2,2,2,2,2,1,1] (.node [10,4,3,2,2,2,2,2,2,2,2,2] (.node [10,4,2,2,2,2,2,2,2,2,2,2,1] (.node [10,4,2,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,3,3,3,3,3,3,3,3,1] .empty .empty) (.node [10,4,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,4,3,2,2,2,2,2,2,2,1,1,1,1] (.node [10,4,3,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,2,2,2,2,2,2,2,2,1,1] .empty .empty))) (.node [10,4,3,3,2,2,2,2,2,2,2,1] (.node [10,4,3,3,2,2,2,2,2,1,1,1,1,1] (.node [10,4,3,3,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,4,3,3,3,2,2,2,1,1,1,1,1,1] (.node [10,4,3,3,3,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,3,2,2,2,2,1,1,1,1] .empty .empty)))) (.node [10,4,3,3,3,3,3,2,1,1,1,1] (.node [10,4,3,3,3,3,2,2,1,1,1,1,1] (.node [10,4,3,3,3,3,1,1,1,1,1,1,1,1,1] (.node [10,4,3,3,3,2,2,2,2,2,2] .empty .empty) (.node [10,4,3,3,3,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,4,3,3,3,3,2,2,2,2,1] (.node [10,4,3,3,3,3,2,2,2,1,1,1] .empty .empty) (.node [10,4,3,3,3,3,3,1,1,1,1,1,1] .empty .empty))) (.node [10,4,3,3,3,3,3,3,2,1] (.node [10,4,3,3,3,3,3,2,2,2] (.node [10,4,3,3,3,3,3,2,2,1,1] .empty .empty) (.node [10,4,3,3,3,3,3,3,1,1,1] .empty .empty)) (.node [10,4,4,2,2,2,2,2,2,1,1,1,1,1] (.node [10,4,4,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,2,2,2,2,2,2,2,1,1,1] .empty .empty)))))

def degreeTree35_11 : RowTree := (.node [10,3,3,3,3,3,3,3,2,2] degreeTree35_9 degreeTree35_10)

def degreeTree35_12 : RowTree := (.node [9,9,7,2,2,2,1,1,1,1] degreeTree35_6 degreeTree35_11)

def degreeTree35_13 : RowTree := (.node [10,4,4,3,3,2,2,2,2,1,1,1] (.node [10,4,4,3,2,2,2,2,2,2,2] (.node [10,4,4,3,2,2,2,2,2,1,1,1,1] (.node [10,4,4,3,2,2,2,2,1,1,1,1,1,1] (.node [10,4,4,3,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,4,4,3,2,2,2,2,2,2,1,1] .empty .empty)) (.node [10,4,4,3,3,2,2,1,1,1,1,1,1,1] (.node [10,4,4,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,3,3,2,2,2,1,1,1,1,1] .empty .empty))) (.node [10,4,4,3,3,3,2,2,1,1,1,1] (.node [10,4,4,3,3,3,1,1,1,1,1,1,1,1] (.node [10,4,4,3,3,2,2,2,2,2,1] .empty .empty) (.node [10,4,4,3,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [10,4,4,3,3,3,2,2,2,2] (.node [10,4,4,3,3,3,2,2,2,1,1] .empty .empty) (.node [10,4,4,3,3,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree35_14 : RowTree := (.node [10,4,4,4,3,1,1,1,1,1,1,1,1,1,1] (.node [10,4,4,4,2,2,2,1,1,1,1,1,1,1] (.node [10,4,4,3,3,3,3,3,1,1] (.node [10,4,4,3,3,3,3,2,2,1] .empty .empty) (.node [10,4,4,4,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,4,4,4,2,2,2,2,2,1,1,1] (.node [10,4,4,4,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,2,2,2,2,2,2,1] .empty .empty))) (.node [10,4,4,4,3,2,2,2,2,1,1] (.node [10,4,4,4,3,2,2,1,1,1,1,1,1] (.node [10,4,4,4,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,3,2,2,2,1,1,1,1] .empty .empty)) (.node [10,4,4,4,3,3,1,1,1,1,1,1,1] (.node [10,4,4,4,3,2,2,2,2,2] .empty .empty) (.node [10,4,4,4,3,3,2,1,1,1,1,1] .empty .empty))))

def degreeTree35_15 : RowTree := (.node [10,4,4,3,3,3,3,2,1,1,1] degreeTree35_13 degreeTree35_14)

def degreeTree35_16 : RowTree := (.node [10,5,2,2,2,2,2,2,2,2,1,1,1,1] (.node [10,4,4,4,4,2,2,2,2,1] (.node [10,4,4,4,4,1,1,1,1,1,1,1,1,1] (.node [10,4,4,4,3,3,3,1,1,1,1] (.node [10,4,4,4,3,3,2,2,2,1] .empty .empty) (.node [10,4,4,4,3,3,3,2,1,1] .empty .empty)) (.node [10,4,4,4,4,2,2,1,1,1,1,1] (.node [10,4,4,4,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,2,2,2,1,1,1] .empty .empty))) (.node [10,4,4,4,4,3,3,1,1,1] (.node [10,4,4,4,4,3,2,1,1,1,1] (.node [10,4,4,4,4,3,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,3,2,2,1,1] .empty .empty)) (.node [10,4,4,4,4,4,2,1,1,1] (.node [10,4,4,4,4,4,1,1,1,1,1] .empty .empty) (.node [10,5,2,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty)))) (.node [10,5,4,3,3,3,3,2,1,1] (.node [10,5,3,3,3,3,3,2,2,1] (.node [10,5,2,2,2,2,2,2,2,2,2,2] (.node [10,5,2,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,5,3,3,3,3,2,2,2,2] .empty .empty)) (.node [10,5,4,3,3,2,2,2,2,2] (.node [10,5,3,3,3,3,3,3,1,1] .empty .empty) (.node [10,5,4,3,3,3,2,2,2,1] .empty .empty))) (.node [10,5,4,4,3,3,3,1,1,1] (.node [10,5,4,4,3,2,2,2,2,1] (.node [10,5,4,4,2,2,2,2,2,2] .empty .empty) (.node [10,5,4,4,3,3,2,2,1,1] .empty .empty)) (.node [10,5,4,4,4,3,2,1,1,1] (.node [10,5,4,4,4,2,2,2,1,1] .empty .empty) (.node [10,5,4,4,4,4,1,1,1,1] .empty .empty)))))

def degreeTree35_17 : RowTree := (.node [10,4,4,4,3,3,2,2,1,1,1] degreeTree35_15 degreeTree35_16)

def degreeTree35_18 : RowTree := (.node [10,5,5,5,2,2,2,2,1,1] (.node [10,5,5,4,3,2,2,2,1,1] (.node [10,5,5,3,3,3,3,1,1,1] (.node [10,5,5,3,3,3,2,2,1,1] (.node [10,5,5,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [10,5,5,4,2,2,2,2,2,1] .empty .empty)) (.node [10,5,5,4,4,2,2,1,1,1] (.node [10,5,5,4,3,3,2,1,1,1] .empty .empty) (.node [10,5,5,4,4,3,1,1,1,1] .empty .empty))) (.node [10,5,5,5,5,1,1,1,1,1] (.node [10,5,5,5,3,3,1,1,1,1] (.node [10,5,5,5,3,2,2,1,1,1] .empty .empty) (.node [10,5,5,5,4,2,1,1,1,1] .empty .empty)) (.node [10,6,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,6,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,2,2,2,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree35_19 : RowTree := (.node [10,6,4,4,2,2,2,2,2,1] (.node [10,6,4,3,2,2,2,2,2,2] (.node [10,6,3,3,3,3,2,2,2,1] (.node [10,6,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,6,3,3,3,3,3,2,1,1] .empty .empty)) (.node [10,6,4,3,3,3,2,2,1,1] (.node [10,6,4,3,3,2,2,2,2,1] .empty .empty) (.node [10,6,4,3,3,3,3,1,1,1] .empty .empty))) (.node [10,6,4,4,4,3,1,1,1,1] (.node [10,6,4,4,3,3,2,1,1,1] (.node [10,6,4,4,3,2,2,2,1,1] .empty .empty) (.node [10,6,4,4,4,2,2,1,1,1] .empty .empty)) (.node [10,6,5,3,2,2,2,2,2,1] (.node [10,6,5,2,2,2,2,2,2,2] .empty .empty) (.node [10,6,5,3,3,2,2,2,1,1] .empty .empty))))

def degreeTree35_20 : RowTree := (.node [10,6,2,2,2,2,2,2,2,2,2,1] degreeTree35_18 degreeTree35_19)

def degreeTree35_21 : RowTree := (.node [10,7,4,3,2,2,2,2,2,1] (.node [10,6,6,3,3,2,2,1,1,1] (.node [10,6,5,4,4,2,1,1,1,1] (.node [10,6,5,4,3,2,2,1,1,1] (.node [10,6,5,4,2,2,2,2,1,1] .empty .empty) (.node [10,6,5,4,3,3,1,1,1,1] .empty .empty)) (.node [10,6,6,2,2,2,2,2,2,1] (.node [10,6,5,5,2,2,2,1,1,1] .empty .empty) (.node [10,6,6,3,2,2,2,2,1,1] .empty .empty))) (.node [10,7,3,3,3,2,2,2,2,1] (.node [10,6,6,4,2,2,2,1,1,1] (.node [10,6,6,3,3,3,1,1,1,1] .empty .empty) (.node [10,7,3,3,2,2,2,2,2,2] .empty .empty)) (.node [10,7,3,3,3,3,3,1,1,1] (.node [10,7,3,3,3,3,2,2,1,1] .empty .empty) (.node [10,7,4,2,2,2,2,2,2,2] .empty .empty)))) (.node [10,7,6,2,2,2,2,2,1,1] (.node [10,7,4,4,3,2,2,1,1,1] (.node [10,7,4,3,3,3,2,1,1,1] (.node [10,7,4,3,3,2,2,2,1,1] .empty .empty) (.node [10,7,4,4,2,2,2,2,1,1] .empty .empty)) (.node [10,7,5,3,2,2,2,2,1,1] (.node [10,7,5,2,2,2,2,2,2,1] .empty .empty) (.node [10,7,5,3,3,2,2,1,1,1] .empty .empty))) (.node [10,8,4,2,2,2,2,2,2,1] (.node [10,8,3,3,2,2,2,2,2,1] (.node [10,8,3,2,2,2,2,2,2,2] .empty .empty) (.node [10,8,3,3,3,2,2,2,1,1] .empty .empty)) (.node [10,9,2,2,2,2,2,2,2,2] (.node [10,8,4,3,2,2,2,2,1,1] .empty .empty) (.node [10,9,3,2,2,2,2,2,2,1] .empty .empty)))))

def degreeTree35_22 : RowTree := (.node [10,6,5,3,3,3,2,1,1,1] degreeTree35_20 degreeTree35_21)

def degreeTree35_23 : RowTree := (.node [10,5,5,3,2,2,2,2,2,2] degreeTree35_17 degreeTree35_22)

def degreeTree35_24 : RowTree := (.node [10,4,4,2,2,2,2,2,2,2,2,1] degreeTree35_12 degreeTree35_23)

def degreeTree35 : RowTree := degreeTree35_24

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP35 := TreeResidual 6 7 degreeQs35 degreeTree35

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree37_0 : RowTree := (.node [10,10,3,2,2,2,2,2,2,2] .empty .empty)

def degreeTree37 : RowTree := degreeTree37_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP37 := TreeResidual 6 8 degreeQs37 degreeTree37

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion89_1 : PrefixRegion := ([(1,18),(2,20),(3,44)], [(2,18),(3,44),(5,47)])
def degreeRegion89_2 : PrefixRegion := ([(1,18),(3,30)], [(2,18),(3,44),(5,47)])
def degreeRegion89_3 : PrefixRegion := ([(1,18),(4,40)], [(2,18),(3,44),(5,47)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree39_0 : RowTree := (.node [8,5,5,5,5,4,3,2,2] (.node [8,5,5,4,4,4,4,4,1] (.node [8,5,4,4,4,4,4,3,3] (.node [7,7,7,7,7,2,1,1] (.node [7,7,7,7,7,1,1,1,1] .empty .empty) (.node [8,4,4,4,4,4,4,4,3] .empty .empty)) (.node [8,5,5,4,4,4,3,3,3] (.node [8,5,4,4,4,4,4,4,2] .empty .empty) (.node [8,5,5,4,4,4,4,3,2] .empty .empty))) (.node [8,5,5,5,4,4,4,3,1] (.node [8,5,5,5,4,4,3,3,2] (.node [8,5,5,5,4,3,3,3,3] .empty .empty) (.node [8,5,5,5,4,4,4,2,2] .empty .empty)) (.node [8,5,5,5,5,3,3,3,2] (.node [8,5,5,5,4,4,4,4] .empty .empty) .empty))) (.node [8,5,5,5,5,5,4,2] (.node [8,5,5,5,5,5,2,2,2] (.node [8,5,5,5,5,4,4,2,1] (.node [8,5,5,5,5,4,3,3,1] .empty .empty) (.node [8,5,5,5,5,4,4,3] .empty .empty)) (.node [8,5,5,5,5,5,3,3] (.node [8,5,5,5,5,5,3,2,1] .empty .empty) (.node [8,5,5,5,5,5,4,1,1] .empty .empty))) (.node [8,6,4,4,4,4,4,4,1] (.node [8,6,4,4,4,4,3,3,3] (.node [8,5,5,5,5,5,5,1] .empty .empty) (.node [8,6,4,4,4,4,4,3,2] .empty .empty)) (.node [8,6,5,4,4,4,3,3,2] (.node [8,6,5,4,4,3,3,3,3] .empty .empty) .empty))))

def degreeTree39_1 : RowTree := (.node [8,6,5,5,5,4,4,2] (.node [8,6,5,5,4,4,4,3] (.node [8,6,5,5,4,3,3,3,2] (.node [8,6,5,4,4,4,4,4] (.node [8,6,5,4,4,4,4,3,1] .empty .empty) (.node [8,6,5,5,3,3,3,3,3] .empty .empty)) (.node [8,6,5,5,4,4,3,3,1] (.node [8,6,5,5,4,4,3,2,2] .empty .empty) (.node [8,6,5,5,4,4,4,2,1] .empty .empty))) (.node [8,6,5,5,5,4,3,2,1] (.node [8,6,5,5,5,3,3,3,1] (.node [8,6,5,5,5,3,3,2,2] .empty .empty) (.node [8,6,5,5,5,4,2,2,2] .empty .empty)) (.node [8,6,5,5,5,4,4,1,1] (.node [8,6,5,5,5,4,3,3] .empty .empty) .empty))) (.node [8,6,6,4,4,4,3,2,2] (.node [8,6,5,5,5,5,4,1] (.node [8,6,5,5,5,5,3,1,1] (.node [8,6,5,5,5,5,2,2,1] .empty .empty) (.node [8,6,5,5,5,5,3,2] .empty .empty)) (.node [8,6,6,4,4,3,3,3,2] (.node [8,6,6,4,3,3,3,3,3] .empty .empty) .empty)) (.node [8,6,6,5,3,3,3,3,2] (.node [8,6,6,4,4,4,4,2,1] (.node [8,6,6,4,4,4,3,3,1] .empty .empty) (.node [8,6,6,4,4,4,4,3] .empty .empty)) (.node [8,6,6,5,4,3,3,3,1] (.node [8,6,6,5,4,3,3,2,2] .empty .empty) .empty))))

def degreeTree39_2 : RowTree := (.node [8,6,5,4,4,4,4,2,2] degreeTree39_0 degreeTree39_1)

def degreeTree39_3 : RowTree := (.node [8,6,6,6,3,3,3,2,2] (.node [8,6,6,5,5,4,2,2,1] (.node [8,6,6,5,4,4,4,2] (.node [8,6,6,5,4,4,3,3] (.node [8,6,6,5,4,4,3,2,1] .empty .empty) (.node [8,6,6,5,4,4,4,1,1] .empty .empty)) (.node [8,6,6,5,5,3,3,2,1] (.node [8,6,6,5,5,3,2,2,2] .empty .empty) (.node [8,6,6,5,5,3,3,3] .empty .empty))) (.node [8,6,6,5,5,5,2,1,1] (.node [8,6,6,5,5,4,3,2] (.node [8,6,6,5,5,4,3,1,1] .empty .empty) (.node [8,6,6,5,5,4,4,1] .empty .empty)) (.node [8,6,6,5,5,5,3,1] (.node [8,6,6,5,5,5,2,2] .empty .empty) .empty))) (.node [8,6,6,6,4,4,3,2] (.node [8,6,6,6,4,3,3,3] (.node [8,6,6,6,4,3,2,2,2] (.node [8,6,6,6,3,3,3,3,1] .empty .empty) (.node [8,6,6,6,4,3,3,2,1] .empty .empty)) (.node [8,6,6,6,4,4,3,1,1] (.node [8,6,6,6,4,4,2,2,1] .empty .empty) .empty)) (.node [8,6,6,6,5,3,3,1,1] (.node [8,6,6,6,5,2,2,2,2] (.node [8,6,6,6,4,4,4,1] .empty .empty) (.node [8,6,6,6,5,3,2,2,1] .empty .empty)) (.node [8,6,6,6,5,4,2,1,1] (.node [8,6,6,6,5,3,3,2] .empty .empty) .empty))))

def degreeTree39_4 : RowTree := (.node [8,7,4,4,4,4,4,4] (.node [8,6,6,6,6,4,1,1,1] (.node [8,6,6,6,6,2,2,2,1] (.node [8,6,6,6,5,5,1,1,1] (.node [8,6,6,6,5,4,3,1] .empty .empty) (.node [8,6,6,6,5,5,2,1] .empty .empty)) (.node [8,6,6,6,6,3,2,2] (.node [8,6,6,6,6,3,2,1,1] .empty .empty) (.node [8,6,6,6,6,3,3,1] .empty .empty))) (.node [8,7,4,4,4,4,3,3,2] (.node [8,6,6,6,6,5,1,1] (.node [8,6,6,6,6,4,2,1] .empty .empty) (.node [8,7,4,4,4,3,3,3,3] .empty .empty)) (.node [8,7,4,4,4,4,4,3,1] (.node [8,7,4,4,4,4,4,2,2] .empty .empty) .empty))) (.node [8,7,5,5,3,3,3,3,2] (.node [8,7,5,4,4,4,3,3,1] (.node [8,7,5,4,4,3,3,3,2] (.node [8,7,5,4,3,3,3,3,3] .empty .empty) (.node [8,7,5,4,4,4,3,2,2] .empty .empty)) (.node [8,7,5,4,4,4,4,3] (.node [8,7,5,4,4,4,4,2,1] .empty .empty) .empty)) (.node [8,7,5,5,4,4,3,2,1] (.node [8,7,5,5,4,3,3,3,1] (.node [8,7,5,5,4,3,3,2,2] .empty .empty) (.node [8,7,5,5,4,4,2,2,2] .empty .empty)) (.node [8,7,5,5,4,4,4,1,1] (.node [8,7,5,5,4,4,3,3] .empty .empty) .empty))))

def degreeTree39_5 : RowTree := (.node [8,6,6,6,5,4,2,2] degreeTree39_3 degreeTree39_4)

def degreeTree39_6 : RowTree := (.node [8,6,6,5,4,4,2,2,2] degreeTree39_2 degreeTree39_5)

def degreeTree39_7 : RowTree := (.node [8,7,6,4,4,4,2,2,2] (.node [8,7,5,5,5,5,2,1,1] (.node [8,7,5,5,5,4,2,2,1] (.node [8,7,5,5,5,3,3,2,1] (.node [8,7,5,5,5,3,2,2,2] .empty .empty) (.node [8,7,5,5,5,3,3,3] .empty .empty)) (.node [8,7,5,5,5,4,3,2] (.node [8,7,5,5,5,4,3,1,1] .empty .empty) (.node [8,7,5,5,5,4,4,1] .empty .empty))) (.node [8,7,6,4,3,3,3,3,2] (.node [8,7,5,5,5,5,3,1] (.node [8,7,5,5,5,5,2,2] .empty .empty) (.node [8,7,6,3,3,3,3,3,3] .empty .empty)) (.node [8,7,6,4,4,3,3,3,1] (.node [8,7,6,4,4,3,3,2,2] .empty .empty) .empty))) (.node [8,7,6,5,4,3,2,2,2] (.node [8,7,6,4,4,4,4,2] (.node [8,7,6,4,4,4,3,3] (.node [8,7,6,4,4,4,3,2,1] .empty .empty) (.node [8,7,6,4,4,4,4,1,1] .empty .empty)) (.node [8,7,6,5,3,3,3,3,1] (.node [8,7,6,5,3,3,3,2,2] .empty .empty) .empty)) (.node [8,7,6,5,4,4,3,1,1] (.node [8,7,6,5,4,3,3,3] (.node [8,7,6,5,4,3,3,2,1] .empty .empty) (.node [8,7,6,5,4,4,2,2,1] .empty .empty)) (.node [8,7,6,5,4,4,4,1] (.node [8,7,6,5,4,4,3,2] .empty .empty) .empty))))

def degreeTree39_8 : RowTree := (.node [8,7,6,6,4,3,3,2] (.node [8,7,6,5,5,5,2,1] (.node [8,7,6,5,5,4,2,1,1] (.node [8,7,6,5,5,3,3,1,1] (.node [8,7,6,5,5,3,2,2,1] .empty .empty) (.node [8,7,6,5,5,3,3,2] .empty .empty)) (.node [8,7,6,5,5,4,3,1] (.node [8,7,6,5,5,4,2,2] .empty .empty) (.node [8,7,6,5,5,5,1,1,1] .empty .empty))) (.node [8,7,6,6,4,2,2,2,2] (.node [8,7,6,6,3,3,3,2,1] (.node [8,7,6,6,3,3,2,2,2] .empty .empty) (.node [8,7,6,6,3,3,3,3] .empty .empty)) (.node [8,7,6,6,4,3,3,1,1] (.node [8,7,6,6,4,3,2,2,1] .empty .empty) .empty))) (.node [8,7,6,6,5,3,3,1] (.node [8,7,6,6,5,2,2,2,1] (.node [8,7,6,6,4,4,2,2] (.node [8,7,6,6,4,4,2,1,1] .empty .empty) (.node [8,7,6,6,4,4,3,1] .empty .empty)) (.node [8,7,6,6,5,3,2,2] (.node [8,7,6,6,5,3,2,1,1] .empty .empty) .empty)) (.node [8,7,6,6,6,2,1,1,1,1] (.node [8,7,6,6,5,4,2,1] (.node [8,7,6,6,5,4,1,1,1] .empty .empty) (.node [8,7,6,6,6,1,1,1,1,1,1] .empty .empty)) (.node [8,7,6,6,6,2,2,2] (.node [8,7,6,6,6,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_9 : RowTree := (.node [8,7,6,5,5,2,2,2,2] degreeTree39_7 degreeTree39_8)

def degreeTree39_10 : RowTree := (.node [8,7,7,5,4,3,2,2,1] (.node [8,7,7,4,4,4,3,1,1] (.node [8,7,7,4,4,3,2,2,2] (.node [8,7,7,4,3,3,3,2,2] (.node [8,7,7,3,3,3,3,3,2] .empty .empty) (.node [8,7,7,4,3,3,3,3,1] .empty .empty)) (.node [8,7,7,4,4,3,3,3] (.node [8,7,7,4,4,3,3,2,1] .empty .empty) (.node [8,7,7,4,4,4,2,2,1] .empty .empty))) (.node [8,7,7,5,3,3,3,2,1] (.node [8,7,7,4,4,4,4,1] (.node [8,7,7,4,4,4,3,2] .empty .empty) (.node [8,7,7,5,3,3,2,2,2] .empty .empty)) (.node [8,7,7,5,4,2,2,2,2] (.node [8,7,7,5,3,3,3,3] .empty .empty) .empty))) (.node [8,7,7,5,5,3,2,1,1] (.node [8,7,7,5,4,4,2,2] (.node [8,7,7,5,4,3,3,2] (.node [8,7,7,5,4,3,3,1,1] .empty .empty) (.node [8,7,7,5,4,4,2,1,1] .empty .empty)) (.node [8,7,7,5,5,2,2,2,1] (.node [8,7,7,5,4,4,3,1] .empty .empty) .empty)) (.node [8,7,7,6,2,2,2,2,2,1] (.node [8,7,7,5,5,3,3,1] (.node [8,7,7,5,5,3,2,2] .empty .empty) (.node [8,7,7,5,5,4,1,1,1] .empty .empty)) (.node [8,7,7,6,3,2,2,2,2] (.node [8,7,7,6,3,2,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_11 : RowTree := (.node [8,7,7,6,6,2,1,1,1] (.node [8,7,7,6,4,3,2,2] (.node [8,7,7,6,4,2,2,1,1,1] (.node [8,7,7,6,3,3,3,1,1] (.node [8,7,7,6,3,3,2,2,1] .empty .empty) (.node [8,7,7,6,3,3,3,2] .empty .empty)) (.node [8,7,7,6,4,3,1,1,1,1] (.node [8,7,7,6,4,2,2,2,1] .empty .empty) (.node [8,7,7,6,4,3,2,1,1] .empty .empty))) (.node [8,7,7,6,5,2,2,2] (.node [8,7,7,6,5,2,1,1,1,1] (.node [8,7,7,6,4,4,1,1,1] .empty .empty) (.node [8,7,7,6,5,2,2,1,1] .empty .empty)) (.node [8,7,7,6,6,1,1,1,1,1] (.node [8,7,7,6,5,3,1,1,1] .empty .empty) .empty))) (.node [8,7,7,7,3,3,2,2] (.node [8,7,7,7,3,2,2,2,1] (.node [8,7,7,7,2,2,2,2,2] (.node [8,7,7,7,2,2,2,2,1,1] .empty .empty) (.node [8,7,7,7,3,2,2,1,1,1] .empty .empty)) (.node [8,7,7,7,3,3,2,1,1] (.node [8,7,7,7,3,3,1,1,1,1] .empty .empty) .empty)) (.node [8,7,7,7,4,3,1,1,1] (.node [8,7,7,7,4,2,2,1,1] (.node [8,7,7,7,4,2,1,1,1,1] .empty .empty) (.node [8,7,7,7,4,2,2,2] .empty .empty)) (.node [8,7,7,7,5,2,1,1,1] (.node [8,7,7,7,5,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_12 : RowTree := (.node [8,7,7,6,3,3,2,1,1,1] degreeTree39_10 degreeTree39_11)

def degreeTree39_13 : RowTree := (.node [8,7,6,6,6,3,1,1,1] degreeTree39_9 degreeTree39_12)

def degreeTree39_14 : RowTree := (.node [8,7,5,5,4,4,4,2] degreeTree39_6 degreeTree39_13)

def degreeTree39_15 : RowTree := (.node [8,8,5,4,4,4,4,2] (.node [8,8,5,4,3,3,3,3,2] (.node [8,8,4,4,4,4,3,3,1] (.node [8,8,4,4,4,3,3,3,2] (.node [8,8,4,4,3,3,3,3,3] .empty .empty) (.node [8,8,4,4,4,4,3,2,2] .empty .empty)) (.node [8,8,4,4,4,4,4,3] (.node [8,8,4,4,4,4,4,2,1] .empty .empty) (.node [8,8,5,3,3,3,3,3,3] .empty .empty))) (.node [8,8,5,4,4,4,3,2,1] (.node [8,8,5,4,4,3,3,3,1] (.node [8,8,5,4,4,3,3,2,2] .empty .empty) (.node [8,8,5,4,4,4,2,2,2] .empty .empty)) (.node [8,8,5,4,4,4,4,1,1] (.node [8,8,5,4,4,4,3,3] .empty .empty) .empty))) (.node [8,8,5,5,4,4,3,1,1] (.node [8,8,5,5,4,3,3,2,1] (.node [8,8,5,5,3,3,3,3,1] (.node [8,8,5,5,3,3,3,2,2] .empty .empty) (.node [8,8,5,5,4,3,2,2,2] .empty .empty)) (.node [8,8,5,5,4,4,2,2,1] (.node [8,8,5,5,4,3,3,3] .empty .empty) .empty)) (.node [8,8,5,5,5,3,3,1,1] (.node [8,8,5,5,5,2,2,2,2] (.node [8,8,5,5,4,4,3,2] .empty .empty) (.node [8,8,5,5,5,3,2,2,1] .empty .empty)) (.node [8,8,5,5,5,4,2,1,1] (.node [8,8,5,5,5,3,3,2] .empty .empty) .empty))))

def degreeTree39_16 : RowTree := (.node [8,8,6,5,4,3,2,2,1] (.node [8,8,6,4,4,4,2,2,1] (.node [8,8,6,4,3,3,3,3,1] (.node [8,8,6,3,3,3,3,3,2] (.node [8,8,5,5,5,5,1,1,1] .empty .empty) (.node [8,8,6,4,3,3,3,2,2] .empty .empty)) (.node [8,8,6,4,4,3,3,2,1] (.node [8,8,6,4,4,3,2,2,2] .empty .empty) (.node [8,8,6,4,4,3,3,3] .empty .empty))) (.node [8,8,6,5,3,3,3,2,1] (.node [8,8,6,4,4,4,3,2] (.node [8,8,6,4,4,4,3,1,1] .empty .empty) (.node [8,8,6,5,3,3,2,2,2] .empty .empty)) (.node [8,8,6,5,4,2,2,2,2] (.node [8,8,6,5,3,3,3,3] .empty .empty) .empty))) (.node [8,8,6,5,5,3,2,2] (.node [8,8,6,5,4,4,2,2] (.node [8,8,6,5,4,3,3,2] (.node [8,8,6,5,4,3,3,1,1] .empty .empty) (.node [8,8,6,5,4,4,2,1,1] .empty .empty)) (.node [8,8,6,5,5,3,2,1,1] (.node [8,8,6,5,5,2,2,2,1] .empty .empty) .empty)) (.node [8,8,6,6,2,2,1,1,1,1,1,1,1] (.node [8,8,6,6,1,1,1,1,1,1,1,1,1,1,1] (.node [8,8,6,5,5,4,1,1,1] .empty .empty) (.node [8,8,6,6,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,8,6,6,2,2,2,2,1,1,1] (.node [8,8,6,6,2,2,2,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_17 : RowTree := (.node [8,8,5,5,5,4,2,2] degreeTree39_15 degreeTree39_16)

def degreeTree39_18 : RowTree := (.node [8,8,6,6,4,3,1,1,1,1] (.node [8,8,6,6,3,3,2,2,1] (.node [8,8,6,6,3,2,2,2,1,1] (.node [8,8,6,6,3,2,1,1,1,1,1,1] (.node [8,8,6,6,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,8,6,6,3,2,2,1,1,1,1] .empty .empty)) (.node [8,8,6,6,3,3,1,1,1,1,1] (.node [8,8,6,6,3,2,2,2,2] .empty .empty) (.node [8,8,6,6,3,3,2,1,1,1] .empty .empty))) (.node [8,8,6,6,4,2,1,1,1,1,1] (.node [8,8,6,6,3,3,3,2] (.node [8,8,6,6,3,3,3,1,1] .empty .empty) (.node [8,8,6,6,4,1,1,1,1,1,1,1] .empty .empty)) (.node [8,8,6,6,4,2,2,2,1] (.node [8,8,6,6,4,2,2,1,1,1] .empty .empty) .empty))) (.node [8,8,6,6,6,1,1,1,1,1] (.node [8,8,6,6,5,2,1,1,1,1] (.node [8,8,6,6,4,4,1,1,1] (.node [8,8,6,6,4,3,2,1,1] .empty .empty) (.node [8,8,6,6,5,1,1,1,1,1,1] .empty .empty)) (.node [8,8,6,6,5,3,1,1,1] (.node [8,8,6,6,5,2,2,1,1] .empty .empty) .empty)) (.node [8,8,7,3,3,3,3,2,1,1] (.node [8,8,7,3,3,2,2,2,2,2] (.node [8,8,6,6,6,2,1,1,1] .empty .empty) (.node [8,8,7,3,3,3,2,2,2,1] .empty .empty)) (.node [8,8,7,3,3,3,3,3,1] (.node [8,8,7,3,3,3,3,2,2] .empty .empty) .empty))))

def degreeTree39_19 : RowTree := (.node [8,8,7,5,2,2,2,2,2,1] (.node [8,8,7,4,4,2,2,2,2] (.node [8,8,7,4,3,3,3,1,1,1] (.node [8,8,7,4,3,3,2,2,1,1] (.node [8,8,7,4,3,2,2,2,2,1] .empty .empty) (.node [8,8,7,4,3,3,2,2,2] .empty .empty)) (.node [8,8,7,4,3,3,3,3] (.node [8,8,7,4,3,3,3,2,1] .empty .empty) (.node [8,8,7,4,4,2,2,2,1,1] .empty .empty))) (.node [8,8,7,4,4,3,3,2] (.node [8,8,7,4,4,3,2,2,1] (.node [8,8,7,4,4,3,2,1,1,1] .empty .empty) (.node [8,8,7,4,4,3,3,1,1] .empty .empty)) (.node [8,8,7,4,4,4,2,1,1] (.node [8,8,7,4,4,4,1,1,1,1] .empty .empty) .empty))) (.node [8,8,7,5,4,2,2,2,1] (.node [8,8,7,5,3,3,2,2,1] (.node [8,8,7,5,3,2,2,2,2] (.node [8,8,7,5,3,2,2,2,1,1] .empty .empty) (.node [8,8,7,5,3,3,2,1,1,1] .empty .empty)) (.node [8,8,7,5,4,2,2,1,1,1] (.node [8,8,7,5,3,3,3,1,1] .empty .empty) .empty)) (.node [8,8,7,5,5,2,1,1,1,1] (.node [8,8,7,5,4,3,2,1,1] (.node [8,8,7,5,4,3,1,1,1,1] .empty .empty) (.node [8,8,7,5,4,4,1,1,1] .empty .empty)) (.node [8,8,7,5,5,3,1,1,1] (.node [8,8,7,5,5,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_20 : RowTree := (.node [8,8,7,4,2,2,2,2,2,2] degreeTree39_18 degreeTree39_19)

def degreeTree39_21 : RowTree := (.node [8,8,6,6,2,2,2,2,2,1] degreeTree39_17 degreeTree39_20)

def degreeTree39_22 : RowTree := (.node [8,8,7,7,3,2,2,1,1] (.node [8,8,7,6,4,3,1,1,1] (.node [8,8,7,6,3,3,1,1,1,1] (.node [8,8,7,6,3,2,2,1,1,1] (.node [8,8,7,6,2,2,2,2,2] .empty .empty) (.node [8,8,7,6,3,2,2,2,1] .empty .empty)) (.node [8,8,7,6,4,2,1,1,1,1] (.node [8,8,7,6,3,3,2,1,1] .empty .empty) (.node [8,8,7,6,4,2,2,1,1] .empty .empty))) (.node [8,8,7,7,2,2,2,1,1,1] (.node [8,8,7,6,5,2,1,1,1] (.node [8,8,7,6,5,1,1,1,1,1] .empty .empty) (.node [8,8,7,6,6,1,1,1,1] .empty .empty)) (.node [8,8,7,7,3,2,1,1,1,1] (.node [8,8,7,7,2,2,2,2,1] .empty .empty) .empty))) (.node [8,8,8,3,3,3,2,2,1,1] (.node [8,8,7,7,5,1,1,1,1] (.node [8,8,7,7,4,1,1,1,1,1] (.node [8,8,7,7,3,3,1,1,1] .empty .empty) (.node [8,8,7,7,4,2,1,1,1] .empty .empty)) (.node [8,8,8,3,3,2,2,2,2,1] (.node [8,8,8,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [8,8,8,3,3,3,3,3] (.node [8,8,8,3,3,3,3,1,1,1] (.node [8,8,8,3,3,3,2,2,2] .empty .empty) (.node [8,8,8,3,3,3,3,2,1] .empty .empty)) (.node [8,8,8,4,3,2,2,2,1,1] (.node [8,8,8,4,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree39_23 : RowTree := (.node [8,8,8,5,4,2,1,1,1,1] (.node [8,8,8,4,4,4,1,1,1] (.node [8,8,8,4,4,2,2,1,1,1] (.node [8,8,8,4,3,3,2,2,1] (.node [8,8,8,4,3,3,2,1,1,1] .empty .empty) (.node [8,8,8,4,3,3,3,1,1] .empty .empty)) (.node [8,8,8,4,4,3,1,1,1,1] (.node [8,8,8,4,4,2,2,2,1] .empty .empty) (.node [8,8,8,4,4,3,2,1,1] .empty .empty))) (.node [8,8,8,5,3,2,2,2,1] (.node [8,8,8,5,2,2,2,2,2] (.node [8,8,8,5,2,2,2,2,1,1] .empty .empty) (.node [8,8,8,5,3,2,2,1,1,1] .empty .empty)) (.node [8,8,8,5,3,3,2,1,1] (.node [8,8,8,5,3,3,1,1,1,1] .empty .empty) .empty))) (.node [8,8,8,6,3,2,1,1,1,1] (.node [8,8,8,5,5,2,1,1,1] (.node [8,8,8,5,4,3,1,1,1] (.node [8,8,8,5,4,2,2,1,1] .empty .empty) (.node [8,8,8,5,5,1,1,1,1,1] .empty .empty)) (.node [8,8,8,6,2,2,2,2,1] (.node [8,8,8,6,2,2,2,1,1,1] .empty .empty) .empty)) (.node [8,8,8,6,4,2,1,1,1] (.node [8,8,8,6,3,3,1,1,1] (.node [8,8,8,6,3,2,2,1,1] .empty .empty) (.node [8,8,8,6,4,1,1,1,1,1] .empty .empty)) (.node [8,8,8,7,2,2,1,1,1,1] (.node [8,8,8,6,5,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_24 : RowTree := (.node [8,8,8,4,3,2,2,2,2] degreeTree39_22 degreeTree39_23)

def degreeTree39_25 : RowTree := (.node [9,5,5,4,4,4,4,3,1] (.node [9,4,4,4,4,4,4,4,2] (.node [8,8,8,8,2,1,1,1,1,1] (.node [8,8,8,7,3,2,1,1,1] (.node [8,8,8,7,3,1,1,1,1,1] .empty .empty) (.node [8,8,8,7,4,1,1,1,1] .empty .empty)) (.node [8,8,8,8,3,1,1,1,1] (.node [8,8,8,8,2,2,1,1,1] .empty .empty) (.node [9,4,4,4,4,4,4,3,3] .empty .empty))) (.node [9,5,5,4,4,3,3,3,3] (.node [9,5,4,4,4,4,4,3,2] (.node [9,5,4,4,4,4,3,3,3] .empty .empty) (.node [9,5,4,4,4,4,4,4,1] .empty .empty)) (.node [9,5,5,4,4,4,4,2,2] (.node [9,5,5,4,4,4,3,3,2] .empty .empty) .empty))) (.node [9,5,5,5,5,3,3,3,1] (.node [9,5,5,5,4,4,3,3,1] (.node [9,5,5,5,4,3,3,3,2] (.node [9,5,5,5,3,3,3,3,3] .empty .empty) (.node [9,5,5,5,4,4,3,2,2] .empty .empty)) (.node [9,5,5,5,5,3,3,2,2] (.node [9,5,5,5,4,4,4,2,1] .empty .empty) .empty)) (.node [9,5,5,5,5,5,2,2,1] (.node [9,5,5,5,5,4,3,2,1] (.node [9,5,5,5,5,4,2,2,2] .empty .empty) (.node [9,5,5,5,5,4,4,1,1] .empty .empty)) (.node [9,6,4,4,4,3,3,3,3] (.node [9,5,5,5,5,5,3,1,1] .empty .empty) .empty))))

def degreeTree39_26 : RowTree := (.node [9,6,5,5,5,3,3,2,1] (.node [9,6,5,5,3,3,3,3,2] (.node [9,6,5,4,4,3,3,3,2] (.node [9,6,4,4,4,4,4,3,1] (.node [9,6,4,4,4,4,4,2,2] .empty .empty) (.node [9,6,5,4,3,3,3,3,3] .empty .empty)) (.node [9,6,5,4,4,4,3,3,1] (.node [9,6,5,4,4,4,3,2,2] .empty .empty) (.node [9,6,5,4,4,4,4,2,1] .empty .empty))) (.node [9,6,5,5,4,4,3,2,1] (.node [9,6,5,5,4,3,3,3,1] (.node [9,6,5,5,4,3,3,2,2] .empty .empty) (.node [9,6,5,5,4,4,2,2,2] .empty .empty)) (.node [9,6,5,5,5,3,2,2,2] (.node [9,6,5,5,4,4,4,1,1] .empty .empty) .empty))) (.node [9,6,6,4,4,3,3,3,1] (.node [9,6,6,3,3,3,3,3,3] (.node [9,6,5,5,5,4,3,1,1] (.node [9,6,5,5,5,4,2,2,1] .empty .empty) (.node [9,6,5,5,5,5,2,1,1] .empty .empty)) (.node [9,6,6,4,4,3,3,2,2] (.node [9,6,6,4,3,3,3,3,2] .empty .empty) .empty)) (.node [9,6,6,5,3,3,3,2,2] (.node [9,6,6,4,4,4,3,2,1] (.node [9,6,6,4,4,4,2,2,2] .empty .empty) (.node [9,6,6,4,4,4,4,1,1] .empty .empty)) (.node [9,6,6,5,4,3,2,2,2] (.node [9,6,6,5,3,3,3,3,1] .empty .empty) .empty))))

def degreeTree39_27 : RowTree := (.node [9,6,4,4,4,4,3,3,2] degreeTree39_25 degreeTree39_26)

def degreeTree39_28 : RowTree := (.node [8,8,8,7,2,2,2,1,1] degreeTree39_24 degreeTree39_27)

def degreeTree39_29 : RowTree := (.node [8,8,7,6,2,2,2,2,1,1] degreeTree39_21 degreeTree39_28)

def degreeTree39_30 : RowTree := (.node [8,7,7,7,6,1,1,1,1] degreeTree39_14 degreeTree39_29)

def degreeTree39_31 : RowTree := (.node [9,6,6,6,5,3,2,1,1] (.node [9,6,6,6,3,3,2,2,2] (.node [9,6,6,5,5,3,2,2,1] (.node [9,6,6,5,4,4,3,1,1] (.node [9,6,6,5,4,4,2,2,1] .empty .empty) (.node [9,6,6,5,5,2,2,2,2] .empty .empty)) (.node [9,6,6,5,5,4,2,1,1] (.node [9,6,6,5,5,3,3,1,1] .empty .empty) (.node [9,6,6,5,5,5,1,1,1] .empty .empty))) (.node [9,6,6,6,4,3,3,1,1] (.node [9,6,6,6,4,2,2,2,2] (.node [9,6,6,6,3,3,3,2,1] .empty .empty) (.node [9,6,6,6,4,3,2,2,1] .empty .empty)) (.node [9,6,6,6,5,2,2,2,1] (.node [9,6,6,6,4,4,2,1,1] .empty .empty) .empty))) (.node [9,7,4,4,4,4,3,3,1] (.node [9,6,6,6,6,2,2,1,1] (.node [9,6,6,6,6,1,1,1,1,1,1] (.node [9,6,6,6,5,4,1,1,1] .empty .empty) (.node [9,6,6,6,6,2,1,1,1,1] .empty .empty)) (.node [9,7,4,4,4,3,3,3,2] (.node [9,7,4,4,3,3,3,3,3] .empty .empty) (.node [9,7,4,4,4,4,3,2,2] .empty .empty))) (.node [9,7,5,4,4,3,3,2,2] (.node [9,7,5,3,3,3,3,3,3] (.node [9,7,4,4,4,4,4,2,1] .empty .empty) (.node [9,7,5,4,3,3,3,3,2] .empty .empty)) (.node [9,7,5,4,4,4,2,2,2] (.node [9,7,5,4,4,3,3,3,1] .empty .empty) .empty))))

def degreeTree39_63 : RowTree := (.node [10,4,4,4,4,4,4,2,1,1,1] (.node [10,4,4,4,4,4,3,1,1,1,1,1,1] (.node [10,4,4,4,4,4,2,1,1,1,1,1,1,1] (.node [10,4,4,4,4,3,3,3,3,1] (.node [10,4,4,4,4,3,3,3,2,2] .empty .empty) (.node [10,4,4,4,4,4,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,4,4,4,4,4,2,2,2,1,1,1] (.node [10,4,4,4,4,4,2,2,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,4,2,2,2,2,1] .empty .empty))) (.node [10,4,4,4,4,4,3,3,1,1,1] (.node [10,4,4,4,4,4,3,2,2,1,1] (.node [10,4,4,4,4,4,3,2,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,4,3,2,2,2] .empty .empty)) (.node [10,4,4,4,4,4,4,1,1,1,1,1] (.node [10,4,4,4,4,4,3,3,2,1] .empty .empty) .empty))) (.node [10,5,2,2,2,2,2,2,2,2,2,2,2,2] (.node [10,5,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] (.node [10,4,4,4,4,4,4,3,1,1] (.node [10,4,4,4,4,4,4,2,2,1] .empty .empty) (.node [10,5,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,2,2,2,2,2,2,2,2,2,2,1,1,1,1] (.node [10,5,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,5,2,2,2,2,2,2,2,2,2,2,2,1,1] .empty .empty))) (.node [10,5,3,2,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,5,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,5,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,3,2,2,2,2,2,2,2,2,2,2,1] (.node [10,5,3,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty) .empty))))

def degreeTree39_64 : RowTree := (.node [10,5,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,3,2,2,2,2,2,2,2,1,1,1,1] (.node [10,5,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1] (.node [10,5,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,3,3,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [10,5,3,3,2,2,2,2,2,2,2,2,2] (.node [10,5,3,3,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,5,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,5,3,3,3,2,2,2,2,2,2,1,1,1] (.node [10,5,3,3,3,2,2,2,2,1,1,1,1,1,1,1] (.node [10,5,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,3,3,3,2,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,5,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,3,3,2,2,2,2,2,2,2,1] .empty .empty) .empty))) (.node [10,5,3,3,3,3,3,2,1,1,1,1,1,1,1] (.node [10,5,3,3,3,3,2,2,2,2,2,1,1] (.node [10,5,3,3,3,3,2,2,2,1,1,1,1,1,1] (.node [10,5,3,3,3,3,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,3,3,3,3,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,5,3,3,3,3,3,1,1,1,1,1,1,1,1,1] (.node [10,5,3,3,3,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [10,5,3,3,3,3,3,3,1,1,1,1,1,1] (.node [10,5,3,3,3,3,3,2,2,2,1,1,1] (.node [10,5,3,3,3,3,3,2,2,1,1,1,1,1] .empty .empty) (.node [10,5,3,3,3,3,3,2,2,2,2,1] .empty .empty)) (.node [10,5,3,3,3,3,3,3,2,2,1,1] (.node [10,5,3,3,3,3,3,3,2,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_65 : RowTree := (.node [10,5,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree39_63 degreeTree39_64)

def degreeTree39_66 : RowTree := (.node [10,5,4,3,2,2,2,2,2,2,1,1,1,1,1] (.node [10,5,4,2,2,2,2,2,2,2,2,1,1,1,1] (.node [10,5,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,3,3,3,3,3,3,2,1] (.node [10,5,3,3,3,3,3,3,3,1,1,1] .empty .empty) (.node [10,5,3,3,3,3,3,3,3,3] .empty .empty)) (.node [10,5,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1] (.node [10,5,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,2,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [10,5,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,2,2,2,2,2,2,2,2,2,2] (.node [10,5,4,2,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,5,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,4,3,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,5,4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,4,3,3,2,2,2,2,1,1,1,1,1,1] (.node [10,5,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,3,2,2,2,2,2,2,2,2,1] (.node [10,5,4,3,2,2,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,5,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,4,3,3,2,2,2,1,1,1,1,1,1,1,1] (.node [10,5,4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,3,3,2,2,2,2,2,2,1,1] (.node [10,5,4,3,3,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,5,4,3,3,2,2,2,2,2,2,2] .empty .empty)) (.node [10,5,4,3,3,3,2,2,1,1,1,1,1,1,1] (.node [10,5,4,3,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_67 : RowTree := (.node [10,5,4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,3,3,3,3,3,1,1,1,1,1] (.node [10,5,4,3,3,3,3,2,1,1,1,1,1,1] (.node [10,5,4,3,3,3,2,2,2,2,2,1] (.node [10,5,4,3,3,3,2,2,2,2,1,1,1] .empty .empty) (.node [10,5,4,3,3,3,3,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,4,3,3,3,3,2,2,2,1,1] (.node [10,5,4,3,3,3,3,2,2,1,1,1,1] .empty .empty) (.node [10,5,4,3,3,3,3,2,2,2,2] .empty .empty))) (.node [10,5,4,3,3,3,3,3,3,2] (.node [10,5,4,3,3,3,3,3,2,2,1] (.node [10,5,4,3,3,3,3,3,2,1,1,1] .empty .empty) (.node [10,5,4,3,3,3,3,3,3,1,1] .empty .empty)) (.node [10,5,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,2,2,2,2,2,2,2,1,1] (.node [10,5,4,4,2,2,2,2,2,1,1,1,1,1,1] (.node [10,5,4,4,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,4,2,2,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,5,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,2,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [10,5,4,4,3,2,2,2,2,2,1,1,1] (.node [10,5,4,4,3,2,2,2,1,1,1,1,1,1,1] (.node [10,5,4,4,3,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,4,3,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,5,4,4,3,3,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,3,2,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree39_68 : RowTree := (.node [10,5,4,3,3,3,2,2,2,1,1,1,1,1] degreeTree39_66 degreeTree39_67)

def degreeTree39_69 : RowTree := (.node [10,5,3,3,3,3,3,3,2,2,2] degreeTree39_65 degreeTree39_68)

def degreeTree39_70 : RowTree := (.node [10,5,4,4,4,2,2,1,1,1,1,1,1,1,1] (.node [10,5,4,4,3,3,3,2,2,2,1] (.node [10,5,4,4,3,3,2,2,2,2,2] (.node [10,5,4,4,3,3,2,2,2,1,1,1,1] (.node [10,5,4,4,3,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,4,3,3,2,2,2,2,1,1] .empty .empty)) (.node [10,5,4,4,3,3,3,2,1,1,1,1,1] (.node [10,5,4,4,3,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,4,3,3,3,2,2,1,1,1] .empty .empty))) (.node [10,5,4,4,3,3,3,3,3,1] (.node [10,5,4,4,3,3,3,3,2,1,1] (.node [10,5,4,4,3,3,3,3,1,1,1,1] .empty .empty) (.node [10,5,4,4,3,3,3,3,2,2] .empty .empty)) (.node [10,5,4,4,4,2,1,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,4,4,4,3,2,2,1,1,1,1,1] (.node [10,5,4,4,4,2,2,2,2,2,2] (.node [10,5,4,4,4,2,2,2,2,1,1,1,1] (.node [10,5,4,4,4,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,5,4,4,4,2,2,2,2,2,1,1] .empty .empty)) (.node [10,5,4,4,4,3,2,1,1,1,1,1,1,1] (.node [10,5,4,4,4,3,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,4,4,4,3,3,2,1,1,1,1] (.node [10,5,4,4,4,3,2,2,2,2,1] (.node [10,5,4,4,4,3,2,2,2,1,1,1] .empty .empty) (.node [10,5,4,4,4,3,3,1,1,1,1,1,1] .empty .empty)) (.node [10,5,4,4,4,3,3,2,2,2] (.node [10,5,4,4,4,3,3,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_71 : RowTree := (.node [10,5,5,2,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,5,4,4,4,4,3,2,1,1,1] (.node [10,5,4,4,4,4,2,2,1,1,1,1] (.node [10,5,4,4,4,4,1,1,1,1,1,1,1,1] (.node [10,5,4,4,4,3,3,3,2,1] .empty .empty) (.node [10,5,4,4,4,4,2,1,1,1,1,1,1] .empty .empty)) (.node [10,5,4,4,4,4,2,2,2,2] (.node [10,5,4,4,4,4,2,2,2,1,1] .empty .empty) (.node [10,5,4,4,4,4,3,1,1,1,1,1] .empty .empty))) (.node [10,5,4,4,4,4,4,2,1,1] (.node [10,5,4,4,4,4,3,3,1,1] (.node [10,5,4,4,4,4,3,2,2,1] .empty .empty) (.node [10,5,4,4,4,4,4,1,1,1,1] .empty .empty)) (.node [10,5,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,2,2,2,2,2,2,2,2,2,1] (.node [10,5,5,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,5,5,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,5,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,5,3,2,2,2,2,2,2,2,1,1] (.node [10,5,5,3,2,2,2,2,2,1,1,1,1,1,1] (.node [10,5,5,3,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,3,2,2,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,5,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,3,2,2,2,2,2,2,2,2] .empty .empty) .empty))))

def degreeTree39_72 : RowTree := (.node [10,5,4,4,4,3,3,3,1,1,1] degreeTree39_70 degreeTree39_71)

def degreeTree39_73 : RowTree := (.node [10,5,5,3,3,3,3,2,2,2,1] (.node [10,5,5,3,3,3,2,2,1,1,1,1,1,1] (.node [10,5,5,3,3,2,2,2,2,2,1,1,1] (.node [10,5,5,3,3,2,2,2,1,1,1,1,1,1,1] (.node [10,5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,3,3,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,5,5,3,3,3,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,3,3,2,2,2,2,2,2,1] .empty .empty) (.node [10,5,5,3,3,3,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,5,5,3,3,3,3,1,1,1,1,1,1,1] (.node [10,5,5,3,3,3,2,2,2,2,1,1] (.node [10,5,5,3,3,3,2,2,2,1,1,1,1] .empty .empty) (.node [10,5,5,3,3,3,2,2,2,2,2] .empty .empty)) (.node [10,5,5,3,3,3,3,2,2,1,1,1] (.node [10,5,5,3,3,3,3,2,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,3,3,3,3,3,3,1] (.node [10,5,5,3,3,3,3,3,2,1,1] (.node [10,5,5,3,3,3,3,3,1,1,1,1] .empty .empty) (.node [10,5,5,3,3,3,3,3,2,2] .empty .empty)) (.node [10,5,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,5,4,2,2,2,2,2,2,1,1,1] (.node [10,5,5,4,2,2,2,2,1,1,1,1,1,1,1] (.node [10,5,5,4,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,4,2,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,5,5,4,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,4,2,2,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree39_74 : RowTree := (.node [10,5,5,4,3,3,3,3,1,1,1] (.node [10,5,5,4,3,3,2,2,1,1,1,1,1] (.node [10,5,5,4,3,2,2,2,2,2,1,1] (.node [10,5,5,4,3,2,2,2,1,1,1,1,1,1] (.node [10,5,5,4,3,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,4,3,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,5,5,4,3,3,1,1,1,1,1,1,1,1,1] (.node [10,5,5,4,3,2,2,2,2,2,2] .empty .empty) (.node [10,5,5,4,3,3,2,1,1,1,1,1,1,1] .empty .empty))) (.node [10,5,5,4,3,3,3,2,1,1,1,1] (.node [10,5,5,4,3,3,2,2,2,2,1] (.node [10,5,5,4,3,3,2,2,2,1,1,1] .empty .empty) (.node [10,5,5,4,3,3,3,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,4,3,3,3,2,2,2] (.node [10,5,5,4,3,3,3,2,2,1,1] .empty .empty) .empty))) (.node [10,5,5,4,4,2,2,2,2,2,1] (.node [10,5,5,4,4,2,2,1,1,1,1,1,1,1] (.node [10,5,5,4,4,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,4,3,3,3,3,2,1] .empty .empty) (.node [10,5,5,4,4,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,4,4,2,2,2,2,1,1,1] (.node [10,5,5,4,4,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,5,4,4,3,2,2,2,1,1] (.node [10,5,5,4,4,3,2,1,1,1,1,1,1] (.node [10,5,5,4,4,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,4,4,3,2,2,1,1,1,1] .empty .empty)) (.node [10,5,5,4,4,3,3,1,1,1,1,1] (.node [10,5,5,4,4,3,2,2,2,2] .empty .empty) .empty))))

def degreeTree39_75 : RowTree := (.node [10,5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] degreeTree39_73 degreeTree39_74)

def degreeTree39_76 : RowTree := (.node [10,5,5,3,3,2,1,1,1,1,1,1,1,1,1,1,1] degreeTree39_72 degreeTree39_75)

def degreeTree39_77 : RowTree := (.node [10,5,4,4,3,3,2,1,1,1,1,1,1,1,1] degreeTree39_69 degreeTree39_76)

def degreeTree39_78 : RowTree := (.node [10,5,5,5,2,2,2,2,2,1,1,1,1] (.node [10,5,5,4,4,4,3,2,1,1] (.node [10,5,5,4,4,4,2,1,1,1,1,1] (.node [10,5,5,4,4,3,3,3,1,1] (.node [10,5,5,4,4,3,3,2,2,1] .empty .empty) (.node [10,5,5,4,4,4,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,4,4,4,2,2,2,1] (.node [10,5,5,4,4,4,2,2,1,1,1] .empty .empty) (.node [10,5,5,4,4,4,3,1,1,1,1] .empty .empty))) (.node [10,5,5,5,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,4,4,4,4,1,1,1] .empty .empty) (.node [10,5,5,5,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,5,2,2,2,2,1,1,1,1,1,1] (.node [10,5,5,5,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,5,5,5,3,2,2,2,2,1,1,1] (.node [10,5,5,5,3,2,1,1,1,1,1,1,1,1,1] (.node [10,5,5,5,2,2,2,2,2,2,2] (.node [10,5,5,5,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,5,5,5,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,5,3,2,2,2,1,1,1,1,1] (.node [10,5,5,5,3,2,2,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,5,5,3,3,2,2,1,1,1,1] (.node [10,5,5,5,3,3,1,1,1,1,1,1,1,1] (.node [10,5,5,5,3,2,2,2,2,2,1] .empty .empty) (.node [10,5,5,5,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,5,3,3,2,2,2,2] (.node [10,5,5,5,3,3,2,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_79 : RowTree := (.node [10,5,5,5,4,3,3,2,1,1] (.node [10,5,5,5,4,2,2,2,2,1,1] (.node [10,5,5,5,4,1,1,1,1,1,1,1,1,1,1] (.node [10,5,5,5,3,3,3,2,2,1] (.node [10,5,5,5,3,3,3,2,1,1,1] .empty .empty) (.node [10,5,5,5,3,3,3,3,1,1] .empty .empty)) (.node [10,5,5,5,4,2,2,1,1,1,1,1,1] (.node [10,5,5,5,4,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,5,4,2,2,2,1,1,1,1] .empty .empty))) (.node [10,5,5,5,4,3,2,2,1,1,1] (.node [10,5,5,5,4,3,1,1,1,1,1,1,1] (.node [10,5,5,5,4,2,2,2,2,2] .empty .empty) (.node [10,5,5,5,4,3,2,1,1,1,1,1] .empty .empty)) (.node [10,5,5,5,4,3,3,1,1,1,1] (.node [10,5,5,5,4,3,2,2,2,1] .empty .empty) .empty))) (.node [10,5,5,5,5,2,2,1,1,1,1,1] (.node [10,5,5,5,4,4,3,1,1,1] (.node [10,5,5,5,4,4,2,1,1,1,1] (.node [10,5,5,5,4,4,1,1,1,1,1,1] .empty .empty) (.node [10,5,5,5,4,4,2,2,1,1] .empty .empty)) (.node [10,5,5,5,5,2,1,1,1,1,1,1,1] (.node [10,5,5,5,5,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,5,5,5,5,3,2,1,1,1,1] (.node [10,5,5,5,5,2,2,2,2,1] (.node [10,5,5,5,5,2,2,2,1,1,1] .empty .empty) (.node [10,5,5,5,5,3,1,1,1,1,1,1] .empty .empty)) (.node [10,5,5,5,5,3,3,1,1,1] (.node [10,5,5,5,5,3,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_80 : RowTree := (.node [10,5,5,5,3,3,3,1,1,1,1,1] degreeTree39_78 degreeTree39_79)

def degreeTree39_81 : RowTree := (.node [10,6,3,2,2,2,2,2,2,2,2,2,2] (.node [10,6,2,2,2,2,2,2,2,2,2,2,2,1] (.node [10,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,5,5,5,5,5,1,1,1,1] (.node [10,5,5,5,5,4,2,1,1,1] .empty .empty) (.node [10,6,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,2,2,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,6,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,2,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty))) (.node [10,6,3,2,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,6,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,6,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,3,2,2,2,2,2,2,2,2,2,1,1] (.node [10,6,3,2,2,2,2,2,2,2,2,1,1,1,1] .empty .empty) .empty))) (.node [10,6,3,3,2,2,2,2,2,2,2,2,1] (.node [10,6,3,3,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,6,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,3,3,2,2,2,2,2,2,2,1,1,1] (.node [10,6,3,3,2,2,2,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,3,3,3,2,2,2,1,1,1,1,1,1,1,1] (.node [10,6,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,3,3,3,2,2,2,2,2,1,1,1,1] (.node [10,6,3,3,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_82 : RowTree := (.node [10,6,3,3,3,3,3,3,2,2,1] (.node [10,6,3,3,3,3,3,1,1,1,1,1,1,1,1] (.node [10,6,3,3,3,3,2,2,1,1,1,1,1,1,1] (.node [10,6,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,3,3,3,2,2,2,2,2,2,2] .empty .empty) (.node [10,6,3,3,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,3,3,3,3,2,2,2,2,1,1,1] (.node [10,6,3,3,3,3,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,6,3,3,3,3,2,2,2,2,2,1] .empty .empty))) (.node [10,6,3,3,3,3,3,2,2,2,2] (.node [10,6,3,3,3,3,3,2,2,1,1,1,1] (.node [10,6,3,3,3,3,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,6,3,3,3,3,3,2,2,2,1,1] .empty .empty)) (.node [10,6,3,3,3,3,3,3,2,1,1,1] (.node [10,6,3,3,3,3,3,3,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,4,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,6,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,3,3,3,3,3,3,3,2] (.node [10,6,3,3,3,3,3,3,3,1,1] .empty .empty) (.node [10,6,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,4,2,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,6,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,2,2,2,2,2,2,2,2,2,1] (.node [10,6,4,2,2,2,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,6,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,4,3,2,2,2,2,1,1,1,1,1,1,1,1] (.node [10,6,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_83 : RowTree := (.node [10,6,3,3,3,2,2,2,2,2,2,1,1] degreeTree39_81 degreeTree39_82)

def degreeTree39_84 : RowTree := (.node [10,5,5,5,5,4,1,1,1,1,1] degreeTree39_80 degreeTree39_83)

def degreeTree39_85 : RowTree := (.node [10,6,4,3,3,3,2,2,2,2,1,1] (.node [10,6,4,3,3,2,2,2,2,1,1,1,1,1] (.node [10,6,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,3,2,2,2,2,2,2,2,1,1] (.node [10,6,4,3,2,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,6,4,3,2,2,2,2,2,2,2,2] .empty .empty)) (.node [10,6,4,3,3,2,2,1,1,1,1,1,1,1,1,1] (.node [10,6,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,4,3,3,2,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [10,6,4,3,3,3,2,1,1,1,1,1,1,1,1] (.node [10,6,4,3,3,2,2,2,2,2,2,1] (.node [10,6,4,3,3,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,6,4,3,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,4,3,3,3,2,2,2,1,1,1,1] (.node [10,6,4,3,3,3,2,2,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,4,3,3,3,3,3,2,1,1] (.node [10,6,4,3,3,3,3,2,2,1,1,1] (.node [10,6,4,3,3,3,3,1,1,1,1,1,1,1] (.node [10,6,4,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,6,4,3,3,3,3,2,1,1,1,1,1] .empty .empty)) (.node [10,6,4,3,3,3,3,3,1,1,1,1] (.node [10,6,4,3,3,3,3,2,2,2,1] .empty .empty) .empty)) (.node [10,6,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,3,3,3,3,3,3,1] (.node [10,6,4,3,3,3,3,3,2,2] .empty .empty) (.node [10,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,4,4,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,6,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_86 : RowTree := (.node [10,6,4,4,3,3,2,2,2,2,1] (.node [10,6,4,4,3,2,2,2,2,1,1,1,1] (.node [10,6,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,4,2,2,2,2,2,2,1,1,1] (.node [10,6,4,4,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,6,4,4,2,2,2,2,2,2,2,1] .empty .empty)) (.node [10,6,4,4,3,2,2,1,1,1,1,1,1,1,1] (.node [10,6,4,4,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,4,4,3,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [10,6,4,4,3,3,2,1,1,1,1,1,1,1] (.node [10,6,4,4,3,2,2,2,2,2,2] (.node [10,6,4,4,3,2,2,2,2,2,1,1] .empty .empty) (.node [10,6,4,4,3,3,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,4,4,3,3,2,2,2,1,1,1] (.node [10,6,4,4,3,3,2,2,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,4,4,4,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,4,3,3,3,2,2,2] (.node [10,6,4,4,3,3,3,2,1,1,1,1] (.node [10,6,4,4,3,3,3,1,1,1,1,1,1] .empty .empty) (.node [10,6,4,4,3,3,3,2,2,1,1] .empty .empty)) (.node [10,6,4,4,3,3,3,3,2,1] (.node [10,6,4,4,3,3,3,3,1,1,1] .empty .empty) .empty)) (.node [10,6,4,4,4,2,2,2,2,1,1,1] (.node [10,6,4,4,4,2,2,1,1,1,1,1,1,1] (.node [10,6,4,4,4,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,4,4,4,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,6,4,4,4,3,1,1,1,1,1,1,1,1] (.node [10,6,4,4,4,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree39_87 : RowTree := (.node [10,6,4,4,2,2,2,2,1,1,1,1,1,1,1] degreeTree39_85 degreeTree39_86)

def degreeTree39_88 : RowTree := (.node [10,6,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,4,4,4,4,1,1,1,1,1,1,1] (.node [10,6,4,4,4,3,3,1,1,1,1,1] (.node [10,6,4,4,4,3,2,2,2,1,1] (.node [10,6,4,4,4,3,2,2,1,1,1,1] .empty .empty) (.node [10,6,4,4,4,3,2,2,2,2] .empty .empty)) (.node [10,6,4,4,4,3,3,2,2,1] (.node [10,6,4,4,4,3,3,2,1,1,1] .empty .empty) (.node [10,6,4,4,4,3,3,3,1,1] .empty .empty))) (.node [10,6,4,4,4,4,3,1,1,1,1] (.node [10,6,4,4,4,4,2,2,1,1,1] (.node [10,6,4,4,4,4,2,1,1,1,1,1] .empty .empty) (.node [10,6,4,4,4,4,2,2,2,1] .empty .empty)) (.node [10,6,4,4,4,4,4,1,1,1] (.node [10,6,4,4,4,4,3,2,1,1] .empty .empty) .empty))) (.node [10,6,5,2,2,2,2,2,2,2,2,2] (.node [10,6,5,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,6,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,5,2,2,2,2,2,2,2,2,1,1] (.node [10,6,5,2,2,2,2,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [10,6,5,3,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,6,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,5,3,2,2,2,2,2,1,1,1,1,1] (.node [10,6,5,3,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_89 : RowTree := (.node [10,6,5,3,3,3,3,2,1,1,1,1] (.node [10,6,5,3,3,2,2,2,2,2,2] (.node [10,6,5,3,3,2,2,1,1,1,1,1,1,1,1] (.node [10,6,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,3,2,2,2,2,2,2,2,1] .empty .empty) (.node [10,6,5,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,5,3,3,2,2,2,2,1,1,1,1] (.node [10,6,5,3,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,3,3,2,2,2,2,2,1,1] .empty .empty))) (.node [10,6,5,3,3,3,2,2,2,1,1,1] (.node [10,6,5,3,3,3,2,1,1,1,1,1,1,1] (.node [10,6,5,3,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,3,3,3,2,2,1,1,1,1,1] .empty .empty)) (.node [10,6,5,3,3,3,3,1,1,1,1,1,1] (.node [10,6,5,3,3,3,2,2,2,2,1] .empty .empty) .empty))) (.node [10,6,5,4,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,3,3,3,3,3,2,1] (.node [10,6,5,3,3,3,3,2,2,2] (.node [10,6,5,3,3,3,3,2,2,1,1] .empty .empty) (.node [10,6,5,3,3,3,3,3,1,1,1] .empty .empty)) (.node [10,6,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,5,4,2,2,2,2,2,2,1,1] (.node [10,6,5,4,2,2,2,2,1,1,1,1,1,1] (.node [10,6,5,4,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,4,2,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,6,5,4,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,4,2,2,2,2,2,2,2] .empty .empty) .empty))))

def degreeTree39_90 : RowTree := (.node [10,6,5,3,2,2,2,2,2,2,1,1,1] degreeTree39_88 degreeTree39_89)

def degreeTree39_91 : RowTree := (.node [10,6,4,4,4,3,2,1,1,1,1,1,1] degreeTree39_87 degreeTree39_90)

def degreeTree39_92 : RowTree := (.node [10,6,4,3,2,2,2,2,2,1,1,1,1,1,1] degreeTree39_84 degreeTree39_91)

def degreeTree39_93 : RowTree := (.node [10,5,5,4,4,3,3,2,1,1,1] degreeTree39_77 degreeTree39_92)

def degreeTree39_94 : RowTree := (.node [10,6,5,4,4,2,1,1,1,1,1,1,1,1] (.node [10,6,5,4,3,3,2,2,2,1,1] (.node [10,6,5,4,3,2,2,2,2,2,1] (.node [10,6,5,4,3,2,2,2,1,1,1,1,1] (.node [10,6,5,4,3,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,4,3,2,2,2,2,1,1,1] .empty .empty)) (.node [10,6,5,4,3,3,2,1,1,1,1,1,1] (.node [10,6,5,4,3,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,4,3,3,2,2,1,1,1,1] .empty .empty))) (.node [10,6,5,4,3,3,3,2,2,1] (.node [10,6,5,4,3,3,3,1,1,1,1,1] (.node [10,6,5,4,3,3,2,2,2,2] .empty .empty) (.node [10,6,5,4,3,3,3,2,1,1,1] .empty .empty)) (.node [10,6,5,4,4,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,4,3,3,3,3,1,1] .empty .empty) .empty))) (.node [10,6,5,4,4,3,2,2,2,1] (.node [10,6,5,4,4,2,2,2,2,2] (.node [10,6,5,4,4,2,2,2,1,1,1,1] (.node [10,6,5,4,4,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,4,4,2,2,2,2,1,1] .empty .empty)) (.node [10,6,5,4,4,3,2,1,1,1,1,1] (.node [10,6,5,4,4,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,4,4,3,2,2,1,1,1] .empty .empty))) (.node [10,6,5,4,4,4,2,1,1,1,1] (.node [10,6,5,4,4,3,3,2,1,1] (.node [10,6,5,4,4,3,3,1,1,1,1] .empty .empty) (.node [10,6,5,4,4,4,1,1,1,1,1,1] .empty .empty)) (.node [10,6,5,4,4,4,3,1,1,1] (.node [10,6,5,4,4,4,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_95 : RowTree := (.node [10,6,5,5,3,3,2,2,1,1,1] (.node [10,6,5,5,3,2,1,1,1,1,1,1,1,1] (.node [10,6,5,5,2,2,2,2,1,1,1,1,1] (.node [10,6,5,5,2,2,1,1,1,1,1,1,1,1,1] (.node [10,6,5,5,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,5,2,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,5,5,2,2,2,2,2,2,1] (.node [10,6,5,5,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,6,5,5,3,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,6,5,5,3,2,2,2,2,2] (.node [10,6,5,5,3,2,2,2,1,1,1,1] (.node [10,6,5,5,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,5,3,2,2,2,2,1,1] .empty .empty)) (.node [10,6,5,5,3,3,2,1,1,1,1,1] (.node [10,6,5,5,3,3,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,5,5,4,2,2,2,1,1,1] (.node [10,6,5,5,4,1,1,1,1,1,1,1,1,1] (.node [10,6,5,5,3,3,3,1,1,1,1] (.node [10,6,5,5,3,3,2,2,2,1] .empty .empty) (.node [10,6,5,5,3,3,3,2,1,1] .empty .empty)) (.node [10,6,5,5,4,2,2,1,1,1,1,1] (.node [10,6,5,5,4,2,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,5,5,4,3,2,2,1,1] (.node [10,6,5,5,4,3,1,1,1,1,1,1] (.node [10,6,5,5,4,2,2,2,2,1] .empty .empty) (.node [10,6,5,5,4,3,2,1,1,1,1] .empty .empty)) (.node [10,6,5,5,4,4,1,1,1,1,1] (.node [10,6,5,5,4,3,3,1,1,1] .empty .empty) .empty))))

def degreeTree39_96 : RowTree := (.node [10,6,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree39_94 degreeTree39_95)

def degreeTree39_97 : RowTree := (.node [10,6,6,2,2,2,2,2,2,2,2,1] (.node [10,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,5,5,5,2,2,2,1,1] (.node [10,6,5,5,5,2,1,1,1,1,1,1] (.node [10,6,5,5,5,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,5,5,5,2,2,1,1,1,1] .empty .empty)) (.node [10,6,5,5,5,3,2,1,1,1] (.node [10,6,5,5,5,3,1,1,1,1,1] .empty .empty) (.node [10,6,5,5,5,4,1,1,1,1] .empty .empty))) (.node [10,6,6,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,2,2,2,2,2,2,2,1,1,1] (.node [10,6,6,2,2,2,2,2,2,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,6,3,2,2,2,2,2,2,1,1] (.node [10,6,6,3,2,2,2,1,1,1,1,1,1,1,1] (.node [10,6,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,3,2,2,2,2,2,1,1,1,1] (.node [10,6,6,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,6,3,3,2,2,1,1,1,1,1,1,1] (.node [10,6,6,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,3,2,2,2,2,2,2,2] .empty .empty) (.node [10,6,6,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,3,3,2,2,2,2,1,1,1] (.node [10,6,6,3,3,2,2,2,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_98 : RowTree := (.node [10,6,6,4,2,2,2,2,2,1,1,1] (.node [10,6,6,3,3,3,3,2,2,1] (.node [10,6,6,3,3,3,2,2,2,1,1] (.node [10,6,6,3,3,3,2,1,1,1,1,1,1] (.node [10,6,6,3,3,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,3,3,3,2,2,1,1,1,1] .empty .empty)) (.node [10,6,6,3,3,3,3,1,1,1,1,1] (.node [10,6,6,3,3,3,2,2,2,2] .empty .empty) (.node [10,6,6,3,3,3,3,2,1,1,1] .empty .empty))) (.node [10,6,6,4,2,2,1,1,1,1,1,1,1,1,1] (.node [10,6,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,3,3,3,3,3,1,1] .empty .empty) (.node [10,6,6,4,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,4,2,2,2,2,1,1,1,1,1] (.node [10,6,6,4,2,2,2,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,6,4,3,2,2,2,2,2] (.node [10,6,6,4,3,2,2,1,1,1,1,1,1] (.node [10,6,6,4,3,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,4,2,2,2,2,2,2,1] .empty .empty) (.node [10,6,6,4,3,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,4,3,2,2,2,2,1,1] (.node [10,6,6,4,3,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [10,6,6,4,3,3,2,2,2,1] (.node [10,6,6,4,3,3,2,1,1,1,1,1] (.node [10,6,6,4,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,4,3,3,2,2,1,1,1] .empty .empty)) (.node [10,6,6,4,3,3,3,2,1,1] (.node [10,6,6,4,3,3,3,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_99 : RowTree := (.node [10,6,6,3,3,2,2,2,2,2,1] degreeTree39_97 degreeTree39_98)

def degreeTree39_100 : RowTree := (.node [10,6,5,5,4,4,2,1,1,1] degreeTree39_96 degreeTree39_99)

def degreeTree39_101 : RowTree := (.node [10,6,6,5,2,2,2,2,1,1,1,1] (.node [10,6,6,4,4,3,3,1,1,1] (.node [10,6,6,4,4,2,2,2,2,1] (.node [10,6,6,4,4,2,2,1,1,1,1,1] (.node [10,6,6,4,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,4,4,2,2,2,1,1,1] .empty .empty)) (.node [10,6,6,4,4,3,2,1,1,1,1] (.node [10,6,6,4,4,3,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,4,4,3,2,2,1,1] .empty .empty))) (.node [10,6,6,5,2,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,4,4,4,2,1,1,1] (.node [10,6,6,4,4,4,1,1,1,1,1] .empty .empty) (.node [10,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,5,2,2,2,1,1,1,1,1,1] (.node [10,6,6,5,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,6,6,5,3,2,2,2,2,1] (.node [10,6,6,5,3,2,1,1,1,1,1,1,1] (.node [10,6,6,5,2,2,2,2,2,2] (.node [10,6,6,5,2,2,2,2,2,1,1] .empty .empty) (.node [10,6,6,5,3,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,5,3,2,2,2,1,1,1] (.node [10,6,6,5,3,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [10,6,6,5,3,3,3,1,1,1] (.node [10,6,6,5,3,3,2,1,1,1,1] (.node [10,6,6,5,3,3,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,5,3,3,2,2,1,1] .empty .empty)) (.node [10,6,6,5,4,2,1,1,1,1,1,1] (.node [10,6,6,5,4,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_102 : RowTree := (.node [10,6,6,6,3,1,1,1,1,1,1,1,1] (.node [10,6,6,5,5,3,1,1,1,1] (.node [10,6,6,5,4,4,1,1,1,1] (.node [10,6,6,5,4,3,1,1,1,1,1] (.node [10,6,6,5,4,2,2,2,1,1] .empty .empty) (.node [10,6,6,5,4,3,2,1,1,1] .empty .empty)) (.node [10,6,6,5,5,2,1,1,1,1,1] (.node [10,6,6,5,5,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,5,5,2,2,1,1,1] .empty .empty))) (.node [10,6,6,6,2,2,2,1,1,1,1,1] (.node [10,6,6,6,2,1,1,1,1,1,1,1,1,1] (.node [10,6,6,6,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,6,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,6,6,6,2,2,2,2,2,1] (.node [10,6,6,6,2,2,2,2,1,1,1] .empty .empty) .empty))) (.node [10,6,6,6,4,2,1,1,1,1,1] (.node [10,6,6,6,3,3,1,1,1,1,1] (.node [10,6,6,6,3,2,2,1,1,1,1] (.node [10,6,6,6,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,6,6,6,3,2,2,2,1,1] .empty .empty)) (.node [10,6,6,6,4,1,1,1,1,1,1,1] (.node [10,6,6,6,3,3,2,1,1,1] .empty .empty) .empty)) (.node [10,7,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,6,6,6,5,1,1,1,1,1,1] (.node [10,6,6,6,4,2,2,1,1,1] .empty .empty) (.node [10,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,2,2,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,7,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_103 : RowTree := (.node [10,6,6,5,4,2,2,1,1,1,1] degreeTree39_101 degreeTree39_102)

def degreeTree39_104 : RowTree := (.node [10,7,3,3,2,2,2,2,2,2,1,1,1,1] (.node [10,7,3,2,2,2,2,2,2,2,2,1,1,1] (.node [10,7,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,2,2,2,2,2,2,2,2,2,2,2] (.node [10,7,2,2,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,3,2,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,7,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,3,2,2,2,2,2,2,2,1,1,1,1,1] .empty .empty))) (.node [10,7,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,3,2,2,2,2,2,2,2,2,2,1] .empty .empty) (.node [10,7,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,3,3,2,2,2,2,2,1,1,1,1,1,1] (.node [10,7,3,3,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,7,3,3,3,2,2,2,2,1,1,1,1,1] (.node [10,7,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,3,3,2,2,2,2,2,2,2,2] (.node [10,7,3,3,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,7,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,3,3,3,2,2,2,1,1,1,1,1,1,1] (.node [10,7,3,3,3,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,7,3,3,3,3,2,1,1,1,1,1,1,1,1] (.node [10,7,3,3,3,2,2,2,2,2,2,1] (.node [10,7,3,3,3,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,7,3,3,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,3,3,3,3,2,2,2,1,1,1,1] (.node [10,7,3,3,3,3,2,2,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_105 : RowTree := (.node [10,7,4,2,2,2,2,2,2,2,1,1,1,1] (.node [10,7,3,3,3,3,3,3,2,2] (.node [10,7,3,3,3,3,3,2,2,1,1,1] (.node [10,7,3,3,3,3,3,1,1,1,1,1,1,1] (.node [10,7,3,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,7,3,3,3,3,3,2,1,1,1,1,1] .empty .empty)) (.node [10,7,3,3,3,3,3,3,1,1,1,1] (.node [10,7,3,3,3,3,3,2,2,2,1] .empty .empty) (.node [10,7,3,3,3,3,3,3,2,1,1] .empty .empty))) (.node [10,7,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,3,3,3,3,3,3,3,1] .empty .empty) (.node [10,7,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,4,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,7,4,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,7,4,3,2,2,2,2,1,1,1,1,1,1,1] (.node [10,7,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,4,2,2,2,2,2,2,2,2,2] (.node [10,7,4,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,4,3,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,7,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,7,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,4,3,2,2,2,2,2,2,1,1,1] (.node [10,7,4,3,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,7,4,3,2,2,2,2,2,2,2,1] .empty .empty)) (.node [10,7,4,3,3,2,2,1,1,1,1,1,1,1,1] (.node [10,7,4,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_106 : RowTree := (.node [10,7,3,3,3,3,2,2,2,2,1,1] degreeTree39_104 degreeTree39_105)

def degreeTree39_107 : RowTree := (.node [10,7,2,2,2,2,2,2,2,2,2,1,1,1,1] degreeTree39_103 degreeTree39_106)

def degreeTree39_108 : RowTree := (.node [10,6,6,4,4,1,1,1,1,1,1,1,1,1] degreeTree39_100 degreeTree39_107)

def degreeTree39_109 : RowTree := (.node [10,7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,4,3,3,3,2,2,2,2,1] (.node [10,7,4,3,3,3,1,1,1,1,1,1,1,1,1] (.node [10,7,4,3,3,2,2,2,2,2,1,1] (.node [10,7,4,3,3,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,7,4,3,3,2,2,2,2,2,2] .empty .empty)) (.node [10,7,4,3,3,3,2,2,1,1,1,1,1] (.node [10,7,4,3,3,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,3,3,3,2,2,2,1,1,1] .empty .empty))) (.node [10,7,4,3,3,3,3,2,2,2] (.node [10,7,4,3,3,3,3,2,1,1,1,1] (.node [10,7,4,3,3,3,3,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,3,3,3,3,2,2,1,1] .empty .empty)) (.node [10,7,4,3,3,3,3,3,2,1] (.node [10,7,4,3,3,3,3,3,1,1,1] .empty .empty) .empty))) (.node [10,7,4,4,2,2,2,2,2,2,2] (.node [10,7,4,4,2,2,2,2,1,1,1,1,1,1] (.node [10,7,4,4,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,7,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,2,2,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,4,4,2,2,2,2,2,2,1,1] (.node [10,7,4,4,2,2,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [10,7,4,4,3,2,2,2,1,1,1,1,1] (.node [10,7,4,4,3,2,1,1,1,1,1,1,1,1,1] (.node [10,7,4,4,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,3,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,7,4,4,3,2,2,2,2,2,1] (.node [10,7,4,4,3,2,2,2,2,1,1,1] .empty .empty) .empty))))

def degreeTree39_110 : RowTree := (.node [10,7,4,4,4,3,1,1,1,1,1,1,1] (.node [10,7,4,4,3,3,3,3,1,1] (.node [10,7,4,4,3,3,2,2,2,2] (.node [10,7,4,4,3,3,2,2,1,1,1,1] (.node [10,7,4,4,3,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,3,3,2,2,2,1,1] .empty .empty)) (.node [10,7,4,4,3,3,3,2,1,1,1] (.node [10,7,4,4,3,3,3,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,3,3,3,2,2,1] .empty .empty))) (.node [10,7,4,4,4,2,2,2,1,1,1,1] (.node [10,7,4,4,4,2,1,1,1,1,1,1,1,1] (.node [10,7,4,4,4,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,4,2,2,1,1,1,1,1,1] .empty .empty)) (.node [10,7,4,4,4,2,2,2,2,2] (.node [10,7,4,4,4,2,2,2,2,1,1] .empty .empty) .empty))) (.node [10,7,4,4,4,4,2,1,1,1,1] (.node [10,7,4,4,4,3,3,1,1,1,1] (.node [10,7,4,4,4,3,2,2,1,1,1] (.node [10,7,4,4,4,3,2,1,1,1,1,1] .empty .empty) (.node [10,7,4,4,4,3,2,2,2,1] .empty .empty)) (.node [10,7,4,4,4,4,1,1,1,1,1,1] (.node [10,7,4,4,4,3,3,2,1,1] .empty .empty) .empty)) (.node [10,7,5,3,3,3,3,2,2,1] (.node [10,7,4,4,4,4,3,1,1,1] (.node [10,7,4,4,4,4,2,2,1,1] .empty .empty) (.node [10,7,5,3,3,3,2,2,2,2] .empty .empty)) (.node [10,7,5,4,3,2,2,2,2,2] (.node [10,7,5,3,3,3,3,3,1,1] .empty .empty) .empty))))

def degreeTree39_111 : RowTree := (.node [10,7,4,4,3,3,1,1,1,1,1,1,1,1] degreeTree39_109 degreeTree39_110)

def degreeTree39_112 : RowTree := (.node [10,7,6,3,3,3,3,2,1,1] (.node [10,7,5,5,3,3,2,2,1,1] (.node [10,7,5,4,4,3,3,1,1,1] (.node [10,7,5,4,4,2,2,2,2,1] (.node [10,7,5,4,3,3,3,2,1,1] .empty .empty) (.node [10,7,5,4,4,3,2,2,1,1] .empty .empty)) (.node [10,7,5,5,2,2,2,2,2,2] (.node [10,7,5,4,4,4,2,1,1,1] .empty .empty) (.node [10,7,5,5,3,2,2,2,2,1] .empty .empty))) (.node [10,7,5,5,5,2,2,1,1,1] (.node [10,7,5,5,4,2,2,2,1,1] (.node [10,7,5,5,3,3,3,1,1,1] .empty .empty) (.node [10,7,5,5,4,3,2,1,1,1] .empty .empty)) (.node [10,7,6,3,3,3,2,2,2,1] (.node [10,7,6,3,3,2,2,2,2,2] .empty .empty) .empty))) (.node [10,7,6,5,2,2,2,2,2,1] (.node [10,7,6,4,3,3,3,1,1,1] (.node [10,7,6,4,3,2,2,2,2,1] (.node [10,7,6,4,2,2,2,2,2,2] .empty .empty) (.node [10,7,6,4,3,3,2,2,1,1] .empty .empty)) (.node [10,7,6,4,4,3,2,1,1,1] (.node [10,7,6,4,4,2,2,2,1,1] .empty .empty) .empty)) (.node [10,7,7,3,3,2,2,2,2,1] (.node [10,7,6,6,2,2,2,2,1,1] (.node [10,7,6,5,3,2,2,2,1,1] .empty .empty) (.node [10,7,7,3,2,2,2,2,2,2] .empty .empty)) (.node [10,7,7,3,3,3,3,1,1,1] (.node [10,7,7,3,3,3,2,2,1,1] .empty .empty) .empty))))

def degreeTree39_113 : RowTree := (.node [10,8,3,2,2,2,2,2,2,2,1,1,1,1] (.node [10,8,2,2,2,2,2,2,2,2,2,1,1,1] (.node [10,8,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,7,7,5,2,2,2,2,1,1] (.node [10,7,7,4,3,2,2,2,1,1] .empty .empty) (.node [10,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,2,2,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,8,2,2,2,2,2,2,2,2,1,1,1,1,1] .empty .empty))) (.node [10,8,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,2,2,2,2,2,2,2,2,2,2,1] .empty .empty) (.node [10,8,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,3,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,8,3,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,8,3,3,2,2,2,2,1,1,1,1,1,1,1] (.node [10,8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,3,2,2,2,2,2,2,2,2,2] (.node [10,8,3,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,3,3,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,8,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,8,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,3,3,2,2,2,2,2,2,1,1,1] (.node [10,8,3,3,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,8,3,3,2,2,2,2,2,2,2,1] .empty .empty)) (.node [10,8,3,3,3,2,2,1,1,1,1,1,1,1,1] (.node [10,8,3,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_114 : RowTree := (.node [10,7,7,4,2,2,2,2,2,1] degreeTree39_112 degreeTree39_113)

def degreeTree39_115 : RowTree := (.node [10,7,5,4,3,3,2,2,2,1] degreeTree39_111 degreeTree39_114)

def degreeTree39_116 : RowTree := (.node [10,8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,3,3,3,3,2,2,2,2,1] (.node [10,8,3,3,3,3,1,1,1,1,1,1,1,1,1] (.node [10,8,3,3,3,2,2,2,2,2,1,1] (.node [10,8,3,3,3,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,8,3,3,3,2,2,2,2,2,2] .empty .empty)) (.node [10,8,3,3,3,3,2,2,1,1,1,1,1] (.node [10,8,3,3,3,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,8,3,3,3,3,2,2,2,1,1,1] .empty .empty))) (.node [10,8,3,3,3,3,3,2,2,2] (.node [10,8,3,3,3,3,3,2,1,1,1,1] (.node [10,8,3,3,3,3,3,1,1,1,1,1,1] .empty .empty) (.node [10,8,3,3,3,3,3,2,2,1,1] .empty .empty)) (.node [10,8,3,3,3,3,3,3,2,1] (.node [10,8,3,3,3,3,3,3,1,1,1] .empty .empty) .empty))) (.node [10,8,4,2,2,2,2,2,2,2,2,1] (.node [10,8,4,2,2,2,2,2,1,1,1,1,1,1,1] (.node [10,8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,8,4,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,4,2,2,2,2,2,2,2,1,1,1] (.node [10,8,4,2,2,2,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [10,8,4,3,2,2,2,1,1,1,1,1,1,1,1] (.node [10,8,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,8,4,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,4,3,2,2,2,2,2,1,1,1,1] (.node [10,8,4,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_117 : RowTree := (.node [10,8,4,3,3,3,3,2,2,1] (.node [10,8,4,3,3,3,1,1,1,1,1,1,1,1] (.node [10,8,4,3,3,2,2,1,1,1,1,1,1,1] (.node [10,8,4,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,4,3,2,2,2,2,2,2,2] .empty .empty) (.node [10,8,4,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,4,3,3,2,2,2,2,1,1,1] (.node [10,8,4,3,3,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,8,4,3,3,2,2,2,2,2,1] .empty .empty))) (.node [10,8,4,3,3,3,2,2,2,2] (.node [10,8,4,3,3,3,2,2,1,1,1,1] (.node [10,8,4,3,3,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,8,4,3,3,3,2,2,2,1,1] .empty .empty)) (.node [10,8,4,3,3,3,3,2,1,1,1] (.node [10,8,4,3,3,3,3,1,1,1,1,1] .empty .empty) .empty))) (.node [10,8,4,4,2,2,2,2,2,1,1,1] (.node [10,8,4,4,2,2,1,1,1,1,1,1,1,1,1] (.node [10,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,4,3,3,3,3,3,1,1] .empty .empty) (.node [10,8,4,4,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,4,4,2,2,2,2,1,1,1,1,1] (.node [10,8,4,4,2,2,2,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,8,4,4,3,2,2,1,1,1,1,1,1] (.node [10,8,4,4,3,1,1,1,1,1,1,1,1,1,1] (.node [10,8,4,4,2,2,2,2,2,2,1] .empty .empty) (.node [10,8,4,4,3,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,8,4,4,3,2,2,2,2,1,1] (.node [10,8,4,4,3,2,2,2,1,1,1,1] .empty .empty) .empty))))

def degreeTree39_118 : RowTree := (.node [10,8,4,3,2,2,2,2,2,2,1,1] degreeTree39_116 degreeTree39_117)

def degreeTree39_119 : RowTree := (.node [10,8,4,4,4,4,1,1,1,1,1] (.node [10,8,4,4,4,2,1,1,1,1,1,1,1] (.node [10,8,4,4,3,3,2,2,2,1] (.node [10,8,4,4,3,3,2,1,1,1,1,1] (.node [10,8,4,4,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,8,4,4,3,3,2,2,1,1,1] .empty .empty)) (.node [10,8,4,4,3,3,3,2,1,1] (.node [10,8,4,4,3,3,3,1,1,1,1] .empty .empty) (.node [10,8,4,4,4,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,8,4,4,4,3,1,1,1,1,1,1] (.node [10,8,4,4,4,2,2,2,1,1,1] (.node [10,8,4,4,4,2,2,1,1,1,1,1] .empty .empty) (.node [10,8,4,4,4,2,2,2,2,1] .empty .empty)) (.node [10,8,4,4,4,3,2,2,1,1] (.node [10,8,4,4,4,3,2,1,1,1,1] .empty .empty) .empty))) (.node [10,8,5,4,4,2,2,2,1,1] (.node [10,8,5,4,2,2,2,2,2,2] (.node [10,8,5,3,3,3,2,2,2,1] (.node [10,8,5,3,3,2,2,2,2,2] .empty .empty) (.node [10,8,5,3,3,3,3,2,1,1] .empty .empty)) (.node [10,8,5,4,3,3,2,2,1,1] (.node [10,8,5,4,3,2,2,2,2,1] .empty .empty) .empty)) (.node [10,8,6,3,3,3,2,2,1,1] (.node [10,8,6,3,2,2,2,2,2,2] (.node [10,8,5,5,2,2,2,2,2,1] .empty .empty) (.node [10,8,6,3,3,2,2,2,2,1] .empty .empty)) (.node [10,8,7,2,2,2,2,2,2,2] (.node [10,8,6,4,2,2,2,2,2,1] .empty .empty) .empty))))

def degreeTree39_120 : RowTree := (.node [10,9,4,4,3,2,2,2,2,1] (.node [10,9,2,2,2,2,2,2,2,2,2,1,1] (.node [10,9,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,9,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,8,8,2,2,2,2,2,2,1] .empty .empty) (.node [10,9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,9,2,2,2,2,2,2,2,1,1,1,1,1,1] (.node [10,9,2,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,9,2,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [10,9,4,3,3,2,2,2,2,2] (.node [10,9,3,3,3,3,2,2,2,2] (.node [10,9,2,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [10,9,3,3,3,3,3,2,2,1] .empty .empty)) (.node [10,9,4,4,2,2,2,2,2,2] (.node [10,9,4,3,3,3,2,2,2,1] .empty .empty) .empty))) (.node [10,10,2,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [10,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,9,5,3,3,2,2,2,2,1] (.node [10,9,5,3,2,2,2,2,2,2] .empty .empty) (.node [10,9,6,2,2,2,2,2,2,2] .empty .empty)) (.node [10,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,10,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,10,2,2,2,2,2,2,2,2,2,1] (.node [10,10,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,10,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,10,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,10,4,3,2,2,2,2,2,2] (.node [10,10,3,3,3,2,2,2,2,2] .empty .empty) .empty))))

def degreeTree39_121 : RowTree := (.node [10,8,7,3,2,2,2,2,2,1] degreeTree39_119 degreeTree39_120)

def degreeTree39_122 : RowTree := (.node [10,8,4,4,3,2,2,2,2,2] degreeTree39_118 degreeTree39_121)

def degreeTree39_123 : RowTree := (.node [10,8,3,3,3,2,2,2,1,1,1,1,1,1] degreeTree39_115 degreeTree39_122)

def degreeTree39_124 : RowTree := (.node [10,7,4,3,3,2,2,2,1,1,1,1,1,1] degreeTree39_108 degreeTree39_123)

def degreeTree39_125 : RowTree := (.node [10,6,5,4,3,2,1,1,1,1,1,1,1,1,1] degreeTree39_93 degreeTree39_124)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 112. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP112 := ResidualProperty 12 17 degreeQs112 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP12 := ResidualProperty 4 1 degreeQs12 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP151 := ResidualProperty 14 23 degreeQs151 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP17 := ResidualProperty 5 1 degreeQs17 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP23 := ResidualProperty 6 1 degreeQs23 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP25 := ResidualProperty 6 2 degreeQs25 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP27 := ResidualProperty 6 3 degreeQs27 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP29 := ResidualProperty 6 4 degreeQs29 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP30 := ResidualProperty 7 1 degreeQs30 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP32 := ResidualProperty 7 2 degreeQs32 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP33 := ResidualProperty 6 6 degreeQs33 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP34 := ResidualProperty 7 3 degreeQs34 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP38 := ResidualProperty 8 1 degreeQs38 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP40 := ResidualProperty 8 2 degreeQs40 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP42 := ResidualProperty 8 3 degreeQs42 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP47 := ResidualProperty 9 1 degreeQs47 []

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

abbrev degreeP48 := ResidualProperty 8 6 degreeQs48 []

end UniversalTensorSquare
end
end

end OAI
end


