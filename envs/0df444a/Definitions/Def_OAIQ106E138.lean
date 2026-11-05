-- Prove2me | Definitions.Def_OAIQ106E138
-- name    : OAIQ106E138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T23:30:14.297056+00:00
-- url     : https://prove2.me/theorems/569b09dc-6fc7-41a7-82ab-11ff3fbbf6c4
-- title:
--   Definitions bundle OAIQ106E138 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1361 declarations of OpenAI's Lean: 1361 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge80`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge802`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge803`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge804`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge805`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge806`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge807`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge808`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge809`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge81`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge810`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge811`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge812`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge813`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge814`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge815`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge816`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge817`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge818`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge819`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge82`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge820`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge821`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge822`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge823`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge824`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge825`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge826`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge827`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge828`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge829`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge83`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge830`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge831`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge832`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge833`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge834`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge835`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge836`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMerge837` and 1321 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedTargets_ReductionData0`, `MutuallyUnbiased_MixedTargets_ReductionData13`, `MutuallyUnbiased_MixedTargets_ReductionData3`, `MutuallyUnbiased_MixedTargets_ReductionData31`, `MutuallyUnbiased_MixedTargets_ReductionData32`, `MutuallyUnbiased_MixedTargets_ReductionData33`, `MutuallyUnbiased_MixedTargets_ReductionData34`, `MutuallyUnbiased_MixedTargets_ReductionData35`, `MutuallyUnbiased_MixedTargets_ReductionData36`, `MutuallyUnbiased_MixedTargets_ReductionData37`, `MutuallyUnbiased_MixedTargets_ReductionData38`, `MutuallyUnbiased_MixedTargets_ReductionData39`, `MutuallyUnbiased_MixedTargets_ReductionData4`, `MutuallyUnbiased_MixedTargets_ReductionData40`, `MutuallyUnbiased_MixedTargets_ReductionData41`, `MutuallyUnbiased_MixedTargets_ReductionData42`, `MutuallyUnbiased_MixedTargets_ReductionData43`, `MutuallyUnbiased_MixedTargets_ReductionData44`, `MutuallyUnbiased_MixedTargets_ReductionData45`, `MutuallyUnbiased_MixedTargets_ReductionData46`, `MutuallyUnbiased_MixedTargets_ReductionData47`, `MutuallyUnbiased_MixedTargets_ReductionData48`, `MutuallyUnbiased_MixedTargets_ReductionData49`, `MutuallyUnbiased_MixedTargets_ReductionData5`, `MutuallyUnbiased_MixedTargets_ReductionData50`, `MutuallyUnbiased_MixedTargets_ReductionData51`, `MutuallyUnbiased_MixedTargets_ReductionData52`, `MutuallyUnbiased_MixedTargets_ReductionData53`, `MutuallyUnbiased_MixedTargets_ReductionData54`, `MutuallyUnbiased_MixedTargets_ReductionData55`, `MutuallyUnbiased_MixedTargets_ReductionData56`, `MutuallyUnbiased_MixedTargets_ReductionData57`, `MutuallyUnbiased_MixedTargets_ReductionData58`, `MutuallyUnbiased_MixedTargets_ReductionData59`, `MutuallyUnbiased_MixedTargets_ReductionData6`, `MutuallyUnbiased_MixedTargets_ReductionData7`, `MutuallyUnbiased_MixedTargets_ReductionData8`, `MutuallyUnbiased_MixedTargets_ReductionMergeData0`, `MutuallyUnbiased_MixedTargets_ReductionMergeData2`, `MutuallyUnbiased_MixedTargets_ReductionMergeData25`, `MutuallyUnbiased_MixedTargets_ReductionMergeData26`, `MutuallyUnbiased_MixedTargets_ReductionMergeData27`, `MutuallyUnbiased_MixedTargets_ReductionMergeData28`, `MutuallyUnbiased_MixedTargets_ReductionMergeData29`, `MutuallyUnbiased_MixedTargets_ReductionMergeData3`, `MutuallyUnbiased_MixedTargets_ReductionMergeData30`, `MutuallyUnbiased_MixedTargets_ReductionMergeData31`.
--
--   **Imports.** It imports the bundle `OAIQ106E043` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`; the proofs of `OAI.MUB6.Certificate.MixedTargetSemantics.originalReductionEval_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval100_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval105_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1075_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval108_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval111_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval113_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval117_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval118_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1194_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1196_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1225_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval122_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval126_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval12_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1315_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval131_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval136_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval137_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval141_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1436_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval143_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1465_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval151_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1523_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval152_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1554_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1555_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval155_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval164_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval165_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1675_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval169_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval174_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval175_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1794_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval181_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval185_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval18_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval190_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval1912_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval201_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval202_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval211_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval212_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval217_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval224_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval226_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval229_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval232_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval234_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval235_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval242_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval246_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval250_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval256_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval260_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval264_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval266_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval268_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval269_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval275_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval280_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval286_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval413_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval84_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval86_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval8_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval92_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval956_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval957_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval145_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval147_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval150_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval215_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval216_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval219_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval21_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval220_e`, `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval223_e` and `OAI.MUB6.Certificate.MixedTargetSemantics.reducedTermEval238_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm0 : Integer.Sparse Master := [(Sum.inl 0, 2563162779156553728000), (Sum.inl 1, 3495221971577118720000), (Sum.inl 2, 2330147981051412480000)]

def reducedTerm1 : Integer.Sparse Master := [(Sum.inl 0, 4056921058202320896000), (Sum.inl 1, -5071151322752901120000), (Sum.inl 2, -5071151322752901120000)]

def reducedTerm2 : Integer.Sparse Master := [(Sum.inl 0, 469974932497760256000), (Sum.inl 2, 2349874662488801280000)]

def reducedTerm10 : Integer.Sparse Master := [(Sum.inl 0, 82045141724528640000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -136741902874214400000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 937658762566041600000), (Sum.inl 6, -117207345320755200000), (Sum.inl 7, -1875317525132083200000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 625105841710694400000), (Sum.inl 35, -1250211683421388800000), (Sum.inl 52, -625105841710694400000), (Sum.inl 58, -19534557553459200000), (Sum.inl 69, -2500423366842777600000), (Sum.inl 70, -1562764604276736000000), (Sum.inl 71, -1875317525132083200000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -625105841710694400000), (Sum.inl 495, -625105841710694400000)]

def reducedTerm11 : Integer.Sparse Master := [(Sum.inl 0, 78138230213836800000), (Sum.inl 1, 97672787767296000000), (Sum.inl 2, 253949248194969600000), (Sum.inl 5, -312552920855347200000), (Sum.inl 6, 117207345320755200000), (Sum.inl 9, -390691151069184000000), (Sum.inl 52, 312552920855347200000), (Sum.inl 58, 39069115106918400000), (Sum.inl 69, 625105841710694400000), (Sum.inl 71, 625105841710694400000), (Sum.inl 495, 312552920855347200000)]

def reducedTerm12 : Integer.Sparse Master := [(Sum.inl 0, -60247541355724800000), (Sum.inl 1, 123233607318528000000), (Sum.inl 2, 41077869106176000000), (Sum.inl 5, 164311476424704000000), (Sum.inl 7, -438163937132544000000), (Sum.inl 9, 219081968566272000000), (Sum.inl 35, -219081968566272000000), (Sum.inl 69, -657245905698816000000), (Sum.inl 70, -657245905698816000000), (Sum.inl 71, -219081968566272000000), (Sum.inl 257, -219081968566272000000)]

def reducedTerm13 : Integer.Sparse Master := [(Sum.inl 0, -25396268601876480000), (Sum.inl 1, 57718792276992000000), (Sum.inl 2, 34631275366195200000), (Sum.inl 5, -92350067643187200000), (Sum.inl 6, 46175033821593600000), (Sum.inl 9, -138525101464780800000), (Sum.inl 58, 34631275366195200000)]

def reducedTerm14 : Integer.Sparse Master := [(Sum.inl 0, -52112700867870720000), (Sum.inl 1, -11843795651788800000), (Sum.inl 2, 11843795651788800000), (Sum.inl 5, 94750365214310400000), (Sum.inl 6, -71062773910732800000), (Sum.inl 9, 189500730428620800000), (Sum.inl 35, -379001460857241600000), (Sum.inl 58, -23687591303577600000), (Sum.inl 69, -189500730428620800000), (Sum.inl 70, -189500730428620800000), (Sum.inl 257, -379001460857241600000), (Sum.inl 495, -379001460857241600000)]

def reducedTerm15 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -136741902874214400000), (Sum.inl 5, 234414690641510400000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 312552920855347200000), (Sum.inl 69, -625105841710694400000), (Sum.inl 70, -312552920855347200000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000)]

def reducedTerm16 : Integer.Sparse Master := [(Sum.inl 0, 52112700867870720000), (Sum.inl 2, -47375182607155200000), (Sum.inl 5, 94750365214310400000), (Sum.inl 6, -94750365214310400000), (Sum.inl 9, 189500730428620800000), (Sum.inl 58, -71062773910732800000), (Sum.inl 495, -379001460857241600000)]

def reducedTerm17 : Integer.Sparse Master := [(Sum.inl 0, -15941264449904640000), (Sum.inl 1, 36230146477056000000), (Sum.inl 2, 14492058590822400000), (Sum.inl 9, -86952351544934400000), (Sum.inl 69, 115936468726579200000), (Sum.inl 70, 115936468726579200000), (Sum.inl 71, 115936468726579200000)]

def reducedTerm18 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -39069115106918400000), (Sum.inl 2, -117207345320755200000), (Sum.inl 9, -468829381283020800000), (Sum.inl 69, 625105841710694400000), (Sum.inl 71, 1250211683421388800000)]

def reducedTerm19 : Integer.Sparse Master := [(Sum.inl 0, -38820060750643200000), (Sum.inl 1, 97050151876608000000), (Sum.inl 2, 97050151876608000000), (Sum.inl 9, -194100303753216000000), (Sum.inl 69, 258800405004288000000), (Sum.inl 70, 258800405004288000000), (Sum.inl 257, 258800405004288000000)]

def reducedTerm20 : Integer.Sparse Master := [(Sum.inl 0, 23884897183580160000), (Sum.inl 1, -59712242958950400000), (Sum.inl 2, -59712242958950400000), (Sum.inl 9, -238848971835801600000), (Sum.inl 58, 119424485917900800000)]

def reducedTerm21 : Integer.Sparse Master := [(Sum.inl 0, -34582896065249280000), (Sum.inl 1, -54035775101952000000), (Sum.inl 2, -54035775101952000000), (Sum.inl 3, 518743440978739200000), (Sum.inl 5, 345828960652492800000), (Sum.inl 6, -129685860244684800000), (Sum.inl 7, 518743440978739200000), (Sum.inl 9, 821343781549670400000), (Sum.inl 35, 864572401631232000000), (Sum.inl 52, 1037486881957478400000), (Sum.inl 58, -43228620081561600000), (Sum.inl 69, 1037486881957478400000), (Sum.inl 70, 518743440978739200000), (Sum.inl 71, 518743440978739200000), (Sum.inl 256, -1556230322936217600000), (Sum.inl 257, 345828960652492800000), (Sum.inl 495, 518743440978739200000)]

def reducedTerm22 : Integer.Sparse Master := [(Sum.inl 0, -36853560336015360000), (Sum.inl 1, 25416248507596800000), (Sum.inl 2, -12708124253798400000), (Sum.inl 6, -57186559142092800000), (Sum.inl 7, 304994982091161600000), (Sum.inl 8, 609989964182323200000), (Sum.inl 9, 406659976121548800000), (Sum.inl 58, -25416248507596800000), (Sum.inl 69, 609989964182323200000), (Sum.inl 70, 203329988060774400000), (Sum.inl 71, 1219979928364646400000)]

def reducedTerm23 : Integer.Sparse Master := [(Sum.inl 0, 34582896065249280000), (Sum.inl 1, 32421465061171200000), (Sum.inl 2, -75650085142732800000), (Sum.inl 5, 43228620081561600000), (Sum.inl 6, -32421465061171200000), (Sum.inl 9, 216143100407808000000), (Sum.inl 52, 345828960652492800000), (Sum.inl 58, -10807155020390400000), (Sum.inl 69, 345828960652492800000), (Sum.inl 71, 172914480326246400000), (Sum.inl 256, -518743440978739200000), (Sum.inl 495, 172914480326246400000)]

def reducedTerm24 : Integer.Sparse Master := [(Sum.inl 0, 43391874277785600000), (Sum.inl 1, 32142129094656000000), (Sum.inl 2, 48213193641984000000), (Sum.inl 6, -16071064547328000000), (Sum.inl 8, 257137032757248000000), (Sum.inl 9, 128568516378624000000), (Sum.inl 58, -8035532273664000000), (Sum.inl 69, 128568516378624000000), (Sum.inl 71, 514274065514496000000)]

def reducedTerm25 : Integer.Sparse Master := [(Sum.inl 0, -14475351711744000000), (Sum.inl 1, 36188379279360000000), (Sum.inl 2, 23028968632320000000), (Sum.inl 3, -52637642588160000000), (Sum.inl 5, -39478231941120000000), (Sum.inl 6, 9869557985280000000), (Sum.inl 7, -52637642588160000000), (Sum.inl 9, -65797053235200000000), (Sum.inl 35, -105275285176320000000), (Sum.inl 52, -52637642588160000000), (Sum.inl 58, 3289852661760000000), (Sum.inl 69, -52637642588160000000), (Sum.inl 70, -52637642588160000000), (Sum.inl 256, 157912927764480000000), (Sum.inl 257, -52637642588160000000), (Sum.inl 495, -52637642588160000000)]

def reducedTerm26 : Integer.Sparse Master := [(Sum.inl 0, 27464140247040000000), (Sum.inl 1, -64082993909760000000), (Sum.inl 2, -36618853662720000000), (Sum.inl 5, 36618853662720000000), (Sum.inl 6, 9154713415680000000), (Sum.inl 58, 9154713415680000000), (Sum.inl 71, -146475414650880000000)]

def reducedTerm27 : Integer.Sparse Master := [(Sum.inl 0, -20421240724684800000), (Sum.inl 1, 18564764295168000000), (Sum.inl 2, -120670967918592000000), (Sum.inl 5, 37129528590336000000), (Sum.inl 9, 74259057180672000000), (Sum.inl 35, 148518114361344000000), (Sum.inl 70, 148518114361344000000), (Sum.inl 257, 148518114361344000000)]

def reducedTerm28 : Integer.Sparse Master := [(Sum.inl 0, 8667910534348800000), (Sum.inl 1, -20225124580147200000), (Sum.inl 2, -11557214045798400000), (Sum.inl 9, -23114428091596800000), (Sum.inl 69, -46228856183193600000), (Sum.inl 71, -46228856183193600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm418 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm100 : Integer.Sparse Master := [(Sum.inl 0, 142182526890700800000), (Sum.inl 1, -473941756302336000000), (Sum.inl 2, -135411930372096000000), (Sum.inl 3, 1083295442976768000000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 406235791116288000000), (Sum.inl 6, -101558947779072000000), (Sum.inl 7, 541647721488384000000), (Sum.inl 26, 1083295442976768000000), (Sum.inl 35, 1083295442976768000000), (Sum.inl 67, 541647721488384000000), (Sum.inl 81, -1624943164465152000000)]

def reducedTerm101 : Integer.Sparse Master := [(Sum.inl 0, -28026684045803520000), (Sum.inl 1, -140133420229017600000), (Sum.inl 2, -38218205517004800000), (Sum.inl 3, 203830429424025600000), (Sum.inl 5, 50957607356006400000), (Sum.inl 6, -12739401839001600000), (Sum.inl 7, 203830429424025600000), (Sum.inl 35, 203830429424025600000)]

def reducedTerm102 : Integer.Sparse Master := [(Sum.inl 0, -135411930372096000000), (Sum.inl 1, 203117895558144000000), (Sum.inl 2, -270823860744192000000), (Sum.inl 5, 270823860744192000000), (Sum.inl 6, -67705965186048000000), (Sum.inl 81, -3249886328930304000000)]

def reducedTerm103 : Integer.Sparse Master := [(Sum.inl 0, -7982631685324800000), (Sum.inl 1, -29934868819968000000), (Sum.inl 2, 19956579213312000000), (Sum.inl 6, 9978289606656000000), (Sum.inl 35, -159652633706496000000)]

def reducedTerm104 : Integer.Sparse Master := [(Sum.inl 0, -7508214844784640000), (Sum.inl 1, 14204730787430400000), (Sum.inl 6, 3043870883020800000), (Sum.inl 7, -16233978042777600000), (Sum.inl 8, -32467956085555200000)]

def reducedTerm105 : Integer.Sparse Master := [(Sum.inl 0, 185868078860943360000), (Sum.inl 1, -391301218654617600000), (Sum.inl 6, 48912652331827200000), (Sum.inl 8, -782602437309235200000)]

def reducedTerm106 : Integer.Sparse Master := [(Sum.inl 0, -14812828578938880000), (Sum.inl 1, 37032071447347200000), (Sum.inl 2, 37032071447347200000), (Sum.inl 5, -74064142894694400000), (Sum.inl 67, -296256571578777600000)]

def reducedTerm107 : Integer.Sparse Master := [(Sum.inl 0, -60285536389693440000), (Sum.inl 1, -602855363896934400000), (Sum.inl 5, -301427681948467200000), (Sum.inl 7, -1205710727793868800000)]

def reducedTerm108 : Integer.Sparse Master := [(Sum.inl 0, -168780258275328000000), (Sum.inl 1, 281300430458880000000), (Sum.inl 5, -562600860917760000000), (Sum.inl 8, -2250403443671040000000)]

def reducedTerm109 : Integer.Sparse Master := [(Sum.inl 0, 85145919251742720000), (Sum.inl 1, 851459192517427200000), (Sum.inl 5, 1702918385034854400000), (Sum.inl 6, 425729596258713600000)]

def reducedTerm110 : Integer.Sparse Master := [(Sum.inl 0, 8075576528732160000), (Sum.inl 1, 15141705991372800000), (Sum.inl 3, -121133647930982400000), (Sum.inl 5, 40377882643660800000), (Sum.inl 6, -15141705991372800000), (Sum.inl 7, -161511530574643200000), (Sum.inl 9, 10094470660915200000), (Sum.inl 13, -40377882643660800000), (Sum.inl 26, -161511530574643200000), (Sum.inl 34, -40377882643660800000), (Sum.inl 35, -323023061149286400000), (Sum.inl 67, -80755765287321600000), (Sum.inl 68, -30283411982745600000), (Sum.inl 69, -40377882643660800000), (Sum.inl 70, -121133647930982400000), (Sum.inl 124, 121133647930982400000), (Sum.inl 196, 121133647930982400000), (Sum.inl 197, 242267295861964800000), (Sum.inl 257, -40377882643660800000), (Sum.inl 266, 121133647930982400000)]

def reducedTerm111 : Integer.Sparse Master := [(Sum.inl 0, 104570620244213760000), (Sum.inl 1, -24897766724812800000), (Sum.inl 2, 24897766724812800000), (Sum.inl 3, -1991821337985024000000), (Sum.inl 5, 398364267597004800000), (Sum.inl 6, -74693300174438400000), (Sum.inl 7, -1593457070388019200000), (Sum.inl 9, 99591066899251200000), (Sum.inl 13, -1195092802791014400000), (Sum.inl 26, -796728535194009600000), (Sum.inl 34, -398364267597004800000), (Sum.inl 35, -2390185605582028800000), (Sum.inl 52, -796728535194009600000), (Sum.inl 60, -398364267597004800000), (Sum.inl 64, 1195092802791014400000), (Sum.inl 67, -398364267597004800000), (Sum.inl 68, -298773200697753600000), (Sum.inl 69, -398364267597004800000), (Sum.inl 70, -796728535194009600000), (Sum.inl 125, 2390185605582028800000), (Sum.inl 126, 1195092802791014400000), (Sum.inl 197, 1195092802791014400000), (Sum.inl 257, -398364267597004800000), (Sum.inl 260, 1195092802791014400000), (Sum.inl 268, 1195092802791014400000)]

def reducedTerm112 : Integer.Sparse Master := [(Sum.inl 0, 5693270466723840000), (Sum.inl 1, -11645325954662400000), (Sum.inl 2, -3881775318220800000), (Sum.inl 3, -20702801697177600000), (Sum.inl 5, 10351400848588800000), (Sum.inl 7, -20702801697177600000), (Sum.inl 13, -20702801697177600000), (Sum.inl 23, 124216810183065600000), (Sum.inl 27, -15527101272883200000), (Sum.inl 35, -20702801697177600000), (Sum.inl 54, 124216810183065600000), (Sum.inl 55, 62108405091532800000), (Sum.inl 63, 62108405091532800000), (Sum.inl 65, 62108405091532800000), (Sum.inl 68, -31054202545766400000), (Sum.inl 124, 62108405091532800000), (Sum.inl 125, 186325215274598400000), (Sum.inl 196, 124216810183065600000), (Sum.inl 197, 62108405091532800000), (Sum.inl 264, 124216810183065600000), (Sum.inl 266, 62108405091532800000)]

def reducedTerm113 : Integer.Sparse Master := [(Sum.inl 0, -166943984356638720000), (Sum.inl 1, 113825443879526400000), (Sum.inl 2, 113825443879526400000), (Sum.inl 3, 1214138068048281600000), (Sum.inl 5, -607069034024140800000), (Sum.inl 6, 75883629253017600000), (Sum.inl 7, 1214138068048281600000), (Sum.inl 9, -151767258506035200000), (Sum.inl 13, 2428276136096563200000), (Sum.inl 32, 607069034024140800000), (Sum.inl 35, 2428276136096563200000), (Sum.inl 52, 1214138068048281600000), (Sum.inl 54, -3642414204144844800000), (Sum.inl 60, 1214138068048281600000), (Sum.inl 62, -3642414204144844800000), (Sum.inl 68, 455301775518105600000), (Sum.inl 69, 607069034024140800000), (Sum.inl 70, 607069034024140800000), (Sum.inl 125, -3642414204144844800000), (Sum.inl 257, 607069034024140800000), (Sum.inl 260, -3642414204144844800000), (Sum.inl 264, -5463621306217267200000)]

def reducedTerm114 : Integer.Sparse Master := [(Sum.inl 0, -22525478519685120000), (Sum.inl 1, -10726418342707200000), (Sum.inl 2, -16089627514060800000), (Sum.inl 5, -21452836685414400000), (Sum.inl 23, -257434040224972800000), (Sum.inl 24, -257434040224972800000), (Sum.inl 27, 128717020112486400000), (Sum.inl 51, -257434040224972800000), (Sum.inl 54, -257434040224972800000), (Sum.inl 55, -257434040224972800000), (Sum.inl 56, -257434040224972800000), (Sum.inl 61, -257434040224972800000), (Sum.inl 68, 128717020112486400000), (Sum.inl 124, -257434040224972800000), (Sum.inl 125, -257434040224972800000), (Sum.inl 126, -257434040224972800000), (Sum.inl 196, -257434040224972800000), (Sum.inl 197, -514868080449945600000), (Sum.inl 263, 514868080449945600000), (Sum.inl 266, -257434040224972800000), (Sum.inl 268, -257434040224972800000)]

def reducedTerm115 : Integer.Sparse Master := [(Sum.inl 0, 55238124229263360000), (Sum.inl 1, -125541191430144000000), (Sum.inl 2, -50216476572057600000), (Sum.inl 68, 301298859432345600000), (Sum.inl 124, -602597718864691200000), (Sum.inl 196, -602597718864691200000), (Sum.inl 197, -602597718864691200000), (Sum.inl 266, -602597718864691200000)]

def reducedTerm116 : Integer.Sparse Master := [(Sum.inl 0, -117207345320755200000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -175811017981132800000), (Sum.inl 68, -703244071924531200000), (Sum.inl 125, 1406488143849062400000), (Sum.inl 126, 1406488143849062400000), (Sum.inl 197, 1406488143849062400000), (Sum.inl 268, 1406488143849062400000)]

def reducedTerm117 : Integer.Sparse Master := [(Sum.inl 0, 15302998754426880000), (Sum.inl 1, -38257496886067200000), (Sum.inl 2, -38257496886067200000), (Sum.inl 68, 76514993772134400000), (Sum.inl 125, -306059975088537600000), (Sum.inl 264, -306059975088537600000)]

def reducedTerm118 : Integer.Sparse Master := [(Sum.inl 0, 148161587722444800000), (Sum.inl 1, -127725506657280000000), (Sum.inl 2, 127725506657280000000), (Sum.inl 3, -1226164863909888000000), (Sum.inl 5, -408721621303296000000), (Sum.inl 6, 25545101331456000000), (Sum.inl 7, -408721621303296000000), (Sum.inl 9, -102180405325824000000), (Sum.inl 12, -408721621303296000000), (Sum.inl 13, -408721621303296000000), (Sum.inl 23, 1226164863909888000000), (Sum.inl 26, -817443242606592000000), (Sum.inl 27, 919623647932416000000), (Sum.inl 35, -1226164863909888000000), (Sum.inl 54, 1226164863909888000000), (Sum.inl 55, 2452329727819776000000), (Sum.inl 68, 1532706079887360000000), (Sum.inl 70, -408721621303296000000), (Sum.inl 125, 2452329727819776000000), (Sum.inl 196, 1226164863909888000000), (Sum.inl 197, 2452329727819776000000)]

def reducedTerm119 : Integer.Sparse Master := [(Sum.inl 0, 32421465061171200000), (Sum.inl 1, -10807155020390400000), (Sum.inl 2, -32421465061171200000), (Sum.inl 3, -345828960652492800000), (Sum.inl 5, -172914480326246400000), (Sum.inl 6, 32421465061171200000), (Sum.inl 9, -43228620081561600000), (Sum.inl 13, -345828960652492800000), (Sum.inl 27, 389057580734054400000), (Sum.inl 33, 518743440978739200000), (Sum.inl 52, -345828960652492800000), (Sum.inl 55, 1037486881957478400000), (Sum.inl 64, 1037486881957478400000), (Sum.inl 68, 648429301223424000000), (Sum.inl 125, 1037486881957478400000), (Sum.inl 197, 518743440978739200000), (Sum.inl 260, 518743440978739200000), (Sum.inl 263, -1037486881957478400000)]

def reducedTerm120 : Integer.Sparse Master := [(Sum.inl 0, -19397401454592000000), (Sum.inl 1, 22630301697024000000), (Sum.inl 2, -87288306545664000000), (Sum.inl 5, -25863201939456000000), (Sum.inl 9, -12931600969728000000), (Sum.inl 13, -51726403878912000000), (Sum.inl 35, -103452807757824000000), (Sum.inl 68, 38794802909184000000), (Sum.inl 70, -51726403878912000000), (Sum.inl 196, 155179211636736000000)]

def reducedTerm121 : Integer.Sparse Master := [(Sum.inl 0, -6552799368192000000), (Sum.inl 1, -22279517851852800000), (Sum.inl 2, -20968957978214400000), (Sum.inl 3, 104844789891072000000), (Sum.inl 4, 41937915956428800000), (Sum.inl 5, 26211197472768000000), (Sum.inl 6, -2621119747276800000), (Sum.inl 7, 41937915956428800000), (Sum.inl 9, 5242239494553600000), (Sum.inl 13, 20968957978214400000), (Sum.inl 24, -125813747869286400000), (Sum.inl 26, 41937915956428800000), (Sum.inl 27, -47180155450982400000), (Sum.inl 35, 62906873934643200000), (Sum.inl 55, -62906873934643200000), (Sum.inl 56, -125813747869286400000), (Sum.inl 68, -78633592418304000000), (Sum.inl 70, 20968957978214400000), (Sum.inl 125, -62906873934643200000), (Sum.inl 197, -251627495738572800000)]

def reducedTerm122 : Integer.Sparse Master := [(Sum.inl 0, 6246161355571200000), (Sum.inl 1, -17697457174118400000), (Sum.inl 2, -12492322711142400000), (Sum.inl 3, 16656430281523200000), (Sum.inl 5, 8328215140761600000), (Sum.inl 6, -1041026892595200000), (Sum.inl 7, 16656430281523200000), (Sum.inl 9, 4164107570380800000), (Sum.inl 26, 16656430281523200000), (Sum.inl 35, 33312860563046400000), (Sum.inl 68, -12492322711142400000), (Sum.inl 70, 16656430281523200000), (Sum.inl 197, -49969290844569600000)]

def reducedTerm123 : Integer.Sparse Master := [(Sum.inl 0, 22913443897344000000), (Sum.inl 1, -57283609743360000000), (Sum.inl 2, -15622802657280000000), (Sum.inl 5, 41660807086080000000), (Sum.inl 6, -10415201771520000000), (Sum.inl 9, 20830403543040000000), (Sum.inl 13, 83321614172160000000), (Sum.inl 52, 83321614172160000000), (Sum.inl 64, -249964842516480000000), (Sum.inl 68, -62491210629120000000), (Sum.inl 125, -249964842516480000000), (Sum.inl 260, -249964842516480000000)]

def reducedTerm124 : Integer.Sparse Master := [(Sum.inl 0, 16481663325388800000), (Sum.inl 1, -18729162869760000000), (Sum.inl 2, 78662484052992000000), (Sum.inl 5, 14983330295808000000), (Sum.inl 13, 59933321183232000000), (Sum.inl 27, -44949990887424000000), (Sum.inl 35, 59933321183232000000), (Sum.inl 63, -179799963549696000000), (Sum.inl 68, -89899981774848000000), (Sum.inl 196, -179799963549696000000), (Sum.inl 264, -179799963549696000000)]

def reducedTerm125 : Integer.Sparse Master := [(Sum.inl 0, -151002500227891200000), (Sum.inl 1, 377506250569728000000), (Sum.inl 2, 226503750341836800000), (Sum.inl 27, 302005000455782400000), (Sum.inl 55, 1208020001823129600000), (Sum.inl 68, 604010000911564800000), (Sum.inl 125, 1208020001823129600000), (Sum.inl 197, 1208020001823129600000)]

def reducedTerm126 : Integer.Sparse Master := [(Sum.inl 0, -37266643303464960000), (Sum.inl 1, -296439208095744000000), (Sum.inl 2, -67757533279027200000), (Sum.inl 3, 813090399348326400000), (Sum.inl 5, 203272599837081600000), (Sum.inl 6, -25409074979635200000), (Sum.inl 7, 406545199674163200000), (Sum.inl 9, 33878766639513600000), (Sum.inl 12, 406545199674163200000), (Sum.inl 13, 542060266232217600000), (Sum.inl 23, -1219635599022489600000), (Sum.inl 27, -304908899755622400000), (Sum.inl 35, 406545199674163200000), (Sum.inl 54, -1219635599022489600000), (Sum.inl 68, -508181499592704000000), (Sum.inl 70, 135515066558054400000), (Sum.inl 125, -1219635599022489600000), (Sum.inl 196, -813090399348326400000)]

def reducedTerm127 : Integer.Sparse Master := [(Sum.inl 0, -17109319431536640000), (Sum.inl 1, -93323560535654400000), (Sum.inl 2, -15553926755942400000), (Sum.inl 3, -124431414047539200000), (Sum.inl 5, -31107853511884800000), (Sum.inl 6, 7776963377971200000), (Sum.inl 7, -124431414047539200000), (Sum.inl 9, -15553926755942400000), (Sum.inl 13, -62215707023769600000), (Sum.inl 35, -124431414047539200000), (Sum.inl 68, 46661780267827200000), (Sum.inl 70, -62215707023769600000), (Sum.inl 125, 186647121071308800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1000 : Integer.Sparse Master := [(Sum.inr 2678, 1249731921884479488000)]

def reducedTerm1001 : Integer.Sparse Master := [(Sum.inr 2680, 328270556047343616000)]

def reducedTerm1002 : Integer.Sparse Master := [(Sum.inr 2681, -304877566989434880000)]

def reducedTerm1003 : Integer.Sparse Master := [(Sum.inr 2682, -2451504521281536000000)]

def reducedTerm1004 : Integer.Sparse Master := [(Sum.inr 2683, -2711614482074566656000)]

def reducedTerm1005 : Integer.Sparse Master := [(Sum.inr 2687, 2753869669962743808000)]

def reducedTerm1006 : Integer.Sparse Master := [(Sum.inr 2688, 2124806707563724800000)]

def reducedTerm1007 : Integer.Sparse Master := [(Sum.inr 2690, -2124806707563724800000)]

def reducedTerm1008 : Integer.Sparse Master := [(Sum.inr 2697, 665857147118026752000)]

def reducedTerm1009 : Integer.Sparse Master := [(Sum.inr 2698, -3210049119603916800000)]

def reducedTerm1010 : Integer.Sparse Master := [(Sum.inr 2700, -450757951040323584000)]

def reducedTerm1011 : Integer.Sparse Master := [(Sum.inr 2702, -423147689038577664000)]

def reducedTerm1012 : Integer.Sparse Master := [(Sum.inr 2706, 4172340565215019008000)]

def reducedTerm1013 : Integer.Sparse Master := [(Sum.inr 2707, -847409560407244800000)]

def reducedTerm1014 : Integer.Sparse Master := [(Sum.inr 2708, 2180351629537837056000)]

def reducedTerm1015 : Integer.Sparse Master := []

def reducedTerm1016 : Integer.Sparse Master := [(Sum.inr 2710, 3772583761333911552000)]

def reducedTerm1017 : Integer.Sparse Master := [(Sum.inr 2712, 669848715789926400000)]

def reducedTerm1018 : Integer.Sparse Master := [(Sum.inr 2714, -18738707098219315200000)]

def reducedTerm1019 : Integer.Sparse Master := [(Sum.inr 2716, 178978720009420800000)]

def reducedTerm1020 : Integer.Sparse Master := [(Sum.inr 2718, 2657205919166496768000)]

def reducedTerm1021 : Integer.Sparse Master := [(Sum.inr 2719, 189716558307655680000)]

def reducedTerm1022 : Integer.Sparse Master := []

def reducedTerm1023 : Integer.Sparse Master := [(Sum.inr 2721, -19158304125686906880000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1024 : Integer.Sparse Master := [(Sum.inr 2722, -53630193427477954560000)]

def reducedTerm1025 : Integer.Sparse Master := [(Sum.inr 2723, -6132895964194406400000)]

def reducedTerm1026 : Integer.Sparse Master := [(Sum.inr 2724, 151499143634485248000)]

def reducedTerm1027 : Integer.Sparse Master := [(Sum.inr 2726, -21951447043276800000)]

def reducedTerm1028 : Integer.Sparse Master := [(Sum.inr 2728, -4207603471599403008000)]

def reducedTerm1029 : Integer.Sparse Master := [(Sum.inr 2729, 160580769836433408000)]

def reducedTerm1030 : Integer.Sparse Master := [(Sum.inr 2730, -5448613796115775488000)]

def reducedTerm1031 : Integer.Sparse Master := [(Sum.inr 2731, 1891520709844598784000)]

def reducedTerm1032 : Integer.Sparse Master := [(Sum.inr 2732, -3902216098532032512000)]

def reducedTerm1033 : Integer.Sparse Master := [(Sum.inr 2734, 6171454343172980736000)]

def reducedTerm1034 : Integer.Sparse Master := [(Sum.inr 2735, 3357311730124455936000)]

def reducedTerm1035 : Integer.Sparse Master := [(Sum.inr 2736, 4773540463463890944000)]

def reducedTerm1036 : Integer.Sparse Master := [(Sum.inr 2737, -189385081118392320000)]

def reducedTerm1037 : Integer.Sparse Master := [(Sum.inr 2738, 4201772064568049664000)]

def reducedTerm1038 : Integer.Sparse Master := [(Sum.inr 2739, 863627382126673920000)]

def reducedTerm1039 : Integer.Sparse Master := [(Sum.inr 2740, -636663027329925120000)]

def reducedTerm1040 : Integer.Sparse Master := []

def reducedTerm1041 : Integer.Sparse Master := []

def reducedTerm1042 : Integer.Sparse Master := [(Sum.inr 2743, 11054987203142615040000)]

def reducedTerm1043 : Integer.Sparse Master := [(Sum.inr 2744, -22996102308321558528000)]

def reducedTerm1044 : Integer.Sparse Master := [(Sum.inr 2745, -5202654127895347200000)]

def reducedTerm1045 : Integer.Sparse Master := [(Sum.inr 2746, 5202654127895347200000)]

def reducedTerm1046 : Integer.Sparse Master := [(Sum.inr 2747, -1346211378226003968000)]

def reducedTerm1047 : Integer.Sparse Master := [(Sum.inr 2748, -3407495751248117760000)]

def reducedTerm1048 : Integer.Sparse Master := [(Sum.inr 2750, 27983833967776038912000)]

def reducedTerm1049 : Integer.Sparse Master := [(Sum.inr 2751, -28257993540927553536000)]

def reducedTerm1050 : Integer.Sparse Master := [(Sum.inl 0, 2171091313262592000), (Sum.inl 1, -6633890123857920000), (Sum.inl 2, -3015404601753600000), (Sum.inl 3, 19298589451223040000), (Sum.inl 12, 9649294725611520000), (Sum.inl 13, 9649294725611520000)]

def reducedTerm1051 : Integer.Sparse Master := [(Sum.inr 2754, -4946831880077574144000)]

def reducedTerm1052 : Integer.Sparse Master := [(Sum.inl 0, -4906555875577036800), (Sum.inl 1, 5257024152403968000), (Sum.inl 2, -26285120762019840000), (Sum.inl 13, 28037462146154496000)]

def reducedTerm1053 : Integer.Sparse Master := [(Sum.inr 2758, -8092322011089469440000)]

def reducedTerm1054 : Integer.Sparse Master := [(Sum.inr 2759, -7444916811245813760000)]

def reducedTerm1055 : Integer.Sparse Master := [(Sum.inr 2760, -416428679821787136000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1056 : Integer.Sparse Master := [(Sum.inr 2761, -1016042941450027008000)]

def reducedTerm1057 : Integer.Sparse Master := [(Sum.inr 2763, -21955095856769531904000)]

def reducedTerm1058 : Integer.Sparse Master := [(Sum.inr 2764, -23846279734862807040000)]

def reducedTerm1059 : Integer.Sparse Master := [(Sum.inr 2765, 9533108969263595520000)]

def reducedTerm1060 : Integer.Sparse Master := [(Sum.inr 2769, -22778979783065468928000)]

def reducedTerm1061 : Integer.Sparse Master := [(Sum.inr 2771, -1080639818309173248000)]

def reducedTerm1062 : Integer.Sparse Master := [(Sum.inr 2773, -7680684652994691072000)]

def reducedTerm1063 : Integer.Sparse Master := [(Sum.inr 2774, 4689897337119375360000)]

def reducedTerm1064 : Integer.Sparse Master := [(Sum.inl 0, 1434278790398361600), (Sum.inl 1, 15646677713436672000), (Sum.inl 2, 1955834714179584000), (Sum.inl 3, 31293355426873344000), (Sum.inl 12, 31293355426873344000), (Sum.inl 13, 20862236951248896000)]

def reducedTerm1065 : Integer.Sparse Master := [(Sum.inl 0, 18893574671066726400), (Sum.inl 1, 60115919407939584000), (Sum.inl 2, -17175976973697024000), (Sum.inl 3, -137407815789576192000), (Sum.inl 12, -137407815789576192000), (Sum.inl 13, -137407815789576192000)]

def reducedTerm1066 : Integer.Sparse Master := [(Sum.inr 2777, -4714450911702024192000)]

def reducedTerm1067 : Integer.Sparse Master := [(Sum.inl 0, 6751740971424153600), (Sum.inl 1, 25319028642840576000), (Sum.inl 2, 25319028642840576000), (Sum.inl 13, 135034819428483072000)]

def reducedTerm1068 : Integer.Sparse Master := [(Sum.inr 2779, 1029413887898812416000)]

def reducedTerm1069 : Integer.Sparse Master := [(Sum.inr 2780, -218973289450438656000)]

def reducedTerm1070 : Integer.Sparse Master := [(Sum.inr 2781, -9759313319373176832000)]

def reducedTerm1071 : Integer.Sparse Master := [(Sum.inr 2782, -28741157247379046400000)]

def reducedTerm1072 : Integer.Sparse Master := [(Sum.inr 2783, -12330745384768634880000)]

def reducedTerm1073 : Integer.Sparse Master := [(Sum.inr 2789, -13743886838351265792000)]

def reducedTerm1074 : Integer.Sparse Master := [(Sum.inr 2797, 10817029381629542400000)]

def reducedTerm1075 : Integer.Sparse Master := [(Sum.inr 2798, -6752922376232632320000)]

def reducedTerm1076 : Integer.Sparse Master := [(Sum.inr 2800, -3995973679581757440000)]

def reducedTerm1077 : Integer.Sparse Master := [(Sum.inr 2801, -1340821167243264000000)]

def reducedTerm1078 : Integer.Sparse Master := [(Sum.inr 2802, 4806257162718412800000)]

def reducedTerm1079 : Integer.Sparse Master := [(Sum.inr 2803, 7655273626113146880000)]

def reducedTerm1080 : Integer.Sparse Master := [(Sum.inr 2806, 416003421044736000000)]

def reducedTerm1081 : Integer.Sparse Master := [(Sum.inr 2807, 9566869889386414080000)]

def reducedTerm1082 : Integer.Sparse Master := [(Sum.inr 2809, -1653558743737958400000)]

def reducedTerm1083 : Integer.Sparse Master := [(Sum.inr 2810, -2050187137963130880000)]

def reducedTerm1084 : Integer.Sparse Master := [(Sum.inr 2811, -3435263414499409920000)]

def reducedTerm1085 : Integer.Sparse Master := [(Sum.inr 2812, 7633541508433182720000)]

def reducedTerm1086 : Integer.Sparse Master := [(Sum.inr 2813, -590178927323381760000)]

def reducedTerm1087 : Integer.Sparse Master := [(Sum.inr 2814, -4479366205522575360000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1088 : Integer.Sparse Master := [(Sum.inr 2815, 5011857085783080960000)]

def reducedTerm1089 : Integer.Sparse Master := [(Sum.inr 2816, 999901708930252800000)]

def reducedTerm1090 : Integer.Sparse Master := [(Sum.inr 2817, -7972461087479562240000)]

def reducedTerm1091 : Integer.Sparse Master := [(Sum.inr 2818, -5777870711254548480000)]

def reducedTerm1092 : Integer.Sparse Master := [(Sum.inr 2819, 8961285504761856000000)]

def reducedTerm1093 : Integer.Sparse Master := [(Sum.inr 2820, 1274912738715893760000)]

def reducedTerm1094 : Integer.Sparse Master := [(Sum.inr 2821, -2262212174315520000000)]

def reducedTerm1095 : Integer.Sparse Master := [(Sum.inr 2824, -11618393320164556800000)]

def reducedTerm1096 : Integer.Sparse Master := [(Sum.inr 2826, -10406241466564608000000)]

def reducedTerm1097 : Integer.Sparse Master := [(Sum.inr 2827, 6238836832370688000000)]

def reducedTerm1098 : Integer.Sparse Master := [(Sum.inr 2846, 2089015568665804800000)]

def reducedTerm1099 : Integer.Sparse Master := [(Sum.inr 2847, 5660818630174310400000)]

def reducedTerm1100 : Integer.Sparse Master := [(Sum.inr 2848, -5194848837860720640000)]

def reducedTerm1101 : Integer.Sparse Master := [(Sum.inr 2861, -3445367674768588800000)]

def reducedTerm1102 : Integer.Sparse Master := [(Sum.inr 2862, -3526248379837317120000)]

def reducedTerm1103 : Integer.Sparse Master := [(Sum.inr 2864, 1340821167243264000000)]

def reducedTerm1104 : Integer.Sparse Master := [(Sum.inr 2865, -21284105174522265600000)]

def reducedTerm1105 : Integer.Sparse Master := [(Sum.inr 2867, -6729430235975516160000)]

def reducedTerm1106 : Integer.Sparse Master := [(Sum.inr 2868, 3526248379837317120000)]

def reducedTerm1107 : Integer.Sparse Master := [(Sum.inr 2878, 9976743826758696960000)]

def reducedTerm1108 : Integer.Sparse Master := [(Sum.inr 2879, -416003421044736000000)]

def reducedTerm1109 : Integer.Sparse Master := [(Sum.inr 2880, -1781271279310602240000)]

def reducedTerm1110 : Integer.Sparse Master := [(Sum.inr 2881, 3469795674486865920000)]

def reducedTerm1111 : Integer.Sparse Master := [(Sum.inr 2882, -9976743826758696960000)]

def reducedTerm1112 : Integer.Sparse Master := [(Sum.inr 2884, 9212700734303109120000)]

def reducedTerm1113 : Integer.Sparse Master := [(Sum.inr 2885, -3934716707045376000000)]

def reducedTerm1114 : Integer.Sparse Master := [(Sum.inr 2886, 3435263414499409920000)]

def reducedTerm1115 : Integer.Sparse Master := [(Sum.inr 2888, 8305600448385515520000)]

def reducedTerm1116 : Integer.Sparse Master := [(Sum.inr 2889, 2724268260332666880000)]

def reducedTerm1117 : Integer.Sparse Master := [(Sum.inr 2890, 1355923199361024000000)]

def reducedTerm1118 : Integer.Sparse Master := [(Sum.inr 2892, 6564939594419404800000)]

def reducedTerm1119 : Integer.Sparse Master := [(Sum.inr 2893, -1057001205647278080000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1120 : Integer.Sparse Master := [(Sum.inr 2895, -5105263763930480640000)]

def reducedTerm1121 : Integer.Sparse Master := [(Sum.inr 2896, 3946875325262069760000)]

def reducedTerm1122 : Integer.Sparse Master := [(Sum.inr 2898, -5660818630174310400000)]

def reducedTerm1123 : Integer.Sparse Master := [(Sum.inr 2899, -9762840630358179840000)]

def reducedTerm1124 : Integer.Sparse Master := [(Sum.inr 2900, 16607243005555507200000)]

def reducedTerm1125 : Integer.Sparse Master := [(Sum.inr 2902, 13705060285808640000000)]

def reducedTerm1126 : Integer.Sparse Master := [(Sum.inr 2916, -2757638739876249600000)]

def reducedTerm1127 : Integer.Sparse Master := [(Sum.inr 2923, -359649951169904640000)]

def reducedTerm1128 : Integer.Sparse Master := [(Sum.inr 2924, 19302033754623836160000)]

def reducedTerm1129 : Integer.Sparse Master := [(Sum.inr 2925, 6891745041155358720000)]

def reducedTerm1130 : Integer.Sparse Master := [(Sum.inr 2928, 20635690283060428800000)]

def reducedTerm1131 : Integer.Sparse Master := [(Sum.inr 2930, 6436794359666442240000)]

def reducedTerm1132 : Integer.Sparse Master := [(Sum.inr 2931, 829623023566848000000)]

def reducedTerm1133 : Integer.Sparse Master := [(Sum.inr 2933, -16476867997522329600000)]

def reducedTerm1134 : Integer.Sparse Master := [(Sum.inr 2942, -8398043666546688000000)]

def reducedTerm1135 : Integer.Sparse Master := [(Sum.inr 2951, 33959038618062028800000)]

def reducedTerm1136 : Integer.Sparse Master := [(Sum.inr 2952, -571357054756454400000)]

def reducedTerm1137 : Integer.Sparse Master := [(Sum.inr 2954, -8958732411045150720000)]

def reducedTerm1138 : Integer.Sparse Master := [(Sum.inr 2955, -39828535728449126400000)]

def reducedTerm1139 : Integer.Sparse Master := [(Sum.inr 2964, -12088519805730816000000)]

def reducedTerm1140 : Integer.Sparse Master := [(Sum.inr 2967, -15967457567244288000000)]

def reducedTerm1141 : Integer.Sparse Master := [(Sum.inr 2979, -421979070165811200000)]

def reducedTerm1142 : Integer.Sparse Master := [(Sum.inr 2981, 669848715789926400000)]

def reducedTerm1143 : Integer.Sparse Master := [(Sum.inr 2984, 15200456282416742400000)]

def reducedTerm1144 : Integer.Sparse Master := [(Sum.inr 3016, -4525925648641818624000)]

def reducedTerm1145 : Integer.Sparse Master := [(Sum.inr 3023, -5814069266409062400000)]

def reducedTerm1146 : Integer.Sparse Master := [(Sum.inr 3024, 1699294017721466880000)]

def reducedTerm1147 : Integer.Sparse Master := [(Sum.inr 3025, -3657804786659229696000)]

def reducedTerm1148 : Integer.Sparse Master := [(Sum.inr 3029, -12883500708986880000000)]

def reducedTerm1149 : Integer.Sparse Master := [(Sum.inr 3030, -4222719607976755200000)]

def reducedTerm1150 : Integer.Sparse Master := [(Sum.inr 3031, 4597326756229939200000)]

def reducedTerm1151 : Integer.Sparse Master := [(Sum.inr 3032, 2216831132152627200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1152 : Integer.Sparse Master := [(Sum.inr 3033, -4250125755517501440000)]

def reducedTerm1153 : Integer.Sparse Master := [(Sum.inr 3036, 3735836684119572480000)]

def reducedTerm1154 : Integer.Sparse Master := [(Sum.inr 3037, -12943331682486976512000)]

def reducedTerm1155 : Integer.Sparse Master := [(Sum.inr 3038, 14492549870804533248000)]

def reducedTerm1156 : Integer.Sparse Master := [(Sum.inr 3039, 9313996009718808576000)]

def reducedTerm1157 : Integer.Sparse Master := [(Sum.inr 3040, 919241958555648000000)]

def reducedTerm1158 : Integer.Sparse Master := [(Sum.inr 3043, -2589617639009157120000)]

def reducedTerm1159 : Integer.Sparse Master := [(Sum.inr 3044, -16300334708112752640000)]

def reducedTerm1160 : Integer.Sparse Master := [(Sum.inr 3045, 4564186441588408320000)]

def reducedTerm1161 : Integer.Sparse Master := [(Sum.inr 3046, 3365072991753338880000)]

def reducedTerm1162 : Integer.Sparse Master := [(Sum.inr 3050, -4404201698619555840000)]

def reducedTerm1163 : Integer.Sparse Master := [(Sum.inr 3051, 3906032471591878656000)]

def reducedTerm1164 : Integer.Sparse Master := [(Sum.inr 3052, 7967955760767959040000)]

def reducedTerm1165 : Integer.Sparse Master := [(Sum.inr 3053, -4769146164905902080000)]

def reducedTerm1166 : Integer.Sparse Master := [(Sum.inr 3054, -6384294458848051200000)]

def reducedTerm1167 : Integer.Sparse Master := [(Sum.inr 3055, 16753008632221532160000)]

def reducedTerm1168 : Integer.Sparse Master := [(Sum.inr 3056, -4052239562185113600000)]

def reducedTerm1169 : Integer.Sparse Master := [(Sum.inr 3058, 259351328607436800000)]

def reducedTerm1170 : Integer.Sparse Master := [(Sum.inr 3059, -1852188959337873408000)]

def reducedTerm1171 : Integer.Sparse Master := [(Sum.inr 3062, -4597326756229939200000)]

def reducedTerm1172 : Integer.Sparse Master := [(Sum.inr 3064, 7350751094580117504000)]

def reducedTerm1173 : Integer.Sparse Master := []

def reducedTerm1174 : Integer.Sparse Master := [(Sum.inr 3066, -5639933671031439360000)]

def reducedTerm1175 : Integer.Sparse Master := [(Sum.inr 3068, -8048462097973248000000)]

def reducedTerm1176 : Integer.Sparse Master := [(Sum.inr 3069, 1668709084299264000000)]

def reducedTerm1177 : Integer.Sparse Master := [(Sum.inr 3073, 4020809998518190080000)]

def reducedTerm1178 : Integer.Sparse Master := [(Sum.inr 3074, 15546685904170057728000)]

def reducedTerm1179 : Integer.Sparse Master := [(Sum.inr 3075, -1716666600863563776000)]

def reducedTerm1180 : Integer.Sparse Master := [(Sum.inr 3077, -16333431861191639040000)]

def reducedTerm1181 : Integer.Sparse Master := [(Sum.inr 3078, 18561918376033320960000)]

def reducedTerm1182 : Integer.Sparse Master := [(Sum.inr 3079, -12298111992747786240000)]

def reducedTerm1183 : Integer.Sparse Master := [(Sum.inr 3083, -1415934024744960000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1184 : Integer.Sparse Master := [(Sum.inr 3084, -50941984034146222080000)]

def reducedTerm1185 : Integer.Sparse Master := []

def reducedTerm1186 : Integer.Sparse Master := [(Sum.inr 3086, -22351245374360125440000)]

def reducedTerm1187 : Integer.Sparse Master := [(Sum.inl 0, 14997999525072076800), (Sum.inl 1, 194091758559756288000), (Sum.inl 2, -13233528992710656000), (Sum.inl 3, -352894106472284160000), (Sum.inl 4, -141157642588913664000), (Sum.inl 26, -141157642588913664000)]

def reducedTerm1188 : Integer.Sparse Master := [(Sum.inl 0, 9524721044953497600), (Sum.inl 1, -6568773134450688000), (Sum.inl 2, -11495352985288704000), (Sum.inl 3, 26275092537802752000)]

def reducedTerm1189 : Integer.Sparse Master := [(Sum.inl 0, 44591733363179520000), (Sum.inl 1, -45903254932684800000), (Sum.inl 2, -59018470627737600000), (Sum.inl 3, 104921725560422400000), (Sum.inl 26, 104921725560422400000)]

def reducedTerm1190 : Integer.Sparse Master := [(Sum.inr 3092, -3891082594516992000000)]

def reducedTerm1191 : Integer.Sparse Master := [(Sum.inr 3096, -10769461456860610560000)]

def reducedTerm1192 : Integer.Sparse Master := [(Sum.inr 3097, 23327342262493839360000)]

def reducedTerm1193 : Integer.Sparse Master := [(Sum.inr 3098, 34405213211462467584000)]

def reducedTerm1194 : Integer.Sparse Master := [(Sum.inl 0, 46025869562988134400), (Sum.inl 2, 54792701860700160000), (Sum.inl 3, 526009937862721536000), (Sum.inl 4, 350673291908481024000), (Sum.inl 26, 350673291908481024000)]

def reducedTerm1195 : Integer.Sparse Master := [(Sum.inl 0, 17735212037033164800), (Sum.inl 1, -31670021494702080000), (Sum.inl 2, -19002012896821248000), (Sum.inl 3, -101344068783046656000), (Sum.inl 26, -101344068783046656000)]

def reducedTerm1196 : Integer.Sparse Master := [(Sum.inr 3108, 12622627890148147200000)]

def reducedTerm1197 : Integer.Sparse Master := [(Sum.inl 0, -78638483840510361600), (Sum.inl 1, 23128965835444224000), (Sum.inl 2, -92515863341776896000), (Sum.inl 3, -370063453367107584000), (Sum.inl 4, -185031726683553792000), (Sum.inl 26, -185031726683553792000)]

def reducedTerm1198 : Integer.Sparse Master := [(Sum.inl 0, -18745441903912550400), (Sum.inl 1, 39464088218763264000), (Sum.inl 2, 24665055136727040000), (Sum.inl 3, 78928176437526528000)]

def reducedTerm1199 : Integer.Sparse Master := []

def reducedTerm1200 : Integer.Sparse Master := []

def reducedTerm1201 : Integer.Sparse Master := [(Sum.inl 0, -32828912319445401600), (Sum.inl 1, 25917562357456896000), (Sum.inl 2, 34556749809942528000), (Sum.inl 26, 138226999239770112000)]

def reducedTerm1202 : Integer.Sparse Master := []

def reducedTerm1203 : Integer.Sparse Master := [(Sum.inr 3118, 6748651458342420480000)]

def reducedTerm1204 : Integer.Sparse Master := [(Sum.inl 0, -77539934375247052800), (Sum.inl 1, 59646103365574656000), (Sum.inl 2, -89469155048361984000), (Sum.inl 3, 477168826924597248000), (Sum.inl 4, 477168826924597248000), (Sum.inl 26, 477168826924597248000)]

def reducedTerm1205 : Integer.Sparse Master := [(Sum.inl 0, -2621271453179904000), (Sum.inl 1, 7863814359539712000), (Sum.inl 2, 5242542906359808000), (Sum.inl 26, -41940343250878464000)]

def reducedTerm1206 : Integer.Sparse Master := [(Sum.inr 3127, -2711226786498478080000)]

def reducedTerm1207 : Integer.Sparse Master := [(Sum.inr 3128, -814591422450892800000)]

def reducedTerm1208 : Integer.Sparse Master := [(Sum.inr 3129, -6439173843973570560000)]

def reducedTerm1209 : Integer.Sparse Master := [(Sum.inr 3130, -2879161744832593920000)]

def reducedTerm1210 : Integer.Sparse Master := [(Sum.inr 3131, -16011049661961338880000)]

def reducedTerm1211 : Integer.Sparse Master := [(Sum.inr 3132, 814591422450892800000)]

def reducedTerm1212 : Integer.Sparse Master := [(Sum.inr 3133, -616542244556636160000)]

def reducedTerm1213 : Integer.Sparse Master := [(Sum.inr 3134, 9470910448608215040000)]

def reducedTerm1214 : Integer.Sparse Master := [(Sum.inr 3136, 6932067331465543680000)]

def reducedTerm1215 : Integer.Sparse Master := [(Sum.inr 3137, 5023829814312960000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1216 : Integer.Sparse Master := [(Sum.inr 3138, 8259752936279900160000)]

def reducedTerm1217 : Integer.Sparse Master := [(Sum.inr 3155, 2995585454962114560000)]

def reducedTerm1218 : Integer.Sparse Master := [(Sum.inr 3156, -4348786044622602240000)]

def reducedTerm1219 : Integer.Sparse Master := [(Sum.inr 3158, -2995585454962114560000)]

def reducedTerm1220 : Integer.Sparse Master := [(Sum.inr 3161, 519512794327941120000)]

def reducedTerm1221 : Integer.Sparse Master := [(Sum.inr 3162, -6260504027114373120000)]

def reducedTerm1222 : Integer.Sparse Master := [(Sum.inr 3163, 10736042127096545280000)]

def reducedTerm1223 : Integer.Sparse Master := [(Sum.inr 3164, -9579839035999518720000)]

def reducedTerm1224 : Integer.Sparse Master := [(Sum.inr 3170, 6664563524103045120000)]

def reducedTerm1225 : Integer.Sparse Master := [(Sum.inr 3172, 9579839035999518720000)]

def reducedTerm1226 : Integer.Sparse Master := [(Sum.inr 3174, -10880841765483970560000)]

def reducedTerm1227 : Integer.Sparse Master := [(Sum.inr 3179, -8772590858152181760000)]

def reducedTerm1228 : Integer.Sparse Master := [(Sum.inr 3180, -8754560341097840640000)]

def reducedTerm1229 : Integer.Sparse Master := [(Sum.inr 3189, -1174798139719680000000)]

def reducedTerm1230 : Integer.Sparse Master := [(Sum.inr 3196, 6466249688175083520000)]

def reducedTerm1231 : Integer.Sparse Master := [(Sum.inr 3197, 1899117244195799040000)]

def reducedTerm1232 : Integer.Sparse Master := [(Sum.inr 3198, 419312052798750720000)]

def reducedTerm1233 : Integer.Sparse Master := [(Sum.inr 3199, 6894774206306058240000)]

def reducedTerm1234 : Integer.Sparse Master := [(Sum.inr 3202, 11475455859405619200000)]

def reducedTerm1235 : Integer.Sparse Master := [(Sum.inr 3221, -12951213345010483200000)]

def reducedTerm1236 : Integer.Sparse Master := [(Sum.inr 3222, -12438782405973245952000)]

def reducedTerm1237 : Integer.Sparse Master := [(Sum.inl 0, -24418675486369382400), (Sum.inl 1, 23479495659970560000), (Sum.inl 2, -4695899131994112000), (Sum.inl 3, -150268772223811584000), (Sum.inl 12, -75134386111905792000), (Sum.inl 13, -225403158335717376000)]

def reducedTerm1238 : Integer.Sparse Master := [(Sum.inl 0, -18204340967453491200), (Sum.inl 1, -45510852418633728000), (Sum.inl 2, 45510852418633728000), (Sum.inl 12, 121362273116356608000), (Sum.inl 13, 242724546232713216000)]

def reducedTerm1239 : Integer.Sparse Master := [(Sum.inl 0, -11961523278544896000), (Sum.inl 1, 43858918687997952000), (Sum.inl 2, 31897395409453056000), (Sum.inl 3, 63794790818906112000), (Sum.inl 13, 63794790818906112000)]

def reducedTerm1240 : Integer.Sparse Master := [(Sum.inl 0, 28204687086582988800), (Sum.inl 1, 249503001150541824000), (Sum.inl 2, 86783652574101504000), (Sum.inl 3, -347134610296406016000), (Sum.inl 12, -86783652574101504000), (Sum.inl 13, -347134610296406016000)]

def reducedTerm1241 : Integer.Sparse Master := [(Sum.inl 0, 22026375546126336000), (Sum.inl 1, -3337329628200960000), (Sum.inl 2, -13349318512803840000), (Sum.inl 3, 53397274051215360000), (Sum.inl 13, 53397274051215360000)]

def reducedTerm1242 : Integer.Sparse Master := []

def reducedTerm1243 : Integer.Sparse Master := []

def reducedTerm1244 : Integer.Sparse Master := []

def reducedTerm1245 : Integer.Sparse Master := []

def reducedTerm1246 : Integer.Sparse Master := [(Sum.inr 3255, 1331003266183987200000)]

def reducedTerm1247 : Integer.Sparse Master := [(Sum.inr 3257, 5933039869919232000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1248 : Integer.Sparse Master := [(Sum.inr 3258, -1531997227471011840000)]

def reducedTerm1249 : Integer.Sparse Master := [(Sum.inr 3259, 9156607353476481024000)]

def reducedTerm1250 : Integer.Sparse Master := [(Sum.inr 3260, 1182595905074626560000)]

def reducedTerm1251 : Integer.Sparse Master := [(Sum.inr 3261, 270860476671590400000)]

def reducedTerm1252 : Integer.Sparse Master := [(Sum.inr 3262, 1979586319187312640000)]

def reducedTerm1253 : Integer.Sparse Master := [(Sum.inr 3266, 3863114615263002624000)]

def reducedTerm1254 : Integer.Sparse Master := [(Sum.inr 3267, 53914691091824640000)]

def reducedTerm1255 : Integer.Sparse Master := [(Sum.inr 3268, -2204937138861047808000)]

def reducedTerm1256 : Integer.Sparse Master := [(Sum.inr 3271, -2066297949707894784000)]

def reducedTerm1257 : Integer.Sparse Master := [(Sum.inr 3272, -992147345927700480000)]

def reducedTerm1258 : Integer.Sparse Master := [(Sum.inr 3288, 305084947161415680000)]

def reducedTerm1259 : Integer.Sparse Master := [(Sum.inr 3289, 2654462499211837440000)]

def reducedTerm1260 : Integer.Sparse Master := [(Sum.inr 3290, 1619043489526579200000)]

def reducedTerm1261 : Integer.Sparse Master := [(Sum.inr 3291, -1521451825330913280000)]

def reducedTerm1262 : Integer.Sparse Master := [(Sum.inr 3294, -8946502007384309760000)]

def reducedTerm1263 : Integer.Sparse Master := [(Sum.inr 3295, -3789395265230733312000)]

def reducedTerm1264 : Integer.Sparse Master := [(Sum.inr 3296, -9536788940949946368000)]

def reducedTerm1265 : Integer.Sparse Master := [(Sum.inr 3297, -1889903966198169600000)]

def reducedTerm1266 : Integer.Sparse Master := [(Sum.inr 3298, 752859079780663296000)]

def reducedTerm1267 : Integer.Sparse Master := [(Sum.inr 3302, -1389583379072286720000)]

def reducedTerm1268 : Integer.Sparse Master := [(Sum.inr 3303, -565455270900989952000)]

def reducedTerm1269 : Integer.Sparse Master := [(Sum.inr 3306, -186994987012915200000)]

def reducedTerm1270 : Integer.Sparse Master := [(Sum.inr 3365, 4501291376384409600000)]

def reducedTerm1271 : Integer.Sparse Master := [(Sum.inr 3375, 654308882759024640000)]

def reducedTerm1272 : Integer.Sparse Master := [(Sum.inr 3376, -4735033992735621120000)]

def reducedTerm1273 : Integer.Sparse Master := [(Sum.inr 3378, 4935862034835701760000)]

def reducedTerm1274 : Integer.Sparse Master := [(Sum.inr 3379, -379671498467573760000)]

def reducedTerm1275 : Integer.Sparse Master := [(Sum.inr 3380, 2452540759969628160000)]

def reducedTerm1276 : Integer.Sparse Master := [(Sum.inr 3388, 28541892592926720000)]

def reducedTerm1277 : Integer.Sparse Master := [(Sum.inr 3390, -2426340427298242560000)]

def reducedTerm1278 : Integer.Sparse Master := [(Sum.inr 3391, -3915341740423249920000)]

def reducedTerm1279 : Integer.Sparse Master := [(Sum.inr 3392, -57083785185853440000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm128 : Integer.Sparse Master := [(Sum.inl 0, 112680633469501440000), (Sum.inl 1, -352126979592192000000), (Sum.inl 2, -305176715646566400000), (Sum.inl 5, 187801055782502400000), (Sum.inl 6, -46950263945625600000), (Sum.inl 9, 93900527891251200000), (Sum.inl 54, -1126806334695014400000), (Sum.inl 62, -1126806334695014400000), (Sum.inl 68, -281701583673753600000), (Sum.inl 260, -1126806334695014400000), (Sum.inl 264, -1126806334695014400000)]

def reducedTerm129 : Integer.Sparse Master := [(Sum.inl 0, 251268317695180800000), (Sum.inl 1, 837561058983936000000), (Sum.inl 2, -418780529491968000000), (Sum.inl 5, 209390264745984000000), (Sum.inl 23, -2512683176951808000000), (Sum.inl 27, -628170794237952000000), (Sum.inl 54, -2512683176951808000000), (Sum.inl 68, -1256341588475904000000), (Sum.inl 125, -2512683176951808000000), (Sum.inl 196, -2512683176951808000000)]

def reducedTerm130 : Integer.Sparse Master := [(Sum.inl 0, 13880764064563200000), (Sum.inl 1, -4957415737344000000), (Sum.inl 2, 4957415737344000000), (Sum.inl 5, 9914831474688000000), (Sum.inl 24, -118977977696256000000), (Sum.inl 27, -29744494424064000000), (Sum.inl 56, -118977977696256000000), (Sum.inl 68, -59488988848128000000), (Sum.inl 197, -237955955392512000000)]

def reducedTerm131 : Integer.Sparse Master := [(Sum.inl 0, -37388795609088000000), (Sum.inl 1, 101969442570240000000), (Sum.inl 2, 50984721285120000000), (Sum.inl 5, -33989814190080000000), (Sum.inl 27, 101969442570240000000), (Sum.inl 68, 203938885140480000000), (Sum.inl 263, -815755540561920000000)]

def reducedTerm132 : Integer.Sparse Master := [(Sum.inl 0, -49831197923082240000), (Sum.inl 1, -249155989615411200000), (Sum.inl 2, -249155989615411200000), (Sum.inl 68, -249155989615411200000), (Sum.inl 196, -996623958461644800000)]

def reducedTerm133 : Integer.Sparse Master := [(Sum.inl 0, -64451690672947200000), (Sum.inl 1, 128903381345894400000), (Sum.inl 2, 64451690672947200000), (Sum.inl 68, -257806762691788800000), (Sum.inl 197, -1031227050767155200000)]

def reducedTerm134 : Integer.Sparse Master := [(Sum.inl 0, -158195148400558080000), (Sum.inl 1, -593231806502092800000), (Sum.inl 2, 197743935500697600000), (Sum.inl 68, -790975742002790400000), (Sum.inl 125, -3163902968011161600000)]

def reducedTerm135 : Integer.Sparse Master := [(Sum.inl 0, -18952681598484480000), (Sum.inl 1, 23690851998105600000), (Sum.inl 2, -71072555994316800000), (Sum.inl 68, -94763407992422400000), (Sum.inl 264, -379053631969689600000)]

def reducedTerm136 : Integer.Sparse Master := [(Sum.inl 0, -6977216593428480000), (Sum.inl 1, -23869425188044800000), (Sum.inl 2, -27541644447744000000), (Sum.inl 3, 88133262232780800000), (Sum.inl 5, 44066631116390400000), (Sum.inl 6, -5508328889548800000), (Sum.inl 9, 7344438519398400000), (Sum.inl 13, 29377754077593600000), (Sum.inl 26, 176266524465561600000), (Sum.inl 27, -66099946674585600000), (Sum.inl 34, 88133262232780800000), (Sum.inl 35, 88133262232780800000), (Sum.inl 54, -264399786698342400000), (Sum.inl 65, -264399786698342400000), (Sum.inl 67, 88133262232780800000), (Sum.inl 68, -110166577790976000000), (Sum.inl 257, 29377754077593600000), (Sum.inl 264, -176266524465561600000), (Sum.inl 266, -264399786698342400000)]

def reducedTerm137 : Integer.Sparse Master := [(Sum.inl 0, 8078882371338240000), (Sum.inl 1, -3672219259699200000), (Sum.inl 2, -11016657779097600000), (Sum.inl 5, 14688877038796800000), (Sum.inl 6, -3672219259699200000), (Sum.inl 9, 7344438519398400000), (Sum.inl 26, 58755508155187200000), (Sum.inl 34, 29377754077593600000), (Sum.inl 35, 58755508155187200000), (Sum.inl 67, 58755508155187200000), (Sum.inl 68, -22033315558195200000), (Sum.inl 257, 29377754077593600000), (Sum.inl 266, -88133262232780800000)]

def reducedTerm138 : Integer.Sparse Master := [(Sum.inl 0, 144001237266432000000), (Sum.inl 1, 288002474532864000000), (Sum.inl 2, 252002165216256000000), (Sum.inl 3, -2304019796262912000000), (Sum.inl 5, -864007423598592000000), (Sum.inl 6, 108000927949824000000), (Sum.inl 9, -144001237266432000000), (Sum.inl 12, -1152009898131456000000), (Sum.inl 13, -3456029694394368000000), (Sum.inl 26, -1152009898131456000000), (Sum.inl 27, 1296011135397888000000), (Sum.inl 32, -576004949065728000000), (Sum.inl 34, -1152009898131456000000), (Sum.inl 35, -1728014847197184000000), (Sum.inl 54, 1728014847197184000000), (Sum.inl 55, 3456029694394368000000), (Sum.inl 60, -1152009898131456000000), (Sum.inl 61, 3456029694394368000000), (Sum.inl 65, 1728014847197184000000), (Sum.inl 67, -576004949065728000000), (Sum.inl 68, 2160018558996480000000), (Sum.inl 257, -576004949065728000000), (Sum.inl 264, 1728014847197184000000), (Sum.inl 266, 3456029694394368000000), (Sum.inl 268, 3456029694394368000000)]

def reducedTerm139 : Integer.Sparse Master := [(Sum.inl 0, 190081633191690240000), (Sum.inl 1, -129601113539788800000), (Sum.inl 2, -129601113539788800000), (Sum.inl 3, 691205938878873600000), (Sum.inl 5, 345602969439436800000), (Sum.inl 6, -86400742359859200000), (Sum.inl 9, 172801484719718400000), (Sum.inl 13, 691205938878873600000), (Sum.inl 26, 691205938878873600000), (Sum.inl 34, 691205938878873600000), (Sum.inl 35, 1382411877757747200000), (Sum.inl 60, 691205938878873600000), (Sum.inl 67, 691205938878873600000), (Sum.inl 68, -518404454159155200000), (Sum.inl 257, 691205938878873600000), (Sum.inl 268, -2073617816636620800000)]

def reducedTerm140 : Integer.Sparse Master := [(Sum.inl 0, 78417345665433600000), (Sum.inl 1, -228717258190848000000), (Sum.inl 2, -228717258190848000000), (Sum.inl 5, 65347788054528000000), (Sum.inl 27, -196043364163584000000), (Sum.inl 54, -784173456654336000000), (Sum.inl 65, -784173456654336000000), (Sum.inl 68, -392086728327168000000), (Sum.inl 264, -784173456654336000000), (Sum.inl 266, -784173456654336000000)]

def reducedTerm141 : Integer.Sparse Master := [(Sum.inl 0, -2611509059174400000), (Sum.inl 1, -2374099144704000000), (Sum.inl 2, -14244594868224000000), (Sum.inl 5, -4748198289408000000), (Sum.inl 6, 1187049572352000000), (Sum.inl 9, -2374099144704000000), (Sum.inl 13, -18992793157632000000), (Sum.inl 32, -9496396578816000000), (Sum.inl 35, -18992793157632000000), (Sum.inl 60, -18992793157632000000), (Sum.inl 68, 7122297434112000000), (Sum.inl 257, -9496396578816000000), (Sum.inl 264, 28489189736448000000)]

def reducedTerm142 : Integer.Sparse Master := [(Sum.inl 0, -190081633191690240000), (Sum.inl 1, 86400742359859200000), (Sum.inl 2, 172801484719718400000), (Sum.inl 5, -172801484719718400000), (Sum.inl 27, 518404454159155200000), (Sum.inl 55, 2073617816636620800000), (Sum.inl 61, 2073617816636620800000), (Sum.inl 68, 1036808908318310400000), (Sum.inl 266, 2073617816636620800000), (Sum.inl 268, 2073617816636620800000)]

def reducedTerm143 : Integer.Sparse Master := [(Sum.inl 0, -91214914532474880000), (Sum.inl 1, 228037286331187200000), (Sum.inl 2, 228037286331187200000), (Sum.inl 68, -456074572662374400000), (Sum.inl 266, -1824298290649497600000)]

def reducedTerm144 : Integer.Sparse Master := [(Sum.inl 0, -158401360993075200000), (Sum.inl 2, 72000618633216000000), (Sum.inl 68, -864007423598592000000), (Sum.inl 268, -3456029694394368000000)]

def reducedTerm145 : Integer.Sparse Master := [(Sum.inl 0, -71563296791347200000), (Sum.inl 1, 123384994467840000000), (Sum.inl 3, 789663964594176000000), (Sum.inl 5, -197415991148544000000), (Sum.inl 6, 123384994467840000000), (Sum.inl 7, 394831982297088000000), (Sum.inl 9, 49353997787136000000), (Sum.inl 13, 987079955742720000000), (Sum.inl 35, 789663964594176000000), (Sum.inl 52, 789663964594176000000), (Sum.inl 58, -12338499446784000000), (Sum.inl 68, -148061993361408000000), (Sum.inl 69, 197415991148544000000), (Sum.inl 70, 197415991148544000000), (Sum.inl 125, -592247973445632000000)]

def reducedTerm146 : Integer.Sparse Master := [(Sum.inl 0, -59296244178124800000), (Sum.inl 1, 80858514788352000000), (Sum.inl 2, 13476419131392000000), (Sum.inl 3, 862490824409088000000), (Sum.inl 5, 215622706102272000000), (Sum.inl 6, 53905676525568000000), (Sum.inl 9, 107811353051136000000), (Sum.inl 12, 431245412204544000000), (Sum.inl 13, 2803095179329536000000), (Sum.inl 32, 646868118306816000000), (Sum.inl 35, 1078113530511360000000), (Sum.inl 52, 862490824409088000000), (Sum.inl 54, -646868118306816000000), (Sum.inl 58, -13476419131392000000), (Sum.inl 60, 1078113530511360000000), (Sum.inl 62, -1293736236613632000000), (Sum.inl 68, -161717029576704000000), (Sum.inl 128, 431245412204544000000), (Sum.inl 257, 215622706102272000000), (Sum.inl 260, -646868118306816000000), (Sum.inl 264, -646868118306816000000), (Sum.inl 495, 215622706102272000000)]

def reducedTerm147 : Integer.Sparse Master := [(Sum.inl 0, 41416495368192000000), (Sum.inl 1, -124249486104576000000), (Sum.inl 2, -69027492280320000000), (Sum.inl 3, -441775950594048000000), (Sum.inl 5, 82832990736384000000), (Sum.inl 6, 13805498456064000000), (Sum.inl 7, -331331962945536000000), (Sum.inl 9, -55221993824256000000), (Sum.inl 12, -110443987648512000000), (Sum.inl 13, -441775950594048000000), (Sum.inl 23, 331331962945536000000), (Sum.inl 27, 82832990736384000000), (Sum.inl 35, -441775950594048000000), (Sum.inl 52, -220887975297024000000), (Sum.inl 54, 662663925891072000000), (Sum.inl 68, 165665981472768000000), (Sum.inl 69, -110443987648512000000), (Sum.inl 70, -110443987648512000000), (Sum.inl 125, 331331962945536000000), (Sum.inl 196, 331331962945536000000)]

def reducedTerm148 : Integer.Sparse Master := [(Sum.inl 0, 88626279245414400000), (Sum.inl 1, 98473643606016000000), (Sum.inl 2, 49236821803008000000), (Sum.inl 5, 344657752621056000000), (Sum.inl 8, -590841861636096000000), (Sum.inl 9, -98473643606016000000), (Sum.inl 24, 590841861636096000000), (Sum.inl 27, 147710465409024000000), (Sum.inl 56, 1181683723272192000000), (Sum.inl 68, 295420930818048000000), (Sum.inl 71, -393894574424064000000), (Sum.inl 197, 1181683723272192000000)]

def reducedTerm149 : Integer.Sparse Master := [(Sum.inl 0, -552349111910400000), (Sum.inl 1, 1196756409139200000), (Sum.inl 2, 460290926592000000), (Sum.inl 6, 184116370636800000), (Sum.inl 9, -368232741273600000), (Sum.inl 13, -1472930965094400000), (Sum.inl 52, -2945861930188800000), (Sum.inl 68, 1104698223820800000), (Sum.inl 69, -1472930965094400000), (Sum.inl 125, 4418792895283200000)]

def reducedTerm150 : Integer.Sparse Master := [(Sum.inl 0, -57972138835968000000), (Sum.inl 1, 72465173544960000000), (Sum.inl 2, -130437312380928000000), (Sum.inl 3, 927554221375488000000), (Sum.inl 4, 231888555343872000000), (Sum.inl 5, 173916416507904000000), (Sum.inl 6, 72465173544960000000), (Sum.inl 9, 115944277671936000000), (Sum.inl 13, 695665666031616000000), (Sum.inl 26, 695665666031616000000), (Sum.inl 34, 463777110687744000000), (Sum.inl 35, 927554221375488000000), (Sum.inl 52, 695665666031616000000), (Sum.inl 56, -695665666031616000000), (Sum.inl 58, -14493034708992000000), (Sum.inl 60, 463777110687744000000), (Sum.inl 67, 231888555343872000000), (Sum.inl 68, -173916416507904000000), (Sum.inl 128, 231888555343872000000), (Sum.inl 257, 231888555343872000000), (Sum.inl 262, -695665666031616000000), (Sum.inl 268, -695665666031616000000), (Sum.inl 495, 231888555343872000000)]

def reducedTerm151 : Integer.Sparse Master := [(Sum.inl 0, 57972138835968000000), (Sum.inl 1, 14493034708992000000), (Sum.inl 2, 72465173544960000000), (Sum.inl 3, -927554221375488000000), (Sum.inl 4, -231888555343872000000), (Sum.inl 5, -57972138835968000000), (Sum.inl 6, 57972138835968000000), (Sum.inl 9, -115944277671936000000), (Sum.inl 12, -463777110687744000000), (Sum.inl 13, -927554221375488000000), (Sum.inl 26, -231888555343872000000), (Sum.inl 27, 173916416507904000000), (Sum.inl 35, -463777110687744000000), (Sum.inl 51, 1391331332063232000000), (Sum.inl 54, 1391331332063232000000), (Sum.inl 55, 695665666031616000000), (Sum.inl 56, 1391331332063232000000), (Sum.inl 59, 695665666031616000000), (Sum.inl 61, 1391331332063232000000), (Sum.inl 68, 347832833015808000000), (Sum.inl 259, 695665666031616000000), (Sum.inl 262, 695665666031616000000), (Sum.inl 266, 695665666031616000000), (Sum.inl 268, 695665666031616000000)]

def reducedTerm152 : Integer.Sparse Master := [(Sum.inl 0, 7382985781248000000), (Sum.inl 1, -20135415767040000000), (Sum.inl 2, -13423610511360000000), (Sum.inl 5, 13423610511360000000), (Sum.inl 6, -3355902627840000000), (Sum.inl 9, 6711805255680000000), (Sum.inl 26, 26847221022720000000), (Sum.inl 35, 26847221022720000000), (Sum.inl 54, -80541663068160000000), (Sum.inl 68, -20135415767040000000), (Sum.inl 259, -80541663068160000000), (Sum.inl 266, -80541663068160000000)]

def reducedTerm153 : Integer.Sparse Master := [(Sum.inl 0, -56114301693542400000), (Sum.inl 2, 25506500769792000000), (Sum.inl 3, 816208024633344000000), (Sum.inl 5, -102026003079168000000), (Sum.inl 12, 204052006158336000000), (Sum.inl 13, 3264832098533376000000), (Sum.inl 32, 816208024633344000000), (Sum.inl 35, 816208024633344000000), (Sum.inl 52, 816208024633344000000), (Sum.inl 60, 816208024633344000000), (Sum.inl 62, -1224312036950016000000), (Sum.inl 128, 204052006158336000000)]

def reducedTerm154 : Integer.Sparse Master := [(Sum.inl 0, 12440199254999040000), (Sum.inl 1, -14809761017856000000), (Sum.inl 2, -17771713221427200000), (Sum.inl 3, -47391235257139200000), (Sum.inl 5, 23695617628569600000), (Sum.inl 6, -5923904407142400000), (Sum.inl 7, -23695617628569600000), (Sum.inl 13, -23695617628569600000), (Sum.inl 26, -47391235257139200000), (Sum.inl 35, -47391235257139200000), (Sum.inl 54, 71086852885708800000)]

def reducedTerm155 : Integer.Sparse Master := [(Sum.inl 0, -7954874605117440000), (Sum.inl 1, -18274711930675200000), (Sum.inl 2, -7524881383219200000), (Sum.inl 3, 51599186627788800000), (Sum.inl 4, 17199728875929600000), (Sum.inl 5, -21499661094912000000), (Sum.inl 6, 3224949164236800000), (Sum.inl 8, 17199728875929600000), (Sum.inl 13, 34399457751859200000), (Sum.inl 26, 17199728875929600000), (Sum.inl 35, 17199728875929600000), (Sum.inl 52, 17199728875929600000), (Sum.inl 56, -51599186627788800000)]

def reducedTerm156 : Integer.Sparse Master := [(Sum.inl 0, -11255418373570560000), (Sum.inl 1, 11847808814284800000), (Sum.inl 2, 14809761017856000000), (Sum.inl 5, 5923904407142400000), (Sum.inl 6, -5923904407142400000), (Sum.inl 26, -23695617628569600000), (Sum.inl 35, -23695617628569600000)]

def reducedTerm157 : Integer.Sparse Master := [(Sum.inl 0, -40854277638881280000), (Sum.inl 1, -85662195049267200000), (Sum.inl 2, -13178799238348800000), (Sum.inl 3, 843443151254323200000), (Sum.inl 5, -79072795430092800000), (Sum.inl 6, 13178799238348800000), (Sum.inl 7, 105430393906790400000), (Sum.inl 12, 421721575627161600000), (Sum.inl 13, 948873545161113600000), (Sum.inl 35, 316291181720371200000), (Sum.inl 52, 210860787813580800000), (Sum.inl 54, -316291181720371200000)]

def reducedTerm158 : Integer.Sparse Master := [(Sum.inl 0, 62090278138183680000), (Sum.inl 1, 80487397586534400000), (Sum.inl 2, 11498199655219200000), (Sum.inl 3, 183971194483507200000), (Sum.inl 5, -45992798620876800000), (Sum.inl 6, 34494598965657600000), (Sum.inl 13, 367942388967014400000), (Sum.inl 35, 183971194483507200000), (Sum.inl 52, 183971194483507200000)]

def reducedTerm159 : Integer.Sparse Master := [(Sum.inl 0, 125222731936727040000), (Sum.inl 1, 113838847215206400000), (Sum.inl 2, -113838847215206400000), (Sum.inl 3, 455355388860825600000), (Sum.inl 6, 56919423607603200000), (Sum.inl 13, 1366066166582476800000), (Sum.inl 32, 455355388860825600000), (Sum.inl 35, 455355388860825600000), (Sum.inl 52, 455355388860825600000), (Sum.inl 60, 455355388860825600000), (Sum.inl 62, -1366066166582476800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1280 : Integer.Sparse Master := [(Sum.inr 3394, 6542432374534963200000)]

def reducedTerm1281 : Integer.Sparse Master := [(Sum.inr 3395, 16453451164259450880000)]

def reducedTerm1282 : Integer.Sparse Master := [(Sum.inr 3396, 10440815232685178880000)]

def reducedTerm1283 : Integer.Sparse Master := [(Sum.inr 3397, -684291540819640320000)]

def reducedTerm1284 : Integer.Sparse Master := [(Sum.inr 3406, 652996879610019840000)]

def reducedTerm1285 : Integer.Sparse Master := [(Sum.inr 3407, 3344441963460820992000)]

def reducedTerm1286 : Integer.Sparse Master := [(Sum.inr 3408, -1985415998552211456000)]

def reducedTerm1287 : Integer.Sparse Master := [(Sum.inr 3413, -2989726119329660928000)]

def reducedTerm1288 : Integer.Sparse Master := [(Sum.inr 3414, 355417517501448192000)]

def reducedTerm1289 : Integer.Sparse Master := [(Sum.inr 3415, -1559990074286407680000)]

def reducedTerm1290 : Integer.Sparse Master := [(Sum.inr 3418, -354715844131160064000)]

def reducedTerm1291 : Integer.Sparse Master := [(Sum.inr 3419, 814999240525381632000)]

def reducedTerm1292 : Integer.Sparse Master := [(Sum.inr 3451, 744619799330684928000)]

def reducedTerm1293 : Integer.Sparse Master := [(Sum.inr 3452, 4783674936826920960000)]

def reducedTerm1294 : Integer.Sparse Master := [(Sum.inr 3454, 5808432531870646272000)]

def reducedTerm1295 : Integer.Sparse Master := [(Sum.inr 3458, 23220776228880384000)]

def reducedTerm1296 : Integer.Sparse Master := [(Sum.inr 3461, 2229127337632333824000)]

def reducedTerm1297 : Integer.Sparse Master := [(Sum.inr 3462, -2370794412740640768000)]

def reducedTerm1298 : Integer.Sparse Master := [(Sum.inr 3463, -3066113985645182976000)]

def reducedTerm1299 : Integer.Sparse Master := [(Sum.inr 3464, 3058373744961454080000)]

def reducedTerm1300 : Integer.Sparse Master := [(Sum.inr 3465, -722635406229897216000)]

def reducedTerm1301 : Integer.Sparse Master := [(Sum.inr 3466, -3632663000341315584000)]

def reducedTerm1302 : Integer.Sparse Master := [(Sum.inr 3472, 506711554922151936000)]

def reducedTerm1303 : Integer.Sparse Master := [(Sum.inr 3474, -1835451633733337088000)]

def reducedTerm1304 : Integer.Sparse Master := [(Sum.inr 3475, -4633408883520700416000)]

def reducedTerm1305 : Integer.Sparse Master := [(Sum.inr 3476, 1856913308405858304000)]

def reducedTerm1306 : Integer.Sparse Master := [(Sum.inr 3480, -4726817018446086144000)]

def reducedTerm1307 : Integer.Sparse Master := [(Sum.inr 3488, -416003421044736000000)]

def reducedTerm1308 : Integer.Sparse Master := [(Sum.inr 3493, 4958849630270914560000)]

def reducedTerm1309 : Integer.Sparse Master := [(Sum.inr 3496, -8093713655448207360000)]

def reducedTerm1310 : Integer.Sparse Master := [(Sum.inr 3497, -416003421044736000000)]

def reducedTerm1311 : Integer.Sparse Master := [(Sum.inr 3505, 7799955337720627200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1312 : Integer.Sparse Master := [(Sum.inr 3506, -3146577964923617280000)]

def reducedTerm1313 : Integer.Sparse Master := [(Sum.inr 3508, -1421726643557498880000)]

def reducedTerm1314 : Integer.Sparse Master := [(Sum.inr 3509, 7390298065975050240000)]

def reducedTerm1315 : Integer.Sparse Master := [(Sum.inr 3510, -1331003266183987200000)]

def reducedTerm1316 : Integer.Sparse Master := [(Sum.inr 3511, -270860476671590400000)]

def reducedTerm1317 : Integer.Sparse Master := [(Sum.inr 3512, -3141806478252244992000)]

def reducedTerm1318 : Integer.Sparse Master := [(Sum.inr 3516, 1646462429022781440000)]

def reducedTerm1319 : Integer.Sparse Master := [(Sum.inr 3517, 3031883170345451520000)]

def reducedTerm1320 : Integer.Sparse Master := [(Sum.inr 3519, -500927005576101888000)]

def reducedTerm1321 : Integer.Sparse Master := [(Sum.inr 3523, -12294580299389337600000)]

def reducedTerm1322 : Integer.Sparse Master := [(Sum.inr 3524, -1072771597873446912000)]

def reducedTerm1323 : Integer.Sparse Master := []

def reducedTerm1324 : Integer.Sparse Master := [(Sum.inr 3526, -8846701964077694976000)]

def reducedTerm1325 : Integer.Sparse Master := [(Sum.inr 3529, 2431584286271078400000)]

def reducedTerm1326 : Integer.Sparse Master := [(Sum.inr 3530, 6558674437762449408000)]

def reducedTerm1327 : Integer.Sparse Master := [(Sum.inr 3532, -1598770106249379840000)]

def reducedTerm1328 : Integer.Sparse Master := [(Sum.inr 3533, -1975281871324446720000)]

def reducedTerm1329 : Integer.Sparse Master := [(Sum.inr 3534, 26110149656309268480000)]

def reducedTerm1330 : Integer.Sparse Master := [(Sum.inr 3535, 4491472530225364992000)]

def reducedTerm1331 : Integer.Sparse Master := [(Sum.inr 3537, 7698731041103413248000)]

def reducedTerm1332 : Integer.Sparse Master := [(Sum.inr 3538, 1252704393088598016000)]

def reducedTerm1333 : Integer.Sparse Master := [(Sum.inr 3539, 6590198986965909504000)]

def reducedTerm1334 : Integer.Sparse Master := [(Sum.inr 3540, 442881254805405696000)]

def reducedTerm1335 : Integer.Sparse Master := [(Sum.inr 3541, -2683554743866687488000)]

def reducedTerm1336 : Integer.Sparse Master := [(Sum.inr 3542, -1438088403369590784000)]

def reducedTerm1337 : Integer.Sparse Master := [(Sum.inr 3543, -3946797413223727104000)]

def reducedTerm1338 : Integer.Sparse Master := [(Sum.inr 3544, -2488508247260528640000)]

def reducedTerm1339 : Integer.Sparse Master := []

def reducedTerm1340 : Integer.Sparse Master := [(Sum.inr 3548, -1028860950356951040000)]

def reducedTerm1341 : Integer.Sparse Master := [(Sum.inr 3549, 1255758373127946240000)]

def reducedTerm1342 : Integer.Sparse Master := [(Sum.inr 3553, -1133832859511095296000)]

def reducedTerm1343 : Integer.Sparse Master := [(Sum.inr 3554, -5933039869919232000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1344 : Integer.Sparse Master := [(Sum.inr 3555, -5743947411554107392000)]

def reducedTerm1345 : Integer.Sparse Master := [(Sum.inr 3556, -1645301575619444736000)]

def reducedTerm1346 : Integer.Sparse Master := [(Sum.inr 3557, 900394580334477312000)]

def reducedTerm1347 : Integer.Sparse Master := [(Sum.inr 3558, 8704054146298871808000)]

def reducedTerm1348 : Integer.Sparse Master := [(Sum.inr 3562, 2987270009704415232000)]

def reducedTerm1349 : Integer.Sparse Master := [(Sum.inr 3565, 5653339486845861888000)]

def reducedTerm1350 : Integer.Sparse Master := [(Sum.inr 3569, 1962225745433985024000)]

def reducedTerm1351 : Integer.Sparse Master := [(Sum.inr 3570, 2433073703307706368000)]

def reducedTerm1352 : Integer.Sparse Master := [(Sum.inr 3571, 12926463385317801984000)]

def reducedTerm1353 : Integer.Sparse Master := [(Sum.inr 3572, -16798163909915049984000)]

def reducedTerm1354 : Integer.Sparse Master := [(Sum.inr 3573, 19725678159807578112000)]

def reducedTerm1355 : Integer.Sparse Master := [(Sum.inr 3577, 4629005356695552000000)]

def reducedTerm1356 : Integer.Sparse Master := [(Sum.inr 3578, 13978224602687471616000)]

def reducedTerm1357 : Integer.Sparse Master := [(Sum.inr 3579, 4549640633792593920000)]

def reducedTerm1358 : Integer.Sparse Master := [(Sum.inr 3580, 831414264535056384000)]

def reducedTerm1359 : Integer.Sparse Master := [(Sum.inr 3581, -220499962681098240000)]

def reducedTerm1360 : Integer.Sparse Master := [(Sum.inr 3582, 4158174109630464000000)]

def reducedTerm1361 : Integer.Sparse Master := [(Sum.inr 3583, -11906431827880181760000)]

def reducedTerm1362 : Integer.Sparse Master := [(Sum.inr 3584, 29008204646800490496000)]

def reducedTerm1363 : Integer.Sparse Master := []

def reducedTerm1364 : Integer.Sparse Master := [(Sum.inr 3619, -9131775422933237760000)]

def reducedTerm1365 : Integer.Sparse Master := [(Sum.inr 3622, 13643436319594905600000)]

def reducedTerm1366 : Integer.Sparse Master := [(Sum.inr 3623, -6320730118534594560000)]

def reducedTerm1367 : Integer.Sparse Master := [(Sum.inr 3625, 3684922744987975680000)]

def reducedTerm1368 : Integer.Sparse Master := [(Sum.inr 3626, 5131131445562572800000)]

def reducedTerm1369 : Integer.Sparse Master := [(Sum.inr 3627, 7417776676181114880000)]

def reducedTerm1370 : Integer.Sparse Master := []

def reducedTerm1371 : Integer.Sparse Master := []

def reducedTerm1372 : Integer.Sparse Master := [(Sum.inr 3632, -3609060248797839360000)]

def reducedTerm1373 : Integer.Sparse Master := [(Sum.inr 3633, 17665403553650442240000)]

def reducedTerm1374 : Integer.Sparse Master := []

def reducedTerm1375 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1376 : Integer.Sparse Master := [(Sum.inr 3670, -3558260895488409600000)]

def reducedTerm1377 : Integer.Sparse Master := [(Sum.inr 3671, 2856821572837048320000)]

def reducedTerm1378 : Integer.Sparse Master := [(Sum.inr 3672, 8029997437000089600000)]

def reducedTerm1379 : Integer.Sparse Master := [(Sum.inr 3673, -2089015568665804800000)]

def reducedTerm1380 : Integer.Sparse Master := [(Sum.inr 3674, -3375760173907968000000)]

def reducedTerm1381 : Integer.Sparse Master := [(Sum.inr 3676, 2139241300593868800000)]

def reducedTerm1382 : Integer.Sparse Master := [(Sum.inr 3685, -669848715789926400000)]

def reducedTerm1383 : Integer.Sparse Master := [(Sum.inr 3689, 5058598529834680320000)]

def reducedTerm1384 : Integer.Sparse Master := [(Sum.inr 3690, -2714220736148275200000)]

def reducedTerm1385 : Integer.Sparse Master := [(Sum.inr 3692, -5214891424162775040000)]

def reducedTerm1386 : Integer.Sparse Master := [(Sum.inr 3693, -1773350590788403200000)]

def reducedTerm1387 : Integer.Sparse Master := [(Sum.inr 3694, -5315776700851814400000)]

def reducedTerm1388 : Integer.Sparse Master := [(Sum.inr 3698, 3611345102733312000000)]

def reducedTerm1389 : Integer.Sparse Master := [(Sum.inr 3699, 3293229788164915200000)]

def reducedTerm1390 : Integer.Sparse Master := [(Sum.inr 3703, -6378432071205519360000)]

def reducedTerm1391 : Integer.Sparse Master := [(Sum.inr 3705, 8915230341595791360000)]

def reducedTerm1392 : Integer.Sparse Master := [(Sum.inr 3706, -10603132867144581120000)]

def reducedTerm1393 : Integer.Sparse Master := [(Sum.inr 3708, 23153419811192832000000)]

def reducedTerm1394 : Integer.Sparse Master := [(Sum.inr 3709, 7818430382751744000000)]

def reducedTerm1395 : Integer.Sparse Master := [(Sum.inr 3710, 3622287461825249280000)]

def reducedTerm1396 : Integer.Sparse Master := [(Sum.inr 3715, 11249654248211742720000)]

def reducedTerm1397 : Integer.Sparse Master := [(Sum.inr 3719, 7397988905631744000000)]

def reducedTerm1398 : Integer.Sparse Master := [(Sum.inr 3720, 6831804330736680960000)]

def reducedTerm1399 : Integer.Sparse Master := [(Sum.inr 3721, 12949195045327994880000)]

def reducedTerm1400 : Integer.Sparse Master := [(Sum.inr 3722, -26217469888567050240000)]

def reducedTerm1401 : Integer.Sparse Master := [(Sum.inr 3723, 3090408338022727680000)]

def reducedTerm1402 : Integer.Sparse Master := [(Sum.inr 3724, -12931866039110860800000)]

def reducedTerm1403 : Integer.Sparse Master := [(Sum.inr 3730, 498588466060984320000)]

def reducedTerm1404 : Integer.Sparse Master := [(Sum.inr 3731, -4479366205522575360000)]

def reducedTerm1405 : Integer.Sparse Master := [(Sum.inr 3732, -15823981309321543680000)]

def reducedTerm1406 : Integer.Sparse Master := [(Sum.inr 3733, 1301788622079590400000)]

def reducedTerm1407 : Integer.Sparse Master := [(Sum.inr 3755, 885060905467576320000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1408 : Integer.Sparse Master := [(Sum.inr 3759, -2229127337632333824000)]

def reducedTerm1409 : Integer.Sparse Master := [(Sum.inr 3760, 7779502517921906688000)]

def reducedTerm1410 : Integer.Sparse Master := [(Sum.inr 3761, -2581778767834054656000)]

def reducedTerm1411 : Integer.Sparse Master := [(Sum.inr 3762, -3482485535088967680000)]

def reducedTerm1412 : Integer.Sparse Master := [(Sum.inr 3763, 722635406229897216000)]

def reducedTerm1413 : Integer.Sparse Master := [(Sum.inr 3768, -629877478875660288000)]

def reducedTerm1414 : Integer.Sparse Master := [(Sum.inr 3772, -1457354951397015552000)]

def reducedTerm1415 : Integer.Sparse Master := [(Sum.inr 3779, -23279727428871782400000)]

def reducedTerm1416 : Integer.Sparse Master := [(Sum.inr 3780, 4493455024472064000000)]

def reducedTerm1417 : Integer.Sparse Master := [(Sum.inr 3781, 1745085365617950720000)]

def reducedTerm1418 : Integer.Sparse Master := [(Sum.inr 3782, -4452974806184755200000)]

def reducedTerm1419 : Integer.Sparse Master := [(Sum.inr 3783, 1278536233166438400000)]

def reducedTerm1420 : Integer.Sparse Master := [(Sum.inr 3786, 5625894605263994880000)]

def reducedTerm1421 : Integer.Sparse Master := [(Sum.inr 3787, -16392111811529932800000)]

def reducedTerm1422 : Integer.Sparse Master := [(Sum.inr 3788, 2738043209843343360000)]

def reducedTerm1423 : Integer.Sparse Master := [(Sum.inr 3789, 1441864010724802560000)]

def reducedTerm1424 : Integer.Sparse Master := [(Sum.inr 3800, 26650108359770112000000)]

def reducedTerm1425 : Integer.Sparse Master := [(Sum.inr 3801, -13178290840890900480000)]

def reducedTerm1426 : Integer.Sparse Master := [(Sum.inr 3802, -5516271414691430400000)]

def reducedTerm1427 : Integer.Sparse Master := [(Sum.inr 3803, -6944207726412988416000)]

def reducedTerm1428 : Integer.Sparse Master := [(Sum.inr 3805, 5260225873509089280000)]

def reducedTerm1429 : Integer.Sparse Master := []

def reducedTerm1430 : Integer.Sparse Master := []

def reducedTerm1431 : Integer.Sparse Master := []

def reducedTerm1432 : Integer.Sparse Master := [(Sum.inr 3809, -28544727109663457280000)]

def reducedTerm1433 : Integer.Sparse Master := [(Sum.inr 3812, 10099373456256860160000)]

def reducedTerm1434 : Integer.Sparse Master := [(Sum.inr 3813, -31930167407745761280000)]

def reducedTerm1435 : Integer.Sparse Master := [(Sum.inr 3814, -18142276456326758400000)]

def reducedTerm1436 : Integer.Sparse Master := []

def reducedTerm1437 : Integer.Sparse Master := []

def reducedTerm1438 : Integer.Sparse Master := [(Sum.inr 3819, 2089015568665804800000)]

def reducedTerm1439 : Integer.Sparse Master := [(Sum.inr 3826, -8130580131269836800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1440 : Integer.Sparse Master := [(Sum.inr 3827, -27260971487782502400000)]

def reducedTerm1441 : Integer.Sparse Master := [(Sum.inr 3832, 7114320400788357120000)]

def reducedTerm1442 : Integer.Sparse Master := [(Sum.inr 3833, 68789051986378752000)]

def reducedTerm1443 : Integer.Sparse Master := [(Sum.inr 3834, 6338956605336649728000)]

def reducedTerm1444 : Integer.Sparse Master := [(Sum.inr 3835, 1889903966198169600000)]

def reducedTerm1445 : Integer.Sparse Master := [(Sum.inr 3837, -19725399924241858560000)]

def reducedTerm1446 : Integer.Sparse Master := [(Sum.inr 3838, 18242460342573465600000)]

def reducedTerm1447 : Integer.Sparse Master := [(Sum.inr 3839, 12880096071349764096000)]

def reducedTerm1448 : Integer.Sparse Master := [(Sum.inr 3840, 31561229726387601408000)]

def reducedTerm1449 : Integer.Sparse Master := [(Sum.inr 3841, -20356532239770058752000)]

def reducedTerm1450 : Integer.Sparse Master := [(Sum.inr 3842, 1438088403369590784000)]

def reducedTerm1451 : Integer.Sparse Master := [(Sum.inr 3843, 6828082052291297280000)]

def reducedTerm1452 : Integer.Sparse Master := []

def reducedTerm1453 : Integer.Sparse Master := [(Sum.inr 3845, -34395325129220751360000)]

def reducedTerm1454 : Integer.Sparse Master := [(Sum.inr 3846, -12145658229120761856000)]

def reducedTerm1455 : Integer.Sparse Master := [(Sum.inl 0, 13747507650448588800), (Sum.inl 1, 249173576164380672000), (Sum.inl 2, -60145345970712576000), (Sum.inl 3, -1099800612035887104000), (Sum.inl 4, -274950153008971776000), (Sum.inl 12, -549900306017943552000), (Sum.inl 13, -412425229513457664000)]

def reducedTerm1456 : Integer.Sparse Master := [(Sum.inr 3848, -9902480791530700800000)]

def reducedTerm1457 : Integer.Sparse Master := [(Sum.inr 3849, -926150382019215360000)]

def reducedTerm1458 : Integer.Sparse Master := [(Sum.inr 3850, -7979084611521085440000)]

def reducedTerm1459 : Integer.Sparse Master := [(Sum.inr 3854, -911950238443732992000)]

def reducedTerm1460 : Integer.Sparse Master := [(Sum.inl 0, 2580311055819571200), (Sum.inl 1, 154818663349174272000), (Sum.inl 2, -38704665837293568000), (Sum.inl 3, -619274653396697088000), (Sum.inl 13, -412849768931131392000)]

def reducedTerm1461 : Integer.Sparse Master := [(Sum.inl 0, 6669814830000537600), (Sum.inl 1, 18527263416668160000), (Sum.inl 2, 7410905366667264000), (Sum.inl 3, 59287242933338112000), (Sum.inl 13, 59287242933338112000)]

def reducedTerm1462 : Integer.Sparse Master := [(Sum.inr 3857, 4770625125647646720000)]

def reducedTerm1463 : Integer.Sparse Master := [(Sum.inr 3866, 3337175163583070208000)]

def reducedTerm1464 : Integer.Sparse Master := [(Sum.inr 3868, 3405889229126565888000)]

def reducedTerm1465 : Integer.Sparse Master := [(Sum.inr 3869, -590135600217784320000)]

def reducedTerm1466 : Integer.Sparse Master := [(Sum.inr 3870, -2103251398787137536000)]

def reducedTerm1467 : Integer.Sparse Master := [(Sum.inr 3871, 11553704265979330560000)]

def reducedTerm1468 : Integer.Sparse Master := [(Sum.inr 3872, -5908225161862840320000)]

def reducedTerm1469 : Integer.Sparse Master := [(Sum.inr 3873, -7328462957249495040000)]

def reducedTerm1470 : Integer.Sparse Master := [(Sum.inr 3874, -3964459607742283776000)]

def reducedTerm1471 : Integer.Sparse Master := [(Sum.inr 3875, -11965485017379962880000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1472 : Integer.Sparse Master := [(Sum.inr 3876, -7904065631923077120000)]

def reducedTerm1473 : Integer.Sparse Master := [(Sum.inr 3877, 6667737054748213248000)]

def reducedTerm1474 : Integer.Sparse Master := [(Sum.inr 3880, 14474271087478702080000)]

def reducedTerm1475 : Integer.Sparse Master := [(Sum.inr 3881, 312413012981121024000)]

def reducedTerm1476 : Integer.Sparse Master := [(Sum.inl 0, -5321123508311654400), (Sum.inl 1, 112682615470129152000), (Sum.inl 2, -14085326933766144000), (Sum.inl 3, -225365230940258304000), (Sum.inl 4, -150243487293505536000), (Sum.inl 12, -150243487293505536000), (Sum.inl 13, -50081162431168512000)]

def reducedTerm1477 : Integer.Sparse Master := [(Sum.inl 0, -63655524557394739200), (Sum.inl 1, 347211952131244032000), (Sum.inl 2, -86802988032811008000), (Sum.inl 3, -694423904262488064000), (Sum.inl 4, -231474634754162688000), (Sum.inl 12, -462949269508325376000), (Sum.inl 13, -231474634754162688000)]

def reducedTerm1478 : Integer.Sparse Master := [(Sum.inr 3884, 22823498120703049728000)]

def reducedTerm1479 : Integer.Sparse Master := [(Sum.inr 3885, 8186717116110274560000)]

def reducedTerm1480 : Integer.Sparse Master := [(Sum.inr 3886, 4732620707567370240000)]

def reducedTerm1481 : Integer.Sparse Master := [(Sum.inr 3899, 9660737213374464000000)]

def reducedTerm1482 : Integer.Sparse Master := [(Sum.inr 3901, -31265001811798917120000)]

def reducedTerm1483 : Integer.Sparse Master := [(Sum.inr 3902, 5315776700851814400000)]

def reducedTerm1484 : Integer.Sparse Master := [(Sum.inr 3903, -30197898181904302080000)]

def reducedTerm1485 : Integer.Sparse Master := []

def reducedTerm1486 : Integer.Sparse Master := []

def reducedTerm1487 : Integer.Sparse Master := [(Sum.inr 3906, -6895433910022963200000)]

def reducedTerm1488 : Integer.Sparse Master := [(Sum.inr 3907, 20494784666407403520000)]

def reducedTerm1489 : Integer.Sparse Master := []

def reducedTerm1490 : Integer.Sparse Master := [(Sum.inr 3909, -6141041806181990400000)]

def reducedTerm1491 : Integer.Sparse Master := [(Sum.inr 3910, 13884969959188070400000)]

def reducedTerm1492 : Integer.Sparse Master := [(Sum.inr 3913, 34895135196929064960000)]

def reducedTerm1493 : Integer.Sparse Master := [(Sum.inr 3922, 3526248379837317120000)]

def reducedTerm1494 : Integer.Sparse Master := [(Sum.inr 3945, -30372260691522355200000)]

def reducedTerm1495 : Integer.Sparse Master := [(Sum.inr 3946, -5798712689427087360000)]

def reducedTerm1496 : Integer.Sparse Master := [(Sum.inr 3949, -7800059930768179200000)]

def reducedTerm1497 : Integer.Sparse Master := []

def reducedTerm1498 : Integer.Sparse Master := [(Sum.inr 3954, 11604214120782495744000)]

def reducedTerm1499 : Integer.Sparse Master := [(Sum.inr 3955, -3649006690387623936000)]

def reducedTerm1500 : Integer.Sparse Master := []

def reducedTerm1501 : Integer.Sparse Master := [(Sum.inr 3957, -10194471562001448960000)]

def reducedTerm1502 : Integer.Sparse Master := [(Sum.inr 3958, -15869111358269030400000)]

def reducedTerm1503 : Integer.Sparse Master := [(Sum.inr 3959, -22837858583598858240000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1504 : Integer.Sparse Master := [(Sum.inr 3960, 6539548315307212800000)]

def reducedTerm1505 : Integer.Sparse Master := [(Sum.inr 3961, 9259209259419893760000)]

def reducedTerm1506 : Integer.Sparse Master := []

def reducedTerm1507 : Integer.Sparse Master := [(Sum.inr 3963, -12658524359512227840000)]

def reducedTerm1508 : Integer.Sparse Master := [(Sum.inr 3964, -11253260405800304640000)]

def reducedTerm1509 : Integer.Sparse Master := [(Sum.inr 3972, 8806052365250789376000)]

def reducedTerm1510 : Integer.Sparse Master := [(Sum.inr 3973, 3649006690387623936000)]

def reducedTerm1511 : Integer.Sparse Master := [(Sum.inr 3974, 51911513818286653440000)]

def reducedTerm1512 : Integer.Sparse Master := []

def reducedTerm1513 : Integer.Sparse Master := [(Sum.inl 0, -1769633697226752000), (Sum.inl 1, 42028800309135360000), (Sum.inl 2, -11060210607667200000), (Sum.inl 3, -141570695778140160000), (Sum.inl 4, -70785347889070080000), (Sum.inl 12, -70785347889070080000), (Sum.inl 13, -35392673944535040000)]

def reducedTerm1514 : Integer.Sparse Master := [(Sum.inr 3978, -19036929296722821120000)]

def reducedTerm1515 : Integer.Sparse Master := [(Sum.inr 3983, -1485688708340121600000)]

def reducedTerm1516 : Integer.Sparse Master := [(Sum.inl 0, -15242027862129868800), (Sum.inl 1, -92540883448645632000), (Sum.inl 2, 27217906896660480000), (Sum.inl 3, 435486510346567680000), (Sum.inl 4, 174194604138627072000), (Sum.inl 12, 174194604138627072000), (Sum.inl 26, 87097302069313536000)]

def reducedTerm1517 : Integer.Sparse Master := [(Sum.inl 0, -24802267503476736000), (Sum.inl 1, 93008503138037760000), (Sum.inl 2, -6200566875869184000), (Sum.inl 3, -297627210041720832000), (Sum.inl 4, -198418140027813888000), (Sum.inl 12, -99209070013906944000), (Sum.inl 26, -99209070013906944000)]

def reducedTerm1518 : Integer.Sparse Master := [(Sum.inl 0, -2358461806873804800), (Sum.inl 1, -577823142684082176000), (Sum.inl 2, 117923090343690240000), (Sum.inl 3, 754707778199617536000), (Sum.inl 4, 566030833649713152000), (Sum.inl 26, 188676944549904384000), (Sum.inl 31, -566030833649713152000)]

def reducedTerm1519 : Integer.Sparse Master := [(Sum.inl 0, -90035296257831321600), (Sum.inl 1, 58087287908278272000), (Sum.inl 2, -43565465931208704000), (Sum.inl 3, -232349151633113088000), (Sum.inl 4, -232349151633113088000), (Sum.inl 31, 697047454899339264000)]

def reducedTerm1520 : Integer.Sparse Master := []

def reducedTerm1521 : Integer.Sparse Master := [(Sum.inl 0, -1394517657673728000), (Sum.inl 1, -464839219224576000), (Sum.inl 2, 1859356876898304000), (Sum.inl 3, -14874855015186432000), (Sum.inl 26, -7437427507593216000)]

def reducedTerm1522 : Integer.Sparse Master := [(Sum.inl 1, 444283450102775808000), (Sum.inl 2, -111070862525693952000), (Sum.inl 3, -444283450102775808000), (Sum.inl 4, -444283450102775808000), (Sum.inl 12, -111070862525693952000), (Sum.inl 31, 666425175154163712000)]

def reducedTerm1523 : Integer.Sparse Master := [(Sum.inl 0, -29997156758342860800), (Sum.inl 1, 65618780408875008000), (Sum.inl 2, -46870557434910720000), (Sum.inl 3, -149985783791714304000), (Sum.inl 12, -74992891895857152000)]

def reducedTerm1524 : Integer.Sparse Master := [(Sum.inl 0, -82151924600180736000), (Sum.inl 1, 72486992294277120000), (Sum.inl 2, -48324661529518080000), (Sum.inl 31, -1159791876708433920000)]

def reducedTerm1525 : Integer.Sparse Master := []

def reducedTerm1526 : Integer.Sparse Master := []

def reducedTerm1527 : Integer.Sparse Master := []

def reducedTerm1528 : Integer.Sparse Master := [(Sum.inr 4010, -41423402361966428160000)]

def reducedTerm1529 : Integer.Sparse Master := [(Sum.inr 4022, 12266190676214415360000)]

def reducedTerm1530 : Integer.Sparse Master := [(Sum.inr 4024, 7296061782863314944000)]

def reducedTerm1531 : Integer.Sparse Master := [(Sum.inr 4025, -6738341217491681280000)]

def reducedTerm1532 : Integer.Sparse Master := [(Sum.inl 0, -5565621384684748800), (Sum.inl 1, 1558373987711729664000), (Sum.inl 2, -250452962310813696000), (Sum.inl 3, -4007247396973019136000), (Sum.inl 4, -2671498264648679424000), (Sum.inl 12, -1780998843099119616000), (Sum.inl 25, 1335749132324339712000), (Sum.inl 26, -890499421549559808000)]

def reducedTerm1533 : Integer.Sparse Master := [(Sum.inl 0, 23847053345508556800), (Sum.inl 1, -49681361136476160000), (Sum.inl 2, 29808816681885696000), (Sum.inl 3, 158980355636723712000), (Sum.inl 4, 79490177818361856000), (Sum.inl 25, -238470533455085568000), (Sum.inl 26, 79490177818361856000)]

def reducedTerm1534 : Integer.Sparse Master := [(Sum.inl 0, 6256213215643238400), (Sum.inl 1, 78202665195540480000), (Sum.inl 2, -15640533039108096000), (Sum.inl 3, 125124264312864768000), (Sum.inl 12, 125124264312864768000), (Sum.inl 25, -187686396469297152000)]

def reducedTerm1535 : Integer.Sparse Master := [(Sum.inl 0, -16942121146589184000), (Sum.inl 1, -67768484586356736000), (Sum.inl 2, -16942121146589184000), (Sum.inl 25, -406610907518140416000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1536 : Integer.Sparse Master := [(Sum.inl 0, 45605150947735142400), (Sum.inl 2, 87702213361029120000), (Sum.inl 3, -561294165510586368000), (Sum.inl 4, -280647082755293184000), (Sum.inl 25, 420970624132939776000), (Sum.inl 26, -280647082755293184000)]

def reducedTerm1537 : Integer.Sparse Master := []

def reducedTerm1538 : Integer.Sparse Master := []

def reducedTerm1539 : Integer.Sparse Master := []

def reducedTerm1540 : Integer.Sparse Master := []

def reducedTerm1541 : Integer.Sparse Master := [(Sum.inr 4046, -8408006041455820800000)]

def reducedTerm1542 : Integer.Sparse Master := [(Sum.inr 4047, -3803939670426255360000)]

def reducedTerm1543 : Integer.Sparse Master := []

def reducedTerm1544 : Integer.Sparse Master := []

def reducedTerm1545 : Integer.Sparse Master := [(Sum.inr 4083, 40954261856247742464000)]

def reducedTerm1546 : Integer.Sparse Master := [(Sum.inr 4084, 57085031128334598144000)]

def reducedTerm1547 : Integer.Sparse Master := [(Sum.inr 4085, 2514535969799798784000)]

def reducedTerm1548 : Integer.Sparse Master := [(Sum.inr 4091, 71116174175593365504000)]

def reducedTerm1549 : Integer.Sparse Master := [(Sum.inr 4092, 82312803291315437568000)]

def reducedTerm1550 : Integer.Sparse Master := [(Sum.inr 4149, -4224921028263936000000)]

def reducedTerm1551 : Integer.Sparse Master := [(Sum.inr 4150, -7805365883397734400000)]

def reducedTerm1552 : Integer.Sparse Master := [(Sum.inr 4151, 4224921028263936000000)]

def reducedTerm1553 : Integer.Sparse Master := [(Sum.inr 4152, -8843655738973224960000)]

def reducedTerm1554 : Integer.Sparse Master := [(Sum.inr 4153, 1116328705839857664000)]

def reducedTerm1555 : Integer.Sparse Master := [(Sum.inr 4154, -11450522454042083328000)]

def reducedTerm1556 : Integer.Sparse Master := [(Sum.inr 4155, 7805365883397734400000)]

def reducedTerm1557 : Integer.Sparse Master := [(Sum.inr 4156, 6128597253147328512000)]

def reducedTerm1558 : Integer.Sparse Master := [(Sum.inr 4157, -462947814736920576000)]

def reducedTerm1559 : Integer.Sparse Master := [(Sum.inr 4158, 5593363103425757184000)]

def reducedTerm1560 : Integer.Sparse Master := [(Sum.inr 4159, 2053490911783944192000)]

def reducedTerm1561 : Integer.Sparse Master := [(Sum.inr 4160, 7912784430110343168000)]

def reducedTerm1562 : Integer.Sparse Master := [(Sum.inr 4161, 14905306338389655552000)]

def reducedTerm1563 : Integer.Sparse Master := [(Sum.inr 4162, -761589926485032960000)]

def reducedTerm1564 : Integer.Sparse Master := [(Sum.inr 4163, 368168093238951936000)]

def reducedTerm1565 : Integer.Sparse Master := [(Sum.inr 4169, -5693122080040550400000)]

def reducedTerm1566 : Integer.Sparse Master := [(Sum.inr 4173, 5693122080040550400000)]

def reducedTerm1567 : Integer.Sparse Master := [(Sum.inr 4176, -7248938720166936576000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1568 : Integer.Sparse Master := [(Sum.inr 4178, 12502505035448451072000)]

def reducedTerm1569 : Integer.Sparse Master := [(Sum.inr 4179, 3231726734524022784000)]

def reducedTerm1570 : Integer.Sparse Master := [(Sum.inr 4184, -716116926716706816000)]

def reducedTerm1571 : Integer.Sparse Master := [(Sum.inr 4188, 12949757789032415232000)]

def reducedTerm1572 : Integer.Sparse Master := [(Sum.inr 4189, 1197078318949072896000)]

def reducedTerm1573 : Integer.Sparse Master := [(Sum.inr 4193, -97261095987707904000)]

def reducedTerm1574 : Integer.Sparse Master := [(Sum.inr 4327, -2940208664430772224000)]

def reducedTerm1575 : Integer.Sparse Master := [(Sum.inr 4328, -4362670631726088192000)]

def reducedTerm1576 : Integer.Sparse Master := [(Sum.inr 4330, -2461303460148019200000)]

def reducedTerm1577 : Integer.Sparse Master := [(Sum.inr 4331, 2418118564976787456000)]

def reducedTerm1578 : Integer.Sparse Master := [(Sum.inr 4332, 11195660614200459264000)]

def reducedTerm1579 : Integer.Sparse Master := [(Sum.inr 4333, 5221252535535009792000)]

def reducedTerm1580 : Integer.Sparse Master := [(Sum.inr 4334, 16817110373118246912000)]

def reducedTerm1581 : Integer.Sparse Master := [(Sum.inr 4335, 14664773306621362176000)]

def reducedTerm1582 : Integer.Sparse Master := [(Sum.inr 4336, 3643443110785056768000)]

def reducedTerm1583 : Integer.Sparse Master := [(Sum.inr 4345, -4407922008608735232000)]

def reducedTerm1584 : Integer.Sparse Master := [(Sum.inr 4347, 1765372925391667200000)]

def reducedTerm1585 : Integer.Sparse Master := [(Sum.inr 4353, 3157621618243534848000)]

def reducedTerm1586 : Integer.Sparse Master := [(Sum.inr 4357, 17560644030085201920000)]

def reducedTerm1587 : Integer.Sparse Master := [(Sum.inr 4358, 3552084349459365888000)]

def reducedTerm1588 : Integer.Sparse Master := [(Sum.inr 4362, -483156672380928000000)]

def reducedTerm1589 : Integer.Sparse Master := [(Sum.inr 4363, 2200392789160624128000)]

def reducedTerm1590 : Integer.Sparse Master := [(Sum.inr 4364, 8030508152059330560000)]

def reducedTerm1591 : Integer.Sparse Master := [(Sum.inr 4365, 2333580197392023552000)]

def reducedTerm1592 : Integer.Sparse Master := [(Sum.inr 4366, -19011338932645527552000)]

def reducedTerm1593 : Integer.Sparse Master := [(Sum.inr 4367, -6166085797247975424000)]

def reducedTerm1594 : Integer.Sparse Master := [(Sum.inr 4368, -19274765724083552256000)]

def reducedTerm1595 : Integer.Sparse Master := [(Sum.inr 4369, 5544829063963607040000)]

def reducedTerm1596 : Integer.Sparse Master := [(Sum.inr 4370, 6870049258648633344000)]

def reducedTerm1597 : Integer.Sparse Master := [(Sum.inr 4371, 476851978047062016000)]

def reducedTerm1598 : Integer.Sparse Master := [(Sum.inr 4372, -382460818968281088000)]

def reducedTerm1599 : Integer.Sparse Master := [(Sum.inr 4373, 9211036774796623872000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm160 : Integer.Sparse Master := [(Sum.inl 0, -160095309357957120000), (Sum.inl 1, -329607989854617600000), (Sum.inl 2, -188347422774067200000), (Sum.inl 5, 376694845548134400000), (Sum.inl 8, -376694845548134400000), (Sum.inl 56, 1130084536644403200000)]

def reducedTerm161 : Integer.Sparse Master := [(Sum.inl 0, 120422896787128320000), (Sum.inl 1, -250881034973184000000), (Sum.inl 2, -401409655957094400000), (Sum.inl 6, 50176206994636800000), (Sum.inl 12, 401409655957094400000), (Sum.inl 13, 2408457935742566400000), (Sum.inl 32, 802819311914188800000), (Sum.inl 60, 802819311914188800000), (Sum.inl 128, 401409655957094400000)]

def reducedTerm162 : Integer.Sparse Master := [(Sum.inl 0, -24575771049984000000), (Sum.inl 1, 22341610045440000000), (Sum.inl 2, -11170805022720000000), (Sum.inl 3, -89366440181760000000), (Sum.inl 5, 44683220090880000000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, -268099320545280000000), (Sum.inl 59, 268099320545280000000), (Sum.inl 61, 268099320545280000000)]

def reducedTerm163 : Integer.Sparse Master := [(Sum.inl 0, -236949982220206080000), (Sum.inl 1, 529356343257907200000), (Sum.inl 2, 504148898340864000000), (Sum.inl 3, 1613276474690764800000), (Sum.inl 5, 100829779668172800000), (Sum.inl 6, -50414889834086400000), (Sum.inl 12, 403319118672691200000), (Sum.inl 13, 1613276474690764800000), (Sum.inl 35, 403319118672691200000), (Sum.inl 52, 806638237345382400000)]

def reducedTerm164 : Integer.Sparse Master := [(Sum.inl 0, 191576581369528320000), (Sum.inl 1, -75622334751129600000), (Sum.inl 2, -151244669502259200000), (Sum.inl 3, 403319118672691200000), (Sum.inl 6, -25207444917043200000), (Sum.inl 13, 403319118672691200000), (Sum.inl 52, 403319118672691200000)]

def reducedTerm165 : Integer.Sparse Master := [(Sum.inl 0, -82987547657011200000), (Sum.inl 1, 110650063542681600000), (Sum.inl 2, 41493773828505600000), (Sum.inl 3, -442600254170726400000), (Sum.inl 5, -55325031771340800000), (Sum.inl 6, 13831257942835200000), (Sum.inl 12, -221300127085363200000), (Sum.inl 13, -663900381256089600000), (Sum.inl 35, -221300127085363200000), (Sum.inl 52, -221300127085363200000)]

def reducedTerm166 : Integer.Sparse Master := [(Sum.inl 0, 67522782084710400000), (Sum.inl 1, -157553158197657600000), (Sum.inl 2, -157553158197657600000), (Sum.inl 6, 22507594028236800000), (Sum.inl 13, -360121504451788800000), (Sum.inl 52, -360121504451788800000)]

def reducedTerm167 : Integer.Sparse Master := [(Sum.inl 0, 146509181650944000000), (Sum.inl 1, 205112854311321600000), (Sum.inl 2, 87905508990566400000), (Sum.inl 3, -3750635050264166400000), (Sum.inl 4, -468829381283020800000), (Sum.inl 5, 117207345320755200000), (Sum.inl 6, -29301836330188800000), (Sum.inl 12, -1875317525132083200000), (Sum.inl 13, -4688293812830208000000), (Sum.inl 26, -468829381283020800000), (Sum.inl 32, -468829381283020800000), (Sum.inl 33, 1406488143849062400000), (Sum.inl 34, -468829381283020800000), (Sum.inl 35, -937658762566041600000), (Sum.inl 51, 1406488143849062400000), (Sum.inl 52, -468829381283020800000), (Sum.inl 54, 2812976287698124800000), (Sum.inl 56, 1406488143849062400000), (Sum.inl 60, -468829381283020800000), (Sum.inl 61, 1406488143849062400000), (Sum.inl 62, 1406488143849062400000)]

def reducedTerm168 : Integer.Sparse Master := [(Sum.inl 0, 114657532364390400000), (Sum.inl 1, 200650681637683200000), (Sum.inl 2, 28664383091097600000), (Sum.inl 3, 917260258915123200000), (Sum.inl 6, 57328766182195200000), (Sum.inl 13, 917260258915123200000), (Sum.inl 26, 458630129457561600000), (Sum.inl 34, 458630129457561600000), (Sum.inl 35, 917260258915123200000), (Sum.inl 52, 458630129457561600000), (Sum.inl 60, 458630129457561600000)]

def reducedTerm169 : Integer.Sparse Master := [(Sum.inl 0, -192795762578227200000), (Sum.inl 1, -289193643867340800000), (Sum.inl 2, -481989406445568000000), (Sum.inl 5, 385591525156454400000), (Sum.inl 51, 2313549150938726400000), (Sum.inl 54, 2313549150938726400000), (Sum.inl 56, 2313549150938726400000), (Sum.inl 61, 2313549150938726400000)]

def reducedTerm170 : Integer.Sparse Master := [(Sum.inl 0, -62681499118264320000), (Sum.inl 1, 140493015265075200000), (Sum.inl 2, 183721635346636800000), (Sum.inl 3, 1037486881957478400000), (Sum.inl 5, 129685860244684800000), (Sum.inl 6, -32421465061171200000), (Sum.inl 13, 518743440978739200000), (Sum.inl 26, 518743440978739200000), (Sum.inl 33, -1556230322936217600000), (Sum.inl 35, 172914480326246400000), (Sum.inl 54, -1556230322936217600000), (Sum.inl 62, -1037486881957478400000)]

def reducedTerm171 : Integer.Sparse Master := [(Sum.inl 0, -29899188670095360000), (Sum.inl 1, -13590540304588800000), (Sum.inl 2, -13590540304588800000), (Sum.inl 3, 652345934620262400000), (Sum.inl 4, 289931526497894400000), (Sum.inl 5, 54362161218355200000), (Sum.inl 6, -13590540304588800000), (Sum.inl 12, 144965763248947200000), (Sum.inl 13, 362414408122368000000), (Sum.inl 26, 289931526497894400000), (Sum.inl 35, 217448644873420800000), (Sum.inl 54, -217448644873420800000), (Sum.inl 56, -434897289746841600000)]

def reducedTerm172 : Integer.Sparse Master := [(Sum.inl 0, 11310602075136000000), (Sum.inl 1, -32837231831040000000), (Sum.inl 2, -21891487887360000000), (Sum.inl 3, 29188650516480000000), (Sum.inl 5, 7297162629120000000), (Sum.inl 6, -1824290657280000000), (Sum.inl 26, 58377301032960000000), (Sum.inl 35, 29188650516480000000), (Sum.inl 54, -87565951549440000000)]

def reducedTerm173 : Integer.Sparse Master := [(Sum.inl 0, -13880764064563200000), (Sum.inl 1, -4957415737344000000), (Sum.inl 2, -12393539343360000000), (Sum.inl 3, -79318651797504000000), (Sum.inl 4, -39659325898752000000), (Sum.inl 5, -9914831474688000000), (Sum.inl 6, 2478707868672000000), (Sum.inl 13, -39659325898752000000), (Sum.inl 26, -39659325898752000000), (Sum.inl 35, -39659325898752000000), (Sum.inl 56, 118977977696256000000)]

def reducedTerm174 : Integer.Sparse Master := [(Sum.inl 0, 7414746200064000000), (Sum.inl 1, -9671408087040000000), (Sum.inl 3, 25790421565440000000), (Sum.inl 5, 6447605391360000000), (Sum.inl 6, -1611901347840000000), (Sum.inl 13, 25790421565440000000), (Sum.inl 33, -77371264696320000000), (Sum.inl 54, -77371264696320000000), (Sum.inl 62, -77371264696320000000)]

def reducedTerm175 : Integer.Sparse Master := [(Sum.inl 0, -38409884190720000000), (Sum.inl 1, 76819768381440000000), (Sum.inl 2, 25606589460480000000), (Sum.inl 6, -12803294730240000000), (Sum.inl 26, 204852715683840000000), (Sum.inl 35, 204852715683840000000)]

def reducedTerm176 : Integer.Sparse Master := [(Sum.inl 0, 275258779864104960000), (Sum.inl 1, 1814205594558873600000), (Sum.inl 2, 375352881632870400000), (Sum.inl 3, 2001882035375308800000), (Sum.inl 5, 250235254421913600000), (Sum.inl 6, -62558813605478400000), (Sum.inl 12, 2001882035375308800000), (Sum.inl 13, 3002823053062963200000), (Sum.inl 35, 1000941017687654400000), (Sum.inl 54, -3002823053062963200000)]

def reducedTerm177 : Integer.Sparse Master := [(Sum.inl 0, -220882817129103360000), (Sum.inl 1, -1606420488211660800000), (Sum.inl 3, 1606420488211660800000), (Sum.inl 6, -100401280513228800000), (Sum.inl 13, 1606420488211660800000), (Sum.inl 35, 1606420488211660800000)]

def reducedTerm178 : Integer.Sparse Master := [(Sum.inl 0, -78191986525470720000), (Sum.inl 1, 162899971928064000000), (Sum.inl 2, 260639955084902400000), (Sum.inl 6, -32579994385612800000), (Sum.inl 62, -1563839730509414400000)]

def reducedTerm179 : Integer.Sparse Master := [(Sum.inl 0, -43027969481441280000), (Sum.inl 1, -197211526789939200000), (Sum.inl 2, 17928320617267200000), (Sum.inl 5, 71713282469068800000), (Sum.inl 54, -860559389628825600000)]

def reducedTerm180 : Integer.Sparse Master := [(Sum.inl 0, 32708143860940800000), (Sum.inl 1, 23362959900672000000), (Sum.inl 2, 46725919801344000000), (Sum.inl 5, -46725919801344000000), (Sum.inl 56, 560711037616128000000)]

def reducedTerm181 : Integer.Sparse Master := [(Sum.inl 0, -27430166318284800000), (Sum.inl 1, 77147342770176000000), (Sum.inl 2, 64289452308480000000), (Sum.inl 3, 617178742161408000000), (Sum.inl 5, 51431561846784000000), (Sum.inl 6, -12857890461696000000), (Sum.inl 12, 205726247387136000000), (Sum.inl 13, 960055821139968000000), (Sum.inl 26, 205726247387136000000), (Sum.inl 32, 137150831591424000000), (Sum.inl 34, 411452494774272000000), (Sum.inl 60, 205726247387136000000), (Sum.inl 61, -617178742161408000000)]

def reducedTerm182 : Integer.Sparse Master := [(Sum.inl 0, 19715432041267200000), (Sum.inl 1, 17143853948928000000), (Sum.inl 2, 8571926974464000000), (Sum.inl 3, 137150831591424000000), (Sum.inl 5, 17143853948928000000), (Sum.inl 6, -4285963487232000000), (Sum.inl 13, 137150831591424000000), (Sum.inl 26, 68575415795712000000), (Sum.inl 34, 137150831591424000000), (Sum.inl 60, 68575415795712000000), (Sum.inl 61, -205726247387136000000)]

def reducedTerm183 : Integer.Sparse Master := [(Sum.inl 0, 60911780364288000000), (Sum.inl 1, -126899542425600000000), (Sum.inl 2, -203039267880960000000), (Sum.inl 6, 25379908485120000000), (Sum.inl 13, -406078535761920000000), (Sum.inl 34, -406078535761920000000), (Sum.inl 60, -406078535761920000000)]

def reducedTerm184 : Integer.Sparse Master := [(Sum.inl 0, -60911780364288000000), (Sum.inl 1, 101519633940480000000), (Sum.inl 2, 101519633940480000000), (Sum.inl 5, 101519633940480000000), (Sum.inl 61, -1218235607285760000000)]

def reducedTerm185 : Integer.Sparse Master := [(Sum.inl 0, -11608641260052480000), (Sum.inl 1, -22712558987059200000), (Sum.inl 2, 30283411982745600000), (Sum.inl 3, 363400943792947200000), (Sum.inl 12, 242267295861964800000), (Sum.inl 13, 686424004942233600000), (Sum.inl 32, 80755765287321600000)]

def reducedTerm186 : Integer.Sparse Master := [(Sum.inl 0, 84373900911820800000), (Sum.inl 1, 379682554103193600000), (Sum.inl 2, 632804256838656000000), (Sum.inl 13, 2024973621883699200000), (Sum.inl 32, 674991207294566400000)]

def reducedTerm187 : Integer.Sparse Master := [(Sum.inl 0, -35229445805998080000), (Sum.inl 1, -311645097514598400000), (Sum.inl 2, -108398294787686400000), (Sum.inl 3, 433593179150745600000), (Sum.inl 12, 108398294787686400000), (Sum.inl 13, 433593179150745600000)]

def reducedTerm188 : Integer.Sparse Master := [(Sum.inl 0, 155386623788605440000), (Sum.inl 1, -23543427846758400000), (Sum.inl 2, -94173711387033600000), (Sum.inl 3, 376694845548134400000), (Sum.inl 13, 376694845548134400000)]

def reducedTerm189 : Integer.Sparse Master := [(Sum.inl 0, 23963664694394880000), (Sum.inl 1, -23041985283072000000), (Sum.inl 2, 4608397056614400000), (Sum.inl 3, 147468705811660800000), (Sum.inl 12, 73734352905830400000), (Sum.inl 13, 221203058717491200000)]

def reducedTerm190 : Integer.Sparse Master := [(Sum.inl 0, -13744640100925440000), (Sum.inl 1, 14726400108134400000), (Sum.inl 2, -73632000540672000000), (Sum.inl 13, 78540800576716800000)]

def reducedTerm191 : Integer.Sparse Master := [(Sum.inl 0, -143914085590302720000), (Sum.inl 1, 457908454150963200000), (Sum.inl 2, 261661973800550400000), (Sum.inl 3, -1046647895202201600000), (Sum.inl 12, -1046647895202201600000), (Sum.inl 13, -3139943685606604800000), (Sum.inl 32, -523323947601100800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1600 : Integer.Sparse Master := [(Sum.inr 4374, 17575348253457383424000)]

def reducedTerm1601 : Integer.Sparse Master := [(Sum.inr 4375, -34507362327330816000)]

def reducedTerm1602 : Integer.Sparse Master := [(Sum.inr 4439, -13515513231445327872000)]

def reducedTerm1603 : Integer.Sparse Master := [(Sum.inr 4440, -19241651017431908352000)]

def reducedTerm1604 : Integer.Sparse Master := [(Sum.inr 4442, -2216492015908552704000)]

def reducedTerm1605 : Integer.Sparse Master := [(Sum.inr 4444, 9836938992486187008000)]

def reducedTerm1606 : Integer.Sparse Master := [(Sum.inr 4445, -2888188832156221440000)]

def reducedTerm1607 : Integer.Sparse Master := [(Sum.inr 4459, -24911231228112273408000)]

def reducedTerm1608 : Integer.Sparse Master := [(Sum.inr 4464, -11076753145762676736000)]

def reducedTerm1609 : Integer.Sparse Master := [(Sum.inr 4473, -3609473985785364480000)]

def reducedTerm1610 : Integer.Sparse Master := [(Sum.inr 4474, -8041495388340879360000)]

def reducedTerm1611 : Integer.Sparse Master := [(Sum.inr 4475, -8553475027189628928000)]

def reducedTerm1612 : Integer.Sparse Master := [(Sum.inr 4476, 15007094450225676288000)]

def reducedTerm1613 : Integer.Sparse Master := [(Sum.inr 4478, -14254645456457957376000)]

def reducedTerm1614 : Integer.Sparse Master := [(Sum.inr 4480, 18099022219727339520000)]

def reducedTerm1615 : Integer.Sparse Master := [(Sum.inr 4481, -1896689902925905920000)]

def reducedTerm1616 : Integer.Sparse Master := [(Sum.inr 4494, -4276208522593566720000)]

def reducedTerm1617 : Integer.Sparse Master := [(Sum.inr 4500, 7704059375140208640000)]

def reducedTerm1618 : Integer.Sparse Master := [(Sum.inr 4508, -4470330666478731264000)]

def reducedTerm1619 : Integer.Sparse Master := [(Sum.inr 4527, 5324013064735948800000)]

def reducedTerm1620 : Integer.Sparse Master := [(Sum.inr 4528, 4730383620298506240000)]

def reducedTerm1621 : Integer.Sparse Master := [(Sum.inr 4529, -6127988909884047360000)]

def reducedTerm1622 : Integer.Sparse Master := [(Sum.inr 4530, 1083441906686361600000)]

def reducedTerm1623 : Integer.Sparse Master := [(Sum.inr 4531, 7918345276749250560000)]

def reducedTerm1624 : Integer.Sparse Master := [(Sum.inr 4532, -4345332613952569344000)]

def reducedTerm1625 : Integer.Sparse Master := [(Sum.inr 4533, 215658764367298560000)]

def reducedTerm1626 : Integer.Sparse Master := [(Sum.inr 4534, -8819748555444191232000)]

def reducedTerm1627 : Integer.Sparse Master := [(Sum.inr 4535, -3968589383710801920000)]

def reducedTerm1628 : Integer.Sparse Master := [(Sum.inr 4536, -14113916079842525184000)]

def reducedTerm1629 : Integer.Sparse Master := [(Sum.inr 4540, 8499226830254899200000)]

def reducedTerm1630 : Integer.Sparse Master := [(Sum.inr 4542, 23732159479676928000000)]

def reducedTerm1631 : Integer.Sparse Master := [(Sum.inr 4545, 36626429413905924096000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1632 : Integer.Sparse Master := [(Sum.inr 4547, 15452458461052010496000)]

def reducedTerm1633 : Integer.Sparse Master := [(Sum.inr 4548, 14639794103047421952000)]

def reducedTerm1634 : Integer.Sparse Master := [(Sum.inr 4552, -11692002548014645248000)]

def reducedTerm1635 : Integer.Sparse Master := [(Sum.inr 4556, -8265191798831579136000)]

def reducedTerm1636 : Integer.Sparse Master := [(Sum.inr 4560, -1142729568214843392000)]

def reducedTerm1637 : Integer.Sparse Master := [(Sum.inr 4589, 1220339788645662720000)]

def reducedTerm1638 : Integer.Sparse Master := [(Sum.inr 4590, 6476173958106316800000)]

def reducedTerm1639 : Integer.Sparse Master := [(Sum.inr 4591, -6085807301323653120000)]

def reducedTerm1640 : Integer.Sparse Master := [(Sum.inr 4592, -15157581060922933248000)]

def reducedTerm1641 : Integer.Sparse Master := [(Sum.inr 4593, -7559615864792678400000)]

def reducedTerm1642 : Integer.Sparse Master := [(Sum.inr 4594, 3011436319122653184000)]

def reducedTerm1643 : Integer.Sparse Master := [(Sum.inr 4599, 10617849996847349760000)]

def reducedTerm1644 : Integer.Sparse Master := [(Sum.inr 4600, -1692590756154310656000)]

def reducedTerm1645 : Integer.Sparse Master := [(Sum.inr 4603, -35786008029537239040000)]

def reducedTerm1646 : Integer.Sparse Master := [(Sum.inr 4607, -38147155763799785472000)]

def reducedTerm1647 : Integer.Sparse Master := [(Sum.inr 4609, -5558333516289146880000)]

def reducedTerm1648 : Integer.Sparse Master := [(Sum.inr 4611, -10846457928298266624000)]

def reducedTerm1649 : Integer.Sparse Master := [(Sum.inr 4616, -2261821083603959808000)]

def reducedTerm1650 : Integer.Sparse Master := [(Sum.inr 4617, -757540324473569280000)]

def reducedTerm1651 : Integer.Sparse Master := [(Sum.inr 4620, -747979948051660800000)]

def reducedTerm1652 : Integer.Sparse Master := [(Sum.inr 4626, -875893157801754624000)]

def reducedTerm1653 : Integer.Sparse Master := [(Sum.inr 4663, -4224921028263936000000)]

def reducedTerm1654 : Integer.Sparse Master := [(Sum.inr 4664, -5601048967764246528000)]

def reducedTerm1655 : Integer.Sparse Master := [(Sum.inr 4665, 4938879732374568960000)]

def reducedTerm1656 : Integer.Sparse Master := [(Sum.inr 4666, -7805365883397734400000)]

def reducedTerm1657 : Integer.Sparse Master := [(Sum.inr 4667, 1400988782872756224000)]

def reducedTerm1658 : Integer.Sparse Master := [(Sum.inr 4668, 1662907014489047040000)]

def reducedTerm1659 : Integer.Sparse Master := [(Sum.inr 4669, -799209977907511296000)]

def reducedTerm1660 : Integer.Sparse Master := [(Sum.inr 4670, -16331923481962217472000)]

def reducedTerm1661 : Integer.Sparse Master := [(Sum.inr 4671, 1843237901377732608000)]

def reducedTerm1662 : Integer.Sparse Master := [(Sum.inr 4677, -5693122080040550400000)]

def reducedTerm1663 : Integer.Sparse Master := [(Sum.inr 4680, 2989735781018370048000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1664 : Integer.Sparse Master := [(Sum.inr 4682, -20337198821419253760000)]

def reducedTerm1665 : Integer.Sparse Master := [(Sum.inr 4683, -4166088676073275392000)]

def reducedTerm1666 : Integer.Sparse Master := [(Sum.inr 4687, 4331084313932070912000)]

def reducedTerm1667 : Integer.Sparse Master := [(Sum.inr 4690, -7832344641172144128000)]

def reducedTerm1668 : Integer.Sparse Master := [(Sum.inr 4694, 419207923271467008000)]

def reducedTerm1669 : Integer.Sparse Master := [(Sum.inr 4695, 2088377879151771648000)]

def reducedTerm1670 : Integer.Sparse Master := [(Sum.inr 4696, 4668687916798574592000)]

def reducedTerm1671 : Integer.Sparse Master := [(Sum.inr 4697, -47757709229948928000)]

def reducedTerm1672 : Integer.Sparse Master := [(Sum.inr 4698, -11360929018687782912000)]

def reducedTerm1673 : Integer.Sparse Master := [(Sum.inr 4699, -12243947554527510528000)]

def reducedTerm1674 : Integer.Sparse Master := [(Sum.inr 4700, -9017233195750391808000)]

def reducedTerm1675 : Integer.Sparse Master := [(Sum.inr 4701, 1426161328576266240000)]

def reducedTerm1676 : Integer.Sparse Master := [(Sum.inr 4702, 323950101685862400000)]

def reducedTerm1677 : Integer.Sparse Master := [(Sum.inr 4703, 2481540634666598400000)]

def reducedTerm1678 : Integer.Sparse Master := [(Sum.inr 4704, 6123206211439951872000)]

def reducedTerm1679 : Integer.Sparse Master := [(Sum.inr 4705, 5611114966542188544000)]

def reducedTerm1680 : Integer.Sparse Master := [(Sum.inr 4756, -4157338039461347328000)]

def reducedTerm1681 : Integer.Sparse Master := [(Sum.inr 4757, -9921532838029295616000)]

def reducedTerm1682 : Integer.Sparse Master := [(Sum.inr 4761, -9955508355996844032000)]

def reducedTerm1683 : Integer.Sparse Master := [(Sum.inr 4762, -3552860462980792320000)]

def reducedTerm1684 : Integer.Sparse Master := [(Sum.inr 4765, 1531209998492762112000)]

def reducedTerm1685 : Integer.Sparse Master := [(Sum.inr 4768, -10577125298707365888000)]

def reducedTerm1686 : Integer.Sparse Master := [(Sum.inr 4771, -2142501973049475072000)]

def reducedTerm1687 : Integer.Sparse Master := [(Sum.inr 4772, -7032198870020653056000)]

def reducedTerm1688 : Integer.Sparse Master := [(Sum.inr 4773, 2026857879932239872000)]

def reducedTerm1689 : Integer.Sparse Master := [(Sum.inr 4774, -2118434941245063168000)]

def reducedTerm1690 : Integer.Sparse Master := [(Sum.inr 4775, 12472080070696501248000)]

def reducedTerm1691 : Integer.Sparse Master := [(Sum.inr 4776, 13670070453059715072000)]

def reducedTerm1692 : Integer.Sparse Master := [(Sum.inr 4777, 1819985088072646656000)]

def reducedTerm1693 : Integer.Sparse Master := [(Sum.inr 4792, -3874325650567593984000)]

def reducedTerm1694 : Integer.Sparse Master := [(Sum.inr 4793, 2175984329530540032000)]

def reducedTerm1695 : Integer.Sparse Master := [(Sum.inr 4795, -657568140574851072000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1696 : Integer.Sparse Master := [(Sum.inr 4803, 9126733393928650752000)]

def reducedTerm1697 : Integer.Sparse Master := [(Sum.inr 4808, 6795525312677412864000)]

def reducedTerm1698 : Integer.Sparse Master := [(Sum.inr 4815, 10203027601367236608000)]

def reducedTerm1699 : Integer.Sparse Master := [(Sum.inr 4816, 16684169003853152256000)]

def reducedTerm1700 : Integer.Sparse Master := [(Sum.inr 4817, -4302249789556260864000)]

def reducedTerm1701 : Integer.Sparse Master := [(Sum.inr 4819, -9689775870270504960000)]

def reducedTerm1702 : Integer.Sparse Master := [(Sum.inr 4821, 24425621100813090816000)]

def reducedTerm1703 : Integer.Sparse Master := [(Sum.inr 4830, 4276208522593566720000)]

def reducedTerm1704 : Integer.Sparse Master := [(Sum.inr 4836, 14865336275325419520000)]

def reducedTerm1705 : Integer.Sparse Master := [(Sum.inr 4844, -10611725918904778752000)]

def reducedTerm1706 : Integer.Sparse Master := [(Sum.inr 4851, -3651536391380140032000)]

def reducedTerm1707 : Integer.Sparse Master := [(Sum.inr 4852, 25540881314177875968000)]

def reducedTerm1708 : Integer.Sparse Master := [(Sum.inr 4853, -8931969569439350784000)]

def reducedTerm1709 : Integer.Sparse Master := [(Sum.inr 4856, 47721697208593809408000)]

def reducedTerm1710 : Integer.Sparse Master := [(Sum.inr 4863, 3301651066537377792000)]

def reducedTerm1711 : Integer.Sparse Master := [(Sum.inr 4867, 25180426029650411520000)]

def reducedTerm1712 : Integer.Sparse Master := [(Sum.inr 4872, -1313798019878486016000)]

def reducedTerm1713 : Integer.Sparse Master := [(Sum.inr 4878, 21125648675937189888000)]

def reducedTerm1714 : Integer.Sparse Master := [(Sum.inr 4879, 58246227271801110528000)]

def reducedTerm1715 : Integer.Sparse Master := [(Sum.inr 4880, 15911341251193995264000)]

def reducedTerm1716 : Integer.Sparse Master := [(Sum.inr 4881, 9824764650698833920000)]

def reducedTerm1717 : Integer.Sparse Master := [(Sum.inr 4884, 19178062513867063296000)]

def reducedTerm1718 : Integer.Sparse Master := [(Sum.inr 4885, -1093534813718839296000)]

def reducedTerm1719 : Integer.Sparse Master := [(Sum.inr 4886, 22163666956793413632000)]

def reducedTerm1720 : Integer.Sparse Master := [(Sum.inr 2243, 9372634478002962432000)]

def reducedTerm1721 : Integer.Sparse Master := [(Sum.inr 2244, 2883452798765629440000), (Sum.inr 2262, 2883452798765629440000)]

def reducedTerm1722 : Integer.Sparse Master := [(Sum.inr 2245, -4057256850042912768000), (Sum.inr 2277, -4057256850042912768000)]

def reducedTerm1723 : Integer.Sparse Master := [(Sum.inr 2247, -757011477946171392000), (Sum.inr 2290, -757011477946171392000)]

def reducedTerm1724 : Integer.Sparse Master := [(Sum.inr 4891, 39451307385118261248000)]

def reducedTerm1725 : Integer.Sparse Master := [(Sum.inr 4892, 6273766636234997760000)]

def reducedTerm1726 : Integer.Sparse Master := []

def reducedTerm1727 : Integer.Sparse Master := []

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1728 : Integer.Sparse Master := []

def reducedTerm1729 : Integer.Sparse Master := [(Sum.inr 2266, -1722459352110465024000), (Sum.inr 2278, -1722459352110465024000)]

def reducedTerm1730 : Integer.Sparse Master := []

def reducedTerm1731 : Integer.Sparse Master := [(Sum.inr 2279, -6553562748283256832000)]

def reducedTerm1732 : Integer.Sparse Master := [(Sum.inr 2281, 1215313374856347648000), (Sum.inr 2294, 1215313374856347648000)]

def reducedTerm1733 : Integer.Sparse Master := [(Sum.inr 4900, -1647434443064868864000)]

def reducedTerm1734 : Integer.Sparse Master := []

def reducedTerm1735 : Integer.Sparse Master := [(Sum.inr 4930, -7941663994208845824000)]

def reducedTerm1736 : Integer.Sparse Master := [(Sum.inr 4931, 2611987518440079360000)]

def reducedTerm1737 : Integer.Sparse Master := [(Sum.inr 4933, 1421670070005792768000)]

def reducedTerm1738 : Integer.Sparse Master := [(Sum.inr 4934, -6239960297145630720000)]

def reducedTerm1739 : Integer.Sparse Master := [(Sum.inr 4935, 3259996962101526528000)]

def reducedTerm1740 : Integer.Sparse Master := [(Sum.inr 4942, 13377767853843283968000)]

def reducedTerm1741 : Integer.Sparse Master := [(Sum.inr 4944, -11958904477318643712000)]

def reducedTerm1742 : Integer.Sparse Master := [(Sum.inr 4945, -127393862378323968000)]

def reducedTerm1743 : Integer.Sparse Master := [(Sum.inr 4951, -1418863376524640256000)]

def reducedTerm1744 : Integer.Sparse Master := [(Sum.inr 4954, 19134699747307683840000)]

def reducedTerm1745 : Integer.Sparse Master := [(Sum.inr 4955, -5686906574229995520000)]

def reducedTerm1746 : Integer.Sparse Master := [(Sum.inr 4956, -5324013064735948800000)]

def reducedTerm1747 : Integer.Sparse Master := [(Sum.inr 4957, 29561192263900200960000)]

def reducedTerm1748 : Integer.Sparse Master := [(Sum.inr 4958, -1083441906686361600000)]

def reducedTerm1749 : Integer.Sparse Master := [(Sum.inr 4959, -12567225913008979968000)]

def reducedTerm1750 : Integer.Sparse Master := [(Sum.inr 4963, -4535331438044381184000)]

def reducedTerm1751 : Integer.Sparse Master := [(Sum.inr 4964, -23732159479676928000000)]

def reducedTerm1752 : Integer.Sparse Master := [(Sum.inr 4965, -18533635534082801664000)]

def reducedTerm1753 : Integer.Sparse Master := [(Sum.inr 4966, -22975789646216429568000)]

def reducedTerm1754 : Integer.Sparse Master := [(Sum.inr 4975, -8499226830254899200000)]

def reducedTerm1755 : Integer.Sparse Master := [(Sum.inr 4976, -16875309640898838528000)]

def reducedTerm1756 : Integer.Sparse Master := [(Sum.inr 5034, 2978479197322739712000)]

def reducedTerm1757 : Integer.Sparse Master := [(Sum.inr 5035, 16389072352617431040000)]

def reducedTerm1758 : Integer.Sparse Master := [(Sum.inr 5040, 23233730127482585088000)]

def reducedTerm1759 : Integer.Sparse Master := [(Sum.inr 5041, 92883104915521536000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1760 : Integer.Sparse Master := [(Sum.inr 5042, -9483177650962563072000)]

def reducedTerm1761 : Integer.Sparse Master := [(Sum.inr 5043, -2890541624919588864000)]

def reducedTerm1762 : Integer.Sparse Master := [(Sum.inr 5044, -7341806534933348352000)]

def reducedTerm1763 : Integer.Sparse Master := [(Sum.inr 5065, -14530652001365262336000)]

def reducedTerm1764 : Integer.Sparse Master := [(Sum.inr 5067, 7427653233623433216000)]

def reducedTerm1765 : Integer.Sparse Master := [(Sum.inr 5074, -12264455942580731904000)]

def reducedTerm1766 : Integer.Sparse Master := [(Sum.inr 5085, 8916509350529335296000)]

def reducedTerm1767 : Integer.Sparse Master := [(Sum.inr 5086, 12233494979845816320000)]

def reducedTerm1768 : Integer.Sparse Master := [(Sum.inr 5087, 2026846219688607744000)]

def reducedTerm1769 : Integer.Sparse Master := [(Sum.inr 5090, -18907268073784344576000)]

def reducedTerm1770 : Integer.Sparse Master := [(Sum.inr 5097, 1037405314429747200000)]

def reducedTerm1771 : Integer.Sparse Master := [(Sum.inr 5103, 6797176070885867520000)]

def reducedTerm1772 : Integer.Sparse Master := [(Sum.inr 5112, -6581206302477778944000)]

def reducedTerm1773 : Integer.Sparse Master := [(Sum.inr 5116, 1658951609427689472000)]

def reducedTerm1774 : Integer.Sparse Master := [(Sum.inr 5128, -2003708022304407552000)]

def reducedTerm1775 : Integer.Sparse Master := [(Sum.inr 5129, 6585849716091125760000)]

def reducedTerm1776 : Integer.Sparse Master := [(Sum.inr 5138, 12127532681381806080000)]

def reducedTerm1777 : Integer.Sparse Master := [(Sum.inr 5139, -49178321197557350400000)]

def reducedTerm1778 : Integer.Sparse Master := [(Sum.inr 5140, -17211622947812278272000)]

def reducedTerm1779 : Integer.Sparse Master := [(Sum.inr 5144, 3601578321337909248000)]

def reducedTerm1780 : Integer.Sparse Master := [(Sum.inr 5145, 11949080038817660928000)]

def reducedTerm1781 : Integer.Sparse Master := [(Sum.inr 5147, 26234697751049797632000)]

def reducedTerm1782 : Integer.Sparse Master := [(Sum.inr 5150, -1803031804161294336000)]

def reducedTerm1783 : Integer.Sparse Master := [(Sum.inr 5151, -1219510267957739520000)]

def reducedTerm1784 : Integer.Sparse Master := [(Sum.inr 5160, 34816216585195487232000)]

def reducedTerm1785 : Integer.Sparse Master := [(Sum.inr 5161, 758866233230622720000)]

def reducedTerm1786 : Integer.Sparse Master := [(Sum.inr 5164, 22613357947383447552000)]

def reducedTerm1787 : Integer.Sparse Master := [(Sum.inr 5173, 13429246920497823744000)]

def reducedTerm1788 : Integer.Sparse Master := [(Sum.inr 5175, -4064171765800108032000)]

def reducedTerm1789 : Integer.Sparse Master := [(Sum.inr 5184, -4291086391493787648000)]

def reducedTerm1790 : Integer.Sparse Master := [(Sum.inr 5185, 9726337145084313600000)]

def reducedTerm1791 : Integer.Sparse Master := [(Sum.inr 5187, 30794924164413652992000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1792 : Integer.Sparse Master := [(Sum.inr 5188, 5010817572354392064000)]

def reducedTerm1793 : Integer.Sparse Master := [(Sum.inr 5189, -5752353613478363136000)]

def reducedTerm1794 : Integer.Sparse Master := [(Sum.inr 5197, 7848902981735940096000)]

def reducedTerm1795 : Integer.Sparse Master := [(Sum.inr 5198, 9732294813230825472000)]

def reducedTerm1796 : Integer.Sparse Master := [(Sum.inr 5199, 55912898410749886464000)]

def reducedTerm1797 : Integer.Sparse Master := [(Sum.inr 5201, 18198562535170375680000)]

def reducedTerm1798 : Integer.Sparse Master := [(Sum.inr 5205, 16689362260860076032000)]

def reducedTerm1799 : Integer.Sparse Master := [(Sum.inr 5206, 11015478679850975232000)]

def reducedTerm1800 : Integer.Sparse Master := [(Sum.inr 5215, -11601654236794847232000)]

def reducedTerm1801 : Integer.Sparse Master := [(Sum.inr 5216, -238272485558059008000)]

def reducedTerm1802 : Integer.Sparse Master := [(Sum.inr 5217, 9806018085126144000000)]

def reducedTerm1803 : Integer.Sparse Master := [(Sum.inr 5219, 10171942174410670080000)]

def reducedTerm1804 : Integer.Sparse Master := [(Sum.inr 5220, -381292928484507648000)]

def reducedTerm1805 : Integer.Sparse Master := [(Sum.inr 5222, 3552860462980792320000)]

def reducedTerm1806 : Integer.Sparse Master := [(Sum.inr 5226, 7805365883397734400000)]

def reducedTerm1807 : Integer.Sparse Master := [(Sum.inr 5229, 12678992556746342400000)]

def reducedTerm1808 : Integer.Sparse Master := [(Sum.inr 5231, 8788145924144627712000)]

def reducedTerm1809 : Integer.Sparse Master := [(Sum.inr 5232, 14640885025087684608000)]

def reducedTerm1810 : Integer.Sparse Master := [(Sum.inr 5233, 4998927687537917952000)]

def reducedTerm1811 : Integer.Sparse Master := [(Sum.inr 5235, 1313082224189374464000)]

def reducedTerm1812 : Integer.Sparse Master := [(Sum.inr 5236, -9806018085126144000000)]

def reducedTerm1813 : Integer.Sparse Master := [(Sum.inr 5243, 2663428588472107008000)]

def reducedTerm1814 : Integer.Sparse Master := [(Sum.inr 5244, -12840196478415667200000)]

def reducedTerm1815 : Integer.Sparse Master := [(Sum.inr 5249, 8721406518151348224000)]

def reducedTerm1816 : Integer.Sparse Master := []

def reducedTerm1817 : Integer.Sparse Master := [(Sum.inr 5251, 20804483957839626240000)]

def reducedTerm1818 : Integer.Sparse Master := [(Sum.inr 5252, -15787189652894908416000)]

def reducedTerm1819 : Integer.Sparse Master := [(Sum.inr 5254, -18103702594567274496000)]

def reducedTerm1820 : Integer.Sparse Master := [(Sum.inr 5255, 10628823676665987072000)]

def reducedTerm1821 : Integer.Sparse Master := []

def reducedTerm1822 : Integer.Sparse Master := [(Sum.inr 2721, 3811256349900668928000), (Sum.inr 3532, 3811256349900668928000)]

def reducedTerm1823 : Integer.Sparse Master := [(Sum.inr 2722, 5665773180262809600000), (Sum.inr 3533, 5665773180262809600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1824 : Integer.Sparse Master := [(Sum.inr 2723, 1418854997041348608000), (Sum.inr 3544, 1418854997041348608000)]

def reducedTerm1825 : Integer.Sparse Master := [(Sum.inr 5260, 9126071378630148096000)]

def reducedTerm1826 : Integer.Sparse Master := [(Sum.inr 5263, -16830413886397612032000)]

def reducedTerm1827 : Integer.Sparse Master := [(Sum.inr 5264, 642323079345733632000)]

def reducedTerm1828 : Integer.Sparse Master := [(Sum.inr 5265, -25288345262529183744000)]

def reducedTerm1829 : Integer.Sparse Master := [(Sum.inr 5266, -23758552131121446912000)]

def reducedTerm1830 : Integer.Sparse Master := [(Sum.inr 5267, -28266402523973419008000)]

def reducedTerm1831 : Integer.Sparse Master := [(Sum.inr 5268, -30906556284937568256000)]

def reducedTerm1832 : Integer.Sparse Master := [(Sum.inr 5269, 19094161853855563776000)]

def reducedTerm1833 : Integer.Sparse Master := [(Sum.inr 5270, 23882407552008585216000)]

def reducedTerm1834 : Integer.Sparse Master := [(Sum.inr 2739, -9991713240911904768000), (Sum.inr 3534, -9991713240911904768000)]

def reducedTerm1835 : Integer.Sparse Master := [(Sum.inr 2740, -7464257958947586048000)]

def reducedTerm1836 : Integer.Sparse Master := []

def reducedTerm1837 : Integer.Sparse Master := []

def reducedTerm1838 : Integer.Sparse Master := [(Sum.inr 2743, -2131060763813216256000), (Sum.inr 3548, -2131060763813216256000)]

def reducedTerm1839 : Integer.Sparse Master := [(Sum.inr 5276, -48308943425120501760000)]

def reducedTerm1840 : Integer.Sparse Master := [(Sum.inr 5277, -7408755837351493632000)]

def reducedTerm1841 : Integer.Sparse Master := [(Sum.inr 5278, -5384845512904015872000)]

def reducedTerm1842 : Integer.Sparse Master := [(Sum.inr 5279, -13629983004992471040000)]

def reducedTerm1843 : Integer.Sparse Master := [(Sum.inr 5281, 68956627891077513216000)]

def reducedTerm1844 : Integer.Sparse Master := [(Sum.inr 5282, -12260480058351157248000)]

def reducedTerm1845 : Integer.Sparse Master := [(Sum.inr 3077, 521061915183022080000), (Sum.inr 3625, 521061915183022080000)]

def reducedTerm1846 : Integer.Sparse Master := [(Sum.inr 5286, -23256277065636249600000)]

def reducedTerm1847 : Integer.Sparse Master := [(Sum.inr 5287, -14631219146636918784000)]

def reducedTerm1848 : Integer.Sparse Master := [(Sum.inr 5288, -1665714719287148544000)]

def reducedTerm1849 : Integer.Sparse Master := [(Sum.inr 5289, -190845340189813112832000)]

def reducedTerm1850 : Integer.Sparse Master := [(Sum.inr 2764, 9468178881528987648000), (Sum.inr 3581, 9468178881528987648000)]

def reducedTerm1851 : Integer.Sparse Master := [(Sum.inr 2765, 2736289857142259712000), (Sum.inr 3582, 2736289857142259712000)]

def reducedTerm1852 : Integer.Sparse Master := [(Sum.inr 5295, -90385457830414516224000)]

def reducedTerm1853 : Integer.Sparse Master := [(Sum.inr 5297, -4322559273236692992000)]

def reducedTerm1854 : Integer.Sparse Master := [(Sum.inr 5299, -9865202604365316096000)]

def reducedTerm1855 : Integer.Sparse Master := [(Sum.inr 5300, -19050929198037467136000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1856 : Integer.Sparse Master := [(Sum.inr 3053, 563280397683720192000), (Sum.inr 3619, 563280397683720192000)]

def reducedTerm1857 : Integer.Sparse Master := [(Sum.inr 3054, 3710011026318557184000), (Sum.inr 3626, 3710011026318557184000)]

def reducedTerm1858 : Integer.Sparse Master := [(Sum.inr 5303, 4117655551595249664000)]

def reducedTerm1859 : Integer.Sparse Master := [(Sum.inr 2782, -12883558326964125696000), (Sum.inr 3583, -12883558326964125696000)]

def reducedTerm1860 : Integer.Sparse Master := [(Sum.inr 2783, -754926178515812352000)]

def reducedTerm1861 : Integer.Sparse Master := [(Sum.inr 5311, -18048588276902658048000)]

def reducedTerm1862 : Integer.Sparse Master := [(Sum.inr 5338, 3540243621870305280000)]

def reducedTerm1863 : Integer.Sparse Master := [(Sum.inr 5339, 31118010071687626752000)]

def reducedTerm1864 : Integer.Sparse Master := [(Sum.inr 5340, 2890541624919588864000)]

def reducedTerm1865 : Integer.Sparse Master := [(Sum.inr 5348, -2519509915502641152000)]

def reducedTerm1866 : Integer.Sparse Master := [(Sum.inr 5353, -10327115071336218624000)]

def reducedTerm1867 : Integer.Sparse Master := [(Sum.inr 5359, -8916509350529335296000)]

def reducedTerm1868 : Integer.Sparse Master := [(Sum.inr 5360, -13929942140355870720000)]

def reducedTerm1869 : Integer.Sparse Master := [(Sum.inr 5361, -5829419805588062208000)]

def reducedTerm1870 : Integer.Sparse Master := [(Sum.inr 5376, 275156207945515008000)]

def reducedTerm1871 : Integer.Sparse Master := [(Sum.inr 5377, 7559615864792678400000)]

def reducedTerm1872 : Integer.Sparse Master := [(Sum.inr 5379, 28457281603153428480000)]

def reducedTerm1873 : Integer.Sparse Master := [(Sum.inr 5381, 25355826421346598912000)]

def reducedTerm1874 : Integer.Sparse Master := [(Sum.inr 5382, 13348700654332280832000)]

def reducedTerm1875 : Integer.Sparse Master := [(Sum.inr 5385, 13623556916506263552000)]

def reducedTerm1876 : Integer.Sparse Master := [(Sum.inr 5402, -22065085658765721600000)]

def reducedTerm1877 : Integer.Sparse Master := [(Sum.inr 3800, 1911204393004892160000), (Sum.inr 3805, 1911204393004892160000)]

def reducedTerm1878 : Integer.Sparse Master := [(Sum.inr 3801, 7423654131242237952000), (Sum.inr 3812, 7423654131242237952000)]

def reducedTerm1879 : Integer.Sparse Master := [(Sum.inr 5407, -37595573886288789504000)]

def reducedTerm1880 : Integer.Sparse Master := []

def reducedTerm1881 : Integer.Sparse Master := []

def reducedTerm1882 : Integer.Sparse Master := []

def reducedTerm1883 : Integer.Sparse Master := [(Sum.inr 3809, -12499630276724785152000), (Sum.inr 3813, -12499630276724785152000)]

def reducedTerm1884 : Integer.Sparse Master := [(Sum.inr 3814, 3201511118400258048000)]

def reducedTerm1885 : Integer.Sparse Master := []

def reducedTerm1886 : Integer.Sparse Master := [(Sum.inr 5414, -2360542400871137280000)]

def reducedTerm1887 : Integer.Sparse Master := [(Sum.inr 5419, 5752353613478363136000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm1888 : Integer.Sparse Master := [(Sum.inr 5420, -8413005595148550144000)]

def reducedTerm1889 : Integer.Sparse Master := [(Sum.inr 5421, -29313851828997980160000)]

def reducedTerm1890 : Integer.Sparse Master := [(Sum.inr 3837, 15154942468785831936000)]

def reducedTerm1891 : Integer.Sparse Master := [(Sum.inr 3838, -4703254311742930944000), (Sum.inr 3843, -4703254311742930944000)]

def reducedTerm1892 : Integer.Sparse Master := [(Sum.inr 5425, -31786630521973899264000)]

def reducedTerm1893 : Integer.Sparse Master := [(Sum.inr 5426, 9684849239753490432000)]

def reducedTerm1894 : Integer.Sparse Master := []

def reducedTerm1895 : Integer.Sparse Master := [(Sum.inr 3845, -8099232324752572416000)]

def reducedTerm1896 : Integer.Sparse Master := [(Sum.inr 5429, -9244716940057116672000)]

def reducedTerm1897 : Integer.Sparse Master := [(Sum.inr 5430, 16445950118093389824000)]

def reducedTerm1898 : Integer.Sparse Master := [(Sum.inr 3849, 24043484381838114816000), (Sum.inr 3875, 24043484381838114816000)]

def reducedTerm1899 : Integer.Sparse Master := [(Sum.inr 3850, 8584939204383080448000)]

def reducedTerm1900 : Integer.Sparse Master := [(Sum.inr 5436, 88096283133573464064000)]

def reducedTerm1901 : Integer.Sparse Master := [(Sum.inr 3899, 11146943761140547584000)]

def reducedTerm1902 : Integer.Sparse Master := [(Sum.inr 3857, -5357289780750974976000), (Sum.inr 3876, -5357289780750974976000)]

def reducedTerm1903 : Integer.Sparse Master := [(Sum.inr 5445, -2629572249391202304000)]

def reducedTerm1904 : Integer.Sparse Master := [(Sum.inr 5446, -164858414417055055872000)]

def reducedTerm1905 : Integer.Sparse Master := [(Sum.inr 3909, 1352191385641549824000), (Sum.inr 4025, 1352191385641549824000)]

def reducedTerm1906 : Integer.Sparse Master := [(Sum.inr 3885, 6756710272894697472000)]

def reducedTerm1907 : Integer.Sparse Master := [(Sum.inr 3886, -7318996335326527488000)]

def reducedTerm1908 : Integer.Sparse Master := [(Sum.inr 5461, 14596026761550495744000)]

def reducedTerm1909 : Integer.Sparse Master := [(Sum.inr 5463, 26158193261228851200000)]

def reducedTerm1910 : Integer.Sparse Master := [(Sum.inr 5470, -14596026761550495744000)]

def reducedTerm1911 : Integer.Sparse Master := []

def reducedTerm1912 : Integer.Sparse Master := [(Sum.inr 3957, 11995653152774946816000)]

def reducedTerm1913 : Integer.Sparse Master := [(Sum.inr 3958, -12546854188188106752000), (Sum.inr 3961, -12546854188188106752000)]

def reducedTerm1914 : Integer.Sparse Master := []

def reducedTerm1915 : Integer.Sparse Master := [(Sum.inr 3963, -20876253780751810560000)]

def reducedTerm1916 : Integer.Sparse Master := [(Sum.inr 3974, -20377110011389673472000)]

def reducedTerm1917 : Integer.Sparse Master := [(Sum.inr 5480, -62042723667542016000000)]

def reducedTerm1918 : Integer.Sparse Master := [(Sum.inr 3983, -803242170820067328000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm192 : Integer.Sparse Master := [(Sum.inl 0, -44788382087823360000), (Sum.inl 1, 111970955219558400000), (Sum.inl 2, -111970955219558400000), (Sum.inl 13, 597178427837644800000), (Sum.inl 32, 298589213918822400000)]

def reducedTerm193 : Integer.Sparse Master := []

def reducedTerm194 : Integer.Sparse Master := []

def reducedTerm195 : Integer.Sparse Master := []

def reducedTerm196 : Integer.Sparse Master := [(Sum.inl 0, -209343304474214400000), (Sum.inl 1, 767592116405452800000), (Sum.inl 2, 558248811931238400000), (Sum.inl 3, 1116497623862476800000), (Sum.inl 13, 1116497623862476800000)]

def reducedTerm197 : Integer.Sparse Master := [(Sum.inl 0, 187546931046236160000), (Sum.inl 1, 468867327615590400000), (Sum.inl 2, -468867327615590400000), (Sum.inl 12, -1250312873641574400000), (Sum.inl 13, -2500625747283148800000)]

def reducedTerm198 : Integer.Sparse Master := [(Sum.inl 0, -39777774389821440000), (Sum.inl 1, -149166653961830400000), (Sum.inl 2, -149166653961830400000), (Sum.inl 13, -795555487796428800000)]

def reducedTerm199 : Integer.Sparse Master := [(Sum.inl 0, 16114944298844160000), (Sum.inl 2, 241724164482662400000), (Sum.inl 32, 322298885976883200000)]

def reducedTerm200 : Integer.Sparse Master := []

def reducedTerm201 : Integer.Sparse Master := [(Sum.inl 0, -700615959659642880000), (Sum.inl 1, 1876649891945472000000), (Sum.inl 2, -125109992796364800000), (Sum.inl 3, -2001759884741836800000), (Sum.inl 5, -500439971185459200000), (Sum.inl 7, -2001759884741836800000), (Sum.inl 24, 6005279654225510400000), (Sum.inl 27, 1501319913556377600000), (Sum.inl 68, 3002639827112755200000), (Sum.inl 126, 6005279654225510400000), (Sum.inl 197, 6005279654225510400000)]

def reducedTerm202 : Integer.Sparse Master := [(Sum.inl 0, 646239782471270400000), (Sum.inl 1, -1153999611555840000000), (Sum.inl 2, 230799922311168000000), (Sum.inl 68, 2769599067734016000000), (Sum.inl 126, 11078396270936064000000)]

def reducedTerm203 : Integer.Sparse Master := [(Sum.inl 0, 234548127353917440000), (Sum.inl 1, -111689584454246400000), (Sum.inl 2, -55844792227123200000), (Sum.inl 3, -1787033351267942400000), (Sum.inl 5, 223379168908492800000), (Sum.inl 7, -1787033351267942400000), (Sum.inl 23, 5361100053803827200000), (Sum.inl 24, 2680550026901913600000), (Sum.inl 27, -1340275013450956800000), (Sum.inl 51, 2680550026901913600000), (Sum.inl 54, 2680550026901913600000), (Sum.inl 55, 2680550026901913600000), (Sum.inl 64, 2680550026901913600000), (Sum.inl 68, -1340275013450956800000), (Sum.inl 124, 5361100053803827200000), (Sum.inl 125, 8041650080705740800000), (Sum.inl 126, 5361100053803827200000), (Sum.inl 196, 2680550026901913600000), (Sum.inl 197, 2680550026901913600000), (Sum.inl 266, 2680550026901913600000)]

def reducedTerm204 : Integer.Sparse Master := [(Sum.inl 0, -133422841914163200000), (Sum.inl 1, 266845683828326400000), (Sum.inl 2, -133422841914163200000), (Sum.inl 68, -800537051484979200000), (Sum.inl 125, 3202148205939916800000), (Sum.inl 126, 3202148205939916800000)]

def reducedTerm205 : Integer.Sparse Master := [(Sum.inl 0, 259915748037120000000), (Sum.inl 1, 410393286374400000000), (Sum.inl 2, 820786572748800000000), (Sum.inl 3, -4377528387993600000000), (Sum.inl 4, -1094382096998400000000), (Sum.inl 5, -1641573145497600000000), (Sum.inl 6, 205196643187200000000), (Sum.inl 7, -1094382096998400000000), (Sum.inl 9, -273595524249600000000), (Sum.inl 12, -1094382096998400000000), (Sum.inl 23, 3283146290995200000000), (Sum.inl 25, 3283146290995200000000), (Sum.inl 26, -2188764193996800000000), (Sum.inl 27, 2462359718246400000000), (Sum.inl 35, -1094382096998400000000), (Sum.inl 51, 3283146290995200000000), (Sum.inl 54, 3283146290995200000000), (Sum.inl 55, 3283146290995200000000), (Sum.inl 64, 3283146290995200000000), (Sum.inl 68, 4103932863744000000000), (Sum.inl 123, 3283146290995200000000), (Sum.inl 124, 3283146290995200000000), (Sum.inl 125, 3283146290995200000000), (Sum.inl 259, 3283146290995200000000), (Sum.inl 266, 3283146290995200000000), (Sum.inl 487, -6566292581990400000000)]

def reducedTerm206 : Integer.Sparse Master := [(Sum.inl 0, 93165661403136000000), (Sum.inl 1, -256205568858624000000), (Sum.inl 2, 69874246052352000000), (Sum.inl 5, 186331322806272000000), (Sum.inl 6, -46582830701568000000), (Sum.inl 9, 93165661403136000000), (Sum.inl 51, -1117987936837632000000), (Sum.inl 68, -279496984209408000000), (Sum.inl 123, -1117987936837632000000), (Sum.inl 124, -1117987936837632000000), (Sum.inl 259, -1117987936837632000000)]

def reducedTerm207 : Integer.Sparse Master := [(Sum.inl 0, -366761185652736000000), (Sum.inl 1, 916902964131840000000), (Sum.inl 2, -183380592826368000000), (Sum.inl 5, -366761185652736000000), (Sum.inl 27, 1100283556958208000000), (Sum.inl 68, 2200567113916416000000), (Sum.inl 487, -8802268455665664000000)]

def reducedTerm208 : Integer.Sparse Master := [(Sum.inl 0, 7337089415577600000), (Sum.inl 1, 20176995892838400000), (Sum.inl 2, -18342723538944000000), (Sum.inl 3, -88045072986931200000), (Sum.inl 4, -29348357662310400000), (Sum.inl 5, -22011268246732800000), (Sum.inl 6, 5502817061683200000), (Sum.inl 7, -58696715324620800000), (Sum.inl 8, -58696715324620800000), (Sum.inl 9, -7337089415577600000), (Sum.inl 24, 176090145973862400000), (Sum.inl 27, 44022536493465600000), (Sum.inl 51, 88045072986931200000), (Sum.inl 52, -29348357662310400000), (Sum.inl 68, 110056341233664000000), (Sum.inl 69, -29348357662310400000), (Sum.inl 124, 88045072986931200000), (Sum.inl 126, 352180291947724800000)]

def reducedTerm209 : Integer.Sparse Master := [(Sum.inl 0, -353677486869504000000), (Sum.inl 1, 654958309017600000000), (Sum.inl 2, -458470816312320000000), (Sum.inl 3, -1047933294428160000000), (Sum.inl 6, 130991661803520000000), (Sum.inl 7, -1047933294428160000000), (Sum.inl 9, -261983323607040000000), (Sum.inl 52, -1047933294428160000000), (Sum.inl 68, 785949970821120000000), (Sum.inl 69, -1047933294428160000000), (Sum.inl 126, 3143799883284480000000)]

def reducedTerm210 : Integer.Sparse Master := [(Sum.inl 0, -68203958729195520000), (Sum.inl 1, -232513495667712000000), (Sum.inl 2, -15500899711180800000), (Sum.inl 3, -248014395378892800000), (Sum.inl 5, -62003598844723200000), (Sum.inl 7, -248014395378892800000), (Sum.inl 23, 744043186136678400000), (Sum.inl 27, 186010796534169600000), (Sum.inl 68, 372021593068339200000), (Sum.inl 124, 744043186136678400000), (Sum.inl 125, 744043186136678400000)]

def reducedTerm211 : Integer.Sparse Master := [(Sum.inl 0, -7337089415577600000), (Sum.inl 1, -3668544707788800000), (Sum.inl 2, 3668544707788800000), (Sum.inl 5, -7337089415577600000), (Sum.inl 8, -29348357662310400000), (Sum.inl 24, 88045072986931200000), (Sum.inl 27, 22011268246732800000), (Sum.inl 68, 44022536493465600000), (Sum.inl 126, 176090145973862400000)]

def reducedTerm212 : Integer.Sparse Master := [(Sum.inl 0, -16201095610613760000), (Sum.inl 1, 44184806210764800000), (Sum.inl 2, 22092403105382400000), (Sum.inl 5, -14728268736921600000), (Sum.inl 27, 44184806210764800000), (Sum.inl 55, 176739224843059200000), (Sum.inl 64, 176739224843059200000), (Sum.inl 68, 88369612421529600000), (Sum.inl 125, 176739224843059200000), (Sum.inl 266, 176739224843059200000)]

def reducedTerm213 : Integer.Sparse Master := [(Sum.inl 0, -268055539450675200000), (Sum.inl 1, 694958805983232000000), (Sum.inl 2, -49639914713088000000), (Sum.inl 5, -198559658852352000000), (Sum.inl 51, 2382715906228224000000), (Sum.inl 68, 1191357953114112000000), (Sum.inl 124, 2382715906228224000000), (Sum.inl 126, 2382715906228224000000)]

def reducedTerm214 : Integer.Sparse Master := [(Sum.inl 0, -14760816738877440000), (Sum.inl 1, -67094621540352000000), (Sum.inl 2, -6709462154035200000), (Sum.inl 68, -80513545848422400000), (Sum.inl 124, -322054183393689600000)]

def reducedTerm215 : Integer.Sparse Master := [(Sum.inl 0, 78685742628864000000), (Sum.inl 1, -85065667706880000000), (Sum.inl 2, 42532833853440000000), (Sum.inl 5, 85065667706880000000), (Sum.inl 6, -85065667706880000000), (Sum.inl 8, -340262670827520000000), (Sum.inl 9, -42532833853440000000), (Sum.inl 58, 10633208463360000000), (Sum.inl 68, 127598501560320000000), (Sum.inl 71, -340262670827520000000), (Sum.inl 236, 510394006241280000000)]

def reducedTerm216 : Integer.Sparse Master := [(Sum.inl 0, 18104725497600000000), (Sum.inl 1, -42599354112000000000), (Sum.inl 2, -69223950432000000000), (Sum.inl 3, -340794832896000000000), (Sum.inl 6, -26624596320000000000), (Sum.inl 7, -85198708224000000000), (Sum.inl 9, -42599354112000000000), (Sum.inl 12, -85198708224000000000), (Sum.inl 13, -340794832896000000000), (Sum.inl 35, -170397416448000000000), (Sum.inl 51, 255596124672000000000), (Sum.inl 52, -340794832896000000000), (Sum.inl 58, 5324919264000000000), (Sum.inl 68, 63899031168000000000), (Sum.inl 69, -85198708224000000000), (Sum.inl 126, 255596124672000000000), (Sum.inl 128, -85198708224000000000), (Sum.inl 262, 255596124672000000000), (Sum.inl 495, -85198708224000000000)]

def reducedTerm217 : Integer.Sparse Master := [(Sum.inl 0, -80686253968588800000), (Sum.inl 1, 116782736007168000000), (Sum.inl 2, 106166123642880000000), (Sum.inl 3, 339731595657216000000), (Sum.inl 5, -169865797828608000000), (Sum.inl 6, -31849837092864000000), (Sum.inl 7, 339731595657216000000), (Sum.inl 8, 339731595657216000000), (Sum.inl 9, 84932898914304000000), (Sum.inl 52, 169865797828608000000), (Sum.inl 68, -254798696742912000000), (Sum.inl 69, 169865797828608000000), (Sum.inl 71, 169865797828608000000), (Sum.inl 126, -509597393485824000000), (Sum.inl 236, -509597393485824000000)]

def reducedTerm218 : Integer.Sparse Master := [(Sum.inl 0, -3558834878054400000), (Sum.inl 1, -2542024912896000000), (Sum.inl 2, 6778733101056000000), (Sum.inl 3, 27114932404224000000), (Sum.inl 6, 5931391463424000000), (Sum.inl 7, 13557466202112000000), (Sum.inl 8, 27114932404224000000), (Sum.inl 9, 3389366550528000000), (Sum.inl 52, 27114932404224000000), (Sum.inl 58, -847341637632000000), (Sum.inl 68, -10168099651584000000), (Sum.inl 69, 13557466202112000000), (Sum.inl 71, 13557466202112000000), (Sum.inl 126, -40672398606336000000)]

def reducedTerm219 : Integer.Sparse Master := [(Sum.inl 0, 52434170860216320000), (Sum.inl 1, -38840126563123200000), (Sum.inl 2, -58260189844684800000), (Sum.inl 3, -776802531262464000000), (Sum.inl 4, -155360506252492800000), (Sum.inl 5, 77680253126246400000), (Sum.inl 6, 29130094922342400000), (Sum.inl 7, -466081518757478400000), (Sum.inl 9, -77680253126246400000), (Sum.inl 24, 466081518757478400000), (Sum.inl 26, -310721012504985600000), (Sum.inl 27, 116520379689369600000), (Sum.inl 35, -466081518757478400000), (Sum.inl 52, -155360506252492800000), (Sum.inl 68, 233040759378739200000), (Sum.inl 69, -155360506252492800000), (Sum.inl 70, -155360506252492800000), (Sum.inl 126, 466081518757478400000), (Sum.inl 197, 466081518757478400000)]

def reducedTerm220 : Integer.Sparse Master := [(Sum.inl 0, -18104725497600000000), (Sum.inl 1, 21299677056000000000), (Sum.inl 2, 79873788960000000000), (Sum.inl 3, 340794832896000000000), (Sum.inl 4, 85198708224000000000), (Sum.inl 5, -21299677056000000000), (Sum.inl 6, -21299677056000000000), (Sum.inl 7, 170397416448000000000), (Sum.inl 8, 85198708224000000000), (Sum.inl 9, 42599354112000000000), (Sum.inl 12, 85198708224000000000), (Sum.inl 13, 85198708224000000000), (Sum.inl 26, 85198708224000000000), (Sum.inl 27, -63899031168000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 35, 170397416448000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 52, 170397416448000000000), (Sum.inl 59, -255596124672000000000), (Sum.inl 68, -127798062336000000000), (Sum.inl 81, -255596124672000000000), (Sum.inl 256, -255596124672000000000), (Sum.inl 486, 511192249344000000000)]

def reducedTerm221 : Integer.Sparse Master := [(Sum.inl 0, -42246268968960000000), (Sum.inl 1, 21123134484480000000), (Sum.inl 2, 63369403453440000000), (Sum.inl 3, 844925379379200000000), (Sum.inl 6, -42246268968960000000), (Sum.inl 7, 506955227627520000000), (Sum.inl 9, 84492537937920000000), (Sum.inl 12, 168985075875840000000), (Sum.inl 13, 168985075875840000000), (Sum.inl 23, -506955227627520000000), (Sum.inl 25, -506955227627520000000), (Sum.inl 26, 168985075875840000000), (Sum.inl 27, -126738806906880000000), (Sum.inl 35, 168985075875840000000), (Sum.inl 51, -1013910455255040000000), (Sum.inl 52, 168985075875840000000), (Sum.inl 54, -1013910455255040000000), (Sum.inl 64, -1013910455255040000000), (Sum.inl 68, -253477613813760000000), (Sum.inl 123, -506955227627520000000), (Sum.inl 124, -506955227627520000000), (Sum.inl 125, -506955227627520000000), (Sum.inl 259, -506955227627520000000), (Sum.inl 260, -506955227627520000000)]

def reducedTerm222 : Integer.Sparse Master := [(Sum.inl 0, -15974757792000000000), (Sum.inl 1, -10649838528000000000), (Sum.inl 2, 37274434848000000000), (Sum.inl 3, 170397416448000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -21299677056000000000), (Sum.inl 9, 42599354112000000000), (Sum.inl 12, 85198708224000000000), (Sum.inl 13, 85198708224000000000), (Sum.inl 31, -255596124672000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 51, -511192249344000000000), (Sum.inl 52, 85198708224000000000), (Sum.inl 59, -255596124672000000000), (Sum.inl 68, -127798062336000000000), (Sum.inl 123, -255596124672000000000), (Sum.inl 124, -255596124672000000000), (Sum.inl 126, -255596124672000000000), (Sum.inl 259, -255596124672000000000), (Sum.inl 262, -255596124672000000000)]

def reducedTerm223 : Integer.Sparse Master := [(Sum.inl 0, 16000397354188800000), (Sum.inl 1, 90002235117312000000), (Sum.inl 2, -50001241731840000000), (Sum.inl 3, -320007947083776000000), (Sum.inl 5, 160003973541888000000), (Sum.inl 6, -20000496692736000000), (Sum.inl 12, -80001986770944000000), (Sum.inl 13, -320007947083776000000), (Sum.inl 52, -320007947083776000000), (Sum.inl 128, -80001986770944000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm224 : Integer.Sparse Master := [(Sum.inl 0, -42001043054745600000), (Sum.inl 1, -130003228502784000000), (Sum.inl 2, 260006457005568000000), (Sum.inl 3, 960023841251328000000), (Sum.inl 5, -160003973541888000000), (Sum.inl 7, 640015894167552000000), (Sum.inl 8, 640015894167552000000), (Sum.inl 12, 160003973541888000000), (Sum.inl 13, 160003973541888000000), (Sum.inl 26, 160003973541888000000), (Sum.inl 33, -480011920625664000000), (Sum.inl 35, 160003973541888000000), (Sum.inl 51, -960023841251328000000), (Sum.inl 59, -480011920625664000000)]

def reducedTerm225 : Integer.Sparse Master := [(Sum.inl 0, 15322003587072000000), (Sum.inl 1, -2070541025280000000), (Sum.inl 2, 33128656404480000000), (Sum.inl 3, -132514625617920000000), (Sum.inl 5, 41410820505600000000), (Sum.inl 6, -8282164101120000000), (Sum.inl 7, -66257312808960000000), (Sum.inl 26, -66257312808960000000), (Sum.inl 35, -33128656404480000000)]

def reducedTerm226 : Integer.Sparse Master := [(Sum.inl 0, -86385496522752000000), (Sum.inl 1, 50814997954560000000), (Sum.inl 2, 76222496931840000000), (Sum.inl 5, 101629995909120000000), (Sum.inl 6, -50814997954560000000)]

def reducedTerm227 : Integer.Sparse Master := [(Sum.inl 0, 3389366550528000000), (Sum.inl 1, 1694683275264000000), (Sum.inl 2, -2542024912896000000), (Sum.inl 3, 13557466202112000000), (Sum.inl 5, -6778733101056000000), (Sum.inl 6, 2542024912896000000), (Sum.inl 52, 13557466202112000000)]

def reducedTerm228 : Integer.Sparse Master := [(Sum.inl 0, 410608225714176000000), (Sum.inl 1, -912462723809280000000), (Sum.inl 2, 836424163491840000000), (Sum.inl 3, 3649850895237120000000), (Sum.inl 5, -912462723809280000000), (Sum.inl 7, 2433233930158080000000), (Sum.inl 26, 1216616965079040000000), (Sum.inl 35, 1216616965079040000000)]

def reducedTerm229 : Integer.Sparse Master := [(Sum.inl 0, -61562169607680000000), (Sum.inl 1, 30781084803840000000), (Sum.inl 2, -61562169607680000000), (Sum.inl 3, -492497356861440000000), (Sum.inl 6, -30781084803840000000), (Sum.inl 12, -246248678430720000000), (Sum.inl 13, -984994713722880000000), (Sum.inl 52, -492497356861440000000), (Sum.inl 128, -246248678430720000000)]

def reducedTerm230 : Integer.Sparse Master := [(Sum.inl 0, 123124339215360000000), (Sum.inl 1, -123124339215360000000), (Sum.inl 2, 246248678430720000000), (Sum.inl 3, 492497356861440000000), (Sum.inl 5, -246248678430720000000), (Sum.inl 12, 492497356861440000000), (Sum.inl 13, 492497356861440000000), (Sum.inl 33, -1477492070584320000000), (Sum.inl 51, -1477492070584320000000), (Sum.inl 59, -1477492070584320000000)]

def reducedTerm231 : Integer.Sparse Master := [(Sum.inl 0, -115030723033497600000), (Sum.inl 1, 233170384527360000000), (Sum.inl 2, 248715076829184000000), (Sum.inl 3, 994860307316736000000), (Sum.inl 4, 497430153658368000000), (Sum.inl 5, 62178769207296000000), (Sum.inl 6, -31089384603648000000), (Sum.inl 26, 497430153658368000000), (Sum.inl 35, 248715076829184000000), (Sum.inl 52, 497430153658368000000)]

def reducedTerm232 : Integer.Sparse Master := [(Sum.inl 0, 102485434938163200000), (Sum.inl 1, 31056192405504000000), (Sum.inl 2, 217393346838528000000), (Sum.inl 3, 496899078488064000000), (Sum.inl 6, -15528096202752000000), (Sum.inl 52, 248449539244032000000)]

def reducedTerm233 : Integer.Sparse Master := [(Sum.inl 0, 38467406186496000000), (Sum.inl 1, -66899836846080000000), (Sum.inl 2, -16724959211520000000), (Sum.inl 3, 401399021076480000000), (Sum.inl 5, 33449918423040000000), (Sum.inl 6, -8362479605760000000), (Sum.inl 12, 133799673692160000000), (Sum.inl 13, 401399021076480000000), (Sum.inl 26, 133799673692160000000), (Sum.inl 34, 267599347384320000000), (Sum.inl 35, 133799673692160000000), (Sum.inl 60, 133799673692160000000)]

def reducedTerm234 : Integer.Sparse Master := [(Sum.inl 0, 18125392396124160000), (Sum.inl 1, -29130094922342400000), (Sum.inl 2, 19420063281561600000), (Sum.inl 4, 51786835417497600000), (Sum.inl 5, 12946708854374400000), (Sum.inl 6, -3236677213593600000), (Sum.inl 26, 51786835417497600000), (Sum.inl 35, 51786835417497600000), (Sum.inl 52, 51786835417497600000)]

def reducedTerm235 : Integer.Sparse Master := [(Sum.inl 0, 71561691526348800000), (Sum.inl 1, -95415588701798400000), (Sum.inl 2, -23853897175449600000), (Sum.inl 3, -381662354807193600000), (Sum.inl 5, -95415588701798400000), (Sum.inl 26, -381662354807193600000), (Sum.inl 35, -381662354807193600000)]

def reducedTerm236 : Integer.Sparse Master := [(Sum.inl 0, 5070089036759040000), (Sum.inl 1, 33272459303731200000), (Sum.inl 2, -4753208471961600000), (Sum.inl 3, -25350445183795200000), (Sum.inl 5, 6337611295948800000), (Sum.inl 6, 6337611295948800000), (Sum.inl 7, -25350445183795200000), (Sum.inl 9, -12675222591897600000), (Sum.inl 12, -25350445183795200000), (Sum.inl 13, -25350445183795200000), (Sum.inl 23, 76051335551385600000), (Sum.inl 27, 19012833887846400000), (Sum.inl 35, -50700890367590400000), (Sum.inl 68, 38025667775692800000), (Sum.inl 69, -25350445183795200000), (Sum.inl 70, -25350445183795200000), (Sum.inl 124, 76051335551385600000), (Sum.inl 125, 76051335551385600000)]

def reducedTerm237 : Integer.Sparse Master := [(Sum.inl 0, 30538656642170880000), (Sum.inl 1, 178142163745996800000), (Sum.inl 2, -101795522140569600000), (Sum.inl 3, -814364177124556800000), (Sum.inl 5, 203591044281139200000), (Sum.inl 6, -25448880535142400000), (Sum.inl 13, -814364177124556800000), (Sum.inl 35, -407182088562278400000), (Sum.inl 52, -814364177124556800000)]

def reducedTerm238 : Integer.Sparse Master := [(Sum.inl 0, -7120733554851840000), (Sum.inl 1, -63711826543411200000), (Sum.inl 2, 18738772512768000000), (Sum.inl 3, 59964072040857600000), (Sum.inl 5, -44973054030643200000), (Sum.inl 6, 5621631753830400000), (Sum.inl 7, 29982036020428800000), (Sum.inl 8, 59964072040857600000)]

def reducedTerm239 : Integer.Sparse Master := [(Sum.inl 0, 19169709350400000000), (Sum.inl 1, 69223950432000000000), (Sum.inl 2, -53249192640000000000), (Sum.inl 3, -596390957568000000000), (Sum.inl 4, -170397416448000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 7, -170397416448000000000), (Sum.inl 12, -170397416448000000000), (Sum.inl 13, -425993541120000000000), (Sum.inl 26, -340794832896000000000), (Sum.inl 34, -170397416448000000000), (Sum.inl 35, -340794832896000000000), (Sum.inl 52, -170397416448000000000), (Sum.inl 67, -85198708224000000000)]

def reducedTerm240 : Integer.Sparse Master := [(Sum.inl 0, -13844790086400000000), (Sum.inl 1, -69223950432000000000), (Sum.inl 2, -21299677056000000000), (Sum.inl 3, -170397416448000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -10649838528000000000), (Sum.inl 13, -170397416448000000000), (Sum.inl 35, -85198708224000000000), (Sum.inl 52, -170397416448000000000)]

def reducedTerm241 : Integer.Sparse Master := [(Sum.inl 0, -16151153057464320000), (Sum.inl 1, -10094470660915200000), (Sum.inl 2, 30283411982745600000), (Sum.inl 3, -161511530574643200000), (Sum.inl 5, 40377882643660800000), (Sum.inl 7, -80755765287321600000), (Sum.inl 13, -80755765287321600000), (Sum.inl 26, -161511530574643200000), (Sum.inl 34, -80755765287321600000), (Sum.inl 35, -161511530574643200000), (Sum.inl 67, -80755765287321600000)]

def reducedTerm242 : Integer.Sparse Master := [(Sum.inl 0, 13556036512972800000), (Sum.inl 1, 4107889852416000000), (Sum.inl 2, 22593394188288000000), (Sum.inl 3, 32863118819328000000), (Sum.inl 5, -32863118819328000000), (Sum.inl 7, 32863118819328000000), (Sum.inl 8, 32863118819328000000)]

def reducedTerm243 : Integer.Sparse Master := [(Sum.inl 0, 3897771533107200000), (Sum.inl 1, 11862782926848000000), (Sum.inl 2, -11015441289216000000), (Sum.inl 3, -54229864808448000000), (Sum.inl 5, 13557466202112000000), (Sum.inl 6, -1694683275264000000), (Sum.inl 7, -27114932404224000000), (Sum.inl 8, -13557466202112000000), (Sum.inl 12, -27114932404224000000), (Sum.inl 13, -27114932404224000000), (Sum.inl 35, -13557466202112000000), (Sum.inl 51, 40672398606336000000), (Sum.inl 52, -13557466202112000000)]

def reducedTerm244 : Integer.Sparse Master := [(Sum.inl 0, 46554147249684480000), (Sum.inl 1, 287540321248051200000), (Sum.inl 3, -2409861739983667200000), (Sum.inl 4, -438156679997030400000), (Sum.inl 5, 109539169999257600000), (Sum.inl 6, -27384792499814400000), (Sum.inl 7, -219078339998515200000), (Sum.inl 13, -876313359994060800000), (Sum.inl 26, -1752626719988121600000), (Sum.inl 34, -1095391699992576000000), (Sum.inl 35, -657235019995545600000), (Sum.inl 52, -219078339998515200000), (Sum.inl 64, 657235019995545600000), (Sum.inl 67, -438156679997030400000)]

def reducedTerm245 : Integer.Sparse Master := [(Sum.inl 0, 17616278421504000000), (Sum.inl 1, 13212208816128000000), (Sum.inl 2, 48444765659136000000), (Sum.inl 3, 140930227372032000000), (Sum.inl 5, -35232556843008000000), (Sum.inl 7, 70465113686016000000), (Sum.inl 26, 140930227372032000000), (Sum.inl 34, 70465113686016000000), (Sum.inl 35, 70465113686016000000), (Sum.inl 64, -211395341058048000000), (Sum.inl 67, 70465113686016000000)]

def reducedTerm246 : Integer.Sparse Master := [(Sum.inl 0, -24494628614400000000), (Sum.inl 1, 5324919264000000000), (Sum.inl 2, 58574111904000000000), (Sum.inl 3, 766788374016000000000), (Sum.inl 4, 255596124672000000000), (Sum.inl 5, 63899031168000000000), (Sum.inl 6, -15974757792000000000), (Sum.inl 7, 85198708224000000000), (Sum.inl 12, 85198708224000000000), (Sum.inl 13, 85198708224000000000), (Sum.inl 26, 425993541120000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 34, 170397416448000000000), (Sum.inl 35, 170397416448000000000), (Sum.inl 67, 85198708224000000000), (Sum.inl 81, -255596124672000000000)]

def reducedTerm247 : Integer.Sparse Master := [(Sum.inl 0, 366776653049856000000), (Sum.inl 1, -1047933294428160000000), (Sum.inl 2, 196487492705280000000), (Sum.inl 3, 3143799883284480000000), (Sum.inl 4, 1047933294428160000000), (Sum.inl 5, 261983323607040000000), (Sum.inl 6, -65495830901760000000), (Sum.inl 7, 1047933294428160000000), (Sum.inl 26, 2095866588856320000000), (Sum.inl 35, 1047933294428160000000)]

def reducedTerm248 : Integer.Sparse Master := [(Sum.inl 0, 14909773939200000000), (Sum.inl 1, 42599354112000000000), (Sum.inl 2, 26624596320000000000), (Sum.inl 3, 170397416448000000000), (Sum.inl 4, 85198708224000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 26, 85198708224000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 81, -255596124672000000000)]

def reducedTerm249 : Integer.Sparse Master := [(Sum.inl 0, 60748852237516800000), (Sum.inl 1, -86784074625024000000), (Sum.inl 2, -136374974410752000000), (Sum.inl 3, -198363599142912000000), (Sum.inl 6, 18596587419648000000), (Sum.inl 7, -99181799571456000000), (Sum.inl 8, -198363599142912000000)]

def reducedTerm250 : Integer.Sparse Master := [(Sum.inl 0, 174007369819422720000), (Sum.inl 1, 870036849097113600000), (Sum.inl 2, -22895706555187200000), (Sum.inl 3, 366331304882995200000), (Sum.inl 6, -22895706555187200000), (Sum.inl 7, 366331304882995200000)]

def reducedTerm251 : Integer.Sparse Master := [(Sum.inl 0, -62081584624926720000), (Sum.inl 1, 26417695585075200000), (Sum.inl 2, -39626543377612800000), (Sum.inl 6, 6604423896268800000), (Sum.inl 8, -105670782340300800000)]

def reducedTerm252 : Integer.Sparse Master := [(Sum.inl 0, -10140178073518080000), (Sum.inl 1, -82388946847334400000), (Sum.inl 2, -3168805647974400000), (Sum.inl 5, -12675222591897600000), (Sum.inl 6, 3168805647974400000), (Sum.inl 7, -50700890367590400000), (Sum.inl 12, -50700890367590400000), (Sum.inl 13, -50700890367590400000), (Sum.inl 35, -50700890367590400000)]

def reducedTerm253 : Integer.Sparse Master := [(Sum.inl 0, -81256640573767680000), (Sum.inl 1, 153728779463884800000), (Sum.inl 2, -109806271045632000000), (Sum.inl 3, -351380067346022400000), (Sum.inl 6, 10980627104563200000), (Sum.inl 7, -175690033673011200000)]

def reducedTerm254 : Integer.Sparse Master := [(Sum.inl 0, 60870745777766400000), (Sum.inl 1, 57972138835968000000), (Sum.inl 2, 115944277671936000000), (Sum.inl 3, 695665666031616000000), (Sum.inl 4, 231888555343872000000), (Sum.inl 5, 57972138835968000000), (Sum.inl 6, -14493034708992000000), (Sum.inl 13, 231888555343872000000), (Sum.inl 26, 695665666031616000000), (Sum.inl 34, 463777110687744000000), (Sum.inl 35, 231888555343872000000), (Sum.inl 67, 231888555343872000000)]

def reducedTerm255 : Integer.Sparse Master := [(Sum.inl 0, -67437749651005440000), (Sum.inl 1, 177467762239488000000), (Sum.inl 2, 106480657343692800000), (Sum.inl 5, -70987104895795200000), (Sum.inl 6, -17746776223948800000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm256 : Integer.Sparse Master := [(Sum.inl 0, -39759154569953280000), (Sum.inl 1, -36144685972684800000), (Sum.inl 2, -18072342986342400000), (Sum.inl 5, 72289371945369600000), (Sum.inl 26, 289157487781478400000), (Sum.inl 34, 289157487781478400000), (Sum.inl 67, 289157487781478400000)]

def reducedTerm257 : Integer.Sparse Master := [(Sum.inl 0, -244968768737280000000), (Sum.inl 1, -1143187587440640000000), (Sum.inl 2, -81656256245760000000), (Sum.inl 3, 1306500099932160000000), (Sum.inl 5, 326625024983040000000), (Sum.inl 7, 1306500099932160000000)]

def reducedTerm258 : Integer.Sparse Master := [(Sum.inl 0, 3893389661306880000), (Sum.inl 1, -3244491384422400000), (Sum.inl 5, -3244491384422400000), (Sum.inl 8, -12977965537689600000)]

def reducedTerm259 : Integer.Sparse Master := [(Sum.inl 0, 22364660908800000000), (Sum.inl 1, 47924273376000000000), (Sum.inl 2, -101173466016000000000), (Sum.inl 3, -851987082240000000000), (Sum.inl 5, 42599354112000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 7, -85198708224000000000), (Sum.inl 12, -340794832896000000000), (Sum.inl 13, -596390957568000000000), (Sum.inl 34, -85198708224000000000), (Sum.inl 35, -85198708224000000000), (Sum.inl 51, 511192249344000000000), (Sum.inl 52, -255596124672000000000), (Sum.inl 54, 255596124672000000000), (Sum.inl 64, 255596124672000000000)]

def reducedTerm260 : Integer.Sparse Master := [(Sum.inl 0, 125095232928153600000), (Sum.inl 1, -218916657624268800000), (Sum.inl 2, 281464274088345600000), (Sum.inl 3, 500380931712614400000), (Sum.inl 5, -250190465856307200000), (Sum.inl 7, 500380931712614400000), (Sum.inl 51, -1501142795137843200000), (Sum.inl 54, -1501142795137843200000), (Sum.inl 64, -1501142795137843200000)]

def reducedTerm261 : Integer.Sparse Master := [(Sum.inl 0, -22364660908800000000), (Sum.inl 2, 85198708224000000000), (Sum.inl 3, 596390957568000000000), (Sum.inl 4, 170397416448000000000), (Sum.inl 5, 63899031168000000000), (Sum.inl 6, -15974757792000000000), (Sum.inl 12, 170397416448000000000), (Sum.inl 13, 170397416448000000000), (Sum.inl 25, -255596124672000000000), (Sum.inl 26, 170397416448000000000), (Sum.inl 31, -511192249344000000000), (Sum.inl 33, -511192249344000000000), (Sum.inl 34, 85198708224000000000), (Sum.inl 51, -511192249344000000000), (Sum.inl 52, 85198708224000000000), (Sum.inl 64, -255596124672000000000), (Sum.inl 123, -511192249344000000000)]

def reducedTerm262 : Integer.Sparse Master := [(Sum.inl 0, 195647888946585600000), (Sum.inl 1, -419245476314112000000), (Sum.inl 2, 326079814910976000000), (Sum.inl 3, 745325291225088000000), (Sum.inl 5, 186331322806272000000), (Sum.inl 6, -46582830701568000000), (Sum.inl 25, -2235975873675264000000), (Sum.inl 26, 745325291225088000000), (Sum.inl 64, -2235975873675264000000), (Sum.inl 123, -2235975873675264000000)]

def reducedTerm263 : Integer.Sparse Master := [(Sum.inl 0, 15974757792000000000), (Sum.inl 1, 21299677056000000000), (Sum.inl 2, 10649838528000000000), (Sum.inl 5, 21299677056000000000), (Sum.inl 6, -5324919264000000000), (Sum.inl 31, -255596124672000000000), (Sum.inl 33, -255596124672000000000), (Sum.inl 51, -255596124672000000000), (Sum.inl 123, -255596124672000000000)]

def reducedTerm264 : Integer.Sparse Master := [(Sum.inl 0, -93165661403136000000), (Sum.inl 1, 139748492104704000000), (Sum.inl 6, -46582830701568000000), (Sum.inl 123, -2235975873675264000000)]

def reducedTerm265 : Integer.Sparse Master := [(Sum.inl 0, -9171361769472000000), (Sum.inl 1, -11005634123366400000), (Sum.inl 2, 55028170616832000000), (Sum.inl 3, 264135218960793600000), (Sum.inl 4, 88045072986931200000), (Sum.inl 5, 22011268246732800000), (Sum.inl 6, -5502817061683200000), (Sum.inl 12, 88045072986931200000), (Sum.inl 13, 58696715324620800000), (Sum.inl 51, -264135218960793600000), (Sum.inl 52, 88045072986931200000)]

def reducedTerm266 : Integer.Sparse Master := [(Sum.inl 0, 7337089415577600000), (Sum.inl 1, 3668544707788800000), (Sum.inl 2, 9171361769472000000), (Sum.inl 3, 58696715324620800000), (Sum.inl 4, 29348357662310400000), (Sum.inl 5, 7337089415577600000), (Sum.inl 6, -1834272353894400000), (Sum.inl 51, -88045072986931200000), (Sum.inl 52, 29348357662310400000)]

def reducedTerm267 : Integer.Sparse Master := [(Sum.inl 0, -296377098135552000000), (Sum.inl 1, 548846478028800000000), (Sum.inl 2, -439077182423040000000), (Sum.inl 3, -1756308729692160000000), (Sum.inl 5, -219538591211520000000), (Sum.inl 6, 54884647802880000000), (Sum.inl 12, -878154364846080000000), (Sum.inl 13, -878154364846080000000), (Sum.inl 51, 2634463094538240000000), (Sum.inl 52, -878154364846080000000)]

def reducedTerm268 : Integer.Sparse Master := [(Sum.inl 0, -6712348286730240000), (Sum.inl 1, 9153202209177600000), (Sum.inl 5, 12204269612236800000), (Sum.inl 64, -146451235346841600000)]

def reducedTerm269 : Integer.Sparse Master := [(Sum.inl 0, 305874420668006400000), (Sum.inl 1, -327722593572864000000), (Sum.inl 2, 327722593572864000000), (Sum.inl 5, -436963458097152000000), (Sum.inl 51, 5243561497165824000000)]

def reducedTerm270 : Integer.Sparse Master := [(Sum.inl 0, -18066028525977600000), (Sum.inl 1, 23771090165760000000), (Sum.inl 2, -47542180331520000000), (Sum.inl 3, 152134977060864000000), (Sum.inl 5, 76067488530432000000), (Sum.inl 12, 76067488530432000000), (Sum.inl 13, 76067488530432000000), (Sum.inl 23, -456404931182592000000), (Sum.inl 25, -228202465591296000000), (Sum.inl 26, 76067488530432000000), (Sum.inl 27, -114101232795648000000), (Sum.inl 33, -228202465591296000000), (Sum.inl 35, 76067488530432000000), (Sum.inl 54, -456404931182592000000), (Sum.inl 55, -456404931182592000000), (Sum.inl 63, -456404931182592000000), (Sum.inl 64, -228202465591296000000), (Sum.inl 65, -456404931182592000000), (Sum.inl 68, -228202465591296000000), (Sum.inl 125, -228202465591296000000), (Sum.inl 196, -228202465591296000000), (Sum.inl 264, -228202465591296000000), (Sum.inl 266, -228202465591296000000)]

def reducedTerm271 : Integer.Sparse Master := [(Sum.inl 0, 11103917727006720000), (Sum.inl 1, 22712558987059200000), (Sum.inl 2, -12618088326144000000), (Sum.inl 3, -323023061149286400000), (Sum.inl 5, 10094470660915200000), (Sum.inl 7, -40377882643660800000), (Sum.inl 12, -121133647930982400000), (Sum.inl 13, -242267295861964800000), (Sum.inl 23, 121133647930982400000), (Sum.inl 26, -161511530574643200000), (Sum.inl 27, -30283411982745600000), (Sum.inl 34, -80755765287321600000), (Sum.inl 35, -121133647930982400000), (Sum.inl 55, 242267295861964800000), (Sum.inl 63, 121133647930982400000), (Sum.inl 65, 121133647930982400000), (Sum.inl 67, -40377882643660800000)]

def reducedTerm272 : Integer.Sparse Master := [(Sum.inl 0, 67004361126420480000), (Sum.inl 1, -151300170285465600000), (Sum.inl 2, 10807155020390400000), (Sum.inl 3, -1037486881957478400000), (Sum.inl 5, -129685860244684800000), (Sum.inl 12, -345828960652492800000), (Sum.inl 13, -518743440978739200000), (Sum.inl 25, 518743440978739200000), (Sum.inl 26, -172914480326246400000), (Sum.inl 27, 389057580734054400000), (Sum.inl 33, 1556230322936217600000), (Sum.inl 35, -172914480326246400000), (Sum.inl 55, 1037486881957478400000), (Sum.inl 63, 518743440978739200000), (Sum.inl 64, 1037486881957478400000)]

def reducedTerm273 : Integer.Sparse Master := [(Sum.inl 0, -8960584204615680000), (Sum.inl 1, -72182483870515200000), (Sum.inl 2, 12445255839744000000), (Sum.inl 3, 398248186871808000000), (Sum.inl 4, 159299274748723200000), (Sum.inl 5, -9956204671795200000), (Sum.inl 7, 39824818687180800000), (Sum.inl 12, 39824818687180800000), (Sum.inl 13, 39824818687180800000), (Sum.inl 24, -119474456061542400000), (Sum.inl 26, 238948912123084800000), (Sum.inl 27, 29868614015385600000), (Sum.inl 33, -119474456061542400000), (Sum.inl 34, 79649637374361600000), (Sum.inl 35, 79649637374361600000), (Sum.inl 55, -358423368184627200000), (Sum.inl 64, -119474456061542400000), (Sum.inl 66, -119474456061542400000), (Sum.inl 67, 39824818687180800000)]

def reducedTerm274 : Integer.Sparse Master := [(Sum.inl 0, -30805224690401280000), (Sum.inl 1, -67952701522944000000), (Sum.inl 2, -95133782132121600000), (Sum.inl 3, 869794579493683200000), (Sum.inl 4, 434897289746841600000), (Sum.inl 5, 54362161218355200000), (Sum.inl 12, 217448644873420800000), (Sum.inl 13, 144965763248947200000), (Sum.inl 26, 434897289746841600000), (Sum.inl 27, -163086483655065600000), (Sum.inl 35, 217448644873420800000), (Sum.inl 55, -652345934620262400000)]

def reducedTerm275 : Integer.Sparse Master := [(Sum.inl 0, -101826617879347200000), (Sum.inl 1, 246354720675840000000), (Sum.inl 2, 197083776540672000000), (Sum.inl 3, -525556737441792000000), (Sum.inl 5, -65694592180224000000), (Sum.inl 12, -262778368720896000000), (Sum.inl 13, -262778368720896000000), (Sum.inl 26, -262778368720896000000), (Sum.inl 27, 197083776540672000000), (Sum.inl 35, -262778368720896000000), (Sum.inl 55, 788335106162688000000)]

def reducedTerm276 : Integer.Sparse Master := [(Sum.inl 0, -73488654138654720000), (Sum.inl 1, -129685860244684800000), (Sum.inl 2, 194528790367027200000), (Sum.inl 3, -345828960652492800000), (Sum.inl 5, -86457240163123200000), (Sum.inl 27, 259371720489369600000), (Sum.inl 33, 1037486881957478400000), (Sum.inl 55, 1037486881957478400000), (Sum.inl 64, 1037486881957478400000)]

def reducedTerm277 : Integer.Sparse Master := [(Sum.inl 0, 26816045856768000000), (Sum.inl 1, 32179255028121600000), (Sum.inl 2, -5363209171353600000), (Sum.inl 3, -600679427191603200000), (Sum.inl 4, -171622693483315200000), (Sum.inl 5, 21452836685414400000), (Sum.inl 7, -85811346741657600000), (Sum.inl 12, -85811346741657600000), (Sum.inl 13, -85811346741657600000), (Sum.inl 23, 257434040224972800000), (Sum.inl 25, 514868080449945600000), (Sum.inl 26, -343245386966630400000), (Sum.inl 27, -64358510056243200000), (Sum.inl 33, 514868080449945600000), (Sum.inl 34, -171622693483315200000), (Sum.inl 35, -85811346741657600000), (Sum.inl 55, 257434040224972800000), (Sum.inl 63, 514868080449945600000), (Sum.inl 64, 514868080449945600000), (Sum.inl 65, 257434040224972800000), (Sum.inl 67, -85811346741657600000)]

def reducedTerm278 : Integer.Sparse Master := [(Sum.inl 0, -153380792709365760000), (Sum.inl 1, 348592710703104000000), (Sum.inl 2, 139437084281241600000), (Sum.inl 23, 1673245011374899200000), (Sum.inl 27, -836622505687449600000), (Sum.inl 55, 1673245011374899200000), (Sum.inl 63, 1673245011374899200000), (Sum.inl 65, 1673245011374899200000)]

def reducedTerm279 : Integer.Sparse Master := [(Sum.inl 0, -1768209428643840000), (Sum.inl 1, 2947015714406400000), (Sum.inl 2, 2947015714406400000), (Sum.inl 5, -1473507857203200000), (Sum.inl 25, 17682094286438400000), (Sum.inl 27, 4420523571609600000), (Sum.inl 33, 17682094286438400000), (Sum.inl 63, 17682094286438400000), (Sum.inl 64, 17682094286438400000)]

def reducedTerm280 : Integer.Sparse Master := [(Sum.inl 0, -77745385499443200000), (Sum.inl 1, 70677623181312000000), (Sum.inl 2, -459404550678528000000), (Sum.inl 27, -424065739087872000000), (Sum.inl 63, -1696262956351488000000)]

def reducedTerm281 : Integer.Sparse Master := [(Sum.inl 0, 6969343270256640000), (Sum.inl 1, 29868614015385600000), (Sum.inl 2, 4978102335897600000), (Sum.inl 24, -119474456061542400000), (Sum.inl 27, 59737228030771200000), (Sum.inl 55, -238948912123084800000), (Sum.inl 66, -119474456061542400000)]

def reducedTerm286 : Integer.Sparse Master := [(Sum.inl 0, -18179750891151360000), (Sum.inl 1, -68174065841817600000), (Sum.inl 2, -68174065841817600000), (Sum.inl 13, -363595017823027200000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge9 : Integer.Sparse Master := [(Sum.inl 0, -85643809957601280000), (Sum.inl 1, 180952399595520000000), (Sum.inl 2, 75709144472371200000), (Sum.inl 5, 71961408781516800000), (Sum.inl 6, 46175033821593600000), (Sum.inl 7, -438163937132544000000), (Sum.inl 9, 80556867101491200000), (Sum.inl 35, -219081968566272000000), (Sum.inl 58, 34631275366195200000), (Sum.inl 69, -657245905698816000000), (Sum.inl 70, -657245905698816000000), (Sum.inl 71, -219081968566272000000), (Sum.inl 257, -219081968566272000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge80 : Integer.Sparse Master := [(Sum.inl 0, 59909030263111680000), (Sum.inl 1, -104351430087475200000), (Sum.inl 2, 48526669707264000000), (Sum.inl 3, 58896921968640000000), (Sum.inl 5, -153460240367616000000), (Sum.inl 6, -17038228348108800000), (Sum.inl 7, 374013434304921600000), (Sum.inl 8, 382971816286617600000), (Sum.inl 9, 112516192464076800000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -17916763963392000000), (Sum.inl 58, -3168805647974400000), (Sum.inl 67, -34308827165491200000), (Sum.inl 69, 292887688878489600000), (Sum.inl 70, 33546476784844800000), (Sum.inl 71, 191485908143308800000), (Sum.inl 257, -17154413582745600000)]

def reducedMerge81 : Integer.Sparse Master := [(Sum.inl 0, -140133420229017600000), (Sum.inl 1, -522315475399065600000), (Sum.inl 2, -12739401839001600000), (Sum.inl 3, -407660858848051200000), (Sum.inl 5, 203830429424025600000), (Sum.inl 6, 76436411034009600000), (Sum.inl 9, -254788036780032000000), (Sum.inl 35, -407660858848051200000), (Sum.inl 58, -12739401839001600000), (Sum.inl 69, -407660858848051200000), (Sum.inl 70, -407660858848051200000)]

def reducedMerge82 : Integer.Sparse Master := [(Sum.inl 0, 113689278739169280000), (Sum.inl 1, -386136786960691200000), (Sum.inl 2, 51955192287129600000), (Sum.inl 3, 541647721488384000000), (Sum.inl 5, -99207510983884800000), (Sum.inl 6, -76757070033100800000), (Sum.inl 7, 1228113120529612800000), (Sum.inl 8, 541647721488384000000), (Sum.inl 9, 307028280132403200000), (Sum.inl 35, 686465399041228800000), (Sum.inl 70, 144817677552844800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000)]

def reducedMerge83 : Integer.Sparse Master := [(Sum.inl 0, -26444141489848320000), (Sum.inl 1, -908452262359756800000), (Sum.inl 2, 39215790448128000000), (Sum.inl 3, 133986862640332800000), (Sum.inl 5, 104622918440140800000), (Sum.inl 6, -320658999091200000), (Sum.inl 7, 1228113120529612800000), (Sum.inl 8, 541647721488384000000), (Sum.inl 9, 52240243352371200000), (Sum.inl 35, 278804540193177600000), (Sum.inl 58, -12739401839001600000), (Sum.inl 69, -407660858848051200000), (Sum.inl 70, -262843181295206400000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000)]

def reducedMerge84 : Integer.Sparse Master := [(Sum.inl 0, 33464888773263360000), (Sum.inl 1, -1012803692447232000000), (Sum.inl 2, 87742460155392000000), (Sum.inl 3, 192883784608972800000), (Sum.inl 5, -48837321927475200000), (Sum.inl 6, -17358887347200000000), (Sum.inl 7, 1602126554834534400000), (Sum.inl 8, 924619537775001600000), (Sum.inl 9, 164756435816448000000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, 260887776229785600000), (Sum.inl 58, -15908207486976000000), (Sum.inl 67, -34308827165491200000), (Sum.inl 69, -114773169969561600000), (Sum.inl 70, -229296704510361600000), (Sum.inl 71, 191485908143308800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, -17154413582745600000)]

def reducedMerge85 : Integer.Sparse Master := [(Sum.inl 0, 28675185395834880000), (Sum.inl 1, -1121719648618598400000), (Sum.inl 2, -470589938425958400000), (Sum.inl 3, -555911278549401600000), (Sum.inl 5, -199385626219315200000), (Sum.inl 6, -58881087743385600000), (Sum.inl 7, 1875671109830246400000), (Sum.inl 8, 1052703422978457600000), (Sum.inl 9, 16778123163648000000), (Sum.inl 26, -17154413582745600000), (Sum.inl 35, -63549230756659200000), (Sum.inl 52, -644490545268326400000), (Sum.inl 58, -31814174291558400000), (Sum.inl 67, 142244621697024000000), (Sum.inl 69, 190595011151462400000), (Sum.inl 70, 457811686770278400000), (Sum.inl 71, 526717135016755200000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, 159399035279769600000), (Sum.inl 495, -541647721488384000000)]

def reducedMerge86 : Integer.Sparse Master := [(Sum.inl 0, -69228300480675840000), (Sum.inl 1, -1475102869302988800000), (Sum.inl 2, -608724985578393600000), (Sum.inl 3, 1649991811468492800000), (Sum.inl 5, 1165792611439411200000), (Sum.inl 6, 58163083853414400000), (Sum.inl 7, 4630438147674931200000), (Sum.inl 8, 843289614345830400000), (Sum.inl 9, -250871296783564800000), (Sum.inl 12, -89366440181760000000), (Sum.inl 13, 54319358332108800000), (Sum.inl 26, 518144426311680000000), (Sum.inl 35, 3705179530493952000000), (Sum.inl 52, -1661451422058086400000), (Sum.inl 58, -31814174291558400000), (Sum.inl 59, 804297961635840000000), (Sum.inl 60, 315769437152870400000), (Sum.inl 67, 1212842301485875200000), (Sum.inl 69, 2331790370729164800000), (Sum.inl 70, 2599007046347980800000), (Sum.inl 71, 1062015974911180800000), (Sum.inl 81, -1624943164465152000000), (Sum.inl 128, 716680257011712000000), (Sum.inl 256, -1624943164465152000000), (Sum.inl 257, 694697875174195200000), (Sum.inl 495, -541647721488384000000)]

def reducedMerge87 : Integer.Sparse Master := [(Sum.inl 0, -22184324592353280000), (Sum.inl 1, -188384061693542400000), (Sum.inl 2, -47676947344588800000), (Sum.inl 5, -24688047631564800000), (Sum.inl 6, -10644875897241600000), (Sum.inl 7, 269070204882124800000), (Sum.inl 9, 42579503588966400000), (Sum.inl 35, -98752190526259200000), (Sum.inl 67, -98752190526259200000), (Sum.inl 69, 269070204882124800000), (Sum.inl 257, -98752190526259200000)]

def reducedMerge88 : Integer.Sparse Master := [(Sum.inl 0, -58435109384601600000), (Sum.inl 1, -110703808567296000000), (Sum.inl 2, -60623656198963200000), (Sum.inl 5, -24688047631564800000), (Sum.inl 6, -23591584751616000000), (Sum.inl 7, 269070204882124800000), (Sum.inl 8, 207147341669990400000), (Sum.inl 9, 94366339006464000000), (Sum.inl 35, -98752190526259200000), (Sum.inl 67, -98752190526259200000), (Sum.inl 69, 269070204882124800000), (Sum.inl 71, 207147341669990400000), (Sum.inl 257, -98752190526259200000)]

def reducedMerge89 : Integer.Sparse Master := [(Sum.inl 0, 289480239059558400000), (Sum.inl 1, -500624680124620800000), (Sum.inl 2, 235007393983488000000), (Sum.inl 5, 95451811673702400000), (Sum.inl 6, 664043215352832000000), (Sum.inl 8, 626686383955968000000), (Sum.inl 35, 1253372767911936000000), (Sum.inl 67, 626686383955968000000)]

def reducedMerge90 : Integer.Sparse Master := [(Sum.inl 0, -241954585850880000000), (Sum.inl 1, 386954463071232000000), (Sum.inl 2, -476621953145856000000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1019307678068736000000), (Sum.inl 6, -180611557733376000000), (Sum.inl 7, -1578722108866560000000), (Sum.inl 8, -789361054433280000000), (Sum.inl 35, -919786494541824000000)]

def reducedMerge91 : Integer.Sparse Master := [(Sum.inl 0, 47525653208678400000), (Sum.inl 1, -113670217053388800000), (Sum.inl 2, -241614559162368000000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1114759489742438400000), (Sum.inl 6, 483431657619456000000), (Sum.inl 7, -1578722108866560000000), (Sum.inl 8, -162674670477312000000), (Sum.inl 35, 333586273370112000000), (Sum.inl 67, 626686383955968000000)]

def reducedMerge92 : Integer.Sparse Master := [(Sum.inl 0, -10909456175923200000), (Sum.inl 1, -224374025620684800000), (Sum.inl 2, -302238215361331200000), (Sum.inl 3, -789361054433280000000), (Sum.inl 5, 1090071442110873600000), (Sum.inl 6, 459840072867840000000), (Sum.inl 7, -1309651903984435200000), (Sum.inl 8, 44472671192678400000), (Sum.inl 9, 94366339006464000000), (Sum.inl 35, 234834082843852800000), (Sum.inl 67, 527934193429708800000), (Sum.inl 69, 269070204882124800000), (Sum.inl 71, 207147341669990400000), (Sum.inl 257, -98752190526259200000)]

def reducedMerge93 : Integer.Sparse Master := [(Sum.inl 0, 66274055221248000000), (Sum.inl 1, -178540491025612800000), (Sum.inl 2, -156261526028697600000), (Sum.inl 3, -205685647559884800000), (Sum.inl 5, 261101640167424000000), (Sum.inl 6, -150832494721843200000), (Sum.inl 7, -205685647559884800000), (Sum.inl 26, -102842823779942400000), (Sum.inl 35, -1044406560669696000000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, -102842823779942400000)]

def reducedMerge94 : Integer.Sparse Master := [(Sum.inl 0, 52981975901675520000), (Sum.inl 1, -97945332710400000000), (Sum.inl 2, 109112309552332800000), (Sum.inl 5, 333929093595955200000), (Sum.inl 7, -115704474491289600000), (Sum.inl 8, -988602950909952000000), (Sum.inl 35, 872898476418662400000), (Sum.inl 67, 872898476418662400000)]

def reducedMerge95 : Integer.Sparse Master := [(Sum.inl 0, 119256031122923520000), (Sum.inl 1, -276485823736012800000), (Sum.inl 2, -47149216476364800000), (Sum.inl 3, -205685647559884800000), (Sum.inl 5, 595030733763379200000), (Sum.inl 6, -150832494721843200000), (Sum.inl 7, -321390122051174400000), (Sum.inl 8, -988602950909952000000), (Sum.inl 26, -102842823779942400000), (Sum.inl 35, -171508084251033600000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, 770055652638720000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge96 : Integer.Sparse Master := [(Sum.inl 0, 114155842844897280000), (Sum.inl 1, -614075176531353600000), (Sum.inl 2, -173630135889100800000), (Sum.inl 3, 1287125872400793600000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 457193398472294400000), (Sum.inl 6, -114298349618073600000), (Sum.inl 7, 745478150912409600000), (Sum.inl 26, 1083295442976768000000), (Sum.inl 35, 1287125872400793600000), (Sum.inl 67, 541647721488384000000), (Sum.inl 81, -1624943164465152000000)]

def reducedMerge97 : Integer.Sparse Master := [(Sum.inl 0, -143394562057420800000), (Sum.inl 1, 173183026738176000000), (Sum.inl 2, -250867281530880000000), (Sum.inl 5, 270823860744192000000), (Sum.inl 6, -57727675579392000000), (Sum.inl 35, -159652633706496000000), (Sum.inl 81, -3249886328930304000000)]

def reducedMerge98 : Integer.Sparse Master := [(Sum.inl 0, -29238719212523520000), (Sum.inl 1, -440892149793177600000), (Sum.inl 2, -424497417419980800000), (Sum.inl 3, 1287125872400793600000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 728017259216486400000), (Sum.inl 6, -172026025197465600000), (Sum.inl 7, 745478150912409600000), (Sum.inl 26, 1083295442976768000000), (Sum.inl 35, 1127473238694297600000), (Sum.inl 67, 541647721488384000000), (Sum.inl 81, -4874829493395456000000)]

def reducedMerge99 : Integer.Sparse Master := [(Sum.inl 0, 90017311910400000000), (Sum.inl 1, -717377973529190400000), (Sum.inl 2, -471646633896345600000), (Sum.inl 3, 1081440224840908800000), (Sum.inl 4, 541647721488384000000), (Sum.inl 5, 1323047992979865600000), (Sum.inl 6, -322858519919308800000), (Sum.inl 7, 424088028861235200000), (Sum.inl 8, -988602950909952000000), (Sum.inl 26, 980452619196825600000), (Sum.inl 35, 955965154443264000000), (Sum.inl 52, -838720913109811200000), (Sum.inl 67, 1311703374127104000000), (Sum.inl 81, -4874829493395456000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge802 : Integer.Sparse Master := [(Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000)]

def reducedMerge803 : Integer.Sparse Master := [(Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000)]

def reducedMerge804 : Integer.Sparse Master := [(Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000)]

def reducedMerge805 : Integer.Sparse Master := [(Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000)]

def reducedMerge806 : Integer.Sparse Master := [(Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000)]

def reducedMerge807 : Integer.Sparse Master := [(Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000)]

def reducedMerge808 : Integer.Sparse Master := [(Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000)]

def reducedMerge809 : Integer.Sparse Master := [(Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000)]

def reducedMerge810 : Integer.Sparse Master := [(Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000)]

def reducedMerge811 : Integer.Sparse Master := [(Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000)]

def reducedMerge812 : Integer.Sparse Master := [(Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000)]

def reducedMerge813 : Integer.Sparse Master := [(Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000)]

def reducedMerge814 : Integer.Sparse Master := [(Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000)]

def reducedMerge815 : Integer.Sparse Master := [(Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000)]

def reducedMerge816 : Integer.Sparse Master := [(Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000)]

def reducedMerge817 : Integer.Sparse Master := [(Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000)]

def reducedMerge818 : Integer.Sparse Master := [(Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000)]

def reducedMerge819 : Integer.Sparse Master := [(Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000)]

def reducedMerge820 : Integer.Sparse Master := [(Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000)]

def reducedMerge821 : Integer.Sparse Master := [(Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000)]

def reducedMerge822 : Integer.Sparse Master := [(Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000)]

def reducedMerge823 : Integer.Sparse Master := [(Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000)]

def reducedMerge824 : Integer.Sparse Master := [(Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000)]

def reducedMerge825 : Integer.Sparse Master := [(Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000)]

def reducedMerge826 : Integer.Sparse Master := [(Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000)]

def reducedMerge827 : Integer.Sparse Master := [(Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000)]

def reducedMerge828 : Integer.Sparse Master := [(Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000)]

def reducedMerge829 : Integer.Sparse Master := [(Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge830 : Integer.Sparse Master := [(Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge831 : Integer.Sparse Master := [(Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge832 : Integer.Sparse Master := [(Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge833 : Integer.Sparse Master := [(Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge834 : Integer.Sparse Master := [(Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000), (Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge835 : Integer.Sparse Master := [(Sum.inr 1804, 2797448960684851200000), (Sum.inr 1805, 3885170543988572160000), (Sum.inr 1806, -9608222007357603840000), (Sum.inr 1807, 9318508415649054720000), (Sum.inr 1808, -4955053941050572800000), (Sum.inr 1809, -3537875996458352640000), (Sum.inr 1810, -3345967769848381440000), (Sum.inr 1811, 4908991524093296640000), (Sum.inr 1812, -11721265473473740800000), (Sum.inr 1813, 6324490501957877760000), (Sum.inr 1814, 2579448756790886400000), (Sum.inr 1815, -8001262491225292800000), (Sum.inr 1816, 8788236653722337280000), (Sum.inr 1817, -1747607698444124160000), (Sum.inr 1818, -7591910646227927040000), (Sum.inr 1819, -10541826291919749120000), (Sum.inr 1820, -629645571257794560000), (Sum.inr 1821, 1301309194638458880000), (Sum.inr 1822, 1098658614922444800000), (Sum.inr 1823, -1301309194638458880000), (Sum.inr 1824, 819808734353817600000), (Sum.inr 1825, 3329639154745344000000), (Sum.inr 1826, 2357878242882355200000), (Sum.inr 1827, -1098658614922444800000), (Sum.inr 1828, -750480790392668160000), (Sum.inr 1829, 6755524079380070400000), (Sum.inr 1830, 2387485449525657600000), (Sum.inr 1831, 4222772882708889600000), (Sum.inr 1832, -971893105435607040000), (Sum.inr 1957, -478232461800898560000), (Sum.inr 1964, -23934621521018880000), (Sum.inr 1965, 2241235474277990400000), (Sum.inr 1966, 5347929085248798720000), (Sum.inr 1967, 842806262366208000000), (Sum.inr 1970, 2206413845208760320000), (Sum.inr 1971, 3110224913045913600000), (Sum.inr 1973, 6990515310978662400000), (Sum.inr 1976, 2052530594103951360000), (Sum.inr 1977, -1235015743301222400000), (Sum.inr 1978, 4959624732475392000000), (Sum.inr 1979, 5755499567677440000000), (Sum.inr 1980, 5338073982173184000000), (Sum.inr 2010, -3936013149156802560000), (Sum.inr 2019, -2983567758946467840000), (Sum.inr 2020, 755963843883171840000), (Sum.inr 2022, 2983567758946467840000), (Sum.inr 2023, 88617370024673280000), (Sum.inr 2025, -4644957617419714560000), (Sum.inr 2026, 3018336835652812800000), (Sum.inr 2028, 590858676786954240000), (Sum.inr 2029, -2441576368615587840000), (Sum.inr 2037, 4121680737526087680000), (Sum.inr 2039, 6300739362226176000000), (Sum.inr 2051, -2470341383010385920000), (Sum.inr 2054, 2470341383010385920000), (Sum.inr 2058, -2837840598442967040000), (Sum.inr 2062, -3893099630053294080000), (Sum.inr 2088, -2282493232765992960000), (Sum.inr 2089, -18920168420746199040000), (Sum.inr 2090, -27244411052347883520000), (Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000), (Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000)]

def reducedMerge836 : Integer.Sparse Master := [(Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000)]

def reducedMerge837 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000)]

def reducedMerge838 : Integer.Sparse Master := [(Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000)]

def reducedMerge839 : Integer.Sparse Master := [(Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000)]

def reducedMerge840 : Integer.Sparse Master := [(Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000)]

def reducedMerge841 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000)]

def reducedMerge842 : Integer.Sparse Master := [(Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000)]

def reducedMerge843 : Integer.Sparse Master := [(Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000)]

def reducedMerge844 : Integer.Sparse Master := [(Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000)]

def reducedMerge845 : Integer.Sparse Master := [(Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000)]

def reducedMerge846 : Integer.Sparse Master := [(Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000)]

def reducedMerge847 : Integer.Sparse Master := [(Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000)]

def reducedMerge848 : Integer.Sparse Master := [(Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000)]

def reducedMerge849 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000)]

def reducedMerge850 : Integer.Sparse Master := [(Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000)]

def reducedMerge851 : Integer.Sparse Master := [(Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000)]

def reducedMerge852 : Integer.Sparse Master := [(Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000)]

def reducedMerge853 : Integer.Sparse Master := [(Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000)]

def reducedMerge854 : Integer.Sparse Master := [(Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000)]

def reducedMerge855 : Integer.Sparse Master := [(Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000)]

def reducedMerge856 : Integer.Sparse Master := [(Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000)]

def reducedMerge857 : Integer.Sparse Master := [(Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000)]

def reducedMerge858 : Integer.Sparse Master := [(Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000)]

def reducedMerge859 : Integer.Sparse Master := [(Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000)]

def reducedMerge860 : Integer.Sparse Master := [(Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000)]

def reducedMerge861 : Integer.Sparse Master := [(Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000)]

def reducedMerge862 : Integer.Sparse Master := [(Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000)]

def reducedMerge863 : Integer.Sparse Master := [(Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge864 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000)]

def reducedMerge866 : Integer.Sparse Master := [(Sum.inr 2262, 4747445379992125440000)]

def reducedMerge867 : Integer.Sparse Master := [(Sum.inr 2266, -17198383075263774720000)]

def reducedMerge868 : Integer.Sparse Master := [(Sum.inr 2267, 2456191162674708480000)]

def reducedMerge869 : Integer.Sparse Master := [(Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000)]

def reducedMerge870 : Integer.Sparse Master := [(Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000)]

def reducedMerge871 : Integer.Sparse Master := [(Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000)]

def reducedMerge872 : Integer.Sparse Master := [(Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000)]

def reducedMerge873 : Integer.Sparse Master := [(Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000)]

def reducedMerge874 : Integer.Sparse Master := [(Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000)]

def reducedMerge875 : Integer.Sparse Master := [(Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000)]

def reducedMerge876 : Integer.Sparse Master := [(Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000)]

def reducedMerge877 : Integer.Sparse Master := [(Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000)]

def reducedMerge878 : Integer.Sparse Master := [(Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000)]

def reducedMerge879 : Integer.Sparse Master := [(Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000)]

def reducedMerge880 : Integer.Sparse Master := [(Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000)]

def reducedMerge881 : Integer.Sparse Master := [(Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000)]

def reducedMerge882 : Integer.Sparse Master := []

def reducedMerge883 : Integer.Sparse Master := [(Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000)]

def reducedMerge884 : Integer.Sparse Master := [(Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000)]

def reducedMerge885 : Integer.Sparse Master := [(Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000)]

def reducedMerge886 : Integer.Sparse Master := [(Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000)]

def reducedMerge887 : Integer.Sparse Master := [(Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000)]

def reducedMerge888 : Integer.Sparse Master := [(Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000)]

def reducedMerge889 : Integer.Sparse Master := [(Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge890 : Integer.Sparse Master := [(Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge891 : Integer.Sparse Master := [(Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge892 : Integer.Sparse Master := [(Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge893 : Integer.Sparse Master := [(Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge894 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000), (Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000)]

def reducedMerge895 : Integer.Sparse Master := [(Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge896 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000)]

def reducedMerge897 : Integer.Sparse Master := [(Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000)]

def reducedMerge898 : Integer.Sparse Master := [(Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000)]

def reducedMerge899 : Integer.Sparse Master := [(Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000)]

def reducedMerge900 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000)]

def reducedMerge901 : Integer.Sparse Master := [(Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000)]

def reducedMerge902 : Integer.Sparse Master := [(Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000)]

def reducedMerge903 : Integer.Sparse Master := [(Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000)]

def reducedMerge904 : Integer.Sparse Master := [(Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000)]

def reducedMerge905 : Integer.Sparse Master := [(Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000)]

def reducedMerge906 : Integer.Sparse Master := [(Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000)]

def reducedMerge907 : Integer.Sparse Master := [(Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000)]

def reducedMerge908 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000)]

def reducedMerge909 : Integer.Sparse Master := [(Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000)]

def reducedMerge910 : Integer.Sparse Master := [(Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000)]

def reducedMerge911 : Integer.Sparse Master := [(Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000)]

def reducedMerge912 : Integer.Sparse Master := [(Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000)]

def reducedMerge913 : Integer.Sparse Master := [(Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000)]

def reducedMerge914 : Integer.Sparse Master := [(Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000)]

def reducedMerge915 : Integer.Sparse Master := [(Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000)]

def reducedMerge916 : Integer.Sparse Master := [(Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000)]

def reducedMerge917 : Integer.Sparse Master := [(Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000)]

def reducedMerge918 : Integer.Sparse Master := [(Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000)]

def reducedMerge919 : Integer.Sparse Master := [(Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000)]

def reducedMerge920 : Integer.Sparse Master := [(Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000)]

def reducedMerge921 : Integer.Sparse Master := [(Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000)]

def reducedMerge922 : Integer.Sparse Master := [(Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000)]

def reducedMerge923 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000)]

def reducedMerge924 : Integer.Sparse Master := [(Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000)]

def reducedMerge925 : Integer.Sparse Master := [(Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000)]

def reducedMerge926 : Integer.Sparse Master := [(Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000)]

def reducedMerge927 : Integer.Sparse Master := [(Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge928 : Integer.Sparse Master := [(Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000)]

def reducedMerge929 : Integer.Sparse Master := [(Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000)]

def reducedMerge930 : Integer.Sparse Master := [(Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000)]

def reducedMerge931 : Integer.Sparse Master := [(Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000)]

def reducedMerge932 : Integer.Sparse Master := [(Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000)]

def reducedMerge933 : Integer.Sparse Master := [(Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000)]

def reducedMerge934 : Integer.Sparse Master := [(Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000)]

def reducedMerge935 : Integer.Sparse Master := [(Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000)]

def reducedMerge936 : Integer.Sparse Master := [(Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000)]

def reducedMerge937 : Integer.Sparse Master := [(Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000)]

def reducedMerge938 : Integer.Sparse Master := [(Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000)]

def reducedMerge939 : Integer.Sparse Master := [(Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000)]

def reducedMerge940 : Integer.Sparse Master := [(Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000)]

def reducedMerge941 : Integer.Sparse Master := [(Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000)]

def reducedMerge942 : Integer.Sparse Master := [(Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000)]

def reducedMerge943 : Integer.Sparse Master := [(Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000)]

def reducedMerge944 : Integer.Sparse Master := [(Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000)]

def reducedMerge945 : Integer.Sparse Master := [(Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000)]

def reducedMerge946 : Integer.Sparse Master := [(Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000)]

def reducedMerge947 : Integer.Sparse Master := [(Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000)]

def reducedMerge948 : Integer.Sparse Master := [(Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge949 : Integer.Sparse Master := [(Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge950 : Integer.Sparse Master := [(Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge951 : Integer.Sparse Master := [(Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge952 : Integer.Sparse Master := [(Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge953 : Integer.Sparse Master := [(Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000), (Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge954 : Integer.Sparse Master := [(Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000), (Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000), (Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000), (Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

set_option maxHeartbeats 1000000 in
def reducedMerge955 : Integer.Sparse Master := [(Sum.inr 1804, 2797448960684851200000), (Sum.inr 1805, 3885170543988572160000), (Sum.inr 1806, -9608222007357603840000), (Sum.inr 1807, 9318508415649054720000), (Sum.inr 1808, -4955053941050572800000), (Sum.inr 1809, -3537875996458352640000), (Sum.inr 1810, -3345967769848381440000), (Sum.inr 1811, 4908991524093296640000), (Sum.inr 1812, -11721265473473740800000), (Sum.inr 1813, 6324490501957877760000), (Sum.inr 1814, 2579448756790886400000), (Sum.inr 1815, -8001262491225292800000), (Sum.inr 1816, 8788236653722337280000), (Sum.inr 1817, -1747607698444124160000), (Sum.inr 1818, -7591910646227927040000), (Sum.inr 1819, -10541826291919749120000), (Sum.inr 1820, -629645571257794560000), (Sum.inr 1821, 1301309194638458880000), (Sum.inr 1822, 1098658614922444800000), (Sum.inr 1823, -1301309194638458880000), (Sum.inr 1824, 819808734353817600000), (Sum.inr 1825, 3329639154745344000000), (Sum.inr 1826, 2357878242882355200000), (Sum.inr 1827, -1098658614922444800000), (Sum.inr 1828, -750480790392668160000), (Sum.inr 1829, 6755524079380070400000), (Sum.inr 1830, 2387485449525657600000), (Sum.inr 1831, 4222772882708889600000), (Sum.inr 1832, -971893105435607040000), (Sum.inr 1957, -478232461800898560000), (Sum.inr 1964, -23934621521018880000), (Sum.inr 1965, 2241235474277990400000), (Sum.inr 1966, 5347929085248798720000), (Sum.inr 1967, 842806262366208000000), (Sum.inr 1970, 2206413845208760320000), (Sum.inr 1971, 3110224913045913600000), (Sum.inr 1973, 6990515310978662400000), (Sum.inr 1976, 2052530594103951360000), (Sum.inr 1977, -1235015743301222400000), (Sum.inr 1978, 4959624732475392000000), (Sum.inr 1979, 5755499567677440000000), (Sum.inr 1980, 5338073982173184000000), (Sum.inr 2010, -3936013149156802560000), (Sum.inr 2019, -2983567758946467840000), (Sum.inr 2020, 755963843883171840000), (Sum.inr 2022, 2983567758946467840000), (Sum.inr 2023, 88617370024673280000), (Sum.inr 2025, -4644957617419714560000), (Sum.inr 2026, 3018336835652812800000), (Sum.inr 2028, 590858676786954240000), (Sum.inr 2029, -2441576368615587840000), (Sum.inr 2037, 4121680737526087680000), (Sum.inr 2039, 6300739362226176000000), (Sum.inr 2051, -2470341383010385920000), (Sum.inr 2054, 2470341383010385920000), (Sum.inr 2058, -2837840598442967040000), (Sum.inr 2062, -3893099630053294080000), (Sum.inr 2088, -2282493232765992960000), (Sum.inr 2089, -18920168420746199040000), (Sum.inr 2090, -27244411052347883520000), (Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000), (Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000), (Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000), (Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000), (Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000), (Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge956part0 : Integer.Sparse Master := [(Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000), (Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000), (Sum.inr 932, -2281209943794647040000), (Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000), (Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000), (Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000), (Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000), (Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000), (Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000), (Sum.inr 1129, 19378969510926090240000), (Sum.inr 1130, -9464678117613895680000), (Sum.inr 1131, 5641023726228602880000), (Sum.inr 1132, -1759585423361310720000)]

def reducedMerge956part1 : Integer.Sparse Master := [(Sum.inr 1133, 1307514346489774080000), (Sum.inr 1134, 3771399734927032320000), (Sum.inr 1135, -4459227814998835200000), (Sum.inr 1137, 467378502645841920000), (Sum.inr 1138, -19215558570607902720000), (Sum.inr 1139, -10083993537718517760000), (Sum.inr 1140, 5594674980160143360000), (Sum.inr 1141, 871459791106867200000), (Sum.inr 1142, 5137435020224102400000), (Sum.inr 1143, -5549518414241464320000), (Sum.inr 1144, -2210692257679933440000), (Sum.inr 1145, 2991047260449669120000), (Sum.inr 1146, 167779287760896000000), (Sum.inr 1148, -54778388874854400000), (Sum.inr 1149, 54778388874854400000), (Sum.inr 1150, 598839592845312000000), (Sum.inr 1151, -3796503149893386240000), (Sum.inr 1153, -2713512723987824640000), (Sum.inr 1155, 3773107777016954880000), (Sum.inr 1156, -4033883256599347200000), (Sum.inr 1159, -1465158899028787200000), (Sum.inr 1160, 5499042155628134400000), (Sum.inr 1169, 4433171053215744000000), (Sum.inr 1171, 6851070957020774400000), (Sum.inr 1174, 606438917347737600000), (Sum.inr 1212, 934778270036459520000), (Sum.inr 1215, -1029645037028966400000), (Sum.inr 1216, 250586732209766400000), (Sum.inr 1217, 18978681323195596800000), (Sum.inr 1219, 11351689807634104320000), (Sum.inr 1221, 972527074748006400000), (Sum.inr 1233, -6722247552986972160000), (Sum.inr 1234, -416003421044736000000), (Sum.inr 1235, 3252202435368714240000), (Sum.inr 1236, 12119156027369717760000), (Sum.inr 1237, 6722247552986972160000), (Sum.inr 1239, -2570828363354603520000), (Sum.inr 1240, -12547178408576286720000), (Sum.inr 1241, 8753467817805742080000), (Sum.inr 1242, -3100873301337047040000), (Sum.inr 1243, -2614211302075269120000), (Sum.inr 1245, 7725885129934110720000), (Sum.inr 1246, -19348453924951818240000), (Sum.inr 1260, -7062722889655910400000), (Sum.inr 1261, -9103216750304624640000), (Sum.inr 1262, 7062722889655910400000), (Sum.inr 1264, 8502527801884999680000), (Sum.inr 1270, -8079242612869693440000), (Sum.inr 1273, -5076859302087229440000), (Sum.inr 1291, -2206050538624450560000), (Sum.inr 1292, 2219882239269273600000), (Sum.inr 1293, 4459227814998835200000), (Sum.inr 1294, 11729049453615513600000), (Sum.inr 1295, 2206050538624450560000), (Sum.inr 1297, 5575466278860226560000), (Sum.inr 1306, -6047328798324817920000), (Sum.inr 1310, -626180907745935360000), (Sum.inr 1314, 5977466481711513600000), (Sum.inr 1315, 3501622812129361920000), (Sum.inr 1316, -9579839035999518720000), (Sum.inr 1317, 7341542882196848640000), (Sum.inr 1318, -4432587559454638080000), (Sum.inr 1319, -3032742142629642240000), (Sum.inr 1320, 11886766950399344640000)]

def reducedMerge956part2 : Integer.Sparse Master := [(Sum.inr 1321, -10548491592982855680000), (Sum.inr 1322, 9579839035999518720000), (Sum.inr 1323, -4933072605979607040000), (Sum.inr 1324, -8886421804453724160000), (Sum.inr 1325, -8635312347795947520000), (Sum.inr 1326, 277114839928012800000), (Sum.inr 1327, -5341116330562682880000), (Sum.inr 1328, -2299907207666073600000), (Sum.inr 1330, -819339736118722560000), (Sum.inr 1332, -3493413807980544000000), (Sum.inr 1333, 7641023538228756480000), (Sum.inr 1334, 8698253102854963200000), (Sum.inr 1335, 7361272231133184000000), (Sum.inr 1336, 3435031202884485120000), (Sum.inr 1337, -1895122181062656000000), (Sum.inr 1338, 4158977745420288000000), (Sum.inr 1348, 1542086242739159040000), (Sum.inr 1366, -1899117244195799040000), (Sum.inr 1367, 2667259420956426240000), (Sum.inr 1369, -3750701327642787840000), (Sum.inr 1370, 1899117244195799040000), (Sum.inr 1372, 8859486641663508480000), (Sum.inr 1375, -11526746062619934720000), (Sum.inr 1383, 4656026210537963520000), (Sum.inr 1385, -3478154931439534080000), (Sum.inr 1388, -2299907207666073600000), (Sum.inr 1391, -2356119002871889920000), (Sum.inr 1406, -22276992136265072640000), (Sum.inr 1408, -17269758213677383680000), (Sum.inr 1435, 847409560407244800000), (Sum.inr 1436, -3245969833485926400000), (Sum.inr 1438, 39708998817546240000), (Sum.inr 1501, -1056230257065984000000), (Sum.inr 1502, -1423280520010137600000), (Sum.inr 1504, -1951341470849433600000), (Sum.inr 1505, 1056230257065984000000), (Sum.inr 1508, 1423280520010137600000), (Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000), (Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000), (Sum.inr 1532, 513372727945986048000), (Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000), (Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000), (Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000), (Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000), (Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000), (Sum.inr 1682, 4390161007521300480000)]

def reducedMerge956part3 : Integer.Sparse Master := [(Sum.inr 1684, 604529641244196864000), (Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000), (Sum.inr 1687, -120789168095232000000), (Sum.inr 1688, 1305313133883752448000), (Sum.inr 1689, 3666193326655340544000), (Sum.inr 1695, 888021087364841472000), (Sum.inr 1697, 550098197290156032000), (Sum.inr 1699, -902368496446341120000), (Sum.inr 1700, -1069052130648391680000), (Sum.inr 1703, 2007627038014832640000), (Sum.inr 1704, 583395049348005888000), (Sum.inr 1709, -2010373847085219840000), (Sum.inr 1711, -4752834733161381888000), (Sum.inr 1712, -4818691431020888064000), (Sum.inr 1713, -3378878307861331968000), (Sum.inr 1714, -6227807807028068352000), (Sum.inr 1715, -2138368756797407232000), (Sum.inr 1716, 1926014843785052160000), (Sum.inr 1720, -1541521449311993856000), (Sum.inr 1721, 1386207265990901760000), (Sum.inr 1722, 1717512314662158336000), (Sum.inr 1723, -4810412754357977088000), (Sum.inr 1729, 3751773612556419072000), (Sum.inr 1734, -95615204742070272000), (Sum.inr 1735, 2302759193699155968000), (Sum.inr 1736, 2459234748121546752000), (Sum.inr 1740, 4524755554931834880000), (Sum.inr 1742, 119212994511765504000), (Sum.inr 1743, -8626840581832704000), (Sum.inr 1744, -554123003977138176000), (Sum.inr 1745, -2769188286440669184000), (Sum.inr 1746, -3563661364114489344000), (Sum.inr 1747, -1117582666619682816000), (Sum.inr 1748, 4393837063364345856000), (Sum.inr 1749, -722047208039055360000), (Sum.inr 1757, -474172475731476480000), (Sum.inr 1789, 654308882759024640000), (Sum.inr 1790, -4566900924634890240000), (Sum.inr 1791, -6742174334468751360000), (Sum.inr 1792, 2282493232765992960000), (Sum.inr 1793, 3731415152240885760000), (Sum.inr 1794, 673420605987225600000), (Sum.inr 1795, 8275744746720460800000), (Sum.inr 1796, 8393450481675141120000), (Sum.inr 1797, 5418404332170117120000), (Sum.inr 1802, 6265573704801976320000), (Sum.inr 1803, 28541892592926720000), (Sum.inr 1804, 2797448960684851200000), (Sum.inr 1805, 3885170543988572160000), (Sum.inr 1806, -9608222007357603840000), (Sum.inr 1807, 9318508415649054720000), (Sum.inr 1808, -4955053941050572800000), (Sum.inr 1809, -3537875996458352640000), (Sum.inr 1810, -3345967769848381440000), (Sum.inr 1811, 4908991524093296640000), (Sum.inr 1812, -11721265473473740800000), (Sum.inr 1813, 6324490501957877760000), (Sum.inr 1814, 2579448756790886400000), (Sum.inr 1815, -8001262491225292800000), (Sum.inr 1816, 8788236653722337280000), (Sum.inr 1817, -1747607698444124160000), (Sum.inr 1818, -7591910646227927040000), (Sum.inr 1819, -10541826291919749120000)]

def reducedMerge956part4 : Integer.Sparse Master := [(Sum.inr 1820, -629645571257794560000), (Sum.inr 1821, 1301309194638458880000), (Sum.inr 1822, 1098658614922444800000), (Sum.inr 1823, -1301309194638458880000), (Sum.inr 1824, 819808734353817600000), (Sum.inr 1825, 3329639154745344000000), (Sum.inr 1826, 2357878242882355200000), (Sum.inr 1827, -1098658614922444800000), (Sum.inr 1828, -750480790392668160000), (Sum.inr 1829, 6755524079380070400000), (Sum.inr 1830, 2387485449525657600000), (Sum.inr 1831, 4222772882708889600000), (Sum.inr 1832, -971893105435607040000), (Sum.inr 1957, -478232461800898560000), (Sum.inr 1964, -23934621521018880000), (Sum.inr 1965, 2241235474277990400000), (Sum.inr 1966, 5347929085248798720000), (Sum.inr 1967, 842806262366208000000), (Sum.inr 1970, 2206413845208760320000), (Sum.inr 1971, 3110224913045913600000), (Sum.inr 1973, 6990515310978662400000), (Sum.inr 1976, 2052530594103951360000), (Sum.inr 1977, -1235015743301222400000), (Sum.inr 1978, 4959624732475392000000), (Sum.inr 1979, 5755499567677440000000), (Sum.inr 1980, 5338073982173184000000), (Sum.inr 2010, -3936013149156802560000), (Sum.inr 2019, -2983567758946467840000), (Sum.inr 2020, 755963843883171840000), (Sum.inr 2022, 2983567758946467840000), (Sum.inr 2023, 88617370024673280000), (Sum.inr 2025, -4644957617419714560000), (Sum.inr 2026, 3018336835652812800000), (Sum.inr 2028, 590858676786954240000), (Sum.inr 2029, -2441576368615587840000), (Sum.inr 2037, 4121680737526087680000), (Sum.inr 2039, 6300739362226176000000), (Sum.inr 2051, -2470341383010385920000), (Sum.inr 2054, 2470341383010385920000), (Sum.inr 2058, -2837840598442967040000), (Sum.inr 2062, -3893099630053294080000), (Sum.inr 2088, -2282493232765992960000), (Sum.inr 2089, -18920168420746199040000), (Sum.inr 2090, -27244411052347883520000), (Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000)]

def reducedMerge956part5 : Integer.Sparse Master := [(Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000), (Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000), (Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000), (Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000)]

def reducedMerge956part6 : Integer.Sparse Master := [(Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000), (Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000), (Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000), (Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000), (Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000)]

def reducedMerge956part7 : Integer.Sparse Master := [(Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000), (Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge956 : Integer.Sparse Master := (((reducedMerge956part0 ++ reducedMerge956part1) ++ (reducedMerge956part2 ++ reducedMerge956part3)) ++ ((reducedMerge956part4 ++ reducedMerge956part5) ++ (reducedMerge956part6 ++ reducedMerge956part7)))

def reducedMerge957part0 : Integer.Sparse Master := [(Sum.inl 0, 19939583051424368640000), (Sum.inl 1, -1869104049556746240000), (Sum.inl 2, 4644371801737543680000), (Sum.inl 3, 92326856811407769600000), (Sum.inl 4, 23131383503877734400000), (Sum.inl 5, 3221049461020876800000), (Sum.inl 6, 365717504568729600000), (Sum.inl 7, 4614860267355340800000), (Sum.inl 8, -3743296719276441600000), (Sum.inl 9, 393661292632473600000), (Sum.inl 12, 22474548704872857600000), (Sum.inl 13, 38992015299221913600000), (Sum.inl 23, 10762160834550988800000), (Sum.inl 24, 18372170846144102400000), (Sum.inl 25, -13985496533978726400000), (Sum.inl 26, 21323362686706483200000), (Sum.inl 27, 1418716175772672000000), (Sum.inl 30, -4680882943930368000000), (Sum.inl 31, -7073333465554944000000), (Sum.inl 32, 4745802201477120000000), (Sum.inl 33, -45071977043939328000000), (Sum.inl 34, 3216637014287155200000), (Sum.inl 35, 20300984533831680000000), (Sum.inl 51, 20844440076334694400000), (Sum.inl 52, 8392474405866700800000), (Sum.inl 54, -12374076546168422400000), (Sum.inl 55, 31850438803874611200000), (Sum.inl 56, 6418437993883238400000), (Sum.inl 58, -176614741297612800000), (Sum.inl 59, 3635458356805632000000), (Sum.inl 60, 10815717612581683200000), (Sum.inl 61, 13348031491591372800000), (Sum.inl 62, -13208691003295334400000), (Sum.inl 63, -4304761391185920000000), (Sum.inl 64, -464566913608089600000), (Sum.inl 65, -2552961633494630400000), (Sum.inl 66, -75222115850649600000), (Sum.inl 67, 3088303514556825600000), (Sum.inl 68, 16182381785549414400000), (Sum.inl 69, 4283407023294873600000), (Sum.inl 70, 3692799467642880000000), (Sum.inl 71, 581673332072448000000), (Sum.inl 81, -7522157156548608000000), (Sum.inl 123, -5779978416672768000000), (Sum.inl 124, 9185931342714470400000), (Sum.inl 125, 11504122430924390400000), (Sum.inl 126, 34702576396546867200000), (Sum.inl 128, 5071126617627033600000), (Sum.inl 194, -15476971187994624000000), (Sum.inl 195, -3484357479751680000000), (Sum.inl 196, -1563346487756390400000), (Sum.inl 197, 15472899725952614400000), (Sum.inl 256, -668797982060544000000), (Sum.inl 257, 3497224054947840000000), (Sum.inl 259, 1776106015617024000000), (Sum.inl 260, -8587699706363904000000), (Sum.inl 263, -8918577379314892800000), (Sum.inl 264, -7410130929421516800000), (Sum.inl 266, 8419210088841216000000), (Sum.inl 268, 2344146906415104000000), (Sum.inl 487, -23459956324245504000000), (Sum.inl 495, 2895341101225574400000), (Sum.inr 577, -654308882759024640000), (Sum.inr 578, -2282493232765992960000)]

def reducedMerge957part1 : Integer.Sparse Master := [(Sum.inr 579, 654308882759024640000), (Sum.inr 580, 877592856526848000000), (Sum.inr 581, 877447660307742720000), (Sum.inr 582, 607591276892651520000), (Sum.inr 583, 2282493232765992960000), (Sum.inr 584, -113253321790586880000), (Sum.inr 585, -2325444766551244800000), (Sum.inr 586, -878028445184163840000), (Sum.inr 587, 4950070676784414720000), (Sum.inr 588, -947351242264412160000), (Sum.inr 589, -877883248965058560000), (Sum.inr 590, -544816666760970240000), (Sum.inr 591, 2291676713032089600000), (Sum.inr 597, -28541892592926720000), (Sum.inr 599, -1211529171307069440000), (Sum.inr 600, 344588552322416640000), (Sum.inr 601, 28541892592926720000), (Sum.inr 603, 533546803510640640000), (Sum.inr 604, 6690208535414046720000), (Sum.inr 605, -2453660793490636800000), (Sum.inr 606, 1441480432653434880000), (Sum.inr 607, 2300979745408942080000), (Sum.inr 608, -1054181617875025920000), (Sum.inr 610, -9473152863350292480000), (Sum.inr 611, 18388973290326589440000), (Sum.inr 612, -584459388199895040000), (Sum.inr 613, -2602745435968634880000), (Sum.inr 614, 677982367796428800000), (Sum.inr 615, 1801435404238848000000), (Sum.inr 616, -2365767237453742080000), (Sum.inr 617, 3002873618910412800000), (Sum.inr 618, 1287214867623444480000), (Sum.inr 619, 3163253859043246080000), (Sum.inr 620, 9267211259630714880000), (Sum.inr 621, 365728146625658880000), (Sum.inr 622, -820112129438515200000), (Sum.inr 623, -1258494730418257920000), (Sum.inr 624, -363229471392399360000), (Sum.inr 626, 4002258833827430400000), (Sum.inr 627, -860150167449108480000), (Sum.inr 628, 363229471392399360000), (Sum.inr 629, 1355923199361024000000), (Sum.inr 630, -1355923199361024000000), (Sum.inr 631, -3620046943302451200000), (Sum.inr 633, 4614435349529886720000), (Sum.inr 634, -4581648092858941440000), (Sum.inr 635, -1883613935960064000000), (Sum.inr 636, -3999431119401123840000), (Sum.inr 637, 5023829814312960000000), (Sum.inr 638, 5237719375993896960000), (Sum.inr 639, -3501219910680576000000), (Sum.inr 640, -5023829814312960000000), (Sum.inr 641, 2600840819146752000000), (Sum.inr 642, -7838560195140648960000), (Sum.inr 643, 3501219910680576000000), (Sum.inr 653, 892167378500321280000), (Sum.inr 654, 315973519843000320000), (Sum.inr 909, 8659257895151861760000), (Sum.inr 911, 7407336363717427200000), (Sum.inr 914, 8137792988223897600000), (Sum.inr 922, 842806262366208000000), (Sum.inr 929, -941481721225543680000), (Sum.inr 930, -4522163694065418240000), (Sum.inr 931, 862331180804997120000)]

def reducedMerge957part2 : Integer.Sparse Master := [(Sum.inr 932, -2281209943794647040000), (Sum.inr 933, -842806262366208000000), (Sum.inr 934, 1048155974782156800000), (Sum.inr 936, -3501622812129361920000), (Sum.inr 937, -690110044530278400000), (Sum.inr 939, -5644648033344552960000), (Sum.inr 940, -3110224913045913600000), (Sum.inr 944, 5755499567677440000000), (Sum.inr 945, 5755499567677440000000), (Sum.inr 946, 4959624732475392000000), (Sum.inr 949, -7458564352880148480000), (Sum.inr 950, -5755499567677440000000), (Sum.inr 951, 7458564352880148480000), (Sum.inr 952, -4959624732475392000000), (Sum.inr 953, -5755499567677440000000), (Sum.inr 954, -3501219910680576000000), (Sum.inr 1024, -2976678613712240640000), (Sum.inr 1027, -4206296272205905920000), (Sum.inr 1039, 84218592777338880000), (Sum.inr 1041, -1011243447920885760000), (Sum.inr 1044, -2007773678972436480000), (Sum.inr 1046, 10725266364412723200000), (Sum.inr 1047, -13781464017158799360000), (Sum.inr 1049, 1567784528782295040000), (Sum.inr 1050, 927024855143546880000), (Sum.inr 1051, 1191593947134689280000), (Sum.inr 1058, 6300739362226176000000), (Sum.inr 1061, -3750701327642787840000), (Sum.inr 1063, -6300739362226176000000), (Sum.inr 1064, 3750701327642787840000), (Sum.inr 1087, -8631272678361661440000), (Sum.inr 1091, 7331333818189086720000), (Sum.inr 1094, -2107338916154572800000), (Sum.inr 1111, 94866766992506880000), (Sum.inr 1112, -26389657073487052800000), (Sum.inr 1113, -8810814575497052160000), (Sum.inr 1115, -1573216023167631360000), (Sum.inr 1116, -1126879414384066560000), (Sum.inr 1117, -250586732209766400000), (Sum.inr 1118, 4772950974038016000000), (Sum.inr 1119, -1307377367220879360000), (Sum.inr 1120, 6812136157446144000000), (Sum.inr 1121, -8762782347893145600000), (Sum.inr 1125, 416003421044736000000), (Sum.inr 1126, 3128439995443445760000), (Sum.inr 1128, 331078441437757440000), (Sum.inr 1129, 19378969510926090240000), (Sum.inr 1130, -9464678117613895680000), (Sum.inr 1131, 5641023726228602880000), (Sum.inr 1132, -1759585423361310720000), (Sum.inr 1133, 1307514346489774080000), (Sum.inr 1134, 3771399734927032320000), (Sum.inr 1135, -4459227814998835200000), (Sum.inr 1137, 467378502645841920000), (Sum.inr 1138, -19215558570607902720000), (Sum.inr 1139, -10083993537718517760000), (Sum.inr 1140, 5594674980160143360000), (Sum.inr 1141, 871459791106867200000), (Sum.inr 1142, 5137435020224102400000), (Sum.inr 1143, -5549518414241464320000), (Sum.inr 1144, -2210692257679933440000), (Sum.inr 1145, 2991047260449669120000), (Sum.inr 1146, 167779287760896000000), (Sum.inr 1148, -54778388874854400000)]

def reducedMerge957part3 : Integer.Sparse Master := [(Sum.inr 1149, 54778388874854400000), (Sum.inr 1150, 598839592845312000000), (Sum.inr 1151, -3796503149893386240000), (Sum.inr 1153, -2713512723987824640000), (Sum.inr 1155, 3773107777016954880000), (Sum.inr 1156, -4033883256599347200000), (Sum.inr 1159, -1465158899028787200000), (Sum.inr 1160, 5499042155628134400000), (Sum.inr 1169, 4433171053215744000000), (Sum.inr 1171, 6851070957020774400000), (Sum.inr 1174, 606438917347737600000), (Sum.inr 1212, 934778270036459520000), (Sum.inr 1215, -1029645037028966400000), (Sum.inr 1216, 250586732209766400000), (Sum.inr 1217, 18978681323195596800000), (Sum.inr 1219, 11351689807634104320000), (Sum.inr 1221, 972527074748006400000), (Sum.inr 1233, -6722247552986972160000), (Sum.inr 1234, -416003421044736000000), (Sum.inr 1235, 3252202435368714240000), (Sum.inr 1236, 12119156027369717760000), (Sum.inr 1237, 6722247552986972160000), (Sum.inr 1239, -2570828363354603520000), (Sum.inr 1240, -12547178408576286720000), (Sum.inr 1241, 8753467817805742080000), (Sum.inr 1242, -3100873301337047040000), (Sum.inr 1243, -2614211302075269120000), (Sum.inr 1245, 7725885129934110720000), (Sum.inr 1246, -19348453924951818240000), (Sum.inr 1260, -7062722889655910400000), (Sum.inr 1261, -9103216750304624640000), (Sum.inr 1262, 7062722889655910400000), (Sum.inr 1264, 8502527801884999680000), (Sum.inr 1270, -8079242612869693440000), (Sum.inr 1273, -5076859302087229440000), (Sum.inr 1291, -2206050538624450560000), (Sum.inr 1292, 2219882239269273600000), (Sum.inr 1293, 4459227814998835200000), (Sum.inr 1294, 11729049453615513600000), (Sum.inr 1295, 2206050538624450560000), (Sum.inr 1297, 5575466278860226560000), (Sum.inr 1306, -6047328798324817920000), (Sum.inr 1310, -626180907745935360000), (Sum.inr 1314, 5977466481711513600000), (Sum.inr 1315, 3501622812129361920000), (Sum.inr 1316, -9579839035999518720000), (Sum.inr 1317, 7341542882196848640000), (Sum.inr 1318, -4432587559454638080000), (Sum.inr 1319, -3032742142629642240000), (Sum.inr 1320, 11886766950399344640000), (Sum.inr 1321, -10548491592982855680000), (Sum.inr 1322, 9579839035999518720000), (Sum.inr 1323, -4933072605979607040000), (Sum.inr 1324, -8886421804453724160000), (Sum.inr 1325, -8635312347795947520000), (Sum.inr 1326, 277114839928012800000), (Sum.inr 1327, -5341116330562682880000), (Sum.inr 1328, -2299907207666073600000), (Sum.inr 1330, -819339736118722560000), (Sum.inr 1332, -3493413807980544000000), (Sum.inr 1333, 7641023538228756480000), (Sum.inr 1334, 8698253102854963200000), (Sum.inr 1335, 7361272231133184000000), (Sum.inr 1336, 3435031202884485120000)]

def reducedMerge957part4 : Integer.Sparse Master := [(Sum.inr 1337, -1895122181062656000000), (Sum.inr 1338, 4158977745420288000000), (Sum.inr 1348, 1542086242739159040000), (Sum.inr 1366, -1899117244195799040000), (Sum.inr 1367, 2667259420956426240000), (Sum.inr 1369, -3750701327642787840000), (Sum.inr 1370, 1899117244195799040000), (Sum.inr 1372, 8859486641663508480000), (Sum.inr 1375, -11526746062619934720000), (Sum.inr 1383, 4656026210537963520000), (Sum.inr 1385, -3478154931439534080000), (Sum.inr 1388, -2299907207666073600000), (Sum.inr 1391, -2356119002871889920000), (Sum.inr 1406, -22276992136265072640000), (Sum.inr 1408, -17269758213677383680000), (Sum.inr 1435, 847409560407244800000), (Sum.inr 1436, -3245969833485926400000), (Sum.inr 1438, 39708998817546240000), (Sum.inr 1501, -1056230257065984000000), (Sum.inr 1502, -1423280520010137600000), (Sum.inr 1504, -1951341470849433600000), (Sum.inr 1505, 1056230257065984000000), (Sum.inr 1508, 1423280520010137600000), (Sum.inr 1510, -2210913934743306240000), (Sum.inr 1511, -2862630613510520832000), (Sum.inr 1512, -1812234680041734144000), (Sum.inr 1513, 807931683631005696000), (Sum.inr 1514, 279082176459964416000), (Sum.inr 1515, 1951341470849433600000), (Sum.inr 1516, 1532149313286832128000), (Sum.inr 1520, 3125626258862112768000), (Sum.inr 1522, 1398340775856439296000), (Sum.inr 1523, 1978196107527585792000), (Sum.inr 1526, 3237439447258103808000), (Sum.inr 1528, -115736953684230144000), (Sum.inr 1529, -190397481621258240000), (Sum.inr 1530, -179029231679176704000), (Sum.inr 1531, -24315273996926976000), (Sum.inr 1532, 513372727945986048000), (Sum.inr 1533, 3726326584597413888000), (Sum.inr 1534, 92042023309737984000), (Sum.inr 1540, 299269579737268224000), (Sum.inr 1667, -1090667657931522048000), (Sum.inr 1668, -1101980502152183808000), (Sum.inr 1670, -735052166107693056000), (Sum.inr 1672, -615325865037004800000), (Sum.inr 1676, 441343231347916800000), (Sum.inr 1678, 2798915153550114816000), (Sum.inr 1679, 4204277593279561728000), (Sum.inr 1682, 4390161007521300480000), (Sum.inr 1684, 604529641244196864000), (Sum.inr 1685, 910860777696264192000), (Sum.inr 1686, 789405404560883712000), (Sum.inr 1687, -120789168095232000000), (Sum.inr 1688, 1305313133883752448000), (Sum.inr 1689, 3666193326655340544000), (Sum.inr 1695, 888021087364841472000), (Sum.inr 1697, 550098197290156032000), (Sum.inr 1699, -902368496446341120000), (Sum.inr 1700, -1069052130648391680000), (Sum.inr 1703, 2007627038014832640000), (Sum.inr 1704, 583395049348005888000), (Sum.inr 1709, -2010373847085219840000), (Sum.inr 1711, -4752834733161381888000)]

def reducedMerge957part5 : Integer.Sparse Master := [(Sum.inr 1712, -4818691431020888064000), (Sum.inr 1713, -3378878307861331968000), (Sum.inr 1714, -6227807807028068352000), (Sum.inr 1715, -2138368756797407232000), (Sum.inr 1716, 1926014843785052160000), (Sum.inr 1720, -1541521449311993856000), (Sum.inr 1721, 1386207265990901760000), (Sum.inr 1722, 1717512314662158336000), (Sum.inr 1723, -4810412754357977088000), (Sum.inr 1729, 3751773612556419072000), (Sum.inr 1734, -95615204742070272000), (Sum.inr 1735, 2302759193699155968000), (Sum.inr 1736, 2459234748121546752000), (Sum.inr 1740, 4524755554931834880000), (Sum.inr 1742, 119212994511765504000), (Sum.inr 1743, -8626840581832704000), (Sum.inr 1744, -554123003977138176000), (Sum.inr 1745, -2769188286440669184000), (Sum.inr 1746, -3563661364114489344000), (Sum.inr 1747, -1117582666619682816000), (Sum.inr 1748, 4393837063364345856000), (Sum.inr 1749, -722047208039055360000), (Sum.inr 1757, -474172475731476480000), (Sum.inr 1789, 654308882759024640000), (Sum.inr 1790, -4566900924634890240000), (Sum.inr 1791, -6742174334468751360000), (Sum.inr 1792, 2282493232765992960000), (Sum.inr 1793, 3731415152240885760000), (Sum.inr 1794, 673420605987225600000), (Sum.inr 1795, 8275744746720460800000), (Sum.inr 1796, 8393450481675141120000), (Sum.inr 1797, 5418404332170117120000), (Sum.inr 1802, 6265573704801976320000), (Sum.inr 1803, 28541892592926720000), (Sum.inr 1804, 2797448960684851200000), (Sum.inr 1805, 3885170543988572160000), (Sum.inr 1806, -9608222007357603840000), (Sum.inr 1807, 9318508415649054720000), (Sum.inr 1808, -4955053941050572800000), (Sum.inr 1809, -3537875996458352640000), (Sum.inr 1810, -3345967769848381440000), (Sum.inr 1811, 4908991524093296640000), (Sum.inr 1812, -11721265473473740800000), (Sum.inr 1813, 6324490501957877760000), (Sum.inr 1814, 2579448756790886400000), (Sum.inr 1815, -8001262491225292800000), (Sum.inr 1816, 8788236653722337280000), (Sum.inr 1817, -1747607698444124160000), (Sum.inr 1818, -7591910646227927040000), (Sum.inr 1819, -10541826291919749120000), (Sum.inr 1820, -629645571257794560000), (Sum.inr 1821, 1301309194638458880000), (Sum.inr 1822, 1098658614922444800000), (Sum.inr 1823, -1301309194638458880000), (Sum.inr 1824, 819808734353817600000), (Sum.inr 1825, 3329639154745344000000), (Sum.inr 1826, 2357878242882355200000), (Sum.inr 1827, -1098658614922444800000), (Sum.inr 1828, -750480790392668160000), (Sum.inr 1829, 6755524079380070400000), (Sum.inr 1830, 2387485449525657600000), (Sum.inr 1831, 4222772882708889600000), (Sum.inr 1832, -971893105435607040000), (Sum.inr 1957, -478232461800898560000)]

def reducedMerge957part6 : Integer.Sparse Master := [(Sum.inr 1964, -23934621521018880000), (Sum.inr 1965, 2241235474277990400000), (Sum.inr 1966, 5347929085248798720000), (Sum.inr 1967, 842806262366208000000), (Sum.inr 1970, 2206413845208760320000), (Sum.inr 1971, 3110224913045913600000), (Sum.inr 1973, 6990515310978662400000), (Sum.inr 1976, 2052530594103951360000), (Sum.inr 1977, -1235015743301222400000), (Sum.inr 1978, 4959624732475392000000), (Sum.inr 1979, 5755499567677440000000), (Sum.inr 1980, 5338073982173184000000), (Sum.inr 2010, -3936013149156802560000), (Sum.inr 2019, -2983567758946467840000), (Sum.inr 2020, 755963843883171840000), (Sum.inr 2022, 2983567758946467840000), (Sum.inr 2023, 88617370024673280000), (Sum.inr 2025, -4644957617419714560000), (Sum.inr 2026, 3018336835652812800000), (Sum.inr 2028, 590858676786954240000), (Sum.inr 2029, -2441576368615587840000), (Sum.inr 2037, 4121680737526087680000), (Sum.inr 2039, 6300739362226176000000), (Sum.inr 2051, -2470341383010385920000), (Sum.inr 2054, 2470341383010385920000), (Sum.inr 2058, -2837840598442967040000), (Sum.inr 2062, -3893099630053294080000), (Sum.inr 2088, -2282493232765992960000), (Sum.inr 2089, -18920168420746199040000), (Sum.inr 2090, -27244411052347883520000), (Sum.inr 2092, 14205848185641369600000), (Sum.inr 2094, 15839955060530872320000), (Sum.inr 2104, -28541892592926720000), (Sum.inr 2105, -338218339097640960000), (Sum.inr 2106, 283347893291581440000), (Sum.inr 2107, 5704108413360537600000), (Sum.inr 2108, -18375094409940172800000), (Sum.inr 2109, 5542318650230046720000), (Sum.inr 2110, -14180570318501314560000), (Sum.inr 2112, -3684095090420613120000), (Sum.inr 2113, -757176972741181440000), (Sum.inr 2115, -12013936625481154560000), (Sum.inr 2116, -1563346111522406400000), (Sum.inr 2131, 1418945220960583680000), (Sum.inr 2132, -1418945220960583680000), (Sum.inr 2133, 11767743613933977600000), (Sum.inr 2134, 4056479869678387200000), (Sum.inr 2136, -40767630952366080000), (Sum.inr 2138, 8053752549762662400000), (Sum.inr 2140, -1056230257065984000000), (Sum.inr 2142, -1423280520010137600000), (Sum.inr 2144, 1234719933093642240000), (Sum.inr 2145, 747433945254592512000), (Sum.inr 2146, -1041522169018318848000), (Sum.inr 2147, -1400262241941061632000), (Sum.inr 2148, -1951341470849433600000), (Sum.inr 2149, -3528479019960631296000), (Sum.inr 2153, -5084299705354813440000), (Sum.inr 2154, 415726753622261760000), (Sum.inr 2155, -199802494476877824000), (Sum.inr 2158, -1958086160293036032000), (Sum.inr 2160, 350247195718189056000), (Sum.inr 2161, 460809475344433152000), (Sum.inr 2162, 1082771078483017728000)]

def reducedMerge957part7 : Integer.Sparse Master := [(Sum.inr 2163, 104801980817866752000), (Sum.inr 2164, -4082980870490554368000), (Sum.inr 2171, -888215115745198080000), (Sum.inr 2172, -1086333153488142336000), (Sum.inr 2175, -2488877088999211008000), (Sum.inr 2176, -1039334509865336832000), (Sum.inr 2178, -2644281324676841472000), (Sum.inr 2179, 382802499623190528000), (Sum.inr 2180, 80987525421465600000), (Sum.inr 2181, -2480383209507323904000), (Sum.inr 2187, 1069052130648391680000), (Sum.inr 2189, -535625493262368768000), (Sum.inr 2192, 2550756900341809152000), (Sum.inr 2194, 506714469983059968000), (Sum.inr 2195, 2281683348482162688000), (Sum.inr 2196, 4171042250963288064000), (Sum.inr 2197, 3716334068831354880000), (Sum.inr 2198, -1758049717505163264000), (Sum.inr 2199, -529608735311265792000), (Sum.inr 2200, -2923000637003661312000), (Sum.inr 2201, -968581412641898496000), (Sum.inr 2207, -1075562447389065216000), (Sum.inr 2211, 3118020017674125312000), (Sum.inr 2212, 3417517613264928768000), (Sum.inr 2213, -164392035143712768000), (Sum.inr 2217, 6106405275203272704000), (Sum.inr 2219, 543996082382635008000), (Sum.inr 2220, 1698881328169353216000), (Sum.inr 2221, -2422443967567626240000), (Sum.inr 2222, -2652931479726194688000), (Sum.inr 2223, 454996272018161664000), (Sum.inr 2231, 522094469787942912000), (Sum.inr 2232, 825412766634344448000), (Sum.inr 2233, -7143996310767009792000), (Sum.inr 2234, 5281412168984297472000), (Sum.inr 2235, 8991466736109355008000), (Sum.inr 2238, 1167171979199643648000), (Sum.inr 2239, -11939427307487232000), (Sum.inr 2240, -912884097845035008000), (Sum.inr 2243, -3530220507746795520000), (Sum.inr 2244, -13288538835716014080000), (Sum.inr 2245, 5084282729677455360000), (Sum.inr 2246, 14561556817950277632000), (Sum.inr 2247, -12514908548880138240000), (Sum.inr 2248, -2840232254671945728000), (Sum.inr 2249, -2254308298937597952000), (Sum.inr 2250, 6385220328544468992000), (Sum.inr 2251, 6295106507412602880000), (Sum.inr 2252, -1717100482923528192000), (Sum.inr 2253, -11806284324964663296000), (Sum.inr 2254, 3977835312798498816000), (Sum.inr 2255, 13423761248418791424000), (Sum.inr 2256, -3060986888631877632000), (Sum.inr 2257, 356540332144066560000), (Sum.inr 2258, -285682392053710848000), (Sum.inr 2259, -2232992392359837696000), (Sum.inr 2262, 4747445379992125440000), (Sum.inr 2266, -17198383075263774720000), (Sum.inr 2267, 2456191162674708480000), (Sum.inr 2272, 620385158666649600000), (Sum.inr 2273, 1530801552859987968000), (Sum.inr 2274, 11930424302148452352000), (Sum.inr 2277, 7044709980352020480000), (Sum.inr 2278, 613475877389598720000)]

def reducedMerge957part8 : Integer.Sparse Master := [(Sum.inr 2279, 4948572573257564160000), (Sum.inr 2280, 4794515628466765824000), (Sum.inr 2281, 9591223123887390720000), (Sum.inr 2282, -328449504969621504000), (Sum.inr 2283, 1069657792115834880000), (Sum.inr 2284, 3942379037195698176000), (Sum.inr 2285, 88491352709136384000), (Sum.inr 2286, 1402778741635547136000), (Sum.inr 2294, -9942532690001264640000), (Sum.inr 2323, -5775400208422010880000), (Sum.inr 2327, 1409374911961497600000), (Sum.inr 2330, -1021462625098137600000), (Sum.inr 2332, 8792971061782118400000), (Sum.inr 2334, 1021462625098137600000), (Sum.inr 2337, 2042925250196275200000), (Sum.inr 2338, 6349509219129753600000), (Sum.inr 2339, -1957928575441305600000), (Sum.inr 2340, -5831241247610634240000), (Sum.inr 2341, -4592195406267678720000), (Sum.inr 2342, -8792971061782118400000), (Sum.inr 2344, -1021462625098137600000), (Sum.inr 2345, -15267702809682247680000), (Sum.inr 2346, 3811111984406200320000), (Sum.inr 2347, 54778388874854400000), (Sum.inr 2348, -54778388874854400000), (Sum.inr 2349, -598839592845312000000), (Sum.inr 2350, -2122040394523607040000), (Sum.inr 2352, 14499441893476270080000), (Sum.inr 2353, -4008567374777548800000), (Sum.inr 2355, -3201531558440140800000), (Sum.inr 2356, 7210098933217689600000), (Sum.inr 2361, -4433171053215744000000), (Sum.inr 2362, -9916201969680384000000), (Sum.inr 2423, 5684917680995696640000), (Sum.inr 2425, -3022934715924480000000), (Sum.inr 2426, -2089015568665804800000), (Sum.inr 2428, 5559732986314752000000), (Sum.inr 2429, -3513264514950758400000), (Sum.inr 2430, 19962365120110264320000), (Sum.inr 2431, 14124724583912570880000), (Sum.inr 2432, 762973624782028800000), (Sum.inr 2433, 2089015568665804800000), (Sum.inr 2434, -4285922492777103360000), (Sum.inr 2435, 5339288646065848320000), (Sum.inr 2437, -29125569354242457600000), (Sum.inr 2438, -4666690457468928000000), (Sum.inr 2440, -1089057424637952000000), (Sum.inr 2441, -27156418471526400000), (Sum.inr 2442, 4167404634193920000000), (Sum.inr 2443, -6201565287992524800000), (Sum.inr 2470, -669848715789926400000), (Sum.inr 2471, 5402275542460661760000), (Sum.inr 2473, 669848715789926400000), (Sum.inr 2479, -21951447043276800000), (Sum.inr 2480, -12811011857783193600000), (Sum.inr 2482, 3044886162967756800000), (Sum.inr 2483, 10730200326977617920000), (Sum.inr 2485, -7075268186112000000000), (Sum.inr 2486, -10132091952404889600000), (Sum.inr 2488, 3036144140609126400000), (Sum.inr 2489, 12048038233001164800000), (Sum.inr 2494, 882109921738752000000), (Sum.inr 2495, 421979070165811200000), (Sum.inr 2497, 2247947368157675520000)]

def reducedMerge957part9 : Integer.Sparse Master := [(Sum.inr 2499, -7786684812636979200000), (Sum.inr 2508, 4693700295180288000000), (Sum.inr 2512, -8251961190668697600000), (Sum.inr 2513, -4629005356695552000000), (Sum.inr 2515, 20072224660871577600000), (Sum.inr 2519, 4382870405576785920000), (Sum.inr 2520, 3829273250294661120000), (Sum.inr 2522, -46570423131832320000), (Sum.inr 2524, 94866766992506880000), (Sum.inr 2529, -1138001372530606080000), (Sum.inr 2545, -1139201814778675200000), (Sum.inr 2553, -5874441005529169920000)]

def reducedMerge957 : Integer.Sparse Master := (((reducedMerge957part0 ++ reducedMerge957part1) ++ (reducedMerge957part2 ++ (reducedMerge957part3 ++ reducedMerge957part4))) ++ ((reducedMerge957part5 ++ reducedMerge957part6) ++ (reducedMerge957part7 ++ (reducedMerge957part8 ++ reducedMerge957part9))))

def reducedMerge958 : Integer.Sparse Master := [(Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000)]

def reducedMerge959 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge960 : Integer.Sparse Master := [(Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000)]

def reducedMerge961 : Integer.Sparse Master := [(Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def reducedMerge962 : Integer.Sparse Master := [(Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def reducedMerge963 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def reducedMerge964 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000)]

def reducedMerge965 : Integer.Sparse Master := [(Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000)]

def reducedMerge966 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000)]

def reducedMerge967 : Integer.Sparse Master := [(Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000)]

def reducedMerge968 : Integer.Sparse Master := [(Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def reducedMerge969 : Integer.Sparse Master := [(Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def reducedMerge970 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def reducedMerge971 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def reducedMerge972 : Integer.Sparse Master := [(Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000)]

def reducedMerge973 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000)]

def reducedMerge974 : Integer.Sparse Master := [(Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000)]

def reducedMerge975 : Integer.Sparse Master := [(Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def reducedMerge976 : Integer.Sparse Master := [(Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def reducedMerge977 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def reducedMerge978 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000)]

def reducedMerge979 : Integer.Sparse Master := [(Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000)]

def reducedMerge980 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000)]

def reducedMerge981 : Integer.Sparse Master := [(Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000)]

def reducedMerge982 : Integer.Sparse Master := [(Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def reducedMerge983 : Integer.Sparse Master := [(Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def reducedMerge984 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def reducedMerge985 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def reducedMerge986 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def reducedMerge987 : Integer.Sparse Master := [(Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000)]

def reducedMerge988 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000)]

def reducedMerge989 : Integer.Sparse Master := [(Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000)]

def reducedMerge990 : Integer.Sparse Master := [(Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000)]

def reducedMerge991 : Integer.Sparse Master := [(Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge992 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000), (Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000)]

def reducedMerge993 : Integer.Sparse Master := [(Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000)]

def reducedMerge994 : Integer.Sparse Master := [(Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000)]

def reducedMerge995 : Integer.Sparse Master := [(Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000)]

def reducedMerge996 : Integer.Sparse Master := [(Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000)]

def reducedMerge997 : Integer.Sparse Master := [(Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000)]

def reducedMerge998 : Integer.Sparse Master := [(Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000)]

def reducedMerge999 : Integer.Sparse Master := [(Sum.inr 2670, -4302905736953069568000), (Sum.inr 2673, 3169748139186585600000), (Sum.inr 2676, 2197036481036156928000), (Sum.inr 2677, 3660221256271921152000), (Sum.inr 2678, 1249731921884479488000), (Sum.inr 2680, 328270556047343616000), (Sum.inr 2681, -304877566989434880000), (Sum.inr 2682, -2451504521281536000000)]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end


