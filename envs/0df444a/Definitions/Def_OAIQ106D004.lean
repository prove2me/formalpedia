-- Prove2me | Definitions.Def_OAIQ106D004
-- name    : OAIQ106D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:57:39.675354+00:00
-- url     : https://prove2.me/theorems/af7b307b-f636-466f-a477-c67d0dace33d
-- title:
--   Definitions bundle OAIQ106D004 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5553 declarations of OpenAI's Lean: 5553 definitions. The definitions and types are `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding0`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding1`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding10`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding2`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding3`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding6`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding7`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding8`, `OAI.MUB6.Certificate.MixedSemantics.labelEmbedding9`, `OAI.MUB6.Certificate.MixedSemantics.node5096Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5097`, `OAI.MUB6.Certificate.MixedSemantics.node5097Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5098`, `OAI.MUB6.Certificate.MixedSemantics.node5098Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5099`, `OAI.MUB6.Certificate.MixedSemantics.node5099Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5100`, `OAI.MUB6.Certificate.MixedSemantics.node5100Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5101`, `OAI.MUB6.Certificate.MixedSemantics.node5101Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5102`, `OAI.MUB6.Certificate.MixedSemantics.node5102Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5103`, `OAI.MUB6.Certificate.MixedSemantics.node5103Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5104`, `OAI.MUB6.Certificate.MixedSemantics.node5104Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5105`, `OAI.MUB6.Certificate.MixedSemantics.node5105Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5106`, `OAI.MUB6.Certificate.MixedSemantics.node5106Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5107`, `OAI.MUB6.Certificate.MixedSemantics.node5107Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5108`, `OAI.MUB6.Certificate.MixedSemantics.node5108Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5109`, `OAI.MUB6.Certificate.MixedSemantics.node5109Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5110`, `OAI.MUB6.Certificate.MixedSemantics.node5110Labels`, `OAI.MUB6.Certificate.MixedSemantics.node5111`, `OAI.MUB6.Certificate.MixedSemantics.node5111Labels` and 5513 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_MixedSemantics_Canonical0`, `MutuallyUnbiased_MixedSemantics_Canonical7`, `MutuallyUnbiased_MixedSemantics_Canonical78`, `MutuallyUnbiased_MixedSemantics_Canonical79`, `MutuallyUnbiased_MixedSemantics_Canonical8`, `MutuallyUnbiased_MixedSemantics_Canonical80`, `MutuallyUnbiased_MixedSemantics_Canonical81`, `MutuallyUnbiased_MixedSemantics_ExtraNodes`, `MutuallyUnbiased_MixedSemantics_Nodes79`, `MutuallyUnbiased_MixedSemantics_Nodes8`, `MutuallyUnbiased_MixedSemantics_Nodes80`, `MutuallyUnbiased_MixedSemantics_Nodes81`, `MutuallyUnbiased_MixedSemantics_Nodes82`, `MutuallyUnbiased_MixedSemantics_Nodes83`, `MutuallyUnbiased_MixedSemantics_Nodes84`, `MutuallyUnbiased_MixedSemantics_Nodes85`, `MutuallyUnbiased_MixedSemantics_Nodes9`, `MutuallyUnbiased_MixedSemantics_Permutations`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ106D131`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Permutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def permutation0 : Equiv.Perm (Fin 2) where
  toFun := ![0, 1]
  invFun := ![0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation1 : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation2 : Equiv.Perm (Fin 3) where
  toFun := ![0, 1, 2]
  invFun := ![0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation3 : Equiv.Perm (Fin 3) where
  toFun := ![0, 2, 1]
  invFun := ![0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation4 : Equiv.Perm (Fin 3) where
  toFun := ![1, 0, 2]
  invFun := ![1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation5 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation6 : Equiv.Perm (Fin 3) where
  toFun := ![2, 0, 1]
  invFun := ![1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation7 : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation8 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 2, 3]
  invFun := ![0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation9 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation10 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation11 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation12 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation13 : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 2, 1]
  invFun := ![0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation14 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 2, 3]
  invFun := ![1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation15 : Equiv.Perm (Fin 4) where
  toFun := ![1, 0, 3, 2]
  invFun := ![1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation16 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 0, 3]
  invFun := ![2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation17 : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation18 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 0, 2]
  invFun := ![2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation19 : Equiv.Perm (Fin 4) where
  toFun := ![1, 3, 2, 0]
  invFun := ![3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation20 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation21 : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation22 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 0, 3]
  invFun := ![2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation23 : Equiv.Perm (Fin 4) where
  toFun := ![2, 1, 3, 0]
  invFun := ![3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation24 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation25 : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation26 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 1, 2]
  invFun := ![1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation27 : Equiv.Perm (Fin 4) where
  toFun := ![3, 0, 2, 1]
  invFun := ![1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation28 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 0, 2]
  invFun := ![2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation29 : Equiv.Perm (Fin 4) where
  toFun := ![3, 1, 2, 0]
  invFun := ![3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation30 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 0, 1]
  invFun := ![2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation31 : Equiv.Perm (Fin 4) where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation32 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation33 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation34 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation35 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 3, 4, 2]
  invFun := ![0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation36 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation37 : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 3, 2]
  invFun := ![0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation38 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 3, 4]
  invFun := ![0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation39 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation40 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 1, 4]
  invFun := ![0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation41 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 3, 4, 1]
  invFun := ![0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation42 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation43 : Equiv.Perm (Fin 5) where
  toFun := ![0, 2, 4, 3, 1]
  invFun := ![0, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation44 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 2, 4]
  invFun := ![0, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation45 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 1, 4, 2]
  invFun := ![0, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation46 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 1, 4]
  invFun := ![0, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation47 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 2, 4, 1]
  invFun := ![0, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation48 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 1, 2]
  invFun := ![0, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation49 : Equiv.Perm (Fin 5) where
  toFun := ![0, 3, 4, 2, 1]
  invFun := ![0, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation50 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 2, 3]
  invFun := ![0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation51 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 1, 3, 2]
  invFun := ![0, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation52 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 1, 3]
  invFun := ![0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation53 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 2, 3, 1]
  invFun := ![0, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation54 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 1, 2]
  invFun := ![0, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation55 : Equiv.Perm (Fin 5) where
  toFun := ![0, 4, 3, 2, 1]
  invFun := ![0, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation56 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation57 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 2, 4, 3]
  invFun := ![1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation58 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 2, 4]
  invFun := ![1, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation59 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation60 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 2, 3]
  invFun := ![1, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation61 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 4, 3, 2]
  invFun := ![1, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation62 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 3, 4]
  invFun := ![2, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation63 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 0, 4, 3]
  invFun := ![2, 0, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation64 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 0, 4]
  invFun := ![3, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation65 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 3, 4, 0]
  invFun := ![4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation66 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 0, 3]
  invFun := ![3, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation67 : Equiv.Perm (Fin 5) where
  toFun := ![1, 2, 4, 3, 0]
  invFun := ![4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation68 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 2, 4]
  invFun := ![2, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation69 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 0, 4, 2]
  invFun := ![2, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation70 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 0, 4]
  invFun := ![3, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation71 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 2, 4, 0]
  invFun := ![4, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation72 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 0, 2]
  invFun := ![3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation73 : Equiv.Perm (Fin 5) where
  toFun := ![1, 3, 4, 2, 0]
  invFun := ![4, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation74 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 2, 3]
  invFun := ![2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation75 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 0, 3, 2]
  invFun := ![2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation76 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 0, 3]
  invFun := ![3, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation77 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 2, 3, 0]
  invFun := ![4, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation78 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 0, 2]
  invFun := ![3, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation79 : Equiv.Perm (Fin 5) where
  toFun := ![1, 4, 3, 2, 0]
  invFun := ![4, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation80 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 3, 4]
  invFun := ![1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation81 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 1, 4, 3]
  invFun := ![1, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation82 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 1, 4]
  invFun := ![1, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation83 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 3, 4, 1]
  invFun := ![1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation84 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 1, 3]
  invFun := ![1, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation85 : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 3, 1]
  invFun := ![1, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation86 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 3, 4]
  invFun := ![2, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation87 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 0, 4, 3]
  invFun := ![2, 1, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation88 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 0, 4]
  invFun := ![3, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation89 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 3, 4, 0]
  invFun := ![4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation90 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 0, 3]
  invFun := ![3, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation91 : Equiv.Perm (Fin 5) where
  toFun := ![2, 1, 4, 3, 0]
  invFun := ![4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation92 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation93 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 0, 4, 1]
  invFun := ![2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation94 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 0, 4]
  invFun := ![3, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation95 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 1, 4, 0]
  invFun := ![4, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation96 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 0, 1]
  invFun := ![3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation97 : Equiv.Perm (Fin 5) where
  toFun := ![2, 3, 4, 1, 0]
  invFun := ![4, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation98 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 1, 3]
  invFun := ![2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation99 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 0, 3, 1]
  invFun := ![2, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation100 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 0, 3]
  invFun := ![3, 2, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation101 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 1, 3, 0]
  invFun := ![4, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation102 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 0, 1]
  invFun := ![3, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation103 : Equiv.Perm (Fin 5) where
  toFun := ![2, 4, 3, 1, 0]
  invFun := ![4, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation104 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 2, 4]
  invFun := ![1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation105 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 1, 4, 2]
  invFun := ![1, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation106 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 1, 4]
  invFun := ![1, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation107 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 2, 4, 1]
  invFun := ![1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation108 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 1, 2]
  invFun := ![1, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation109 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 2, 1]
  invFun := ![1, 4, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation110 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 2, 4]
  invFun := ![2, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation111 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 0, 4, 2]
  invFun := ![2, 1, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation112 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 0, 4]
  invFun := ![3, 1, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation113 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 2, 4, 0]
  invFun := ![4, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation114 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 0, 2]
  invFun := ![3, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation115 : Equiv.Perm (Fin 5) where
  toFun := ![3, 1, 4, 2, 0]
  invFun := ![4, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation116 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation117 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 0, 4, 1]
  invFun := ![2, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation118 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 0, 4]
  invFun := ![3, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation119 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 1, 4, 0]
  invFun := ![4, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation120 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 0, 1]
  invFun := ![3, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation121 : Equiv.Perm (Fin 5) where
  toFun := ![3, 2, 4, 1, 0]
  invFun := ![4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation122 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation123 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 2, 1]
  invFun := ![2, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation124 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 0, 2]
  invFun := ![3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation125 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 1, 2, 0]
  invFun := ![4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation126 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 0, 1]
  invFun := ![3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation127 : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 1, 0]
  invFun := ![4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation128 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 2, 3]
  invFun := ![1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation129 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 3, 2]
  invFun := ![1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation130 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 1, 3]
  invFun := ![1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation131 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 2, 3, 1]
  invFun := ![1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation132 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 3, 1, 2]
  invFun := ![1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation133 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 3, 2, 1]
  invFun := ![1, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation134 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 2, 3]
  invFun := ![2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation135 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 0, 3, 2]
  invFun := ![2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation136 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 0, 3]
  invFun := ![3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation137 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 2, 3, 0]
  invFun := ![4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation138 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 0, 2]
  invFun := ![3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation139 : Equiv.Perm (Fin 5) where
  toFun := ![4, 1, 3, 2, 0]
  invFun := ![4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation140 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 1, 3]
  invFun := ![2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation141 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 0, 3, 1]
  invFun := ![2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation142 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 0, 3]
  invFun := ![3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation143 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 1, 3, 0]
  invFun := ![4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation144 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 0, 1]
  invFun := ![3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation145 : Equiv.Perm (Fin 5) where
  toFun := ![4, 2, 3, 1, 0]
  invFun := ![4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation146 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 1, 2]
  invFun := ![2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation147 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 0, 2, 1]
  invFun := ![2, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation148 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 0, 2]
  invFun := ![3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation149 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 1, 2, 0]
  invFun := ![4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation150 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 0, 1]
  invFun := ![3, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation151 : Equiv.Perm (Fin 5) where
  toFun := ![4, 3, 2, 1, 0]
  invFun := ![4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation152 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation153 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation154 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation155 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation156 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation157 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 2, 5, 4, 3]
  invFun := ![0, 1, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation158 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation159 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 2, 5, 4]
  invFun := ![0, 1, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation160 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 2, 5]
  invFun := ![0, 1, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation161 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 4, 5, 2]
  invFun := ![0, 1, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation162 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 2, 4]
  invFun := ![0, 1, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation163 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 3, 5, 4, 2]
  invFun := ![0, 1, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation164 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation165 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 2, 5, 3]
  invFun := ![0, 1, 3, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation166 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 3, 2, 5]
  invFun := ![0, 1, 4, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation167 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 3, 5, 2]
  invFun := ![0, 1, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation168 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation169 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 4, 5, 3, 2]
  invFun := ![0, 1, 5, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation170 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation171 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 2, 4, 3]
  invFun := ![0, 1, 3, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation172 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 3, 2, 4]
  invFun := ![0, 1, 4, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation173 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 3, 4, 2]
  invFun := ![0, 1, 5, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation174 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 4, 2, 3]
  invFun := ![0, 1, 4, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation175 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 4, 3, 2]
  invFun := ![0, 1, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation176 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation177 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 3, 5, 4]
  invFun := ![0, 2, 1, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation178 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation179 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 5, 3]
  invFun := ![0, 2, 1, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation180 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 5, 3, 4]
  invFun := ![0, 2, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation181 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 5, 4, 3]
  invFun := ![0, 2, 1, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation182 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation183 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 1, 5, 4]
  invFun := ![0, 3, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation184 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 1, 5]
  invFun := ![0, 4, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation185 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation186 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 5, 1, 4]
  invFun := ![0, 4, 1, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation187 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 5, 4, 1]
  invFun := ![0, 5, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation188 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation189 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 5, 3]
  invFun := ![0, 3, 1, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation190 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 3, 1, 5]
  invFun := ![0, 4, 1, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation191 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 3, 5, 1]
  invFun := ![0, 5, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation192 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 5, 1, 3]
  invFun := ![0, 4, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation193 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 5, 3, 1]
  invFun := ![0, 5, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation194 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 1, 3, 4]
  invFun := ![0, 3, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation195 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 1, 4, 3]
  invFun := ![0, 3, 1, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation196 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 3, 1, 4]
  invFun := ![0, 4, 1, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation197 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 3, 4, 1]
  invFun := ![0, 5, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation198 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 4, 1, 3]
  invFun := ![0, 4, 1, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation199 : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 5, 4, 3, 1]
  invFun := ![0, 5, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation200 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation201 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation202 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 4, 2, 5]
  invFun := ![0, 2, 4, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation203 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 4, 5, 2]
  invFun := ![0, 2, 5, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation204 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 5, 2, 4]
  invFun := ![0, 2, 4, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation205 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 1, 5, 4, 2]
  invFun := ![0, 2, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation206 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 1, 4, 5]
  invFun := ![0, 3, 2, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation207 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 1, 5, 4]
  invFun := ![0, 3, 2, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation208 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 4, 1, 5]
  invFun := ![0, 4, 2, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation209 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 4, 5, 1]
  invFun := ![0, 5, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation210 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 5, 1, 4]
  invFun := ![0, 4, 2, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation211 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 2, 5, 4, 1]
  invFun := ![0, 5, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation212 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation213 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 5, 2]
  invFun := ![0, 3, 5, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation214 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 2, 1, 5]
  invFun := ![0, 4, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation215 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 2, 5, 1]
  invFun := ![0, 5, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation216 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation217 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 5, 2, 1]
  invFun := ![0, 5, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation218 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation219 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 1, 4, 2]
  invFun := ![0, 3, 5, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation220 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 2, 1, 4]
  invFun := ![0, 4, 3, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation221 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 2, 4, 1]
  invFun := ![0, 5, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation222 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 4, 1, 2]
  invFun := ![0, 4, 5, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation223 : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 5, 4, 2, 1]
  invFun := ![0, 5, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation224 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation225 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 2, 5, 3]
  invFun := ![0, 2, 3, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation226 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 2, 5]
  invFun := ![0, 2, 4, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation227 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 3, 5, 2]
  invFun := ![0, 2, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation228 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation229 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 1, 5, 3, 2]
  invFun := ![0, 2, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation230 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 1, 3, 5]
  invFun := ![0, 3, 2, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation231 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 1, 5, 3]
  invFun := ![0, 3, 2, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation232 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 1, 5]
  invFun := ![0, 4, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation233 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 2, 3, 5, 1]
  invFun := ![0, 5, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation234 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 1, 2, 5]
  invFun := ![0, 3, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation235 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 1, 5, 2]
  invFun := ![0, 3, 5, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation236 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 2, 1, 5]
  invFun := ![0, 4, 3, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation237 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 2, 5, 1]
  invFun := ![0, 5, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation238 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 5, 1, 2]
  invFun := ![0, 4, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation239 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 3, 5, 2, 1]
  invFun := ![0, 5, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation240 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation241 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 1, 3, 2]
  invFun := ![0, 3, 5, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation242 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 2, 1, 3]
  invFun := ![0, 4, 3, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation243 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation244 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 3, 1, 2]
  invFun := ![0, 4, 5, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation245 : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 3, 2, 1]
  invFun := ![0, 5, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation246 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation247 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 2, 4, 3]
  invFun := ![0, 2, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation248 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 3, 2, 4]
  invFun := ![0, 2, 4, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation249 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 3, 4, 2]
  invFun := ![0, 2, 5, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation250 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 4, 2, 3]
  invFun := ![0, 2, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation251 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 1, 4, 3, 2]
  invFun := ![0, 2, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation252 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 1, 3, 4]
  invFun := ![0, 3, 2, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation253 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 1, 4, 3]
  invFun := ![0, 3, 2, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation254 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 3, 1, 4]
  invFun := ![0, 4, 2, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation255 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 3, 4, 1]
  invFun := ![0, 5, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation256 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 2, 4, 3, 1]
  invFun := ![0, 5, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation257 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation258 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation259 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 3, 4, 2, 1]
  invFun := ![0, 5, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation260 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation261 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 1, 3, 2]
  invFun := ![0, 3, 5, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation262 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 2, 1, 3]
  invFun := ![0, 4, 3, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation263 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation264 : Equiv.Perm (Fin 6) where
  toFun := ![0, 5, 4, 3, 2, 1]
  invFun := ![0, 5, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation265 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation266 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 5, 4]
  invFun := ![1, 0, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation267 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 4, 3, 5]
  invFun := ![1, 0, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation268 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 4, 5, 3]
  invFun := ![1, 0, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation269 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation270 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 5, 4, 3]
  invFun := ![1, 0, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation271 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 4, 5]
  invFun := ![1, 0, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation272 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation273 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 2, 5]
  invFun := ![1, 0, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation274 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 4, 5, 2]
  invFun := ![1, 0, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation275 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 5, 2, 4]
  invFun := ![1, 0, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation276 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 3, 5, 4, 2]
  invFun := ![1, 0, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation277 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 2, 3, 5]
  invFun := ![1, 0, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation278 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 2, 5, 3]
  invFun := ![1, 0, 3, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation279 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 3, 2, 5]
  invFun := ![1, 0, 4, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation280 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 3, 5, 2]
  invFun := ![1, 0, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation281 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 5, 2, 3]
  invFun := ![1, 0, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation282 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 4, 5, 3, 2]
  invFun := ![1, 0, 5, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation283 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 2, 3, 4]
  invFun := ![1, 0, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation284 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 2, 4, 3]
  invFun := ![1, 0, 3, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation285 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 3, 2, 4]
  invFun := ![1, 0, 4, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation286 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 3, 4, 2]
  invFun := ![1, 0, 5, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation287 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 4, 2, 3]
  invFun := ![1, 0, 4, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation288 : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 4, 3, 2]
  invFun := ![1, 0, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation289 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation290 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 5, 4]
  invFun := ![2, 0, 1, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation291 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 4, 3, 5]
  invFun := ![2, 0, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation292 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 4, 5, 3]
  invFun := ![2, 0, 1, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation293 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 5, 3, 4]
  invFun := ![2, 0, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation294 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 5, 4, 3]
  invFun := ![2, 0, 1, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation295 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 0, 4, 5]
  invFun := ![3, 0, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation296 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 0, 5, 4]
  invFun := ![3, 0, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation297 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation298 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 5, 4, 0]
  invFun := ![5, 0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation300 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 3, 0, 5]
  invFun := ![4, 0, 1, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation301 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 3, 5, 0]
  invFun := ![5, 0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation302 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 4, 5, 3, 0]
  invFun := ![5, 0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation303 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 5, 0, 3, 4]
  invFun := ![3, 0, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation304 : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 5, 3, 4, 0]
  invFun := ![5, 0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation305 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 2, 4, 5]
  invFun := ![2, 0, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation306 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 2, 5, 4]
  invFun := ![2, 0, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation307 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 4, 2, 5]
  invFun := ![2, 0, 4, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation308 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 4, 5, 2]
  invFun := ![2, 0, 5, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation309 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 5, 2, 4]
  invFun := ![2, 0, 4, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation310 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 0, 5, 4, 2]
  invFun := ![2, 0, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation311 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 2, 0, 5, 4]
  invFun := ![3, 0, 2, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation312 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 2, 5, 4, 0]
  invFun := ![5, 0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation313 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 0, 2, 5]
  invFun := ![3, 0, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation314 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 0, 5, 2]
  invFun := ![3, 0, 5, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation315 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 2, 0, 5]
  invFun := ![4, 0, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation316 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 2, 5, 0]
  invFun := ![5, 0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation317 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 4, 5, 2, 0]
  invFun := ![5, 0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation318 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 5, 0, 2, 4]
  invFun := ![3, 0, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation319 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 5, 2, 4, 0]
  invFun := ![5, 0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation320 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 5, 4, 0, 2]
  invFun := ![4, 0, 5, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation321 : Equiv.Perm (Fin 6) where
  toFun := ![1, 3, 5, 4, 2, 0]
  invFun := ![5, 0, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation322 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 2, 3, 5]
  invFun := ![2, 0, 3, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation323 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 3, 5, 2]
  invFun := ![2, 0, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation324 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 5, 2, 3]
  invFun := ![2, 0, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation325 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 0, 5, 3, 2]
  invFun := ![2, 0, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation326 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 2, 0, 3, 5]
  invFun := ![3, 0, 2, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation327 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 3, 0, 2, 5]
  invFun := ![3, 0, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation328 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 3, 5, 2, 0]
  invFun := ![5, 0, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation329 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 5, 0, 2, 3]
  invFun := ![3, 0, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation330 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 5, 0, 3, 2]
  invFun := ![3, 0, 5, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation331 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 5, 2, 0, 3]
  invFun := ![4, 0, 3, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation332 : Equiv.Perm (Fin 6) where
  toFun := ![1, 4, 5, 2, 3, 0]
  invFun := ![5, 0, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation333 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 3, 4]
  invFun := ![2, 0, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation334 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 2, 4, 3]
  invFun := ![2, 0, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation335 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 3, 2, 4]
  invFun := ![2, 0, 4, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation336 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 3, 4, 2]
  invFun := ![2, 0, 5, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation337 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 2, 3]
  invFun := ![2, 0, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation338 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 0, 4, 3, 2]
  invFun := ![2, 0, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation339 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 2, 3, 0, 4]
  invFun := ![4, 0, 2, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation340 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 2, 3, 4, 0]
  invFun := ![5, 0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation341 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 3, 0, 2, 4]
  invFun := ![3, 0, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation342 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 3, 4, 0, 2]
  invFun := ![4, 0, 5, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation343 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 3, 4, 2, 0]
  invFun := ![5, 0, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation344 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 4, 0, 2, 3]
  invFun := ![3, 0, 4, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation345 : Equiv.Perm (Fin 6) where
  toFun := ![1, 5, 4, 2, 3, 0]
  invFun := ![5, 0, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation346 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation347 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 3, 5, 4]
  invFun := ![1, 2, 0, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation348 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation349 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation350 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation351 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 1, 5, 4, 3]
  invFun := ![1, 2, 0, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation352 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 1, 4, 5]
  invFun := ![1, 3, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation353 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 1, 5, 4]
  invFun := ![1, 3, 0, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation354 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 4, 1, 5]
  invFun := ![1, 4, 0, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation355 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 3, 4, 5, 1]
  invFun := ![1, 5, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation356 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 4, 1, 3, 5]
  invFun := ![1, 3, 0, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation357 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 4, 1, 5, 3]
  invFun := ![1, 3, 0, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation358 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 4, 3, 1, 5]
  invFun := ![1, 4, 0, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation359 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 4, 5, 1, 3]
  invFun := ![1, 4, 0, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation360 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 4, 5, 3, 1]
  invFun := ![1, 5, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation361 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 1, 3, 4]
  invFun := ![1, 3, 0, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation362 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 1, 4, 3]
  invFun := ![1, 3, 0, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation363 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 3, 1, 4]
  invFun := ![1, 4, 0, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation364 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 3, 4, 1]
  invFun := ![1, 5, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation365 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 4, 1, 3]
  invFun := ![1, 4, 0, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation366 : Equiv.Perm (Fin 6) where
  toFun := ![2, 0, 5, 4, 3, 1]
  invFun := ![1, 5, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation367 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 3, 4, 5]
  invFun := ![2, 1, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation368 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 3, 5, 4]
  invFun := ![2, 1, 0, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation369 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 4, 5, 3]
  invFun := ![2, 1, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation370 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 5, 3, 4]
  invFun := ![2, 1, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation371 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 0, 5, 4, 3]
  invFun := ![2, 1, 0, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation372 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 3, 0, 4, 5]
  invFun := ![3, 1, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation373 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 3, 4, 5, 0]
  invFun := ![5, 1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation374 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 3, 5, 4, 0]
  invFun := ![5, 1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation375 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 4, 0, 3, 5]
  invFun := ![3, 1, 0, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation376 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 4, 0, 5, 3]
  invFun := ![3, 1, 0, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation377 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 4, 3, 0, 5]
  invFun := ![4, 1, 0, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation378 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 4, 5, 3, 0]
  invFun := ![5, 1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation379 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 5, 0, 3, 4]
  invFun := ![3, 1, 0, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation380 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 5, 0, 4, 3]
  invFun := ![3, 1, 0, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation381 : Equiv.Perm (Fin 6) where
  toFun := ![2, 1, 5, 3, 4, 0]
  invFun := ![5, 1, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation382 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 4, 1, 5]
  invFun := ![2, 4, 0, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation383 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 4, 5, 1]
  invFun := ![2, 5, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation384 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 0, 5, 1, 4]
  invFun := ![2, 4, 0, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation385 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 1, 0, 4, 5]
  invFun := ![3, 2, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation386 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 1, 0, 5, 4]
  invFun := ![3, 2, 0, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation387 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 1, 4, 5, 0]
  invFun := ![5, 2, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation388 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 1, 5, 4, 0]
  invFun := ![5, 2, 0, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation389 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation390 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 0, 5, 1]
  invFun := ![3, 5, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation391 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 1, 0, 5]
  invFun := ![4, 3, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation392 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 1, 5, 0]
  invFun := ![5, 3, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation393 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation394 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 1, 0]
  invFun := ![5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation395 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 5, 0, 1, 4]
  invFun := ![3, 4, 0, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation396 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 5, 0, 4, 1]
  invFun := ![3, 5, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation397 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 5, 1, 4, 0]
  invFun := ![5, 3, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation398 : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 5, 4, 0, 1]
  invFun := ![4, 5, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation399 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation400 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 3, 5, 1]
  invFun := ![2, 5, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation401 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation402 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 3, 1]
  invFun := ![2, 5, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation403 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 1, 0, 3, 5]
  invFun := ![3, 2, 0, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation404 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 1, 3, 0, 5]
  invFun := ![4, 2, 0, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation405 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 1, 5, 0, 3]
  invFun := ![4, 2, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation406 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 1, 5, 3, 0]
  invFun := ![5, 2, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation407 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 3, 0, 1, 5]
  invFun := ![3, 4, 0, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation408 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 3, 5, 0, 1]
  invFun := ![4, 5, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation409 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation410 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 0, 3, 1]
  invFun := ![3, 5, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation411 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 1, 0, 3]
  invFun := ![4, 3, 0, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation412 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 1, 3, 0]
  invFun := ![5, 3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation413 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 5, 3, 0, 1]
  invFun := ![4, 5, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation414 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation415 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation416 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 3, 4, 1]
  invFun := ![2, 5, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation417 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 4, 1, 3]
  invFun := ![2, 4, 0, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation418 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 0, 4, 3, 1]
  invFun := ![2, 5, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation419 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 0, 3, 4]
  invFun := ![3, 2, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation420 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 0, 4, 3]
  invFun := ![3, 2, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation421 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 3, 4, 0]
  invFun := ![5, 2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation422 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 4, 0, 3]
  invFun := ![4, 2, 0, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation423 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 1, 4, 3, 0]
  invFun := ![5, 2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation424 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 0, 1, 4]
  invFun := ![3, 4, 0, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation425 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 1, 4, 0]
  invFun := ![5, 3, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation426 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 4, 0, 1]
  invFun := ![4, 5, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation427 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 3, 4, 1, 0]
  invFun := ![5, 4, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation428 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation429 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 0, 3, 1]
  invFun := ![3, 5, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation430 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 1, 0, 3]
  invFun := ![4, 3, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation431 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 1, 3, 0]
  invFun := ![5, 3, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation432 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 3, 0, 1]
  invFun := ![4, 5, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation433 : Equiv.Perm (Fin 6) where
  toFun := ![2, 5, 4, 3, 1, 0]
  invFun := ![5, 4, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation434 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation435 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation436 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 4, 2, 5]
  invFun := ![1, 2, 4, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation437 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 4, 5, 2]
  invFun := ![1, 2, 5, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation438 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 5, 2, 4]
  invFun := ![1, 2, 4, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation439 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 1, 5, 4, 2]
  invFun := ![1, 2, 5, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation440 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 1, 4, 5]
  invFun := ![1, 3, 2, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation441 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 4, 5, 1]
  invFun := ![1, 5, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation442 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 2, 5, 4, 1]
  invFun := ![1, 5, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation443 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 1, 2, 5]
  invFun := ![1, 3, 4, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation444 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 1, 5, 2]
  invFun := ![1, 3, 5, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation445 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 2, 1, 5]
  invFun := ![1, 4, 3, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation446 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 5, 1, 2]
  invFun := ![1, 4, 5, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation447 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 4, 5, 2, 1]
  invFun := ![1, 5, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation448 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 5, 1, 2, 4]
  invFun := ![1, 3, 4, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation449 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 5, 4, 1, 2]
  invFun := ![1, 4, 5, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation450 : Equiv.Perm (Fin 6) where
  toFun := ![3, 0, 5, 4, 2, 1]
  invFun := ![1, 5, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation451 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 2, 4, 5]
  invFun := ![2, 1, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation452 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 2, 5, 4]
  invFun := ![2, 1, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation453 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 4, 2, 5]
  invFun := ![2, 1, 4, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation454 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 4, 5, 2]
  invFun := ![2, 1, 5, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation455 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 5, 2, 4]
  invFun := ![2, 1, 4, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation456 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 0, 5, 4, 2]
  invFun := ![2, 1, 5, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation457 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 2, 0, 5, 4]
  invFun := ![3, 1, 2, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation458 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 2, 5, 0, 4]
  invFun := ![4, 1, 2, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation459 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 4, 0, 2, 5]
  invFun := ![3, 1, 4, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation460 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 4, 0, 5, 2]
  invFun := ![3, 1, 5, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation462 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 4, 2, 5, 0]
  invFun := ![5, 1, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation463 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 4, 5, 2, 0]
  invFun := ![5, 1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation464 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 5, 0, 2, 4]
  invFun := ![3, 1, 4, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation465 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 5, 2, 4, 0]
  invFun := ![5, 1, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation466 : Equiv.Perm (Fin 6) where
  toFun := ![3, 1, 5, 4, 2, 0]
  invFun := ![5, 1, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation467 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 0, 4, 1, 5]
  invFun := ![2, 4, 1, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation468 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 0, 4, 5, 1]
  invFun := ![2, 5, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation469 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 0, 5, 1, 4]
  invFun := ![2, 4, 1, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation470 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 1, 0, 4, 5]
  invFun := ![3, 2, 1, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation471 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 1, 0, 5, 4]
  invFun := ![3, 2, 1, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation472 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 1, 4, 0, 5]
  invFun := ![4, 2, 1, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation473 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 1, 4, 5, 0]
  invFun := ![5, 2, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation475 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 0, 1, 5]
  invFun := ![3, 4, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation476 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 0, 5, 1]
  invFun := ![3, 5, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation477 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 1, 0, 5]
  invFun := ![4, 3, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation478 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 1, 5, 0]
  invFun := ![5, 3, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation479 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 5, 0, 1]
  invFun := ![4, 5, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation480 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 4, 5, 1, 0]
  invFun := ![5, 4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation481 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 5, 0, 4, 1]
  invFun := ![3, 5, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation482 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 5, 1, 4, 0]
  invFun := ![5, 3, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation483 : Equiv.Perm (Fin 6) where
  toFun := ![3, 2, 5, 4, 0, 1]
  invFun := ![4, 5, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation484 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation485 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation486 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 2, 5, 1]
  invFun := ![2, 5, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation487 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 5, 1, 2]
  invFun := ![2, 4, 5, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation488 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 0, 5, 2, 1]
  invFun := ![2, 5, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation489 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 0, 2, 5]
  invFun := ![3, 2, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation490 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation491 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation492 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation493 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 5, 0, 2]
  invFun := ![4, 2, 5, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation494 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 1, 5, 2, 0]
  invFun := ![5, 2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation495 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 0, 1, 5]
  invFun := ![3, 4, 2, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation496 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 1, 0, 5]
  invFun := ![4, 3, 2, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation497 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation498 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 2, 5, 1, 0]
  invFun := ![5, 4, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation499 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation500 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation501 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation502 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation503 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation504 : Equiv.Perm (Fin 6) where
  toFun := ![3, 4, 5, 2, 1, 0]
  invFun := ![5, 4, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation505 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation506 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation507 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 0, 4, 1, 2]
  invFun := ![2, 4, 5, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation508 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 0, 2, 4]
  invFun := ![3, 2, 4, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation509 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation510 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 4, 0, 2]
  invFun := ![4, 2, 5, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation511 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation513 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation514 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation515 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation516 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation517 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation518 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation519 : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation520 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation521 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation522 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 2, 5]
  invFun := ![1, 2, 4, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation523 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 3, 5, 2]
  invFun := ![1, 2, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation524 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation525 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 1, 5, 3, 2]
  invFun := ![1, 2, 5, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation526 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation527 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation528 : Equiv.Perm (Fin 6) where
  toFun := ![4, 0, 5, 2, 3, 1]
  invFun := ![1, 5, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation529 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 2, 3, 5]
  invFun := ![2, 1, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation530 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 0, 3, 5, 2]
  invFun := ![2, 1, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation531 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 0, 5, 3]
  invFun := ![3, 1, 2, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation532 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 3, 0, 5]
  invFun := ![4, 1, 2, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation533 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 3, 5, 0]
  invFun := ![5, 1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation534 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 5, 0, 3]
  invFun := ![4, 1, 2, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation535 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 2, 5, 3, 0]
  invFun := ![5, 1, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation536 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 2, 5, 0]
  invFun := ![5, 1, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation537 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 3, 5, 2, 0]
  invFun := ![5, 1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation538 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 5, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation539 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 5, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation540 : Equiv.Perm (Fin 6) where
  toFun := ![4, 1, 5, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation541 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 1, 3, 5]
  invFun := ![2, 3, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation542 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 0, 3, 5, 1]
  invFun := ![2, 5, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation543 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 1, 0, 3, 5]
  invFun := ![3, 2, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation545 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 3, 5, 0, 1]
  invFun := ![4, 5, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation547 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation548 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation549 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 1, 0, 3]
  invFun := ![4, 3, 1, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation550 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation551 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation552 : Equiv.Perm (Fin 6) where
  toFun := ![4, 2, 5, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation553 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation554 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 0, 2, 5]
  invFun := ![3, 2, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation555 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation556 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation557 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation558 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 5, 0, 2]
  invFun := ![4, 2, 5, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation559 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 1, 5, 2, 0]
  invFun := ![5, 2, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation560 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 1, 0, 5]
  invFun := ![4, 3, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation561 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation562 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 2, 5, 1, 0]
  invFun := ![5, 4, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation563 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation564 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation565 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation566 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation567 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation568 : Equiv.Perm (Fin 6) where
  toFun := ![4, 3, 5, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation569 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation570 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation571 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation572 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation573 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 3, 1, 2]
  invFun := ![2, 4, 5, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation574 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 0, 3, 2, 1]
  invFun := ![2, 5, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation576 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation577 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation578 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation579 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 1, 3, 2, 0]
  invFun := ![5, 2, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation580 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 0, 1, 3]
  invFun := ![3, 4, 2, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation581 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 0, 3, 1]
  invFun := ![3, 5, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation582 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation583 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation584 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation585 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation586 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation587 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation588 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation589 : Equiv.Perm (Fin 6) where
  toFun := ![4, 5, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation590 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation591 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 2, 4, 3]
  invFun := ![1, 2, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation593 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 2, 3]
  invFun := ![1, 2, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation594 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 1, 4, 3, 2]
  invFun := ![1, 2, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation595 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 3, 4, 1]
  invFun := ![1, 5, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation596 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 2, 4, 3, 1]
  invFun := ![1, 5, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation597 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 1, 2]
  invFun := ![1, 4, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation598 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 3, 4, 2, 1]
  invFun := ![1, 5, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation599 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation600 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation601 : Equiv.Perm (Fin 6) where
  toFun := ![5, 0, 4, 3, 1, 2]
  invFun := ![1, 4, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation602 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 3, 4]
  invFun := ![2, 1, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation603 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 2, 4, 3]
  invFun := ![2, 1, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation605 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 3, 4, 2]
  invFun := ![2, 1, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation606 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 0, 4, 2, 3]
  invFun := ![2, 1, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation607 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 0, 3, 4]
  invFun := ![3, 1, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation608 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 0, 4]
  invFun := ![4, 1, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation609 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 3, 4, 0]
  invFun := ![5, 1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation610 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 0, 3]
  invFun := ![4, 1, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation611 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 2, 4, 3, 0]
  invFun := ![5, 1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation612 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 0, 2, 4]
  invFun := ![3, 1, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation613 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 0, 4]
  invFun := ![4, 1, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation614 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 2, 4, 0]
  invFun := ![5, 1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation615 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 0, 2]
  invFun := ![4, 1, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation616 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 3, 4, 2, 0]
  invFun := ![5, 1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation617 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation618 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 0, 3, 2]
  invFun := ![3, 1, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation619 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation620 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation621 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 0, 2]
  invFun := ![4, 1, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation622 : Equiv.Perm (Fin 6) where
  toFun := ![5, 1, 4, 3, 2, 0]
  invFun := ![5, 1, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation623 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation624 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 1, 4, 3]
  invFun := ![2, 3, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation625 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 3, 1, 4]
  invFun := ![2, 4, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation626 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 3, 4, 1]
  invFun := ![2, 5, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation627 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 4, 1, 3]
  invFun := ![2, 4, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation628 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 0, 4, 3, 1]
  invFun := ![2, 5, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation629 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 3, 4]
  invFun := ![3, 2, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation630 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 0, 4, 3]
  invFun := ![3, 2, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation631 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 0, 4]
  invFun := ![4, 2, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation632 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 3, 4, 0]
  invFun := ![5, 2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation633 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 0, 3]
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation634 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 3, 0]
  invFun := ![5, 2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation635 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 0, 1, 4]
  invFun := ![3, 4, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation636 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 0, 4, 1]
  invFun := ![3, 5, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation637 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 0, 4]
  invFun := ![4, 3, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation638 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 1, 4, 0]
  invFun := ![5, 3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation639 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 0, 1]
  invFun := ![4, 5, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation640 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 3, 4, 1, 0]
  invFun := ![5, 4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation641 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation642 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation643 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 1, 0, 3]
  invFun := ![4, 3, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation644 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation645 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation646 : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 4, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation647 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation648 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation649 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 2, 4, 1]
  invFun := ![2, 5, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation650 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 4, 1, 2]
  invFun := ![2, 4, 5, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation651 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 0, 4, 2, 1]
  invFun := ![2, 5, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation652 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation653 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation654 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation655 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 0, 4, 1]
  invFun := ![3, 5, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation656 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 1, 0, 4]
  invFun := ![4, 3, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation657 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 0, 1]
  invFun := ![4, 5, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation658 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation659 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation660 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation661 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation662 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation663 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation664 : Equiv.Perm (Fin 6) where
  toFun := ![5, 3, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation665 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation666 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation667 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation668 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation669 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 3, 1, 2]
  invFun := ![2, 4, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation670 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 0, 3, 2, 1]
  invFun := ![2, 5, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation671 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation672 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation673 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation674 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation675 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation676 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 1, 3, 2, 0]
  invFun := ![5, 2, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation677 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 0, 1, 3]
  invFun := ![3, 4, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation678 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 0, 3, 1]
  invFun := ![3, 5, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation679 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 1, 0, 3]
  invFun := ![4, 3, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation680 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation681 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation682 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation683 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation684 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation685 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation686 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation687 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation688 : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def labelEmbedding0 : Fin 1 ↪ Fin 2 :=
  ⟨![1], by decide +kernel⟩

def labelEmbedding1 : Fin 2 ↪ Fin 2 :=
  ⟨![1, 0], by decide +kernel⟩

def labelEmbedding2 : Fin 2 ↪ Fin 3 :=
  ⟨![0, 2], by decide +kernel⟩

def labelEmbedding3 : Fin 2 ↪ Fin 3 :=
  ⟨![1, 2], by decide +kernel⟩

def labelEmbedding6 : Fin 3 ↪ Fin 3 :=
  ⟨![0, 2, 1], by decide +kernel⟩

def labelEmbedding7 : Fin 3 ↪ Fin 3 :=
  ⟨![1, 0, 2], by decide +kernel⟩

def labelEmbedding8 : Fin 3 ↪ Fin 3 :=
  ⟨![1, 2, 0], by decide +kernel⟩

def labelEmbedding9 : Fin 3 ↪ Fin 3 :=
  ⟨![2, 0, 1], by decide +kernel⟩

def labelEmbedding10 : Fin 3 ↪ Fin 3 :=
  ⟨![2, 1, 0], by decide +kernel⟩

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw0step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw0step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw0step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw0step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]

def raw10 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]

def raw100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw101step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw102 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw103 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw103step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw104 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1000 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1001 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1001Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw1001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1002 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1002step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1003 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1004 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1004Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw1004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1005 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1005step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1005step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1006 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1006step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1007 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1007Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1007step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw1007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1008 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1008step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1008step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1009 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1009step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1010 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1010Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1010step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw1010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1011 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1011step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1012 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1012step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1013 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1013Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw1013step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1014 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1014step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1014step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1014step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1015 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1015step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1016 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1016Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1016step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-2, 2, 0], ![-2, -2, 4]]
def raw1016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1016step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw1016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1016step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw1016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1017 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1017step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1017step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1017step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1018 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1018step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1019 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1019Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1019step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw1019step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1019step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1020step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1022Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1023step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node5097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node5099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5103 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node5103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5104 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node5106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5107 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def node5107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node5108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def node5109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def node5110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5111 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def node5111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node5112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node5113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node5114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node5115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node5116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node5117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def node5118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def node5119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def node5120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node5121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node5122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node5123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node5125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node5126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node5127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node5128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node5129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node5131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node5132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node5133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node5136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node5139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5140 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node5140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node5141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node5142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node5143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node5144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node5145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node5146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5147 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node5147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node5150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node5151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node5152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node5153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node5154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node5155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5156 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node5156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def node5158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node5159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5161 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node5161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5163 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5164 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def node5165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5171 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def node5171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5172 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node5173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def node5174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def node5175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5176 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def node5176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node5177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node5180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node5181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node5182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5188 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node5188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5189 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node5189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node5190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node5191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node5192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node5193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5195 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node5195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5198 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node5198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5199 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node5199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5200 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node5200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5201 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def node5201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node5205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5206 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def node5206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5207 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def node5207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5210 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node5210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node5211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node5212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5213 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node5213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5214 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def node5214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node5215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node5216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node5217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node5218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node5219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node5221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node5222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node5223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node5224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node5225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node5228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node5229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5232 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node5232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node5233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node5234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5235 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def node5235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5236 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node5236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5238 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def node5238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node5239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node5240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node5241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node5242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node5243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node5244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node5245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node5246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5248 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node5248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node5249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node5251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5252 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node5252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node5253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node5254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node5255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5258 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node5258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5259 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5260 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node5260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5261 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def node5261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node5262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node5263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5264 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node5264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5266 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node5266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5267 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node5267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5268 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def node5268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5269 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node5269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node5270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5272 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def node5272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def node5274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5275 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node5275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def node5276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def node5277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def node5278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5279 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def node5279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node5280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node5281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5282 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node5282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node5283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5284 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node5284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def node5285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node5286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node5287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node5288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5289 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node5289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node5290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node5291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5292 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5293 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node5294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5295 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node5295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5296 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def node5296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5297 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def node5297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5298 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def node5298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node5299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5300 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node5300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node5301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node5302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5303 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def node5303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5304 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node5304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5305 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def node5305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5306 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5307 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5308 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def node5308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5309 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def node5309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5310 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def node5310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5311 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def node5311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node5376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5384 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5389 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def node5389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def node5390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node5391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node5404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node5406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node5407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node5409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node5411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node5412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def node5413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5418 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def node5418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node5419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node5420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node5421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node5423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node5425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node5426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5428 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def node5428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node5429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node5430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node5431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node5432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node5435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node5436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node5437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node5438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5440 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5443 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node5444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node5445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node5446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node5447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5448 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node5448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def node5449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5450 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5451 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def node5451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5452 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node5452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5453 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def node5453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5454 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node5454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5455 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def node5455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5456 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def node5456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node5457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5463 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5466 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def node5466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5473 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5474 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5475 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def node5475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node5477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node5480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node5481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node5483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5484 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node5484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5485 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node5485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5486 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5487 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def node5487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def node5488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node5489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node5490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5491 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def node5491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5492 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def node5492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5493 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def node5493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5494 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def node5494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5495 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def node5495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5496 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1]]
def node5496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node5498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5499 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node5499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node5500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5501 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def node5501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]

def raw10000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw10001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10002step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10007step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw10013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw10017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10017step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10023step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw10027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw10027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw10028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw10028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw10028step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw10028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10032step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10037step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10037step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10037step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10037step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10037step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10038step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10041step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10041step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10042step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10042step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw10047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10047step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10047step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10047step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10047step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw10050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw10050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw10050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw10053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw10054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw10055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw10057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw10058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw10058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw10058step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw10064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10065 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]
def raw10065Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw10065step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw10065step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10065step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw10078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw10078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10085step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10085step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10085step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10086step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10087step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10087step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10087step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10087step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10088step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw10089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10090step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10093step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10094step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10096step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10097step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10098step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10099step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10100step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10106step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10111step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes83
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5312 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def node5312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node5313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node5314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node5315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node5316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node5317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node5318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node5319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node5320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node5322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5327 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node5327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node5329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5330 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node5330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5331 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node5332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node5333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node5334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node5335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node5336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node5337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node5338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node5339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node5340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node5341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node5342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node5343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node5344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node5345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node5347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node5348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node5349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node5350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node5351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node5353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node5354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node5355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node5356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node5357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node5358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node5359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node5361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node5362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node5363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node5364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node5365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node5366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node5367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node5368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node5369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node5370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5371 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def node5371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node5372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node5373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node5374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def node5375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node5375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw10113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw10118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw10118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw10119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10131step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10136step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10142step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw10143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw10144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw10144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10145 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10145step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10146 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10146step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10147 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10147step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10148step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10148step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10149 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10149step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10150 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10150step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw10151step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10151step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10152 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10152step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10153 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10153step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10154step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10154step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10155 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10155step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10156step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10156step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10156step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10157step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10157step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10158 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10158step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10159step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10160 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10161 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10162 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10169 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10170 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10171 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10172 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10173 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10179 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10182 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10183 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10187step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw10192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw10197step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw10197step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw10197step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw10219step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10219step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10219step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10219step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10219step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw10236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw10237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw10237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10238step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10238step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10239step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1025Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1025step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1026 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1026step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1028Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1029 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1029step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1030 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1031 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1031Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw1031step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw1031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw1031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1032step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1034Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1035step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1037Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1038step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1040Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1041 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1041step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1042 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1043 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1043Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw1043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1044 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1044step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1045 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10240step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10240step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10240step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10241step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10241step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10241step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10241step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10245step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10249step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10253step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10254step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10258step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw10259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10259step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw10259step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10260step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10263step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10263step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10264step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10264step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10264step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10265step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10268step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10269step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10270step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10275step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10279step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10280step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10280step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10280step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10282step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10283step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw10283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10284step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10284step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10284step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10284step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw10285step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10285step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw10285step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10286step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10287step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw10288step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw10288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10289step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10289step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw10289step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10290step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10291step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10292step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -2, 1], ![1, 2, -3]]
def raw10293step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10293step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10293step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10293step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10293step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10294step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10294step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10297step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10297step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10297step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10298step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10298step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10301step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw10302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -2, 1], ![1, 2, -3]]
def raw10305step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10305step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10305step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10305step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10306step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw10306step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10306step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw10306step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10306step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw10306step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10308step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10308step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10308step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw10309step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10309step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw10309step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -3, 1], ![1, 2, -3]]
def raw10310step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -3, 1], ![1, 2, -3]]
def raw10310step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10310step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10310step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10310step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw10310step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10311step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10311step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10311step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10311step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw10311step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10312step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10312step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10313step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10313step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10314step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10314step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw10315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10315step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10315step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10315step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10315step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw10316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10316step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw10316step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10317step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10317step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10318step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10320step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10320step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10321step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10321step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10321step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10322step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10322step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10323step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10325step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10325step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10325step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10326step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10326step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw10329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10329step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10329step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 2, -2], ![2, -3, 1]]
def raw10330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10330step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![1, -2, 1]]
def raw10331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10331step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10331step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, 0, -2], ![2, -3, 1]]
def raw10332step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10332step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10332step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10332step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10332step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10333step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10334step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10334step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw10335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10335step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10335step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw10336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, 0, -2], ![1, -2, 1]]
def raw10336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10336step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10336step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10336step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10336step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw10337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10337step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw10337step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10337step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw10337step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10338step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10338step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10339step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -4, 1]]
def raw10340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10340step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10340step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw10340step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -4, 1]]
def raw10341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![3, -4, 1]]
def raw10341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10341step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10341step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10341step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw10341step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10345step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10345step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10345step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10345step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10346step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10346step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10346step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10346step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10346step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10346step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw10374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10384step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10390step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10391step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10391step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10392step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw10394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw10397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw10398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw10399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw10400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw10400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw10401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10403step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10404step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10404step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10405step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10405step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10405step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10406step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10407step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10409step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10410step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10410step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10410step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10411step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10411step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10412step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10413step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10414step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10418step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10418step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10419step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10419step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10420step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10420step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10420step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10420step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10421step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10421step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10421step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10421step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10421step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10422step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw10422step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10422step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10422step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10422step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10424step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10424step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10424step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw10425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10425step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10425step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10425step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10426step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10426step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10426step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10426step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10427step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw10427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10427step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10427step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10427step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10428step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10428step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10428step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10429step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw10430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw10431step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10431step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw10431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10431step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw10431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw10437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10438 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw10438step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10438step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10438step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw10446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw10448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw10449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10451step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10451step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10452step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10452step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw10453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10454step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10456step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10458step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_ExtraNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node5502 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def node5502Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node5503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5504 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node5504Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def node5505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def node5506Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5507 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def node5507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node5508Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node5509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node5509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node512Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node513Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node514Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node515Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node516 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def node516Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node517Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node518Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node519Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node520Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node521Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node522Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node523 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node523Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def node524Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def node525Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node526Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node527 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def node527Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node528 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def node528Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def node529Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node530 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def node530Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def node531Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node532Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def node533Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 0, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node536 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node540 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node542 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node544 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node545 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node546 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node547 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node549 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def node549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node551 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node552 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node553 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node554 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node555 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node556 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node557 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node558 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node559 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node560 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node561 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node562 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node563 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node564 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def node564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node565 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def node565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node566 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def node566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node570 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def node570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node573 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def node574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node575 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node576 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node579 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node581 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node582 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node583 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node584 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node585 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node586 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node587 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node588 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node589 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node590 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node591 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def node591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node593 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node594 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node595 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node596 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def node596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node598 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node601 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node602 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node603 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node604 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node605 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node606 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node607 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node608 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node609 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def node609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node610 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node611 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node612 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node613 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node614 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node615 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def node615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node617 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def node617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node618 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def node618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node619 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def node619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node620 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def node620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node621 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def node621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node622 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def node622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node627 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node628 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def node628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node630 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node631 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node633 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def node633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node634 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def node634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node635 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def node635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node636 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node639 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def node639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


