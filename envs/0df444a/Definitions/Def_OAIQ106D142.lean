-- Prove2me | Definitions.Def_OAIQ106D142
-- name    : OAIQ106D142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:08:12.561811+00:00
-- url     : https://prove2.me/theorems/3a10fd23-2a36-4afe-bea4-a3f33938c988
-- title:
--   Definitions bundle OAIQ106D142 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 654 declarations of OpenAI's Lean: 653 definitions and 1 inductive type or structure. The definitions and types are `OAI.MUB6.Certificate.GramAssembly.Block1.node431`, `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial`, `OAI.MUB6.Certificate.GramAssembly.Block1.rows`, `OAI.MUB6.Certificate.GramAssembly.Block2.polynomial`, `OAI.MUB6.Certificate.GramAssembly.Block2.rows`, `OAI.MUB6.Certificate.GramAssembly.Block3.entries`, `OAI.MUB6.Certificate.GramAssembly.Block3.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block3.entryRows`, `OAI.MUB6.Certificate.GramAssembly.Block3.node711`, `OAI.MUB6.Certificate.GramAssembly.Block3.node719`, `OAI.MUB6.Certificate.GramAssembly.Block3.node725`, `OAI.MUB6.Certificate.GramAssembly.Block3.node726`, `OAI.MUB6.Certificate.GramAssembly.Block3.rows`, `OAI.MUB6.Certificate.GramAssembly.Block4.entries`, `OAI.MUB6.Certificate.GramAssembly.Block4.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block4.entryRows`, `OAI.MUB6.Certificate.GramAssembly.Block4.node465`, `OAI.MUB6.Certificate.GramAssembly.Block4.node469`, `OAI.MUB6.Certificate.GramAssembly.Block4.node480`, `OAI.MUB6.Certificate.GramAssembly.Block4.rows`, `OAI.MUB6.Certificate.GramAssembly.Block5.entries`, `OAI.MUB6.Certificate.GramAssembly.Block5.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block5.entryRow1`, `OAI.MUB6.Certificate.GramAssembly.Block5.entryRows`, `OAI.MUB6.Certificate.GramAssembly.Block5.node142`, `OAI.MUB6.Certificate.GramAssembly.Block5.polynomial`, `OAI.MUB6.Certificate.GramAssembly.Block5.rows`, `OAI.MUB6.Certificate.GramAssembly.combined4`, `OAI.MUB6.Certificate.GramAssembly.polynomial`, `OAI.MUB6.Certificate.GramEntries.Block0.rows0_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows1_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows1_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows2_2`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_0`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_1`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_2`, `OAI.MUB6.Certificate.GramEntries.Block0.rows3_3`, `OAI.MUB6.Certificate.GramEntries.Block0.rows4_0` and 614 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_GramAssembly_Block1`, `MutuallyUnbiased_GramAssembly_Block1Part13`, `MutuallyUnbiased_GramAssembly_Block2`, `MutuallyUnbiased_GramAssembly_Block3`, `MutuallyUnbiased_GramAssembly_Block3Data`, `MutuallyUnbiased_GramAssembly_Block3Part22`, `MutuallyUnbiased_GramAssembly_Block4`, `MutuallyUnbiased_GramAssembly_Block4Data`, `MutuallyUnbiased_GramAssembly_Block4Part14`, `MutuallyUnbiased_GramAssembly_Block4Part15`, `MutuallyUnbiased_GramAssembly_Block5`, `MutuallyUnbiased_GramAssembly_Block5Data`, `MutuallyUnbiased_GramAssembly_Block5Part4`, `MutuallyUnbiased_GramAssembly_Combined`, `MutuallyUnbiased_GramEntries_Block0Row0`, `MutuallyUnbiased_GramEntries_Block0Row1`, `MutuallyUnbiased_GramEntries_Block0Row2`, `MutuallyUnbiased_GramEntries_Block0Row3`, `MutuallyUnbiased_GramEntries_Block0Row4`, `MutuallyUnbiased_GramEntries_Block1Data`, `MutuallyUnbiased_GramEntries_Block1Row0`, `MutuallyUnbiased_GramEntries_Block1Row1`, `MutuallyUnbiased_GramEntries_Block1Row10`, `MutuallyUnbiased_GramEntries_Block1Row11`, `MutuallyUnbiased_GramEntries_Block1Row12`, `MutuallyUnbiased_GramEntries_Block1Row13`, `MutuallyUnbiased_GramEntries_Block1Row14`, `MutuallyUnbiased_GramEntries_Block1Row15`, `MutuallyUnbiased_GramEntries_Block1Row16`, `MutuallyUnbiased_GramEntries_Block1Row17`, `MutuallyUnbiased_GramEntries_Block1Row18`, `MutuallyUnbiased_GramEntries_Block1Row19`, `MutuallyUnbiased_GramEntries_Block1Row2`, `MutuallyUnbiased_GramEntries_Block1Row20`, `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramFunctions_Basic`, `MutuallyUnbiased_GramFunctions_Block0`, `MutuallyUnbiased_GramFunctions_Block1`, `MutuallyUnbiased_GramRows_Block17`, `MutuallyUnbiased_GramRows_Block19`, `MutuallyUnbiased_GramRows_Block32`, `MutuallyUnbiased_GramRows_Block35`, `MutuallyUnbiased_GramRows_Block36`, `MutuallyUnbiased_GramRows_Block37`, `MutuallyUnbiased_GramRows_Block46`, `MutuallyUnbiased_GramRows_Block48`, `MutuallyUnbiased_GramRows_Block49`, `MutuallyUnbiased_GramRows_Block52`, `MutuallyUnbiased_GramRows_Block53`, `MutuallyUnbiased_GramRows_Block55`, `MutuallyUnbiased_GramRows_Block56`, `MutuallyUnbiased_GramRows_Block58`, `MutuallyUnbiased_GramRows_Block61`, `MutuallyUnbiased_GramRows_Block62`.
--
--   **Imports.** It imports the bundles `OAIQ106D069`, `OAIQ106D070`, `OAIQ106D071`, `OAIQ106D072`, `OAIQ106D073`, `OAIQ106D074`, `OAIQ106D075`, `OAIQ106D076`, `OAIQ106D077`, `OAIQ106D078`, `OAIQ106D079`, `OAIQ106D080`, `OAIQ106D081`, `OAIQ106D082`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D090` and `OAIQ106D092` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D198`, `OAIQ106D199` and `OAIQ106D200`; the statements `OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_10`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9`, `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval` and `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval`; the proofs of `OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_10`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_26`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8`, `OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9`, `OAI.MUB6.Certificate.GramAssembly.Block3.rows_eval` and `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D069
import Definitions.Def_OAIQ106D070
import Definitions.Def_OAIQ106D071
import Definitions.Def_OAIQ106D072
import Definitions.Def_OAIQ106D073
import Definitions.Def_OAIQ106D074
import Definitions.Def_OAIQ106D075
import Definitions.Def_OAIQ106D076
import Definitions.Def_OAIQ106D077
import Definitions.Def_OAIQ106D078
import Definitions.Def_OAIQ106D079
import Definitions.Def_OAIQ106D080
import Definitions.Def_OAIQ106D081
import Definitions.Def_OAIQ106D082
import Definitions.Def_OAIQ106D083
import Definitions.Def_OAIQ106D084
import Definitions.Def_OAIQ106D085
import Definitions.Def_OAIQ106D086
import Definitions.Def_OAIQ106D087
import Definitions.Def_OAIQ106D090
import Definitions.Def_OAIQ106D092

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions

open scoped BigOperators

structure LinearForm where
  size : ℕ
  terms : Fin size → TaggedTerm
  deriving Inhabited

end MUB6.Certificate.GramFunctions

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node431 : Integer.Sparse (Fin 2886) := (((node431part0 ++ node431part1) ++ (node431part2 ++ node431part3)) ++ ((node431part4 ++ node431part5) ++ (node431part6 ++ node431part7)))

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

def rows (i : Fin 21) : Integer.Sparse (Fin 2886) :=
  (#[node19, node39, node59, node79, node99, node119, node139, node159, node179, node199, node219, node239, node259, node279, node299, node319, node339, node359, node379, node399, node419]).getD i.val []

def polynomial : Integer.Sparse (Fin 2886) := node439

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block2

open scoped BigOperators

def rows (i : Fin 11) : Integer.Sparse (Fin 2886) :=
  (#[node9, node19, node29, node39, node49, node59, node69, node79, node89, node99, node109]).getD i.val []

def polynomial : Integer.Sparse (Fin 2886) := node119

end MUB6.Certificate.GramAssembly.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11, entry_0_12, entry_0_13, entry_0_14, entry_0_15, entry_0_16, entry_0_17, entry_0_18, entry_0_19, entry_0_20, entry_0_21, entry_0_22, entry_0_23, entry_0_24, entry_0_25, entry_0_26]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11, entryRow12, entryRow13, entryRow14, entryRow15, entryRow16, entryRow17, entryRow18, entryRow19, entryRow20, entryRow21, entryRow22, entryRow23, entryRow24, entryRow25, entryRow26]

def entries (i j : Fin 27) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node711 : Integer.Sparse (Fin 2886) := (((node711part0 ++ node711part1) ++ (node711part2 ++ (node711part3 ++ node711part4))) ++ ((node711part5 ++ node711part6) ++ (node711part7 ++ (node711part8 ++ node711part9))))

def node719 : Integer.Sparse (Fin 2886) := (((node719part0 ++ (node719part1 ++ node719part2)) ++ ((node719part3 ++ node719part4) ++ (node719part5 ++ node719part6))) ++ (((node719part7 ++ node719part8) ++ (node719part9 ++ node719part10)) ++ ((node719part11 ++ node719part12) ++ (node719part13 ++ node719part14))))

def node725 : Integer.Sparse (Fin 2886) := (((node725part0 ++ (node725part1 ++ node725part2)) ++ (node725part3 ++ (node725part4 ++ node725part5))) ++ ((node725part6 ++ (node725part7 ++ node725part8)) ++ ((node725part9 ++ node725part10) ++ (node725part11 ++ node725part12))))

def node726 : Integer.Sparse (Fin 2886) := ((((node726part0 ++ node726part1) ++ (node726part2 ++ (node726part3 ++ node726part4))) ++ ((node726part5 ++ (node726part6 ++ node726part7)) ++ (node726part8 ++ (node726part9 ++ node726part10)))) ++ (((node726part11 ++ node726part12) ++ (node726part13 ++ (node726part14 ++ node726part15))) ++ ((node726part16 ++ (node726part17 ++ node726part18)) ++ (node726part19 ++ (node726part20 ++ node726part21)))))

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

def rows (i : Fin 27) : Integer.Sparse (Fin 2886) :=
  (#[node25, node51, node77, node103, node129, node155, node181, node207, node233, node259, node285, node311, node337, node363, node389, node415, node441, node467, node493, node519, node545, node571, node597, node623, node649, node675, node701]).getD i.val []

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11, entry_0_12, entry_0_13, entry_0_14, entry_0_15, entry_0_16, entry_0_17, entry_0_18, entry_0_19, entry_0_20, entry_0_21]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11, entryRow12, entryRow13, entryRow14, entryRow15, entryRow16, entryRow17, entryRow18, entryRow19, entryRow20, entryRow21]

def entries (i j : Fin 22) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node465 : Integer.Sparse (Fin 2886) := (((node465part0 ++ node465part1) ++ (node465part2 ++ (node465part3 ++ node465part4))) ++ ((node465part5 ++ node465part6) ++ (node465part7 ++ (node465part8 ++ node465part9))))

def node469 : Integer.Sparse (Fin 2886) := (((node469part0 ++ node469part1) ++ (node469part2 ++ node469part3)) ++ ((node469part4 ++ node469part5) ++ (node469part6 ++ node469part7)))

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

def node480 : Integer.Sparse (Fin 2886) := (((node480part0 ++ (node480part1 ++ node480part2)) ++ (node480part3 ++ (node480part4 ++ node480part5))) ++ ((node480part6 ++ (node480part7 ++ node480part8)) ++ ((node480part9 ++ node480part10) ++ (node480part11 ++ node480part12))))

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

def rows (i : Fin 22) : Integer.Sparse (Fin 2886) :=
  (#[node20, node41, node62, node83, node104, node125, node146, node167, node188, node209, node230, node251, node272, node293, node314, node335, node356, node377, node398, node419, node440, node461]).getD i.val []

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11]

def entryRow1 : Array (Integer.Sparse (Fin 2886)) := #[entry_1_0, entry_1_1, entry_1_2, entry_1_3, entry_1_4, entry_1_5, entry_1_6, entry_1_7, entry_1_8, entry_1_9, entry_1_10, entry_1_11]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11]

def entries (i j : Fin 12) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

def node142 : Integer.Sparse (Fin 2886) := (((node142part0 ++ node142part1) ++ (node142part2 ++ (node142part3 ++ node142part4))) ++ ((node142part5 ++ node142part6) ++ (node142part7 ++ (node142part8 ++ node142part9))))

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

open scoped BigOperators

def rows (i : Fin 12) : Integer.Sparse (Fin 2886) :=
  (#[node10, node21, node32, node43, node54, node65, node76, node87, node98, node109, node120, node131]).getD i.val []

def polynomial : Integer.Sparse (Fin 2886) := node142

end MUB6.Certificate.GramAssembly.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Combined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly

def combined4 : Integer.Sparse (Fin 2886) := (((((combined4part0 ++ combined4part1) ++ (combined4part2 ++ (combined4part3 ++ combined4part4))) ++ ((combined4part5 ++ (combined4part6 ++ combined4part7)) ++ (combined4part8 ++ (combined4part9 ++ combined4part10)))) ++ (((combined4part11 ++ (combined4part12 ++ combined4part13)) ++ (combined4part14 ++ (combined4part15 ++ combined4part16))) ++ ((combined4part17 ++ (combined4part18 ++ combined4part19)) ++ (combined4part20 ++ (combined4part21 ++ combined4part22))))) ++ ((((combined4part23 ++ combined4part24) ++ (combined4part25 ++ (combined4part26 ++ combined4part27))) ++ ((combined4part28 ++ (combined4part29 ++ combined4part30)) ++ (combined4part31 ++ (combined4part32 ++ combined4part33)))) ++ (((combined4part34 ++ (combined4part35 ++ combined4part36)) ++ (combined4part37 ++ (combined4part38 ++ combined4part39))) ++ ((combined4part40 ++ (combined4part41 ++ combined4part42)) ++ (combined4part43 ++ (combined4part44 ++ combined4part45))))))

def polynomial : Integer.Sparse (Fin 2886) := combined4

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block0

def terms0 : Array TaggedTerm := #[
  ⟨0, ![2, -2, -1, 0, 0, 1], -1⟩,
  ⟨0, ![2, -2, -1, 0, 1, 0], -1⟩,
  ⟨0, ![2, -2, -1, 1, 0, 0], 2⟩,
  ⟨0, ![2, -2, 0, -1, 0, 1], 1⟩,
  ⟨0, ![2, -2, 0, -1, 1, 0], 1⟩,
  ⟨0, ![2, -2, 0, 1, -1, 0], -1⟩,
  ⟨0, ![2, -2, 0, 1, 0, -1], -1⟩,
  ⟨0, ![2, -2, 1, -1, 0, 0], -2⟩,
  ⟨0, ![2, -2, 1, 0, -1, 0], 1⟩,
  ⟨0, ![2, -2, 1, 0, 0, -1], 1⟩,
  ⟨0, ![2, -1, -2, 0, 0, 1], 1⟩,
  ⟨0, ![2, -1, -2, 0, 1, 0], 1⟩,
  ⟨0, ![2, -1, -2, 1, 0, 0], -2⟩,
  ⟨0, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨0, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨0, ![2, -1, 0, 1, -2, 0], 1⟩,
  ⟨0, ![2, -1, 0, 1, 0, -2], 1⟩,
  ⟨0, ![2, -1, 1, -2, 0, 0], 2⟩,
  ⟨0, ![2, -1, 1, 0, -2, 0], -1⟩,
  ⟨0, ![2, -1, 1, 0, 0, -2], -1⟩,
  ⟨0, ![2, 0, -2, -1, 0, 1], -1⟩,
  ⟨0, ![2, 0, -2, -1, 1, 0], -1⟩,
  ⟨0, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨0, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨0, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨0, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨0, ![2, 0, -1, 1, -2, 0], -1⟩,
  ⟨0, ![2, 0, -1, 1, 0, -2], -1⟩,
  ⟨0, ![2, 0, 1, -2, -1, 0], -1⟩,
  ⟨0, ![2, 0, 1, -2, 0, -1], -1⟩,
  ⟨0, ![2, 0, 1, -1, -2, 0], 1⟩,
  ⟨0, ![2, 0, 1, -1, 0, -2], 1⟩,
  ⟨0, ![2, 1, -2, -1, 0, 0], 2⟩,
  ⟨0, ![2, 1, -2, 0, -1, 0], -1⟩,
  ⟨0, ![2, 1, -2, 0, 0, -1], -1⟩,
  ⟨0, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨0, ![2, 1, -1, 0, -2, 0], 1⟩,
  ⟨0, ![2, 1, -1, 0, 0, -2], 1⟩,
  ⟨0, ![2, 1, 0, -2, -1, 0], 1⟩,
  ⟨0, ![2, 1, 0, -2, 0, -1], 1⟩,
  ⟨0, ![2, 1, 0, -1, -2, 0], -1⟩,
  ⟨0, ![2, 1, 0, -1, 0, -2], -1⟩
]

def form0 : LinearForm := ⟨42, fun k => terms0[k.val]!⟩

def terms1 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 1, 1], -2⟩,
  ⟨1, ![1, -2, -1, 1, 0, 1], 1⟩,
  ⟨1, ![1, -2, -1, 1, 1, 0], 1⟩,
  ⟨1, ![1, -2, 0, -1, 1, 1], 2⟩,
  ⟨1, ![1, -2, 0, 1, -1, 1], -1⟩,
  ⟨1, ![1, -2, 0, 1, 1, -1], -1⟩,
  ⟨1, ![1, -2, 1, -1, 0, 1], -1⟩,
  ⟨1, ![1, -2, 1, -1, 1, 0], -1⟩,
  ⟨1, ![1, -2, 1, 0, -1, 1], 1⟩,
  ⟨1, ![1, -2, 1, 0, 1, -1], 1⟩,
  ⟨1, ![1, -1, -2, 0, 1, 1], 2⟩,
  ⟨1, ![1, -1, -2, 1, 0, 1], -1⟩,
  ⟨1, ![1, -1, -2, 1, 1, 0], -1⟩,
  ⟨1, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], 1⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], 1⟩,
  ⟨1, ![1, -1, 1, -2, 0, 1], 1⟩,
  ⟨1, ![1, -1, 1, -2, 1, 0], 1⟩,
  ⟨1, ![1, -1, 1, 0, -2, 1], -1⟩,
  ⟨1, ![1, -1, 1, 0, 1, -2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 1, 1], -2⟩,
  ⟨1, ![1, 0, -2, 1, -1, 1], 1⟩,
  ⟨1, ![1, 0, -2, 1, 1, -1], 1⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], -1⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], 1⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], 1⟩,
  ⟨1, ![1, 1, -2, -1, 0, 1], 1⟩,
  ⟨1, ![1, 1, -2, -1, 1, 0], 1⟩,
  ⟨1, ![1, 1, -2, 0, -1, 1], -1⟩,
  ⟨1, ![1, 1, -2, 0, 1, -1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨1, ![1, 1, -1, 0, -2, 1], 1⟩,
  ⟨1, ![1, 1, -1, 0, 1, -2], 1⟩,
  ⟨1, ![1, 1, 0, -2, -1, 1], 1⟩,
  ⟨1, ![1, 1, 0, -2, 1, -1], 1⟩,
  ⟨1, ![1, 1, 0, -1, -2, 1], -1⟩,
  ⟨1, ![1, 1, 0, -1, 1, -2], -1⟩
]

def form1 : LinearForm := ⟨42, fun k => terms1[k.val]!⟩

def terms2 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], -1⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], -1⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], 2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], 1⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], 1⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], -1⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], -1⟩,
  ⟨1, ![1, -2, 2, -1, 0, 0], -2⟩,
  ⟨1, ![1, -2, 2, 0, -1, 0], 1⟩,
  ⟨1, ![1, -2, 2, 0, 0, -1], 1⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 1⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 1⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], -2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], 1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], 1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], -1⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], 1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], 1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], -1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], -1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], -1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], 1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], 1⟩,
  ⟨1, ![1, 2, -2, -1, 0, 0], 2⟩,
  ⟨1, ![1, 2, -2, 0, -1, 0], -1⟩,
  ⟨1, ![1, 2, -2, 0, 0, -1], -1⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], 1⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], 1⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], 1⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], 1⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], -1⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], -1⟩
]

def form2 : LinearForm := ⟨42, fun k => terms2[k.val]!⟩

def terms3 : Array TaggedTerm := #[
  ⟨0, ![1, -2, -1, 0, 1, 1], -2⟩,
  ⟨0, ![1, -2, -1, 1, 0, 1], 1⟩,
  ⟨0, ![1, -2, -1, 1, 1, 0], 1⟩,
  ⟨0, ![1, -2, 0, -1, 1, 1], 2⟩,
  ⟨0, ![1, -2, 0, 1, -1, 1], -1⟩,
  ⟨0, ![1, -2, 0, 1, 1, -1], -1⟩,
  ⟨0, ![1, -2, 1, -1, 0, 1], -1⟩,
  ⟨0, ![1, -2, 1, -1, 1, 0], -1⟩,
  ⟨0, ![1, -2, 1, 0, -1, 1], 1⟩,
  ⟨0, ![1, -2, 1, 0, 1, -1], 1⟩,
  ⟨0, ![1, -1, -2, 0, 1, 1], 2⟩,
  ⟨0, ![1, -1, -2, 1, 0, 1], -1⟩,
  ⟨0, ![1, -1, -2, 1, 1, 0], -1⟩,
  ⟨0, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨0, ![1, -1, 0, 1, -2, 1], 1⟩,
  ⟨0, ![1, -1, 0, 1, 1, -2], 1⟩,
  ⟨0, ![1, -1, 1, -2, 0, 1], 1⟩,
  ⟨0, ![1, -1, 1, -2, 1, 0], 1⟩,
  ⟨0, ![1, -1, 1, 0, -2, 1], -1⟩,
  ⟨0, ![1, -1, 1, 0, 1, -2], -1⟩,
  ⟨0, ![1, 0, -2, -1, 1, 1], -2⟩,
  ⟨0, ![1, 0, -2, 1, -1, 1], 1⟩,
  ⟨0, ![1, 0, -2, 1, 1, -1], 1⟩,
  ⟨0, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨0, ![1, 0, -1, 1, -2, 1], -1⟩,
  ⟨0, ![1, 0, -1, 1, 1, -2], -1⟩,
  ⟨0, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨0, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨0, ![1, 0, 1, -1, -2, 1], 1⟩,
  ⟨0, ![1, 0, 1, -1, 1, -2], 1⟩,
  ⟨0, ![1, 1, -2, -1, 0, 1], 1⟩,
  ⟨0, ![1, 1, -2, -1, 1, 0], 1⟩,
  ⟨0, ![1, 1, -2, 0, -1, 1], -1⟩,
  ⟨0, ![1, 1, -2, 0, 1, -1], -1⟩,
  ⟨0, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨0, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨0, ![1, 1, -1, 0, -2, 1], 1⟩,
  ⟨0, ![1, 1, -1, 0, 1, -2], 1⟩,
  ⟨0, ![1, 1, 0, -2, -1, 1], 1⟩,
  ⟨0, ![1, 1, 0, -2, 1, -1], 1⟩,
  ⟨0, ![1, 1, 0, -1, -2, 1], -1⟩,
  ⟨0, ![1, 1, 0, -1, 1, -2], -1⟩
]

def form3 : LinearForm := ⟨42, fun k => terms3[k.val]!⟩

def terms4 : Array TaggedTerm := #[
  ⟨1, ![2, -2, -1, 0, 0, 1], -1⟩,
  ⟨1, ![2, -2, -1, 0, 1, 0], -1⟩,
  ⟨1, ![2, -2, -1, 1, 0, 0], 2⟩,
  ⟨1, ![2, -2, 0, -1, 0, 1], 1⟩,
  ⟨1, ![2, -2, 0, -1, 1, 0], 1⟩,
  ⟨1, ![2, -2, 0, 1, -1, 0], -1⟩,
  ⟨1, ![2, -2, 0, 1, 0, -1], -1⟩,
  ⟨1, ![2, -2, 1, -1, 0, 0], -2⟩,
  ⟨1, ![2, -2, 1, 0, -1, 0], 1⟩,
  ⟨1, ![2, -2, 1, 0, 0, -1], 1⟩,
  ⟨1, ![2, -1, -2, 0, 0, 1], 1⟩,
  ⟨1, ![2, -1, -2, 0, 1, 0], 1⟩,
  ⟨1, ![2, -1, -2, 1, 0, 0], -2⟩,
  ⟨1, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], 1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], 1⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], 2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], -1⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], -1⟩,
  ⟨1, ![2, 0, -2, -1, 0, 1], -1⟩,
  ⟨1, ![2, 0, -2, -1, 1, 0], -1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], 1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], -1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], -1⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], -1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], -1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], 1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], 1⟩,
  ⟨1, ![2, 1, -2, -1, 0, 0], 2⟩,
  ⟨1, ![2, 1, -2, 0, -1, 0], -1⟩,
  ⟨1, ![2, 1, -2, 0, 0, -1], -1⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], 1⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], 1⟩,
  ⟨1, ![2, 1, 0, -2, -1, 0], 1⟩,
  ⟨1, ![2, 1, 0, -2, 0, -1], 1⟩,
  ⟨1, ![2, 1, 0, -1, -2, 0], -1⟩,
  ⟨1, ![2, 1, 0, -1, 0, -2], -1⟩
]

def form4 : LinearForm := ⟨42, fun k => terms4[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block0.form0.size → Integer.Sparse Key := ![row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23, row24, row25, row26, row27, row28, row29, row30, row31, row32, row33, row34, row35, row36, row37, row38, row39, row40, row41]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row42, row43, row44, row45, row46, row47, row48, row49, row50, row51, row52, row53, row54, row55, row56, row57, row58, row59, row60, row61, row62, row63, row64, row65, row66, row67, row68, row69, row70, row71, row72, row73, row74, row75, row76, row77, row78, row79, row80, row81, row82, row83]

def rows1_1 : Fin GramFunctions.Block0.form1.size → Integer.Sparse Key := ![row84, row85, row86, row87, row88, row89, row90, row91, row92, row93, row94, row95, row96, row97, row98, row99, row100, row101, row102, row103, row104, row105, row106, row107, row108, row109, row110, row111, row112, row113, row114, row115, row116, row117, row118, row119, row120, row121, row122, row123, row124, row125]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row126, row127, row128, row129, row130, row131, row132, row133, row134, row135, row136, row137, row138, row139, row140, row141, row142, row143, row144, row145, row146, row147, row148, row149, row150, row151, row152, row153, row154, row155, row156, row157, row158, row159, row160, row161, row162, row163, row164, row165, row166, row167]

def rows2_1 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row168, row169, row170, row171, row172, row173, row174, row175, row176, row177, row178, row179, row180, row181, row182, row183, row184, row185, row186, row187, row188, row189, row190, row191, row192, row193, row194, row195, row196, row197, row198, row199, row200, row201, row202, row203, row204, row205, row206, row207, row208, row209]

def rows2_2 : Fin GramFunctions.Block0.form2.size → Integer.Sparse Key := ![row210, row211, row212, row213, row214, row215, row216, row217, row218, row219, row220, row221, row222, row223, row224, row225, row226, row227, row228, row229, row230, row231, row232, row233, row234, row235, row236, row237, row238, row239, row240, row241, row242, row243, row244, row245, row246, row247, row248, row249, row250, row251]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows3_0 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row252, row253, row254, row255, row256, row257, row258, row259, row260, row261, row262, row263, row264, row265, row266, row267, row268, row269, row270, row271, row272, row273, row274, row275, row276, row277, row278, row279, row280, row281, row282, row283, row284, row285, row286, row287, row288, row289, row290, row291, row292, row293]

def rows3_1 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row294, row295, row296, row297, row298, row299, row300, row301, row302, row303, row304, row305, row306, row307, row308, row309, row310, row311, row312, row313, row314, row315, row316, row317, row318, row319, row320, row321, row322, row323, row324, row325, row326, row327, row328, row329, row330, row331, row332, row333, row334, row335]

def rows3_2 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row336, row337, row338, row339, row340, row341, row342, row343, row344, row345, row346, row347, row348, row349, row350, row351, row352, row353, row354, row355, row356, row357, row358, row359, row360, row361, row362, row363, row364, row365, row366, row367, row368, row369, row370, row371, row372, row373, row374, row375, row376, row377]

def rows3_3 : Fin GramFunctions.Block0.form3.size → Integer.Sparse Key := ![row378, row379, row380, row381, row382, row383, row384, row385, row386, row387, row388, row389, row390, row391, row392, row393, row394, row395, row396, row397, row398, row399, row400, row401, row402, row403, row404, row405, row406, row407, row408, row409, row410, row411, row412, row413, row414, row415, row416, row417, row418, row419]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block1

def terms0 : Array TaggedTerm := #[
  ⟨1, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], -2⟩,
  ⟨1, ![1, -1, 1, -2, 0, 1], 1⟩,
  ⟨1, ![1, -1, 1, -2, 1, 0], 1⟩,
  ⟨1, ![1, -1, 1, 0, -2, 1], 1⟩,
  ⟨1, ![1, -1, 1, 0, 1, -2], 1⟩,
  ⟨1, ![1, -1, 1, 1, -2, 0], 1⟩,
  ⟨1, ![1, -1, 1, 1, 0, -2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], 2⟩,
  ⟨1, ![1, 0, 1, -2, -1, 1], -1⟩,
  ⟨1, ![1, 0, 1, -2, 1, -1], -1⟩,
  ⟨1, ![1, 0, 1, -1, -2, 1], -1⟩,
  ⟨1, ![1, 0, 1, -1, 1, -2], -1⟩,
  ⟨1, ![1, 0, 1, 1, -2, -1], -1⟩,
  ⟨1, ![1, 0, 1, 1, -1, -2], -1⟩,
  ⟨1, ![1, 1, -1, -2, 0, 1], -1⟩,
  ⟨1, ![1, 1, -1, -2, 1, 0], -1⟩,
  ⟨1, ![1, 1, -1, 0, -2, 1], -1⟩,
  ⟨1, ![1, 1, -1, 0, 1, -2], -1⟩,
  ⟨1, ![1, 1, -1, 1, -2, 0], -1⟩,
  ⟨1, ![1, 1, -1, 1, 0, -2], -1⟩,
  ⟨1, ![1, 1, 0, -2, -1, 1], 1⟩,
  ⟨1, ![1, 1, 0, -2, 1, -1], 1⟩,
  ⟨1, ![1, 1, 0, -1, -2, 1], 1⟩,
  ⟨1, ![1, 1, 0, -1, 1, -2], 1⟩,
  ⟨1, ![1, 1, 0, 1, -2, -1], 1⟩,
  ⟨1, ![1, 1, 0, 1, -1, -2], 1⟩
]

def form0 : LinearForm := ⟨30, fun k => terms0[k.val]!⟩

def terms1 : Array TaggedTerm := #[
  ⟨0, ![3, -2, -1, 0, 0, 0], -6⟩,
  ⟨0, ![3, -2, 0, -1, 0, 0], 2⟩,
  ⟨0, ![3, -2, 0, 0, -1, 0], 2⟩,
  ⟨0, ![3, -2, 0, 0, 0, -1], 2⟩,
  ⟨0, ![3, -1, -2, 0, 0, 0], 6⟩,
  ⟨0, ![3, -1, 0, -2, 0, 0], -2⟩,
  ⟨0, ![3, -1, 0, 0, -2, 0], -2⟩,
  ⟨0, ![3, -1, 0, 0, 0, -2], -2⟩,
  ⟨0, ![3, 0, -2, -1, 0, 0], -2⟩,
  ⟨0, ![3, 0, -2, 0, -1, 0], -2⟩,
  ⟨0, ![3, 0, -2, 0, 0, -1], -2⟩,
  ⟨0, ![3, 0, -1, -2, 0, 0], 2⟩,
  ⟨0, ![3, 0, -1, 0, -2, 0], 2⟩,
  ⟨0, ![3, 0, -1, 0, 0, -2], 2⟩
]

def form1 : LinearForm := ⟨14, fun k => terms1[k.val]!⟩

def terms2 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 0, 2], -2⟩,
  ⟨1, ![1, -2, -1, 0, 2, 0], -2⟩,
  ⟨1, ![1, -2, -1, 2, 0, 0], -2⟩,
  ⟨1, ![1, -2, 0, -1, 0, 2], 1⟩,
  ⟨1, ![1, -2, 0, -1, 2, 0], 1⟩,
  ⟨1, ![1, -2, 0, 0, -1, 2], 1⟩,
  ⟨1, ![1, -2, 0, 0, 2, -1], 1⟩,
  ⟨1, ![1, -2, 0, 2, -1, 0], 1⟩,
  ⟨1, ![1, -2, 0, 2, 0, -1], 1⟩,
  ⟨1, ![1, -1, -2, 0, 0, 2], 2⟩,
  ⟨1, ![1, -1, -2, 0, 2, 0], 2⟩,
  ⟨1, ![1, -1, -2, 2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 0, 2], -1⟩,
  ⟨1, ![1, 0, -2, -1, 2, 0], -1⟩,
  ⟨1, ![1, 0, -2, 0, -1, 2], -1⟩,
  ⟨1, ![1, 0, -2, 0, 2, -1], -1⟩,
  ⟨1, ![1, 0, -2, 2, -1, 0], -1⟩,
  ⟨1, ![1, 0, -2, 2, 0, -1], -1⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 1⟩
]

def form2 : LinearForm := ⟨30, fun k => terms2[k.val]!⟩

def terms10 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 0, 2], -2⟩,
  ⟨1, ![1, -3, 0, 0, 2, 0], -2⟩,
  ⟨1, ![1, -3, 0, 2, 0, 0], -2⟩,
  ⟨1, ![1, -3, 2, 0, 0, 0], 6⟩,
  ⟨1, ![1, 0, -3, 0, 0, 2], 2⟩,
  ⟨1, ![1, 0, -3, 0, 2, 0], 2⟩,
  ⟨1, ![1, 0, -3, 2, 0, 0], 2⟩,
  ⟨1, ![1, 0, 2, -3, 0, 0], -2⟩,
  ⟨1, ![1, 0, 2, 0, -3, 0], -2⟩,
  ⟨1, ![1, 0, 2, 0, 0, -3], -2⟩,
  ⟨1, ![1, 2, -3, 0, 0, 0], -6⟩,
  ⟨1, ![1, 2, 0, -3, 0, 0], 2⟩,
  ⟨1, ![1, 2, 0, 0, -3, 0], 2⟩,
  ⟨1, ![1, 2, 0, 0, 0, -3], 2⟩
]

def form10 : LinearForm := ⟨14, fun k => terms10[k.val]!⟩

def terms11 : Array TaggedTerm := #[
  ⟨1, ![2, -3, 0, 0, 0, 1], -2⟩,
  ⟨1, ![2, -3, 0, 0, 1, 0], -2⟩,
  ⟨1, ![2, -3, 0, 1, 0, 0], -2⟩,
  ⟨1, ![2, -3, 1, 0, 0, 0], 6⟩,
  ⟨1, ![2, 0, -3, 0, 0, 1], 2⟩,
  ⟨1, ![2, 0, -3, 0, 1, 0], 2⟩,
  ⟨1, ![2, 0, -3, 1, 0, 0], 2⟩,
  ⟨1, ![2, 0, 1, -3, 0, 0], -2⟩,
  ⟨1, ![2, 0, 1, 0, -3, 0], -2⟩,
  ⟨1, ![2, 0, 1, 0, 0, -3], -2⟩,
  ⟨1, ![2, 1, -3, 0, 0, 0], -6⟩,
  ⟨1, ![2, 1, 0, -3, 0, 0], 2⟩,
  ⟨1, ![2, 1, 0, 0, -3, 0], 2⟩,
  ⟨1, ![2, 1, 0, 0, 0, -3], 2⟩
]

def form11 : LinearForm := ⟨14, fun k => terms11[k.val]!⟩

def terms12 : Array TaggedTerm := #[
  ⟨1, ![2, -2, -1, 0, 0, 1], -2⟩,
  ⟨1, ![2, -2, -1, 0, 1, 0], -2⟩,
  ⟨1, ![2, -2, -1, 1, 0, 0], -2⟩,
  ⟨1, ![2, -2, 0, -1, 0, 1], 1⟩,
  ⟨1, ![2, -2, 0, -1, 1, 0], 1⟩,
  ⟨1, ![2, -2, 0, 0, -1, 1], 1⟩,
  ⟨1, ![2, -2, 0, 0, 1, -1], 1⟩,
  ⟨1, ![2, -2, 0, 1, -1, 0], 1⟩,
  ⟨1, ![2, -2, 0, 1, 0, -1], 1⟩,
  ⟨1, ![2, -1, -2, 0, 0, 1], 2⟩,
  ⟨1, ![2, -1, -2, 0, 1, 0], 2⟩,
  ⟨1, ![2, -1, -2, 1, 0, 0], 2⟩,
  ⟨1, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], -1⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], -1⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], -1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], -1⟩,
  ⟨1, ![2, 0, -2, -1, 0, 1], -1⟩,
  ⟨1, ![2, 0, -2, -1, 1, 0], -1⟩,
  ⟨1, ![2, 0, -2, 0, -1, 1], -1⟩,
  ⟨1, ![2, 0, -2, 0, 1, -1], -1⟩,
  ⟨1, ![2, 0, -2, 1, -1, 0], -1⟩,
  ⟨1, ![2, 0, -2, 1, 0, -1], -1⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], 1⟩
]

def form12 : LinearForm := ⟨30, fun k => terms12[k.val]!⟩

def terms13 : Array TaggedTerm := #[
  ⟨0, ![-1, -1, 0, 0, 0, 2], -2⟩,
  ⟨0, ![-1, -1, 0, 0, 2, 0], -2⟩,
  ⟨0, ![-1, -1, 0, 2, 0, 0], -2⟩,
  ⟨0, ![-1, -1, 2, 0, 0, 0], 6⟩,
  ⟨0, ![-1, 0, -1, 0, 0, 2], 2⟩,
  ⟨0, ![-1, 0, -1, 0, 2, 0], 2⟩,
  ⟨0, ![-1, 0, -1, 2, 0, 0], 2⟩,
  ⟨0, ![-1, 0, 2, -1, 0, 0], -2⟩,
  ⟨0, ![-1, 0, 2, 0, -1, 0], -2⟩,
  ⟨0, ![-1, 0, 2, 0, 0, -1], -2⟩,
  ⟨0, ![-1, 2, -1, 0, 0, 0], -6⟩,
  ⟨0, ![-1, 2, 0, -1, 0, 0], 2⟩,
  ⟨0, ![-1, 2, 0, 0, -1, 0], 2⟩,
  ⟨0, ![-1, 2, 0, 0, 0, -1], 2⟩
]

def form13 : LinearForm := ⟨14, fun k => terms13[k.val]!⟩

def terms14 : Array TaggedTerm := #[
  ⟨1, ![1, -3, 0, 0, 1, 1], -2⟩,
  ⟨1, ![1, -3, 0, 1, 0, 1], -2⟩,
  ⟨1, ![1, -3, 0, 1, 1, 0], -2⟩,
  ⟨1, ![1, -3, 1, 0, 0, 1], 2⟩,
  ⟨1, ![1, -3, 1, 0, 1, 0], 2⟩,
  ⟨1, ![1, -3, 1, 1, 0, 0], 2⟩,
  ⟨1, ![1, 0, -3, 0, 1, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 0, 1], 2⟩,
  ⟨1, ![1, 0, -3, 1, 1, 0], 2⟩,
  ⟨1, ![1, 0, 1, -3, 0, 1], -1⟩,
  ⟨1, ![1, 0, 1, -3, 1, 0], -1⟩,
  ⟨1, ![1, 0, 1, 0, -3, 1], -1⟩,
  ⟨1, ![1, 0, 1, 0, 1, -3], -1⟩,
  ⟨1, ![1, 0, 1, 1, -3, 0], -1⟩,
  ⟨1, ![1, 0, 1, 1, 0, -3], -1⟩,
  ⟨1, ![1, 1, -3, 0, 0, 1], -2⟩,
  ⟨1, ![1, 1, -3, 0, 1, 0], -2⟩,
  ⟨1, ![1, 1, -3, 1, 0, 0], -2⟩,
  ⟨1, ![1, 1, 0, -3, 0, 1], 1⟩,
  ⟨1, ![1, 1, 0, -3, 1, 0], 1⟩,
  ⟨1, ![1, 1, 0, 0, -3, 1], 1⟩,
  ⟨1, ![1, 1, 0, 0, 1, -3], 1⟩,
  ⟨1, ![1, 1, 0, 1, -3, 0], 1⟩,
  ⟨1, ![1, 1, 0, 1, 0, -3], 1⟩
]

def form14 : LinearForm := ⟨24, fun k => terms14[k.val]!⟩

def terms15 : Array TaggedTerm := #[
  ⟨1, ![1, -1, 0, -2, 0, 2], -1⟩,
  ⟨1, ![1, -1, 0, -2, 2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 0, -2, 2], -1⟩,
  ⟨1, ![1, -1, 0, 0, 2, -2], -1⟩,
  ⟨1, ![1, -1, 0, 2, -2, 0], -1⟩,
  ⟨1, ![1, -1, 0, 2, 0, -2], -1⟩,
  ⟨1, ![1, -1, 2, -2, 0, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, -2, 0], 2⟩,
  ⟨1, ![1, -1, 2, 0, 0, -2], 2⟩,
  ⟨1, ![1, 0, -1, -2, 0, 2], 1⟩,
  ⟨1, ![1, 0, -1, -2, 2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 0, -2, 2], 1⟩,
  ⟨1, ![1, 0, -1, 0, 2, -2], 1⟩,
  ⟨1, ![1, 0, -1, 2, -2, 0], 1⟩,
  ⟨1, ![1, 0, -1, 2, 0, -2], 1⟩,
  ⟨1, ![1, 0, 2, -2, -1, 0], -1⟩,
  ⟨1, ![1, 0, 2, -2, 0, -1], -1⟩,
  ⟨1, ![1, 0, 2, -1, -2, 0], -1⟩,
  ⟨1, ![1, 0, 2, -1, 0, -2], -1⟩,
  ⟨1, ![1, 0, 2, 0, -2, -1], -1⟩,
  ⟨1, ![1, 0, 2, 0, -1, -2], -1⟩,
  ⟨1, ![1, 2, -1, -2, 0, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, -2, 0], -2⟩,
  ⟨1, ![1, 2, -1, 0, 0, -2], -2⟩,
  ⟨1, ![1, 2, 0, -2, -1, 0], 1⟩,
  ⟨1, ![1, 2, 0, -2, 0, -1], 1⟩,
  ⟨1, ![1, 2, 0, -1, -2, 0], 1⟩,
  ⟨1, ![1, 2, 0, -1, 0, -2], 1⟩,
  ⟨1, ![1, 2, 0, 0, -2, -1], 1⟩,
  ⟨1, ![1, 2, 0, 0, -1, -2], 1⟩
]

def form15 : LinearForm := ⟨30, fun k => terms15[k.val]!⟩

def terms16 : Array TaggedTerm := #[
  ⟨1, ![2, -2, -1, 0, 0, 1], -2⟩,
  ⟨1, ![2, -2, -1, 0, 1, 0], -2⟩,
  ⟨1, ![2, -2, -1, 1, 0, 0], -2⟩,
  ⟨1, ![2, -2, 1, -1, 0, 0], 2⟩,
  ⟨1, ![2, -2, 1, 0, -1, 0], 2⟩,
  ⟨1, ![2, -2, 1, 0, 0, -1], 2⟩,
  ⟨1, ![2, -1, -2, 0, 0, 1], 2⟩,
  ⟨1, ![2, -1, -2, 0, 1, 0], 2⟩,
  ⟨1, ![2, -1, -2, 1, 0, 0], 2⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], -2⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], -2⟩,
  ⟨1, ![2, 1, -2, -1, 0, 0], -2⟩,
  ⟨1, ![2, 1, -2, 0, -1, 0], -2⟩,
  ⟨1, ![2, 1, -2, 0, 0, -1], -2⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], 2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], 2⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], 2⟩
]

def form16 : LinearForm := ⟨18, fun k => terms16[k.val]!⟩

def terms17 : Array TaggedTerm := #[
  ⟨0, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨0, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨0, ![2, -1, 0, 0, -2, 1], -1⟩,
  ⟨0, ![2, -1, 0, 0, 1, -2], -1⟩,
  ⟨0, ![2, -1, 0, 1, -2, 0], -1⟩,
  ⟨0, ![2, -1, 0, 1, 0, -2], -1⟩,
  ⟨0, ![2, -1, 1, -2, 0, 0], 2⟩,
  ⟨0, ![2, -1, 1, 0, -2, 0], 2⟩,
  ⟨0, ![2, -1, 1, 0, 0, -2], 2⟩,
  ⟨0, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨0, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨0, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨0, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨0, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨0, ![2, 0, -1, 1, 0, -2], 1⟩,
  ⟨0, ![2, 0, 1, -2, -1, 0], -1⟩,
  ⟨0, ![2, 0, 1, -2, 0, -1], -1⟩,
  ⟨0, ![2, 0, 1, -1, -2, 0], -1⟩,
  ⟨0, ![2, 0, 1, -1, 0, -2], -1⟩,
  ⟨0, ![2, 0, 1, 0, -2, -1], -1⟩,
  ⟨0, ![2, 0, 1, 0, -1, -2], -1⟩,
  ⟨0, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨0, ![2, 1, -1, 0, -2, 0], -2⟩,
  ⟨0, ![2, 1, -1, 0, 0, -2], -2⟩,
  ⟨0, ![2, 1, 0, -2, -1, 0], 1⟩,
  ⟨0, ![2, 1, 0, -2, 0, -1], 1⟩,
  ⟨0, ![2, 1, 0, -1, -2, 0], 1⟩,
  ⟨0, ![2, 1, 0, -1, 0, -2], 1⟩,
  ⟨0, ![2, 1, 0, 0, -2, -1], 1⟩,
  ⟨0, ![2, 1, 0, 0, -1, -2], 1⟩
]

def form17 : LinearForm := ⟨30, fun k => terms17[k.val]!⟩

def terms18 : Array TaggedTerm := #[
  ⟨1, ![2, -1, 0, -2, 0, 1], -1⟩,
  ⟨1, ![2, -1, 0, -2, 1, 0], -1⟩,
  ⟨1, ![2, -1, 0, 0, -2, 1], -1⟩,
  ⟨1, ![2, -1, 0, 0, 1, -2], -1⟩,
  ⟨1, ![2, -1, 0, 1, -2, 0], -1⟩,
  ⟨1, ![2, -1, 0, 1, 0, -2], -1⟩,
  ⟨1, ![2, -1, 1, -2, 0, 0], 2⟩,
  ⟨1, ![2, -1, 1, 0, -2, 0], 2⟩,
  ⟨1, ![2, -1, 1, 0, 0, -2], 2⟩,
  ⟨1, ![2, 0, -1, -2, 0, 1], 1⟩,
  ⟨1, ![2, 0, -1, -2, 1, 0], 1⟩,
  ⟨1, ![2, 0, -1, 0, -2, 1], 1⟩,
  ⟨1, ![2, 0, -1, 0, 1, -2], 1⟩,
  ⟨1, ![2, 0, -1, 1, -2, 0], 1⟩,
  ⟨1, ![2, 0, -1, 1, 0, -2], 1⟩,
  ⟨1, ![2, 0, 1, -2, -1, 0], -1⟩,
  ⟨1, ![2, 0, 1, -2, 0, -1], -1⟩,
  ⟨1, ![2, 0, 1, -1, -2, 0], -1⟩,
  ⟨1, ![2, 0, 1, -1, 0, -2], -1⟩,
  ⟨1, ![2, 0, 1, 0, -2, -1], -1⟩,
  ⟨1, ![2, 0, 1, 0, -1, -2], -1⟩,
  ⟨1, ![2, 1, -1, -2, 0, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, -2, 0], -2⟩,
  ⟨1, ![2, 1, -1, 0, 0, -2], -2⟩,
  ⟨1, ![2, 1, 0, -2, -1, 0], 1⟩,
  ⟨1, ![2, 1, 0, -2, 0, -1], 1⟩,
  ⟨1, ![2, 1, 0, -1, -2, 0], 1⟩,
  ⟨1, ![2, 1, 0, -1, 0, -2], 1⟩,
  ⟨1, ![2, 1, 0, 0, -2, -1], 1⟩,
  ⟨1, ![2, 1, 0, 0, -1, -2], 1⟩
]

def form18 : LinearForm := ⟨30, fun k => terms18[k.val]!⟩

def terms19 : Array TaggedTerm := #[
  ⟨0, ![1, -2, 0, 0, 0, 1], -2⟩,
  ⟨0, ![1, -2, 0, 0, 1, 0], -2⟩,
  ⟨0, ![1, -2, 0, 1, 0, 0], -2⟩,
  ⟨0, ![1, -2, 1, 0, 0, 0], 6⟩,
  ⟨0, ![1, 0, -2, 0, 0, 1], 2⟩,
  ⟨0, ![1, 0, -2, 0, 1, 0], 2⟩,
  ⟨0, ![1, 0, -2, 1, 0, 0], 2⟩,
  ⟨0, ![1, 0, 1, -2, 0, 0], -2⟩,
  ⟨0, ![1, 0, 1, 0, -2, 0], -2⟩,
  ⟨0, ![1, 0, 1, 0, 0, -2], -2⟩,
  ⟨0, ![1, 1, -2, 0, 0, 0], -6⟩,
  ⟨0, ![1, 1, 0, -2, 0, 0], 2⟩,
  ⟨0, ![1, 1, 0, 0, -2, 0], 2⟩,
  ⟨0, ![1, 1, 0, 0, 0, -2], 2⟩
]

def form19 : LinearForm := ⟨14, fun k => terms19[k.val]!⟩

def terms20 : Array TaggedTerm := #[
  ⟨1, ![1, -2, -1, 0, 1, 1], -2⟩,
  ⟨1, ![1, -2, -1, 1, 0, 1], -2⟩,
  ⟨1, ![1, -2, -1, 1, 1, 0], -2⟩,
  ⟨1, ![1, -2, 0, -1, 1, 1], 2⟩,
  ⟨1, ![1, -2, 0, 1, -1, 1], 2⟩,
  ⟨1, ![1, -2, 0, 1, 1, -1], 2⟩,
  ⟨1, ![1, -1, -2, 0, 1, 1], 2⟩,
  ⟨1, ![1, -1, -2, 1, 0, 1], 2⟩,
  ⟨1, ![1, -1, -2, 1, 1, 0], 2⟩,
  ⟨1, ![1, -1, 0, -2, 1, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, -2, 1], -2⟩,
  ⟨1, ![1, -1, 0, 1, 1, -2], -2⟩,
  ⟨1, ![1, 0, -2, -1, 1, 1], -2⟩,
  ⟨1, ![1, 0, -2, 1, -1, 1], -2⟩,
  ⟨1, ![1, 0, -2, 1, 1, -1], -2⟩,
  ⟨1, ![1, 0, -1, -2, 1, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, -2, 1], 2⟩,
  ⟨1, ![1, 0, -1, 1, 1, -2], 2⟩
]

def form20 : LinearForm := ⟨18, fun k => terms20[k.val]!⟩

end MUB6.Certificate.GramFunctions.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows4_0 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row420, row421, row422, row423, row424, row425, row426, row427, row428, row429, row430, row431, row432, row433, row434, row435, row436, row437, row438, row439, row440, row441, row442, row443, row444, row445, row446, row447, row448, row449, row450, row451, row452, row453, row454, row455, row456, row457, row458, row459, row460, row461]

def rows4_1 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row462, row463, row464, row465, row466, row467, row468, row469, row470, row471, row472, row473, row474, row475, row476, row477, row478, row479, row480, row481, row482, row483, row484, row485, row486, row487, row488, row489, row490, row491, row492, row493, row494, row495, row496, row497, row498, row499, row500, row501, row502, row503]

def rows4_2 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row504, row505, row506, row507, row508, row509, row510, row511, row512, row513, row514, row515, row516, row517, row518, row519, row520, row521, row522, row523, row524, row525, row526, row527, row528, row529, row530, row531, row532, row533, row534, row535, row536, row537, row538, row539, row540, row541, row542, row543, row544, row545]

def rows4_3 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row546, row547, row548, row549, row550, row551, row552, row553, row554, row555, row556, row557, row558, row559, row560, row561, row562, row563, row564, row565, row566, row567, row568, row569, row570, row571, row572, row573, row574, row575, row576, row577, row578, row579, row580, row581, row582, row583, row584, row585, row586, row587]

def rows4_4 : Fin GramFunctions.Block0.form4.size → Integer.Sparse Key := ![row588, row589, row590, row591, row592, row593, row594, row595, row596, row597, row598, row599, row600, row601, row602, row603, row604, row605, row606, row607, row608, row609, row610, row611, row612, row613, row614, row615, row616, row617, row618, row619, row620, row621, row622, row623, row624, row625, row626, row627, row628, row629]

end MUB6.Certificate.GramEntries.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization

def entry5_3 : Integer.Sparse Key := [(key18, 12), (key23, -12), (key35, 12), (key43, 108), (key48, -72), (key100, -76), (key115, 84), (key137, 12), (key195, 36), (key196, -60), (key200, -12), (key206, -12), (key212, 12), (key218, -12), (key375, 12), (key381, -48), (key426, -44), (key460, 84), (key486, 36), (key490, -60), (key659, -12), (key663, 12)]

def entry6_0 : Integer.Sparse Key := [(key2686, 12), (key2693, 128), (key2695, -72), (key2719, -96), (key2733, 96), (key2756, 48), (key2759, -84), (key2822, 12), (key2836, -12), (key3018, 8), (key3051, -12), (key3055, -8), (key3057, -48), (key3070, -24), (key3074, 72), (key3077, 24), (key3078, -36), (key3107, -12), (key3116, 12), (key3117, -8)]

def entry7_3 : Integer.Sparse Key := [(key18, -12), (key23, 36), (key35, -60), (key43, 12), (key48, -36), (key74, 60), (key115, 48), (key137, -48), (key206, 12), (key212, 84), (key218, -60), (key375, -12), (key381, -84), (key486, 72), (key654, 60), (key659, -72)]

def entry9_6 : Integer.Sparse Key := [(key2693, 144), (key2695, -84), (key2719, 12), (key2733, -12), (key2756, -12), (key2759, 24), (key2822, -96), (key2836, 96), (key3015, 48), (key3018, -84), (key3055, -24), (key3057, -36), (key3070, -12), (key3074, 12), (key3077, 12), (key3078, -24), (key3107, -24), (key3112, 72), (key3116, 24), (key3117, -36)]

def entries : Fin 21 → Fin 21 → Integer.Sparse Key := ![
  ![entry0_0, entry1_0, entry2_0, entry3_0, entry4_0, entry5_0, entry6_0, entry7_0, entry8_0, entry9_0, entry10_0, entry11_0, entry12_0, entry13_0, entry14_0, entry15_0, entry16_0, entry17_0, entry18_0, entry19_0, entry20_0],
  ![entry1_0, entry1_1, entry2_1, entry3_1, entry4_1, entry5_1, entry6_1, entry7_1, entry8_1, entry9_1, entry10_1, entry11_1, entry12_1, entry13_1, entry14_1, entry15_1, entry16_1, entry17_1, entry18_1, entry19_1, entry20_1],
  ![entry2_0, entry2_1, entry2_2, entry3_2, entry4_2, entry5_2, entry6_2, entry7_2, entry8_2, entry9_2, entry10_2, entry11_2, entry12_2, entry13_2, entry14_2, entry15_2, entry16_2, entry17_2, entry18_2, entry19_2, entry20_2],
  ![entry3_0, entry3_1, entry3_2, entry3_3, entry4_3, entry5_3, entry6_3, entry7_3, entry8_3, entry9_3, entry10_3, entry11_3, entry12_3, entry13_3, entry14_3, entry15_3, entry16_3, entry17_3, entry18_3, entry19_3, entry20_3],
  ![entry4_0, entry4_1, entry4_2, entry4_3, entry4_4, entry5_4, entry6_4, entry7_4, entry8_4, entry9_4, entry10_4, entry11_4, entry12_4, entry13_4, entry14_4, entry15_4, entry16_4, entry17_4, entry18_4, entry19_4, entry20_4],
  ![entry5_0, entry5_1, entry5_2, entry5_3, entry5_4, entry5_5, entry6_5, entry7_5, entry8_5, entry9_5, entry10_5, entry11_5, entry12_5, entry13_5, entry14_5, entry15_5, entry16_5, entry17_5, entry18_5, entry19_5, entry20_5],
  ![entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry7_6, entry8_6, entry9_6, entry10_6, entry11_6, entry12_6, entry13_6, entry14_6, entry15_6, entry16_6, entry17_6, entry18_6, entry19_6, entry20_6],
  ![entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry8_7, entry9_7, entry10_7, entry11_7, entry12_7, entry13_7, entry14_7, entry15_7, entry16_7, entry17_7, entry18_7, entry19_7, entry20_7],
  ![entry8_0, entry8_1, entry8_2, entry8_3, entry8_4, entry8_5, entry8_6, entry8_7, entry8_8, entry9_8, entry10_8, entry11_8, entry12_8, entry13_8, entry14_8, entry15_8, entry16_8, entry17_8, entry18_8, entry19_8, entry20_8],
  ![entry9_0, entry9_1, entry9_2, entry9_3, entry9_4, entry9_5, entry9_6, entry9_7, entry9_8, entry9_9, entry10_9, entry11_9, entry12_9, entry13_9, entry14_9, entry15_9, entry16_9, entry17_9, entry18_9, entry19_9, entry20_9],
  ![entry10_0, entry10_1, entry10_2, entry10_3, entry10_4, entry10_5, entry10_6, entry10_7, entry10_8, entry10_9, entry10_10, entry11_10, entry12_10, entry13_10, entry14_10, entry15_10, entry16_10, entry17_10, entry18_10, entry19_10, entry20_10],
  ![entry11_0, entry11_1, entry11_2, entry11_3, entry11_4, entry11_5, entry11_6, entry11_7, entry11_8, entry11_9, entry11_10, entry11_11, entry12_11, entry13_11, entry14_11, entry15_11, entry16_11, entry17_11, entry18_11, entry19_11, entry20_11],
  ![entry12_0, entry12_1, entry12_2, entry12_3, entry12_4, entry12_5, entry12_6, entry12_7, entry12_8, entry12_9, entry12_10, entry12_11, entry12_12, entry13_12, entry14_12, entry15_12, entry16_12, entry17_12, entry18_12, entry19_12, entry20_12],
  ![entry13_0, entry13_1, entry13_2, entry13_3, entry13_4, entry13_5, entry13_6, entry13_7, entry13_8, entry13_9, entry13_10, entry13_11, entry13_12, entry13_13, entry14_13, entry15_13, entry16_13, entry17_13, entry18_13, entry19_13, entry20_13],
  ![entry14_0, entry14_1, entry14_2, entry14_3, entry14_4, entry14_5, entry14_6, entry14_7, entry14_8, entry14_9, entry14_10, entry14_11, entry14_12, entry14_13, entry14_14, entry15_14, entry16_14, entry17_14, entry18_14, entry19_14, entry20_14],
  ![entry15_0, entry15_1, entry15_2, entry15_3, entry15_4, entry15_5, entry15_6, entry15_7, entry15_8, entry15_9, entry15_10, entry15_11, entry15_12, entry15_13, entry15_14, entry15_15, entry16_15, entry17_15, entry18_15, entry19_15, entry20_15],
  ![entry16_0, entry16_1, entry16_2, entry16_3, entry16_4, entry16_5, entry16_6, entry16_7, entry16_8, entry16_9, entry16_10, entry16_11, entry16_12, entry16_13, entry16_14, entry16_15, entry16_16, entry17_16, entry18_16, entry19_16, entry20_16],
  ![entry17_0, entry17_1, entry17_2, entry17_3, entry17_4, entry17_5, entry17_6, entry17_7, entry17_8, entry17_9, entry17_10, entry17_11, entry17_12, entry17_13, entry17_14, entry17_15, entry17_16, entry17_17, entry18_17, entry19_17, entry20_17],
  ![entry18_0, entry18_1, entry18_2, entry18_3, entry18_4, entry18_5, entry18_6, entry18_7, entry18_8, entry18_9, entry18_10, entry18_11, entry18_12, entry18_13, entry18_14, entry18_15, entry18_16, entry18_17, entry18_18, entry19_18, entry20_18],
  ![entry19_0, entry19_1, entry19_2, entry19_3, entry19_4, entry19_5, entry19_6, entry19_7, entry19_8, entry19_9, entry19_10, entry19_11, entry19_12, entry19_13, entry19_14, entry19_15, entry19_16, entry19_17, entry19_18, entry19_19, entry20_19],
  ![entry20_0, entry20_1, entry20_2, entry20_3, entry20_4, entry20_5, entry20_6, entry20_7, entry20_8, entry20_9, entry20_10, entry20_11, entry20_12, entry20_13, entry20_14, entry20_15, entry20_16, entry20_17, entry20_18, entry20_19, entry20_20]
]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row652 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row653 : Integer.Sparse Key := [(key2617, -1), (key2620, 1), (key2633, 1), (key2650, -2), (key2655, 1), (key2707, 1), (key2730, 1), (key2797, -1), (key2810, -1), (key2833, 1), (key2899, 1), (key2906, -2), (key2946, -1), (key2952, -1), (key2962, -1), (key2964, 2), (key2978, 1), (key2985, 1), (key2994, -1), (key2999, 1), (key3001, -2), (key3004, 1)]

def row654 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row655 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row656 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row657 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row658 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

def row659 : Integer.Sparse Key := [(key2617, 1), (key2620, -1), (key2633, -1), (key2643, 1), (key2650, 1), (key2655, -1), (key2672, 1), (key2675, -1), (key2707, -1), (key2730, 1), (key2739, 1), (key2749, -1), (key2945, 1), (key2946, -1), (key2962, 1), (key2964, -1), (key2978, -1), (key2985, -1), (key2994, 2), (key2999, 1), (key3001, 1), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows0_0 : Fin GramFunctions.Block1.form0.size → Integer.Sparse Key := ![row630, row631, row632, row633, row634, row635, row636, row637, row638, row639, row640, row641, row642, row643, row644, row645, row646, row647, row648, row649, row650, row651, row652, row653, row654, row655, row656, row657, row658, row659]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows1_0 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row660, row661, row662, row663, row664, row665, row666, row667, row668, row669, row670, row671, row672, row673]

def rows1_1 : Fin GramFunctions.Block1.form1.size → Integer.Sparse Key := ![row674, row675, row676, row677, row678, row679, row680, row681, row682, row683, row684, row685, row686, row687]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1674 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1675 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1676 : Integer.Sparse Key := [(key1296, 2), (key1316, -4), (key1330, -2), (key1337, 2), (key1346, 2), (key1391, -2), (key1424, 2), (key1546, 4), (key1560, 2), (key1573, -2), (key1655, -2), (key1660, -2), (key1772, -2), (key1781, -2), (key1813, 2), (key1818, 2)]

def row1683 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1684 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1685 : Integer.Sparse Key := [(key1296, -2), (key1316, 4), (key1330, 2), (key1337, -2), (key1346, -2), (key1391, 2), (key1424, -2), (key1546, -4), (key1560, -2), (key1573, 2), (key1655, 2), (key1660, 2), (key1772, 2), (key1781, 2), (key1813, -2), (key1818, -2)]

def row1704 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1705 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1706 : Integer.Sparse Key := [(key998, -4), (key1005, 6), (key1018, -2), (key1040, -2), (key1075, 2), (key1111, 4), (key1126, 2), (key1154, -6), (key1192, -4), (key1211, 4)]

def row1713 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1714 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1715 : Integer.Sparse Key := [(key998, 4), (key1005, -6), (key1018, 2), (key1040, 2), (key1075, -2), (key1111, -4), (key1126, -2), (key1154, 6), (key1192, 4), (key1211, -4)]

def row1734 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1735 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1736 : Integer.Sparse Key := [(key2617, -2), (key2620, 2), (key2643, 2), (key2655, -4), (key2656, 2), (key2797, -2), (key2810, 2), (key2833, -2), (key2899, 4), (key2915, -2), (key2945, 2), (key2952, -2), (key2962, 2), (key2978, -2), (key2999, -2), (key3004, 2)]

def row1743 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

def row1744 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

def row1745 : Integer.Sparse Key := [(key2617, 2), (key2620, -2), (key2643, -2), (key2655, 4), (key2656, -2), (key2797, 2), (key2810, -2), (key2833, 4), (key2899, -4), (key2906, 2), (key2915, 4), (key2945, -2), (key2962, -2), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1764, row1765, row1766, row1767, row1768, row1769, row1770, row1771, row1772, row1773, row1774, row1775, row1776, row1777]

def rows10_1 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1778, row1779, row1780, row1781, row1782, row1783, row1784, row1785, row1786, row1787, row1788, row1789, row1790, row1791]

def rows10_2 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1792, row1793, row1794, row1795, row1796, row1797, row1798, row1799, row1800, row1801, row1802, row1803, row1804, row1805]

def rows10_3 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1806, row1807, row1808, row1809, row1810, row1811, row1812, row1813, row1814, row1815, row1816, row1817, row1818, row1819]

def rows10_4 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1820, row1821, row1822, row1823, row1824, row1825, row1826, row1827, row1828, row1829, row1830, row1831, row1832, row1833]

def rows10_5 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1834, row1835, row1836, row1837, row1838, row1839, row1840, row1841, row1842, row1843, row1844, row1845, row1846, row1847]

def rows10_6 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1848, row1849, row1850, row1851, row1852, row1853, row1854, row1855, row1856, row1857, row1858, row1859, row1860, row1861]

def rows10_7 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1862, row1863, row1864, row1865, row1866, row1867, row1868, row1869, row1870, row1871, row1872, row1873, row1874, row1875]

def rows10_8 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1876, row1877, row1878, row1879, row1880, row1881, row1882, row1883, row1884, row1885, row1886, row1887, row1888, row1889]

def rows10_9 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1890, row1891, row1892, row1893, row1894, row1895, row1896, row1897, row1898, row1899, row1900, row1901, row1902, row1903]

def rows10_10 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1904, row1905, row1906, row1907, row1908, row1909, row1910, row1911, row1912, row1913, row1914, row1915, row1916, row1917]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1918, row1919, row1920, row1921, row1922, row1923, row1924, row1925, row1926, row1927, row1928, row1929, row1930, row1931]

def rows11_1 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1932, row1933, row1934, row1935, row1936, row1937, row1938, row1939, row1940, row1941, row1942, row1943, row1944, row1945]

def rows11_2 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1946, row1947, row1948, row1949, row1950, row1951, row1952, row1953, row1954, row1955, row1956, row1957, row1958, row1959]

def rows11_3 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1960, row1961, row1962, row1963, row1964, row1965, row1966, row1967, row1968, row1969, row1970, row1971, row1972, row1973]

def rows11_4 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1974, row1975, row1976, row1977, row1978, row1979, row1980, row1981, row1982, row1983, row1984, row1985, row1986, row1987]

def rows11_5 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1988, row1989, row1990, row1991, row1992, row1993, row1994, row1995, row1996, row1997, row1998, row1999, row2000, row2001]

def rows11_6 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2002, row2003, row2004, row2005, row2006, row2007, row2008, row2009, row2010, row2011, row2012, row2013, row2014, row2015]

def rows11_7 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2016, row2017, row2018, row2019, row2020, row2021, row2022, row2023, row2024, row2025, row2026, row2027, row2028, row2029]

def rows11_8 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2030, row2031, row2032, row2033, row2034, row2035, row2036, row2037, row2038, row2039, row2040, row2041, row2042, row2043]

def rows11_9 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2044, row2045, row2046, row2047, row2048, row2049, row2050, row2051, row2052, row2053, row2054, row2055, row2056, row2057]

def rows11_10 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2058, row2059, row2060, row2061, row2062, row2063, row2064, row2065, row2066, row2067, row2068, row2069, row2070, row2071]

def rows11_11 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2072, row2073, row2074, row2075, row2076, row2077, row2078, row2079, row2080, row2081, row2082, row2083, row2084, row2085]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows12_0 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2086, row2087, row2088, row2089, row2090, row2091, row2092, row2093, row2094, row2095, row2096, row2097, row2098, row2099, row2100, row2101, row2102, row2103, row2104, row2105, row2106, row2107, row2108, row2109, row2110, row2111, row2112, row2113, row2114, row2115]

def rows12_1 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2116, row2117, row2118, row2119, row2120, row2121, row2122, row2123, row2124, row2125, row2126, row2127, row2128, row2129, row2130, row2131, row2132, row2133, row2134, row2135, row2136, row2137, row2138, row2139, row2140, row2141, row2142, row2143, row2144, row2145]

def rows12_2 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2146, row2147, row2148, row2149, row2150, row2151, row2152, row2153, row2154, row2155, row2156, row2157, row2158, row2159, row2160, row2161, row2162, row2163, row2164, row2165, row2166, row2167, row2168, row2169, row2170, row2171, row2172, row2173, row2174, row2175]

def rows12_3 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2176, row2177, row2178, row2179, row2180, row2181, row2182, row2183, row2184, row2185, row2186, row2187, row2188, row2189, row2190, row2191, row2192, row2193, row2194, row2195, row2196, row2197, row2198, row2199, row2200, row2201, row2202, row2203, row2204, row2205]

def rows12_4 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2206, row2207, row2208, row2209, row2210, row2211, row2212, row2213, row2214, row2215, row2216, row2217, row2218, row2219, row2220, row2221, row2222, row2223, row2224, row2225, row2226, row2227, row2228, row2229, row2230, row2231, row2232, row2233, row2234, row2235]

def rows12_5 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2236, row2237, row2238, row2239, row2240, row2241, row2242, row2243, row2244, row2245, row2246, row2247, row2248, row2249, row2250, row2251, row2252, row2253, row2254, row2255, row2256, row2257, row2258, row2259, row2260, row2261, row2262, row2263, row2264, row2265]

def rows12_6 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2266, row2267, row2268, row2269, row2270, row2271, row2272, row2273, row2274, row2275, row2276, row2277, row2278, row2279, row2280, row2281, row2282, row2283, row2284, row2285, row2286, row2287, row2288, row2289, row2290, row2291, row2292, row2293, row2294, row2295]

def rows12_7 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2296, row2297, row2298, row2299, row2300, row2301, row2302, row2303, row2304, row2305, row2306, row2307, row2308, row2309, row2310, row2311, row2312, row2313, row2314, row2315, row2316, row2317, row2318, row2319, row2320, row2321, row2322, row2323, row2324, row2325]

def rows12_8 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2326, row2327, row2328, row2329, row2330, row2331, row2332, row2333, row2334, row2335, row2336, row2337, row2338, row2339, row2340, row2341, row2342, row2343, row2344, row2345, row2346, row2347, row2348, row2349, row2350, row2351, row2352, row2353, row2354, row2355]

def rows12_9 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2356, row2357, row2358, row2359, row2360, row2361, row2362, row2363, row2364, row2365, row2366, row2367, row2368, row2369, row2370, row2371, row2372, row2373, row2374, row2375, row2376, row2377, row2378, row2379, row2380, row2381, row2382, row2383, row2384, row2385]

def rows12_10 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2386, row2387, row2388, row2389, row2390, row2391, row2392, row2393, row2394, row2395, row2396, row2397, row2398, row2399, row2400, row2401, row2402, row2403, row2404, row2405, row2406, row2407, row2408, row2409, row2410, row2411, row2412, row2413, row2414, row2415]

def rows12_11 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2416, row2417, row2418, row2419, row2420, row2421, row2422, row2423, row2424, row2425, row2426, row2427, row2428, row2429, row2430, row2431, row2432, row2433, row2434, row2435, row2436, row2437, row2438, row2439, row2440, row2441, row2442, row2443, row2444, row2445]

def rows12_12 : Fin GramFunctions.Block1.form12.size → Integer.Sparse Key := ![row2446, row2447, row2448, row2449, row2450, row2451, row2452, row2453, row2454, row2455, row2456, row2457, row2458, row2459, row2460, row2461, row2462, row2463, row2464, row2465, row2466, row2467, row2468, row2469, row2470, row2471, row2472, row2473, row2474, row2475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows13_0 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2476, row2477, row2478, row2479, row2480, row2481, row2482, row2483, row2484, row2485, row2486, row2487, row2488, row2489]

def rows13_1 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2490, row2491, row2492, row2493, row2494, row2495, row2496, row2497, row2498, row2499, row2500, row2501, row2502, row2503]

def rows13_2 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2504, row2505, row2506, row2507, row2508, row2509, row2510, row2511, row2512, row2513, row2514, row2515, row2516, row2517]

def rows13_3 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2518, row2519, row2520, row2521, row2522, row2523, row2524, row2525, row2526, row2527, row2528, row2529, row2530, row2531]

def rows13_4 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2532, row2533, row2534, row2535, row2536, row2537, row2538, row2539, row2540, row2541, row2542, row2543, row2544, row2545]

def rows13_5 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2546, row2547, row2548, row2549, row2550, row2551, row2552, row2553, row2554, row2555, row2556, row2557, row2558, row2559]

def rows13_6 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2560, row2561, row2562, row2563, row2564, row2565, row2566, row2567, row2568, row2569, row2570, row2571, row2572, row2573]

def rows13_7 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2574, row2575, row2576, row2577, row2578, row2579, row2580, row2581, row2582, row2583, row2584, row2585, row2586, row2587]

def rows13_8 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2588, row2589, row2590, row2591, row2592, row2593, row2594, row2595, row2596, row2597, row2598, row2599, row2600, row2601]

def rows13_9 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2602, row2603, row2604, row2605, row2606, row2607, row2608, row2609, row2610, row2611, row2612, row2613, row2614, row2615]

def rows13_10 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2616, row2617, row2618, row2619, row2620, row2621, row2622, row2623, row2624, row2625, row2626, row2627, row2628, row2629]

def rows13_11 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2630, row2631, row2632, row2633, row2634, row2635, row2636, row2637, row2638, row2639, row2640, row2641, row2642, row2643]

def rows13_12 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2644, row2645, row2646, row2647, row2648, row2649, row2650, row2651, row2652, row2653, row2654, row2655, row2656, row2657]

def rows13_13 : Fin GramFunctions.Block1.form13.size → Integer.Sparse Key := ![row2658, row2659, row2660, row2661, row2662, row2663, row2664, row2665, row2666, row2667, row2668, row2669, row2670, row2671]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row2831 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2832 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2833 : Integer.Sparse Key := [(key2421, -2), (key2428, -4), (key2496, 6), (key3036, 2), (key3042, 4), (key3132, -2), (key3140, -4), (key3145, -4), (key3148, 4)]

def row2834 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2835 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2836 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2837 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2838 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

def row2839 : Integer.Sparse Key := [(key2421, -2), (key2428, 4), (key2496, -2), (key3036, 2), (key3040, -2), (key3042, -2), (key3140, 2), (key3145, 2), (key3148, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows14_0 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2672, row2673, row2674, row2675, row2676, row2677, row2678, row2679, row2680, row2681, row2682, row2683, row2684, row2685, row2686, row2687, row2688, row2689, row2690, row2691, row2692, row2693, row2694, row2695]

def rows14_1 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2696, row2697, row2698, row2699, row2700, row2701, row2702, row2703, row2704, row2705, row2706, row2707, row2708, row2709, row2710, row2711, row2712, row2713, row2714, row2715, row2716, row2717, row2718, row2719]

def rows14_2 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2720, row2721, row2722, row2723, row2724, row2725, row2726, row2727, row2728, row2729, row2730, row2731, row2732, row2733, row2734, row2735, row2736, row2737, row2738, row2739, row2740, row2741, row2742, row2743]

def rows14_3 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2744, row2745, row2746, row2747, row2748, row2749, row2750, row2751, row2752, row2753, row2754, row2755, row2756, row2757, row2758, row2759, row2760, row2761, row2762, row2763, row2764, row2765, row2766, row2767]

def rows14_4 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2768, row2769, row2770, row2771, row2772, row2773, row2774, row2775, row2776, row2777, row2778, row2779, row2780, row2781, row2782, row2783, row2784, row2785, row2786, row2787, row2788, row2789, row2790, row2791]

def rows14_5 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2792, row2793, row2794, row2795, row2796, row2797, row2798, row2799, row2800, row2801, row2802, row2803, row2804, row2805, row2806, row2807, row2808, row2809, row2810, row2811, row2812, row2813, row2814, row2815]

def rows14_6 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2816, row2817, row2818, row2819, row2820, row2821, row2822, row2823, row2824, row2825, row2826, row2827, row2828, row2829, row2830, row2831, row2832, row2833, row2834, row2835, row2836, row2837, row2838, row2839]

def rows14_7 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2840, row2841, row2842, row2843, row2844, row2845, row2846, row2847, row2848, row2849, row2850, row2851, row2852, row2853, row2854, row2855, row2856, row2857, row2858, row2859, row2860, row2861, row2862, row2863]

def rows14_8 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2864, row2865, row2866, row2867, row2868, row2869, row2870, row2871, row2872, row2873, row2874, row2875, row2876, row2877, row2878, row2879, row2880, row2881, row2882, row2883, row2884, row2885, row2886, row2887]

def rows14_9 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2888, row2889, row2890, row2891, row2892, row2893, row2894, row2895, row2896, row2897, row2898, row2899, row2900, row2901, row2902, row2903, row2904, row2905, row2906, row2907, row2908, row2909, row2910, row2911]

def rows14_10 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2912, row2913, row2914, row2915, row2916, row2917, row2918, row2919, row2920, row2921, row2922, row2923, row2924, row2925, row2926, row2927, row2928, row2929, row2930, row2931, row2932, row2933, row2934, row2935]

def rows14_11 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2936, row2937, row2938, row2939, row2940, row2941, row2942, row2943, row2944, row2945, row2946, row2947, row2948, row2949, row2950, row2951, row2952, row2953, row2954, row2955, row2956, row2957, row2958, row2959]

def rows14_12 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2960, row2961, row2962, row2963, row2964, row2965, row2966, row2967, row2968, row2969, row2970, row2971, row2972, row2973, row2974, row2975, row2976, row2977, row2978, row2979, row2980, row2981, row2982, row2983]

def rows14_13 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row2984, row2985, row2986, row2987, row2988, row2989, row2990, row2991, row2992, row2993, row2994, row2995, row2996, row2997, row2998, row2999, row3000, row3001, row3002, row3003, row3004, row3005, row3006, row3007]

def rows14_14 : Fin GramFunctions.Block1.form14.size → Integer.Sparse Key := ![row3008, row3009, row3010, row3011, row3012, row3013, row3014, row3015, row3016, row3017, row3018, row3019, row3020, row3021, row3022, row3023, row3024, row3025, row3026, row3027, row3028, row3029, row3030, row3031]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row718 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row719 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row720 : Integer.Sparse Key := [(key1289, -6), (key1309, 4), (key1350, 2), (key1384, 6), (key1417, -4), (key1471, -2), (key1539, -4), (key1566, 4), (key1895, -2), (key1902, 2)]

def row721 : Integer.Sparse Key := [(key1289, 2), (key1309, -4), (key1350, 2), (key1384, -2), (key1417, 2), (key1539, 4), (key1566, -2), (key1680, -2), (key1895, -2), (key1917, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3176 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row3177 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3014, -2), (key3024, 2)]

def row3178 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

def row3179 : Integer.Sparse Key := [(key2684, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3115, -2)]

def row3180 : Integer.Sparse Key := [(key2679, -2), (key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3058, -2), (key3115, -2)]

def row3181 : Integer.Sparse Key := [(key2684, 2), (key2691, 2), (key2710, 2), (key2717, -4), (key2754, -2), (key2755, 4), (key2820, 2), (key2921, -2), (key3024, 2), (key3047, -2), (key3058, -2), (key3115, -2)]

def row3182 : Integer.Sparse Key := [(key2679, 4), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2813, 2), (key2921, -2), (key3024, 2), (key3053, -4), (key3105, -2)]

def row3183 : Integer.Sparse Key := [(key2679, 2), (key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 2), (key3053, -4), (key3096, 2), (key3105, -2)]

def row3184 : Integer.Sparse Key := [(key2710, -6), (key2717, 4), (key2754, 6), (key2755, -4), (key2921, -2), (key3024, 2), (key3047, 4), (key3053, -4), (key3096, 2), (key3105, -2)]

def row3185 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

def row3186 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3014, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3142, 2), (key3143, -2)]

def row3187 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3188 : Integer.Sparse Key := [(key2684, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3189 : Integer.Sparse Key := [(key2679, 2), (key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3190 : Integer.Sparse Key := [(key2684, -2), (key2691, -2), (key2717, 6), (key2755, -6), (key2820, -2), (key3047, 2), (key3058, 2), (key3061, -2), (key3068, 2), (key3075, -2), (key3076, 2), (key3115, 2), (key3142, 2), (key3143, -2)]

def row3191 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3192 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3193 : Integer.Sparse Key := [(key2679, -6), (key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, 2), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3194 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3195 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3196 : Integer.Sparse Key := [(key2684, 6), (key2691, -2), (key2717, -2), (key2820, -2), (key3047, -4), (key3053, -2), (key3058, 2), (key3061, 2), (key3068, -2), (key3076, 2), (key3096, 2), (key3105, -2), (key3115, 2)]

def row3197 : Integer.Sparse Key := [(key2679, -4), (key2710, 6), (key2813, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3105, 2), (key3142, 2), (key3143, -2)]

def row3198 : Integer.Sparse Key := [(key2679, -2), (key2710, 6), (key3047, -2), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

def row3199 : Integer.Sparse Key := [(key2710, 6), (key3047, -4), (key3053, 4), (key3068, -6), (key3075, -4), (key3076, 4), (key3096, -2), (key3105, 2), (key3142, 2), (key3143, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3200 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3201 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3202 : Integer.Sparse Key := [(key2679, 6), (key3047, -2), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3203 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3204 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3205 : Integer.Sparse Key := [(key3047, 4), (key3053, -4), (key3061, -2), (key3068, 2), (key3075, 2), (key3076, -2), (key3096, -2), (key3105, 2), (key3113, 2), (key3115, -2)]

def row3206 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3207 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3208 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3209 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3210 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3211 : Integer.Sparse Key := [(key1291, -1), (key1299, -1), (key1311, 1), (key1319, 1), (key1386, 1), (key1394, 1), (key1419, -1), (key1427, -2), (key1445, -1), (key1473, 1), (key1481, 1), (key1541, -1), (key1549, -1), (key1568, 1), (key1576, 2), (key1594, 1), (key1682, -1), (key1690, -1), (key1904, -1), (key1912, -1), (key1919, 1), (key1927, 1)]

def row3215 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3216 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3217 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3218 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3219 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3220 : Integer.Sparse Key := [(key1291, 1), (key1299, 1), (key1311, -1), (key1319, -1), (key1386, -1), (key1394, -1), (key1419, 1), (key1427, 2), (key1445, 1), (key1473, -1), (key1481, -1), (key1541, 1), (key1549, 1), (key1568, -1), (key1576, -2), (key1594, -1), (key1682, 1), (key1690, 1), (key1904, 1), (key1912, 1), (key1919, -1), (key1927, -1)]

def row3221 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3222 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3223 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3224 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3225 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3226 : Integer.Sparse Key := [(key1319, -1), (key1327, -1), (key1352, 1), (key1355, 1), (key1427, -1), (key1445, -1), (key1473, 1), (key1481, 1), (key1549, 1), (key1557, 1), (key1576, 1), (key1594, 1), (key1682, -2), (key1684, -1), (key1690, -1), (key1897, -1), (key1900, -1), (key1904, -1), (key1912, -1), (key1919, 2), (key1921, 1), (key1927, 1)]

def row3230 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3231 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3232 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3233 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3234 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3235 : Integer.Sparse Key := [(key1319, 1), (key1327, 1), (key1352, -1), (key1355, -1), (key1427, 1), (key1445, 1), (key1473, -1), (key1481, -1), (key1549, -1), (key1557, -1), (key1576, -1), (key1594, -1), (key1682, 2), (key1684, 1), (key1690, 1), (key1897, 1), (key1900, 1), (key1904, 1), (key1912, 1), (key1919, -2), (key1921, -1), (key1927, -1)]

def row3236 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3237 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3238 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3239 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3240 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3241 : Integer.Sparse Key := [(key1000, -2), (key1014, 2), (key1029, -2), (key1035, 4), (key1070, -2), (key1107, 2), (key1122, -4), (key1149, 2), (key1231, -2), (key1234, 2)]

def row3242 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3243 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3244 : Integer.Sparse Key := [(key994, -2), (key1014, 2), (key1029, 6), (key1035, -4), (key1070, -2), (key1107, -4), (key1122, 4), (key1231, 4), (key1234, -6), (key1241, 2)]

def row3245 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3246 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3247 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3248 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3249 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3250 : Integer.Sparse Key := [(key1000, 2), (key1014, -2), (key1029, 2), (key1035, -4), (key1070, 2), (key1107, -2), (key1122, 4), (key1149, -2), (key1231, 2), (key1234, -2)]

def row3251 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3252 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3253 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3254 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3255 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3256 : Integer.Sparse Key := [(key994, -2), (key1000, 2), (key1029, -2), (key1035, 2), (key1107, 4), (key1122, -2), (key1149, -2), (key1231, -4), (key1234, 2), (key1241, 2)]

def row3257 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3258 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3259 : Integer.Sparse Key := [(key994, 2), (key1014, -2), (key1029, -6), (key1035, 4), (key1070, 2), (key1107, 4), (key1122, -4), (key1231, -4), (key1234, 6), (key1241, -2)]

def row3260 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3261 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3262 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3263 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3264 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3265 : Integer.Sparse Key := [(key994, 2), (key1000, -2), (key1029, 2), (key1035, -2), (key1107, -4), (key1122, 2), (key1149, 2), (key1231, 4), (key1234, -2), (key1241, -2)]

def row3305 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3306 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3307 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3308 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3309 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3310 : Integer.Sparse Key := [(key2398, 2), (key2404, 2), (key2435, 2), (key2464, -2), (key2470, -2), (key2478, 6), (key2501, -2), (key2589, 2), (key2604, -2), (key2768, -6), (key2845, 2), (key2876, 2), (key2916, -2), (key2925, -2)]

def row3311 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3312 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3313 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3314 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2839, -2), (key2845, 2), (key2876, -6)]

def row3315 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2589, 2), (key2762, -2), (key2768, 2), (key2845, 2), (key2876, -6)]

def row3316 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2470, -2), (key2478, -2), (key2501, -2), (key2568, 2), (key2570, 2), (key2575, 2), (key2583, -2), (key2589, 2), (key2768, 2), (key2845, 2), (key2876, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows15_0 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row700, row701, row702, row703, row704, row705, row3032, row3033, row3034, row712, row713, row714, row715, row716, row717, row3035, row3036, row3037, row3038, row3039, row3040, row3041, row3042, row3043, row3044, row3045, row3046, row3047, row3048, row3049]

def rows15_1 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row730, row731, row732, row733, row734, row735, row3050, row3051, row3052, row742, row743, row744, row745, row746, row747, row3053, row3054, row3055, row3056, row3057, row3058, row3059, row3060, row3061, row3062, row3063, row3064, row3065, row3066, row3067]

def rows15_2 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row760, row761, row762, row763, row764, row765, row3068, row3069, row3070, row772, row773, row774, row775, row776, row777, row3071, row3072, row3073, row3074, row3075, row3076, row3077, row3078, row3079, row3080, row3081, row3082, row3083, row3084, row3085]

def rows15_3 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3086, row3087, row3088, row3089, row3090, row3091, row3092, row3093, row3094, row3095, row3096, row3097, row3098, row3099, row3100, row3101, row3102, row3103, row3104, row3105, row3106, row3107, row3108, row3109, row3110, row3111, row3112, row3113, row3114, row3115]

def rows15_4 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3116, row3117, row3118, row3119, row3120, row3121, row3122, row3123, row3124, row3125, row3126, row3127, row3128, row3129, row3130, row3131, row3132, row3133, row3134, row3135, row3136, row3137, row3138, row3139, row3140, row3141, row3142, row3143, row3144, row3145]

def rows15_5 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3146, row3147, row3148, row3149, row3150, row3151, row3152, row3153, row3154, row3155, row3156, row3157, row3158, row3159, row3160, row3161, row3162, row3163, row3164, row3165, row3166, row3167, row3168, row3169, row3170, row3171, row3172, row3173, row3174, row3175]

def rows15_6 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3176, row3177, row3178, row3179, row3180, row3181, row3182, row3183, row3184, row3185, row3186, row3187, row3188, row3189, row3190, row3191, row3192, row3193, row3194, row3195, row3196, row3197, row3198, row3199, row3200, row3201, row3202, row3203, row3204, row3205]

def rows15_7 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3206, row3207, row3208, row3209, row3210, row3211, row3212, row3213, row3214, row3215, row3216, row3217, row3218, row3219, row3220, row3221, row3222, row3223, row3224, row3225, row3226, row3227, row3228, row3229, row3230, row3231, row3232, row3233, row3234, row3235]

def rows15_8 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3236, row3237, row3238, row3239, row3240, row3241, row3242, row3243, row3244, row3245, row3246, row3247, row3248, row3249, row3250, row3251, row3252, row3253, row3254, row3255, row3256, row3257, row3258, row3259, row3260, row3261, row3262, row3263, row3264, row3265]

def rows15_9 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3266, row3267, row3268, row3269, row3270, row3271, row3272, row3273, row3274, row3275, row3276, row3277, row3278, row3279, row3280, row3281, row3282, row3283, row3284, row3285, row3286, row3287, row3288, row3289, row3290, row3291, row3292, row3293, row3294, row3295]

def rows15_10 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3296, row3297, row3298, row3299, row3300, row3301, row3302, row3303, row3304, row3305, row3306, row3307, row3308, row3309, row3310, row3311, row3312, row3313, row3314, row3315, row3316, row3317, row3318, row3319, row3320, row3321, row3322, row3323, row3324, row3325]

def rows15_11 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3326, row3327, row3328, row3329, row3330, row3331, row3332, row3333, row3334, row3335, row3336, row3337, row3338, row3339, row3340, row3341, row3342, row3343, row3344, row3345, row3346, row3347, row3348, row3349, row3350, row3351, row3352, row3353, row3354, row3355]

def rows15_12 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3356, row3357, row3358, row3359, row3360, row3361, row3362, row3363, row3364, row3365, row3366, row3367, row3368, row3369, row3370, row3371, row3372, row3373, row3374, row3375, row3376, row3377, row3378, row3379, row3380, row3381, row3382, row3383, row3384, row3385]

def rows15_13 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3386, row3387, row3388, row3389, row3390, row3391, row3392, row3393, row3394, row3395, row3396, row3397, row3398, row3399, row3400, row3401, row3402, row3403, row3404, row3405, row3406, row3407, row3408, row3409, row3410, row3411, row3412, row3413, row3414, row3415]

def rows15_14 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3416, row3417, row3418, row3419, row3420, row3421, row3422, row3423, row3424, row3425, row3426, row3427, row3428, row3429, row3430, row3431, row3432, row3433, row3434, row3435, row3436, row3437, row3438, row3439, row3440, row3441, row3442, row3443, row3444, row3445]

def rows15_15 : Fin GramFunctions.Block1.form15.size → Integer.Sparse Key := ![row3446, row3447, row3448, row3449, row3450, row3451, row3452, row3453, row3454, row3455, row3456, row3457, row3458, row3459, row3460, row3461, row3462, row3463, row3464, row3465, row3466, row3467, row3468, row3469, row3470, row3471, row3472, row3473, row3474, row3475]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3704 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3705 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3706 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3707 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3708 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

def row3709 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1424, -1), (key1447, -1), (key1455, 1), (key1466, 1), (key1573, 1), (key1596, 1), (key1655, -1), (key1667, -1), (key1788, -2), (key1790, 1), (key1798, -1), (key1813, 2), (key1817, -1), (key1825, 1), (key1839, -1), (key1841, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows16_0 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2086, row2087, row2088, row3476, row3477, row3478, row2095, row2096, row2097, row3479, row3480, row3481, row3482, row3483, row3484, row3485, row3486, row3487]

def rows16_1 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2116, row2117, row2118, row3488, row3489, row3490, row2125, row2126, row2127, row3491, row3492, row3493, row3494, row3495, row3496, row3497, row3498, row3499]

def rows16_2 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2146, row2147, row2148, row3500, row3501, row3502, row2155, row2156, row2157, row3503, row3504, row3505, row3506, row3507, row3508, row3509, row3510, row3511]

def rows16_3 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2176, row2177, row2178, row3512, row3513, row3514, row2185, row2186, row2187, row3515, row3516, row3517, row3518, row3519, row3520, row3521, row3522, row3523]

def rows16_4 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2206, row2207, row2208, row3524, row3525, row3526, row2215, row2216, row2217, row3527, row3528, row3529, row3530, row3531, row3532, row3533, row3534, row3535]

def rows16_5 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2236, row2237, row2238, row3536, row3537, row3538, row2245, row2246, row2247, row3539, row3540, row3541, row3542, row3543, row3544, row3545, row3546, row3547]

def rows16_6 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2266, row2267, row2268, row3548, row3549, row3550, row2275, row2276, row2277, row3551, row3552, row3553, row3554, row3555, row3556, row3557, row3558, row3559]

def rows16_7 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2296, row2297, row2298, row3560, row3561, row3562, row2305, row2306, row2307, row3563, row3564, row3565, row3566, row3567, row3568, row3569, row3570, row3571]

def rows16_8 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2326, row2327, row2328, row3572, row3573, row3574, row2335, row2336, row2337, row3575, row3576, row3577, row3578, row3579, row3580, row3581, row3582, row3583]

def rows16_9 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2356, row2357, row2358, row3584, row3585, row3586, row2365, row2366, row2367, row3587, row3588, row3589, row3590, row3591, row3592, row3593, row3594, row3595]

def rows16_10 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2386, row2387, row2388, row3596, row3597, row3598, row2395, row2396, row2397, row3599, row3600, row3601, row3602, row3603, row3604, row3605, row3606, row3607]

def rows16_11 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2416, row2417, row2418, row3608, row3609, row3610, row2425, row2426, row2427, row3611, row3612, row3613, row3614, row3615, row3616, row3617, row3618, row3619]

def rows16_12 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row2446, row2447, row2448, row3620, row3621, row3622, row2455, row2456, row2457, row3623, row3624, row3625, row3626, row3627, row3628, row3629, row3630, row3631]

def rows16_13 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3632, row3633, row3634, row3635, row3636, row3637, row3638, row3639, row3640, row3641, row3642, row3643, row3644, row3645, row3646, row3647, row3648, row3649]

def rows16_14 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3650, row3651, row3652, row3653, row3654, row3655, row3656, row3657, row3658, row3659, row3660, row3661, row3662, row3663, row3664, row3665, row3666, row3667]

def rows16_15 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3668, row3669, row3670, row3671, row3672, row3673, row3674, row3675, row3676, row3677, row3678, row3679, row3680, row3681, row3682, row3683, row3684, row3685]

def rows16_16 : Fin GramFunctions.Block1.form16.size → Integer.Sparse Key := ![row3686, row3687, row3688, row3689, row3690, row3691, row3692, row3693, row3694, row3695, row3696, row3697, row3698, row3699, row3700, row3701, row3702, row3703]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3713 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3714 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3715 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3716 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3717 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3718 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1424, 1), (key1447, 1), (key1455, -1), (key1466, -1), (key1573, -1), (key1596, -1), (key1655, 1), (key1667, 1), (key1788, 2), (key1790, -1), (key1798, 1), (key1813, -2), (key1817, 1), (key1825, -1), (key1839, 1), (key1841, -1)]

def row3719 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3720 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3721 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3722 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3723 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3724 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1316, 1), (key1329, -1), (key1339, -1), (key1345, 1), (key1391, -1), (key1397, 1), (key1455, -1), (key1457, 1), (key1546, 1), (key1559, -1), (key1655, 1), (key1659, -1), (key1774, -1), (key1780, 1), (key1788, -1), (key1790, 1), (key1813, 1), (key1817, -1), (key1839, -2), (key1841, 2)]

def row3728 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3729 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3730 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3731 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3732 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3733 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1316, -1), (key1329, 1), (key1339, 1), (key1345, -1), (key1391, 1), (key1397, -1), (key1455, 1), (key1457, -1), (key1546, -1), (key1559, 1), (key1655, -1), (key1659, 1), (key1774, 1), (key1780, -1), (key1788, 1), (key1790, -1), (key1813, -1), (key1817, 1), (key1839, 2), (key1841, -2)]

def row3764 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3765 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3766 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3767 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3768 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3769 : Integer.Sparse Key := [(key1292, -1), (key1298, -1), (key1312, 1), (key1318, 1), (key1387, 1), (key1393, 1), (key1420, -1), (key1426, -1), (key1542, -1), (key1548, -2), (key1556, 1), (key1569, 1), (key1575, 2), (key1593, -1), (key1624, -1), (key1633, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3773 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3774 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3775 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3776 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3777 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3778 : Integer.Sparse Key := [(key1292, 1), (key1298, 1), (key1312, -1), (key1318, -1), (key1387, -1), (key1393, -1), (key1420, 1), (key1426, 1), (key1542, 1), (key1548, 2), (key1556, -1), (key1569, -1), (key1575, -2), (key1593, 1), (key1624, 1), (key1633, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3779 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3780 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3781 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3782 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3783 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3784 : Integer.Sparse Key := [(key1318, -1), (key1326, 1), (key1351, -1), (key1354, 1), (key1426, 1), (key1444, -1), (key1472, 1), (key1480, -1), (key1548, -1), (key1556, 1), (key1575, 1), (key1593, -1), (key1624, -2), (key1633, 2), (key1683, -1), (key1689, 1), (key1896, -1), (key1899, 1), (key1903, 1), (key1911, -1), (key1920, -1), (key1926, 1)]

def row3788 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3789 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3790 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3791 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3792 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3793 : Integer.Sparse Key := [(key1318, 1), (key1326, -1), (key1351, 1), (key1354, -1), (key1426, -1), (key1444, 1), (key1472, -1), (key1480, 1), (key1548, 1), (key1556, -1), (key1575, -1), (key1593, 1), (key1624, 2), (key1633, -2), (key1683, 1), (key1689, -1), (key1896, 1), (key1899, -1), (key1903, -1), (key1911, 1), (key1920, 1), (key1926, -1)]

def row3794 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3795 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3796 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3797 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3798 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3799 : Integer.Sparse Key := [(key22, -2), (key34, 2), (key44, -2), (key47, 4), (key73, -2), (key101, 2), (key114, -4), (key136, 2), (key172, -2), (key176, 2)]

def row3800 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3801 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3802 : Integer.Sparse Key := [(key19, -2), (key34, 2), (key44, 6), (key47, -4), (key73, -2), (key101, -4), (key114, 4), (key172, 4), (key176, -6), (key181, 2)]

def row3803 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3804 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3805 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3806 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3807 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3808 : Integer.Sparse Key := [(key22, 2), (key34, -2), (key44, 2), (key47, -4), (key73, 2), (key101, -2), (key114, 4), (key136, -2), (key172, 2), (key176, -2)]

def row3809 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3810 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3811 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3812 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3813 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3814 : Integer.Sparse Key := [(key19, -2), (key22, 2), (key44, -2), (key47, 2), (key101, 4), (key114, -2), (key136, -2), (key172, -4), (key176, 2), (key181, 2)]

def row3815 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3816 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3817 : Integer.Sparse Key := [(key19, 2), (key34, -2), (key44, -6), (key47, 4), (key73, 2), (key101, 4), (key114, -4), (key172, -4), (key176, 6), (key181, -2)]

def row3818 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3819 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3820 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3821 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3822 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

def row3823 : Integer.Sparse Key := [(key19, 2), (key22, -2), (key44, 2), (key47, -2), (key101, -4), (key114, 2), (key136, 2), (key172, 4), (key176, -2), (key181, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row3974 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3975 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3976 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3977 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3978 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3979 : Integer.Sparse Key := [(key1316, -1), (key1329, -1), (key1337, 1), (key1345, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1546, 1), (key1559, 1), (key1655, -1), (key1659, -1), (key1772, -2), (key1774, 1), (key1780, -1), (key1813, 2), (key1817, 1), (key1825, -1), (key1839, -1), (key1844, 1)]

def row3983 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3984 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3985 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3986 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3987 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3988 : Integer.Sparse Key := [(key1316, 1), (key1329, 1), (key1337, -1), (key1345, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1546, -1), (key1559, -1), (key1655, 1), (key1659, 1), (key1772, 2), (key1774, -1), (key1780, 1), (key1813, -2), (key1817, -1), (key1825, 1), (key1839, 1), (key1844, -1)]

def row3989 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3990 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3991 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3992 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3993 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3994 : Integer.Sparse Key := [(key1296, -1), (key1302, 1), (key1337, -1), (key1339, 1), (key1391, -1), (key1397, 1), (key1424, 1), (key1447, -1), (key1457, -1), (key1466, 1), (key1573, 1), (key1596, -1), (key1655, 1), (key1667, -1), (key1772, -1), (key1774, 1), (key1790, -1), (key1798, 1), (key1813, 1), (key1825, -1), (key1839, -2), (key1844, 2)]

def row3998 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row3999 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4000 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4001 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4002 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

def row4003 : Integer.Sparse Key := [(key1296, 1), (key1302, -1), (key1337, 1), (key1339, -1), (key1391, 1), (key1397, -1), (key1424, -1), (key1447, 1), (key1457, 1), (key1466, -1), (key1573, -1), (key1596, 1), (key1655, -1), (key1667, 1), (key1772, 1), (key1774, -1), (key1790, 1), (key1798, -1), (key1813, -1), (key1825, 1), (key1839, 2), (key1844, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4145 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4146 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4147 : Integer.Sparse Key := [(key1256, 2), (key1267, -2), (key1531, -4), (key1535, 2), (key1609, 2), (key1641, -2), (key1650, -2), (key1673, 4), (key1765, -2), (key1767, 4), (key1806, 2), (key1831, -4), (key1836, -2), (key1847, 2)]

def row4148 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4149 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4150 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4151 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4152 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4153 : Integer.Sparse Key := [(key1256, 1), (key1260, -1), (key1265, 1), (key1267, -1), (key1531, 1), (key1535, -1), (key1609, -2), (key1641, 2), (key1648, -1), (key1650, 1), (key1765, 1), (key1767, -1), (key1806, -1), (key1808, 1), (key1836, 2), (key1847, -2)]

def row4154 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4155 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4156 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4157 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4158 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4159 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1426, -1), (key1444, -1), (key1472, 1), (key1480, 1), (key1569, -1), (key1575, 2), (key1593, 1), (key1618, 1), (key1624, -1), (key1681, -2), (key1683, 1), (key1689, -1), (key1903, -1), (key1911, -1), (key1918, 1), (key1926, 1)]

def row4163 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4164 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4165 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4166 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4167 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4168 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1426, 1), (key1444, 1), (key1472, -1), (key1480, -1), (key1569, 1), (key1575, -2), (key1593, -1), (key1618, -1), (key1624, 1), (key1681, 2), (key1683, -1), (key1689, 1), (key1903, 1), (key1911, 1), (key1918, -1), (key1926, -1)]

def row4169 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4170 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4171 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4172 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4173 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4174 : Integer.Sparse Key := [(key1292, -1), (key1298, 1), (key1312, 1), (key1326, -1), (key1351, -1), (key1354, 1), (key1387, -1), (key1393, 1), (key1420, -1), (key1426, 1), (key1542, 1), (key1556, -1), (key1569, -1), (key1575, 1), (key1618, 2), (key1624, -2), (key1681, -1), (key1683, 1), (key1896, -1), (key1899, 1), (key1918, -1), (key1920, 1)]

def row4178 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4179 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4180 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4181 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4182 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

def row4183 : Integer.Sparse Key := [(key1292, 1), (key1298, -1), (key1312, -1), (key1326, 1), (key1351, 1), (key1354, -1), (key1387, 1), (key1393, -1), (key1420, 1), (key1426, -1), (key1542, -1), (key1556, 1), (key1569, 1), (key1575, -1), (key1618, -2), (key1624, 2), (key1681, 1), (key1683, -1), (key1896, 1), (key1899, -1), (key1918, 1), (key1920, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows17_0 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3704, row3705, row3706, row3707, row3708, row3709, row3710, row3711, row3712, row3713, row3714, row3715, row3716, row3717, row3718, row3719, row3720, row3721, row3722, row3723, row3724, row3725, row3726, row3727, row3728, row3729, row3730, row3731, row3732, row3733]

def rows17_1 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3734, row3735, row3736, row3737, row3738, row3739, row3740, row3741, row3742, row3743, row3744, row3745, row3746, row3747, row3748, row3749, row3750, row3751, row3752, row3753, row3754, row3755, row3756, row3757, row3758, row3759, row3760, row3761, row3762, row3763]

def rows17_2 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3764, row3765, row3766, row3767, row3768, row3769, row3770, row3771, row3772, row3773, row3774, row3775, row3776, row3777, row3778, row3779, row3780, row3781, row3782, row3783, row3784, row3785, row3786, row3787, row3788, row3789, row3790, row3791, row3792, row3793]

def rows17_3 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3794, row3795, row3796, row3797, row3798, row3799, row3800, row3801, row3802, row3803, row3804, row3805, row3806, row3807, row3808, row3809, row3810, row3811, row3812, row3813, row3814, row3815, row3816, row3817, row3818, row3819, row3820, row3821, row3822, row3823]

def rows17_4 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3824, row3825, row3826, row3827, row3828, row3829, row3830, row3831, row3832, row3833, row3834, row3835, row3836, row3837, row3838, row3839, row3840, row3841, row3842, row3843, row3844, row3845, row3846, row3847, row3848, row3849, row3850, row3851, row3852, row3853]

def rows17_5 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3854, row3855, row3856, row3857, row3858, row3859, row3860, row3861, row3862, row3863, row3864, row3865, row3866, row3867, row3868, row3869, row3870, row3871, row3872, row3873, row3874, row3875, row3876, row3877, row3878, row3879, row3880, row3881, row3882, row3883]

def rows17_6 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3884, row3885, row3886, row3887, row3888, row3889, row3890, row3891, row3892, row3893, row3894, row3895, row3896, row3897, row3898, row3899, row3900, row3901, row3902, row3903, row3904, row3905, row3906, row3907, row3908, row3909, row3910, row3911, row3912, row3913]

def rows17_7 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3914, row3915, row3916, row3917, row3918, row3919, row3920, row3921, row3922, row3923, row3924, row3925, row3926, row3927, row3928, row3929, row3930, row3931, row3932, row3933, row3934, row3935, row3936, row3937, row3938, row3939, row3940, row3941, row3942, row3943]

def rows17_8 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3944, row3945, row3946, row3947, row3948, row3949, row3950, row3951, row3952, row3953, row3954, row3955, row3956, row3957, row3958, row3959, row3960, row3961, row3962, row3963, row3964, row3965, row3966, row3967, row3968, row3969, row3970, row3971, row3972, row3973]

def rows17_9 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row3974, row3975, row3976, row3977, row3978, row3979, row3980, row3981, row3982, row3983, row3984, row3985, row3986, row3987, row3988, row3989, row3990, row3991, row3992, row3993, row3994, row3995, row3996, row3997, row3998, row3999, row4000, row4001, row4002, row4003]

def rows17_10 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4004, row4005, row4006, row4007, row4008, row4009, row4010, row4011, row4012, row4013, row4014, row4015, row4016, row4017, row4018, row4019, row4020, row4021, row4022, row4023, row4024, row4025, row4026, row4027, row4028, row4029, row4030, row4031, row4032, row4033]

def rows17_11 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4034, row4035, row4036, row4037, row4038, row4039, row4040, row4041, row4042, row4043, row4044, row4045, row4046, row4047, row4048, row4049, row4050, row4051, row4052, row4053, row4054, row4055, row4056, row4057, row4058, row4059, row4060, row4061, row4062, row4063]

def rows17_12 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4064, row4065, row4066, row4067, row4068, row4069, row4070, row4071, row4072, row4073, row4074, row4075, row4076, row4077, row4078, row4079, row4080, row4081, row4082, row4083, row4084, row4085, row4086, row4087, row4088, row4089, row4090, row4091, row4092, row4093]

def rows17_13 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4094, row4095, row4096, row4097, row4098, row4099, row4100, row4101, row4102, row4103, row4104, row4105, row4106, row4107, row4108, row4109, row4110, row4111, row4112, row4113, row4114, row4115, row4116, row4117, row4118, row4119, row4120, row4121, row4122, row4123]

def rows17_14 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4124, row4125, row4126, row4127, row4128, row4129, row4130, row4131, row4132, row4133, row4134, row4135, row4136, row4137, row4138, row4139, row4140, row4141, row4142, row4143, row4144, row4145, row4146, row4147, row4148, row4149, row4150, row4151, row4152, row4153]

def rows17_15 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4154, row4155, row4156, row4157, row4158, row4159, row4160, row4161, row4162, row4163, row4164, row4165, row4166, row4167, row4168, row4169, row4170, row4171, row4172, row4173, row4174, row4175, row4176, row4177, row4178, row4179, row4180, row4181, row4182, row4183]

def rows17_16 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4184, row4185, row4186, row4187, row4188, row4189, row4190, row4191, row4192, row4193, row4194, row4195, row4196, row4197, row4198, row4199, row4200, row4201, row4202, row4203, row4204, row4205, row4206, row4207, row4208, row4209, row4210, row4211, row4212, row4213]

def rows17_17 : Fin GramFunctions.Block1.form17.size → Integer.Sparse Key := ![row4214, row4215, row4216, row4217, row4218, row4219, row4220, row4221, row4222, row4223, row4224, row4225, row4226, row4227, row4228, row4229, row4230, row4231, row4232, row4233, row4234, row4235, row4236, row4237, row4238, row4239, row4240, row4241, row4242, row4243]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4376 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4377 : Integer.Sparse Key := [(key2370, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4378 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4379 : Integer.Sparse Key := [(key2398, -2), (key2464, 6), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2839, -2), (key2842, 2), (key2874, -6)]

def row4380 : Integer.Sparse Key := [(key2370, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2586, 2), (key2762, -2), (key2765, 2), (key2842, 2), (key2874, -6)]

def row4381 : Integer.Sparse Key := [(key2398, -2), (key2464, 4), (key2467, -2), (key2476, -2), (key2499, -2), (key2534, 2), (key2540, 2), (key2551, 2), (key2583, -2), (key2586, 2), (key2765, 2), (key2842, 2), (key2874, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows18_0 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2098, row2099, row2100, row2101, row2102, row2103, row3479, row3480, row3481, row2110, row2111, row2112, row2113, row2114, row2115, row4244, row4245, row4246, row4247, row4248, row4249, row3485, row3486, row3487, row4250, row4251, row4252, row4253, row4254, row4255]

def rows18_1 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2128, row2129, row2130, row2131, row2132, row2133, row3491, row3492, row3493, row2140, row2141, row2142, row2143, row2144, row2145, row4256, row4257, row4258, row4259, row4260, row4261, row3497, row3498, row3499, row4262, row4263, row4264, row4265, row4266, row4267]

def rows18_2 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2158, row2159, row2160, row2161, row2162, row2163, row3503, row3504, row3505, row2170, row2171, row2172, row2173, row2174, row2175, row4268, row4269, row4270, row4271, row4272, row4273, row3509, row3510, row3511, row4274, row4275, row4276, row4277, row4278, row4279]

def rows18_3 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2188, row2189, row2190, row2191, row2192, row2193, row3515, row3516, row3517, row2200, row2201, row2202, row2203, row2204, row2205, row4280, row4281, row4282, row4283, row4284, row4285, row3521, row3522, row3523, row4286, row4287, row4288, row4289, row4290, row4291]

def rows18_4 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2218, row2219, row2220, row2221, row2222, row2223, row3527, row3528, row3529, row2230, row2231, row2232, row2233, row2234, row2235, row4292, row4293, row4294, row4295, row4296, row4297, row3533, row3534, row3535, row4298, row4299, row4300, row4301, row4302, row4303]

def rows18_5 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2248, row2249, row2250, row2251, row2252, row2253, row3539, row3540, row3541, row2260, row2261, row2262, row2263, row2264, row2265, row4304, row4305, row4306, row4307, row4308, row4309, row3545, row3546, row3547, row4310, row4311, row4312, row4313, row4314, row4315]

def rows18_6 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2278, row2279, row2280, row2281, row2282, row2283, row3551, row3552, row3553, row2290, row2291, row2292, row2293, row2294, row2295, row4316, row4317, row4318, row4319, row4320, row4321, row3557, row3558, row3559, row4322, row4323, row4324, row4325, row4326, row4327]

def rows18_7 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2308, row2309, row2310, row2311, row2312, row2313, row3563, row3564, row3565, row2320, row2321, row2322, row2323, row2324, row2325, row4328, row4329, row4330, row4331, row4332, row4333, row3569, row3570, row3571, row4334, row4335, row4336, row4337, row4338, row4339]

def rows18_8 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2338, row2339, row2340, row2341, row2342, row2343, row3575, row3576, row3577, row2350, row2351, row2352, row2353, row2354, row2355, row4340, row4341, row4342, row4343, row4344, row4345, row3581, row3582, row3583, row4346, row4347, row4348, row4349, row4350, row4351]

def rows18_9 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2368, row2369, row2370, row2371, row2372, row2373, row3587, row3588, row3589, row2380, row2381, row2382, row2383, row2384, row2385, row4352, row4353, row4354, row4355, row4356, row4357, row3593, row3594, row3595, row4358, row4359, row4360, row4361, row4362, row4363]

def rows18_10 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2398, row2399, row2400, row2401, row2402, row2403, row3599, row3600, row3601, row2410, row2411, row2412, row2413, row2414, row2415, row4364, row4365, row4366, row4367, row4368, row4369, row3605, row3606, row3607, row4370, row4371, row4372, row4373, row4374, row4375]

def rows18_11 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2428, row2429, row2430, row2431, row2432, row2433, row3611, row3612, row3613, row2440, row2441, row2442, row2443, row2444, row2445, row4376, row4377, row4378, row4379, row4380, row4381, row3617, row3618, row3619, row4382, row4383, row4384, row4385, row4386, row4387]

def rows18_12 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row2458, row2459, row2460, row2461, row2462, row2463, row3623, row3624, row3625, row2470, row2471, row2472, row2473, row2474, row2475, row4388, row4389, row4390, row4391, row4392, row4393, row3629, row3630, row3631, row4394, row4395, row4396, row4397, row4398, row4399]

def rows18_13 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4400, row4401, row4402, row4403, row4404, row4405, row3641, row3642, row3643, row4406, row4407, row4408, row4409, row4410, row4411, row4412, row4413, row4414, row4415, row4416, row4417, row3647, row3648, row3649, row4418, row4419, row4420, row4421, row4422, row4423]

def rows18_14 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4424, row4425, row4426, row4427, row4428, row4429, row3659, row3660, row3661, row4430, row4431, row4432, row4433, row4434, row4435, row4436, row4437, row4438, row4439, row4440, row4441, row3665, row3666, row3667, row4442, row4443, row4444, row4445, row4446, row4447]

def rows18_15 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4448, row4449, row4450, row4451, row4452, row4453, row3677, row3678, row3679, row4454, row4455, row4456, row4457, row4458, row4459, row4460, row4461, row4462, row4463, row4464, row4465, row3683, row3684, row3685, row4466, row4467, row4468, row4469, row4470, row4471]

def rows18_16 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4472, row4473, row4474, row4475, row4476, row4477, row3695, row3696, row3697, row4478, row4479, row4480, row4481, row4482, row4483, row4484, row4485, row4486, row4487, row4488, row4489, row3701, row3702, row3703, row4490, row4491, row4492, row4493, row4494, row4495]

def rows18_17 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4496, row4497, row4498, row4499, row4500, row4501, row4502, row4503, row4504, row4505, row4506, row4507, row4508, row4509, row4510, row4511, row4512, row4513, row4514, row4515, row4516, row4517, row4518, row4519, row4520, row4521, row4522, row4523, row4524, row4525]

def rows18_18 : Fin GramFunctions.Block1.form18.size → Integer.Sparse Key := ![row4526, row4527, row4528, row4529, row4530, row4531, row4532, row4533, row4534, row4535, row4536, row4537, row4538, row4539, row4540, row4541, row4542, row4543, row4544, row4545, row4546, row4547, row4548, row4549, row4550, row4551, row4552, row4553, row4554, row4555]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4836 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4837 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4838 : Integer.Sparse Key := [(key2707, -2), (key2730, -4), (key2739, 2), (key2749, 2), (key2751, 2), (key2810, 2), (key2833, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2952, -2), (key2962, -2), (key2964, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4839 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4840 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4841 : Integer.Sparse Key := [(key2707, 2), (key2730, 4), (key2739, -2), (key2749, -2), (key2751, -2), (key2810, -2), (key2833, -4), (key2899, 2), (key2906, 2), (key2915, 2), (key2952, 2), (key2962, 2), (key2964, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4842 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4843 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4844 : Integer.Sparse Key := [(key1294, -6), (key1314, 2), (key1335, 4), (key1389, 6), (key1422, -2), (key1453, -4), (key1544, -2), (key1571, 2), (key1770, -4), (key1786, 4)]

def row4845 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

def row4846 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

def row4847 : Integer.Sparse Key := [(key1294, 6), (key1314, -2), (key1335, -4), (key1389, -6), (key1422, 2), (key1453, 4), (key1544, 2), (key1571, -2), (key1770, 4), (key1786, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows19_0 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4556, row4557, row4558, row4559, row4560, row4561, row4562, row4563, row4564, row4565, row4566, row4567, row4568, row4569]

def rows19_1 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4570, row4571, row4572, row4573, row4574, row4575, row4576, row4577, row4578, row4579, row4580, row4581, row4582, row4583]

def rows19_2 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4584, row4585, row4586, row4587, row4588, row4589, row4590, row4591, row4592, row4593, row4594, row4595, row4596, row4597]

def rows19_3 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4598, row4599, row4600, row4601, row4602, row4603, row4604, row4605, row4606, row4607, row4608, row4609, row4610, row4611]

def rows19_4 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4612, row4613, row4614, row4615, row4616, row4617, row4618, row4619, row4620, row4621, row4622, row4623, row4624, row4625]

def rows19_5 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4626, row4627, row4628, row4629, row4630, row4631, row4632, row4633, row4634, row4635, row4636, row4637, row4638, row4639]

def rows19_6 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4640, row4641, row4642, row4643, row4644, row4645, row4646, row4647, row4648, row4649, row4650, row4651, row4652, row4653]

def rows19_7 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4654, row4655, row4656, row4657, row4658, row4659, row4660, row4661, row4662, row4663, row4664, row4665, row4666, row4667]

def rows19_8 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4668, row4669, row4670, row4671, row4672, row4673, row4674, row4675, row4676, row4677, row4678, row4679, row4680, row4681]

def rows19_9 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4682, row4683, row4684, row4685, row4686, row4687, row4688, row4689, row4690, row4691, row4692, row4693, row4694, row4695]

def rows19_10 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4696, row4697, row4698, row4699, row4700, row4701, row4702, row4703, row4704, row4705, row4706, row4707, row4708, row4709]

def rows19_11 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4710, row4711, row4712, row4713, row4714, row4715, row4716, row4717, row4718, row4719, row4720, row4721, row4722, row4723]

def rows19_12 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4724, row4725, row4726, row4727, row4728, row4729, row4730, row4731, row4732, row4733, row4734, row4735, row4736, row4737]

def rows19_13 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4738, row4739, row4740, row4741, row4742, row4743, row4744, row4745, row4746, row4747, row4748, row4749, row4750, row4751]

def rows19_14 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4752, row4753, row4754, row4755, row4756, row4757, row4758, row4759, row4760, row4761, row4762, row4763, row4764, row4765]

def rows19_15 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4766, row4767, row4768, row4769, row4770, row4771, row4772, row4773, row4774, row4775, row4776, row4777, row4778, row4779]

def rows19_16 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4780, row4781, row4782, row4783, row4784, row4785, row4786, row4787, row4788, row4789, row4790, row4791, row4792, row4793]

def rows19_17 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4794, row4795, row4796, row4797, row4798, row4799, row4800, row4801, row4802, row4803, row4804, row4805, row4806, row4807]

def rows19_18 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4808, row4809, row4810, row4811, row4812, row4813, row4814, row4815, row4816, row4817, row4818, row4819, row4820, row4821]

def rows19_19 : Fin GramFunctions.Block1.form19.size → Integer.Sparse Key := ![row4822, row4823, row4824, row4825, row4826, row4827, row4828, row4829, row4830, row4831, row4832, row4833, row4834, row4835]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows2_0 : Fin GramFunctions.Block1.form2.size → Integer.Sparse Key := ![row688, row689, row690, row691, row692, row693, row694, row695, row696, row697, row698, row699, row700, row701, row702, row703, row704, row705, row706, row707, row708, row709, row710, row711, row712, row713, row714, row715, row716, row717]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1476 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1477 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1478 : Integer.Sparse Key := [(key2672, -2), (key2675, 2), (key2730, 2), (key2749, -4), (key2751, 2), (key2787, 2), (key2797, -2), (key2833, -2), (key2906, 4), (key2915, -2), (key2940, -2), (key2945, 2), (key2962, 2), (key2985, -2), (key3001, -2), (key3004, 2)]

def row1485 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1486 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1487 : Integer.Sparse Key := [(key2672, 2), (key2675, -2), (key2707, -2), (key2749, 4), (key2751, -2), (key2797, 2), (key2833, 2), (key2915, 2), (key2945, -2), (key2962, -2), (key2978, -4), (key2985, 2), (key2994, 2), (key3004, -2)]

def row1494 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1495 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1496 : Integer.Sparse Key := [(key1294, 2), (key1314, -6), (key1335, 4), (key1389, -2), (key1422, 2), (key1544, 6), (key1571, -2), (key1653, -4), (key1770, -4), (key1811, 4)]

def row1503 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

def row1504 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

def row1505 : Integer.Sparse Key := [(key1294, -2), (key1314, 6), (key1335, -4), (key1389, 2), (key1422, -2), (key1544, -6), (key1571, 2), (key1653, 4), (key1770, 4), (key1811, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1554 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1555 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1556 : Integer.Sparse Key := [(key998, -4), (key1006, 6), (key1019, -2), (key1041, -2), (key1076, 2), (key1111, 4), (key1127, 2), (key1155, -6), (key1193, -4), (key1212, 4)]

def row1563 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1564 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1565 : Integer.Sparse Key := [(key998, 4), (key1006, -6), (key1019, 2), (key1041, 2), (key1076, -2), (key1111, -4), (key1127, -2), (key1155, 6), (key1193, 4), (key1212, -4)]

def row1584 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1585 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1586 : Integer.Sparse Key := [(key2615, 2), (key2631, -6), (key2639, 4), (key2670, -2), (key2705, 6), (key2725, -4), (key2785, 2), (key2808, -2), (key2859, -4), (key2869, 4)]

def row1593 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1594 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1595 : Integer.Sparse Key := [(key2615, -2), (key2631, 6), (key2639, -4), (key2670, 2), (key2705, -6), (key2725, 4), (key2785, -2), (key2808, 2), (key2859, 4), (key2869, -4)]

def row1614 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1615 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1616 : Integer.Sparse Key := [(key1391, -2), (key1398, 2), (key1424, 2), (key1448, -2), (key1458, -2), (key1467, 2), (key1772, -2), (key1775, 4), (key1781, -2), (key1791, -2), (key1799, 2), (key1813, 2), (key1818, 2), (key1826, -4), (key1840, -2), (key1845, 2)]

def row1623 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1624 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1625 : Integer.Sparse Key := [(key1391, 2), (key1398, -2), (key1424, -2), (key1448, 2), (key1458, 2), (key1467, -2), (key1772, 2), (key1775, -4), (key1781, 2), (key1791, 2), (key1799, -2), (key1813, -2), (key1818, -2), (key1826, 4), (key1840, 2), (key1845, -2)]

def row1644 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1645 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1646 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2733, 2), (key2759, -2), (key2822, 4), (key2836, -6), (key2924, 2), (key3015, -4), (key3018, 6), (key3027, -2)]

def row1653 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

def row1654 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

def row1655 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, -2), (key2759, 2), (key2836, 6), (key3018, -6), (key3107, -4), (key3112, 4), (key3146, -2), (key3147, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row4866 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4867 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4868 : Integer.Sparse Key := [(key998, -4), (key1006, -2), (key1019, 6), (key1033, 4), (key1041, 2), (key1076, -6), (key1127, -2), (key1155, 2), (key1199, -4), (key1212, 4)]

def row4869 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4870 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4871 : Integer.Sparse Key := [(key998, 4), (key1006, 2), (key1019, -6), (key1033, -4), (key1041, -2), (key1076, 6), (key1127, 2), (key1155, -2), (key1199, 4), (key1212, -4)]

def row4878 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4879 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4880 : Integer.Sparse Key := [(key2615, -6), (key2631, 2), (key2639, 4), (key2670, 6), (key2705, -2), (key2725, -4), (key2785, -2), (key2793, -4), (key2808, 2), (key2828, 4)]

def row4881 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4882 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4883 : Integer.Sparse Key := [(key2615, 6), (key2631, -2), (key2639, -4), (key2670, -6), (key2705, 2), (key2725, 4), (key2785, 2), (key2793, 4), (key2808, -2), (key2828, -4)]

def row4890 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4891 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4892 : Integer.Sparse Key := [(key1546, -2), (key1560, 2), (key1573, 2), (key1597, -2), (key1660, -2), (key1668, 2), (key1772, -2), (key1775, -2), (key1781, 4), (key1788, 2), (key1791, 2), (key1799, -4), (key1818, -2), (key1826, 2), (key1842, -2), (key1845, 2)]

def row4893 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4894 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4895 : Integer.Sparse Key := [(key1546, 2), (key1560, -2), (key1573, -2), (key1597, 2), (key1660, 2), (key1668, -2), (key1772, 2), (key1775, 2), (key1781, -4), (key1788, -2), (key1791, -2), (key1799, 4), (key1818, 2), (key1826, -2), (key1842, 2), (key1845, -2)]

def row4908 : Integer.Sparse Key := [(key2693, -4), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3018, -2), (key3027, 2)]

def row4909 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

def row4910 : Integer.Sparse Key := [(key2693, -2), (key2695, 4), (key2719, 4), (key2733, -6), (key2756, -4), (key2759, 6), (key2836, 2), (key2924, -2), (key3027, 2), (key3055, -2), (key3117, -2)]

def row4911 : Integer.Sparse Key := [(key2693, 4), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3018, 2), (key3070, -4), (key3074, 4), (key3146, 2), (key3147, -2)]

def row4912 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

def row4913 : Integer.Sparse Key := [(key2693, 2), (key2695, -4), (key2733, 6), (key2759, -6), (key2836, -2), (key3055, 2), (key3070, -4), (key3074, 4), (key3117, 2), (key3146, 2), (key3147, -2)]

def row4914 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4915 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4916 : Integer.Sparse Key := [(key1296, -4), (key1303, -2), (key1316, 2), (key1337, 2), (key1340, 2), (key1391, 4), (key1398, 2), (key1424, -2), (key1455, -2), (key1458, -2), (key1546, -2), (key1573, 2), (key1772, -2), (key1775, -2), (key1788, 2), (key1791, 2)]

def row4917 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4918 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4919 : Integer.Sparse Key := [(key1296, 4), (key1303, 2), (key1316, -2), (key1337, -2), (key1340, -2), (key1391, -4), (key1398, -2), (key1424, 2), (key1455, 2), (key1458, 2), (key1546, 2), (key1573, -2), (key1772, 2), (key1775, 2), (key1788, -2), (key1791, -2)]

def row4920 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4921 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4922 : Integer.Sparse Key := [(key1296, -2), (key1316, 2), (key1391, 2), (key1424, -4), (key1448, -2), (key1455, 2), (key1467, 2), (key1546, -2), (key1573, 4), (key1597, 2), (key1655, -2), (key1668, -2), (key1788, -2), (key1799, -2), (key1813, 2), (key1826, 2)]

def row4923 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4924 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4925 : Integer.Sparse Key := [(key1296, 2), (key1316, -2), (key1391, -2), (key1424, 4), (key1448, 2), (key1455, -2), (key1467, -2), (key1546, 2), (key1573, -4), (key1597, -2), (key1655, 2), (key1668, 2), (key1788, 2), (key1799, 2), (key1813, -2), (key1826, -2)]

def row4926 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4927 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4928 : Integer.Sparse Key := [(key998, -4), (key1005, -2), (key1018, 6), (key1033, 4), (key1040, 2), (key1075, -6), (key1126, -2), (key1154, 2), (key1198, -4), (key1211, 4)]

def row4929 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4930 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4931 : Integer.Sparse Key := [(key998, 4), (key1005, 2), (key1018, -6), (key1033, -4), (key1040, -2), (key1075, 6), (key1126, 2), (key1154, -2), (key1198, 4), (key1211, -4)]

def row4932 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4933 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4934 : Integer.Sparse Key := [(key1005, -2), (key1018, 2), (key1033, -4), (key1040, 6), (key1075, -2), (key1111, 4), (key1126, -6), (key1154, 2), (key1192, -4), (key1198, 4)]

def row4935 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4936 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4937 : Integer.Sparse Key := [(key1005, 2), (key1018, -2), (key1033, 4), (key1040, -6), (key1075, 2), (key1111, -4), (key1126, 6), (key1154, -2), (key1192, 4), (key1198, -4)]

def row4938 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4939 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4940 : Integer.Sparse Key := [(key2633, -2), (key2643, -4), (key2650, 2), (key2655, 2), (key2656, 2), (key2787, 2), (key2797, 4), (key2899, -2), (key2906, -2), (key2915, -2), (key2940, -2), (key2945, -2), (key2946, -2), (key2978, 2), (key2985, 2), (key2994, 2)]

def row4941 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4942 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4943 : Integer.Sparse Key := [(key2633, 2), (key2643, 4), (key2650, -2), (key2655, -2), (key2656, -2), (key2707, -2), (key2730, 2), (key2739, -4), (key2749, 2), (key2751, 2), (key2899, 2), (key2906, 2), (key2915, 2), (key2978, -2), (key2985, -2), (key2994, -2)]

def row4944 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4945 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4946 : Integer.Sparse Key := [(key2643, -2), (key2655, 2), (key2672, -2), (key2675, 2), (key2707, 2), (key2730, -2), (key2749, -2), (key2751, 2), (key2899, -2), (key2978, 4), (key2994, -2), (key2999, -2), (key3004, 2)]

def row4947 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

def row4948 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

def row4949 : Integer.Sparse Key := [(key2643, 2), (key2655, -2), (key2672, 2), (key2675, -2), (key2730, 2), (key2749, 2), (key2787, -2), (key2899, 2), (key2906, -4), (key2915, 2), (key2946, -2), (key2994, 2), (key3004, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block1Row20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows20_0 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4836, row4837, row4838, row1476, row1477, row1478, row4839, row4840, row4841, row630, row631, row632, row1485, row1486, row1487, row639, row640, row641]

def rows20_1 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4842, row4843, row4844, row1494, row1495, row1496, row4845, row4846, row4847, row4848, row4849, row4850, row1503, row1504, row1505, row4851, row4852, row4853]

def rows20_2 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4854, row4855, row4856, row1524, row1525, row1526, row4857, row4858, row4859, row4860, row4861, row4862, row1533, row1534, row1535, row4863, row4864, row4865]

def rows20_3 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4866, row4867, row4868, row1554, row1555, row1556, row4869, row4870, row4871, row4872, row4873, row4874, row1563, row1564, row1565, row4875, row4876, row4877]

def rows20_4 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4878, row4879, row4880, row1584, row1585, row1586, row4881, row4882, row4883, row4884, row4885, row4886, row1593, row1594, row1595, row4887, row4888, row4889]

def rows20_5 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4890, row4891, row4892, row1614, row1615, row1616, row4893, row4894, row4895, row4896, row4897, row4898, row1623, row1624, row1625, row4899, row4900, row4901]

def rows20_6 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4902, row4903, row4904, row1644, row1645, row1646, row4905, row4906, row4907, row4908, row4909, row4910, row1653, row1654, row1655, row4911, row4912, row4913]

def rows20_7 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4914, row4915, row4916, row1674, row1675, row1676, row4917, row4918, row4919, row4920, row4921, row4922, row1683, row1684, row1685, row4923, row4924, row4925]

def rows20_8 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4926, row4927, row4928, row1704, row1705, row1706, row4929, row4930, row4931, row4932, row4933, row4934, row1713, row1714, row1715, row4935, row4936, row4937]

def rows20_9 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4938, row4939, row4940, row1734, row1735, row1736, row4941, row4942, row4943, row4944, row4945, row4946, row1743, row1744, row1745, row4947, row4948, row4949]

def rows20_10 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4950, row4951, row4952, row4953, row4954, row4955, row4956, row4957, row4958, row4959, row4960, row4961, row4962, row4963, row4964, row4965, row4966, row4967]

def rows20_11 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4968, row4969, row4970, row4971, row4972, row4973, row4974, row4975, row4976, row4977, row4978, row4979, row4980, row4981, row4982, row4983, row4984, row4985]

def rows20_12 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row4986, row4987, row4988, row4989, row4990, row4991, row4992, row4993, row4994, row4995, row4996, row4997, row4998, row4999, row5000, row5001, row5002, row5003]

def rows20_13 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5004, row5005, row5006, row5007, row5008, row5009, row5010, row5011, row5012, row5013, row5014, row5015, row5016, row5017, row5018, row5019, row5020, row5021]

def rows20_14 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5022, row5023, row5024, row5025, row5026, row5027, row5028, row5029, row5030, row5031, row5032, row5033, row5034, row5035, row5036, row5037, row5038, row5039]

def rows20_15 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5040, row5041, row5042, row5043, row5044, row5045, row5046, row5047, row5048, row5049, row5050, row5051, row5052, row5053, row5054, row5055, row5056, row5057]

def rows20_16 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5058, row5059, row5060, row5061, row5062, row5063, row5064, row5065, row5066, row5067, row5068, row5069, row5070, row5071, row5072, row5073, row5074, row5075]

def rows20_17 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5076, row5077, row5078, row5079, row5080, row5081, row5082, row5083, row5084, row5085, row5086, row5087, row5088, row5089, row5090, row5091, row5092, row5093]

def rows20_18 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5094, row5095, row5096, row5097, row5098, row5099, row5100, row5101, row5102, row5103, row5104, row5105, row5106, row5107, row5108, row5109, row5110, row5111]

def rows20_19 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5112, row5113, row5114, row5115, row5116, row5117, row5118, row5119, row5120, row5121, row5122, row5123, row5124, row5125, row5126, row5127, row5128, row5129]

def rows20_20 : Fin GramFunctions.Block1.form20.size → Integer.Sparse Key := ![row5130, row5131, row5132, row5133, row5134, row5135, row5136, row5137, row5138, row5139, row5140, row5141, row5142, row5143, row5144, row5145, row5146, row5147]

end MUB6.Certificate.GramEntries.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization

def entry10_8 : Integer.Sparse Key := [(key513, 2880), (key515, 8640), (key547, 2880)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row1121 : Integer.Sparse Key := [(key2717, -6), (key2755, 6), (key2820, 6), (key2921, -6), (key3014, -6), (key3024, 6)]

end MUB6.Certificate.GramRows

end OAI
end


