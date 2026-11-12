-- Prove2me | Definitions.Def_OAIQ259US003
-- name    : OAIQ259US003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:06:51.960979+00:00
-- url     : https://prove2.me/theorems/39f4acf4-902b-49d4-8b09-728b8a27822a
-- title:
--   Definitions bundle OAIQ259US003 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 310 declarations of OpenAI's Lean: 309 definitions and 1 theorem. The definitions and types are `OAI.UniversalTensorSquare.sgFlag881`, `OAI.UniversalTensorSquare.sgFlag884`, `OAI.UniversalTensorSquare.sgFlag885`, `OAI.UniversalTensorSquare.sgFlag886`, `OAI.UniversalTensorSquare.sgFlag887`, `OAI.UniversalTensorSquare.sgFlag889`, `OAI.UniversalTensorSquare.sgFlag890`, `OAI.UniversalTensorSquare.sgFlag891`, `OAI.UniversalTensorSquare.sgFlag892`, `OAI.UniversalTensorSquare.sgFlag897`, `OAI.UniversalTensorSquare.sgFlag898`, `OAI.UniversalTensorSquare.sgFlag899`, `OAI.UniversalTensorSquare.sgFlag902`, `OAI.UniversalTensorSquare.sgFlag903`, `OAI.UniversalTensorSquare.sgFlag909`, `OAI.UniversalTensorSquare.sgFlag915`, `OAI.UniversalTensorSquare.sgFlag922`, `OAI.UniversalTensorSquare.sgFlag932`, `OAI.UniversalTensorSquare.sgFlag939`, `OAI.UniversalTensorSquare.sgFlag940`, `OAI.UniversalTensorSquare.sgFlag941`, `OAI.UniversalTensorSquare.sgFlag942`, `OAI.UniversalTensorSquare.sgFlag943`, `OAI.UniversalTensorSquare.sgFlag948`, `OAI.UniversalTensorSquare.sgFlag949`, `OAI.UniversalTensorSquare.sgFlag950`, `OAI.UniversalTensorSquare.sgFlag951`, `OAI.UniversalTensorSquare.sgFlag958`, `OAI.UniversalTensorSquare.sgFlag959`, `OAI.UniversalTensorSquare.sgFlag960`, `OAI.UniversalTensorSquare.sgFlag961`, `OAI.UniversalTensorSquare.sgFlag964`, `OAI.UniversalTensorSquare.sgFlag975`, `OAI.UniversalTensorSquare.sgFlag976`, `OAI.UniversalTensorSquare.sgFlag977`, `OAI.UniversalTensorSquare.sgFlag982`, `OAI.UniversalTensorSquare.sgFlag998`, `OAI.UniversalTensorSquare.sgFlag999`, `OAI.UniversalTensorSquare.sgT1000`, `OAI.UniversalTensorSquare.sgT1001` and 269 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `UniversalSquare_Finite_ChoiceCertificates13`, `UniversalSquare_Finite_SmallContracts11_0`, `UniversalSquare_Finite_SmallContracts11_1`, `UniversalSquare_Finite_SmallContracts11_2`, `UniversalSquare_Finite_SmallContracts11_3`, `UniversalSquare_Finite_SmallContracts11_4`, `UniversalSquare_Finite_SmallContracts11_5`, `UniversalSquare_Finite_SmallContracts11_6`, `UniversalSquare_Finite_SmallContracts13_10`, `UniversalSquare_Finite_SmallContracts13_11`, `UniversalSquare_Finite_SmallContracts13_12`, `UniversalSquare_Finite_SmallContracts13_2`, `UniversalSquare_Finite_SmallContracts13_3`, `UniversalSquare_Finite_SmallContracts13_4`, `UniversalSquare_Finite_SmallContracts13_5`, `UniversalSquare_Finite_SmallContracts13_6`, `UniversalSquare_Finite_SmallContracts13_7`, `UniversalSquare_Finite_SmallContracts13_8`, `UniversalSquare_Finite_SmallContracts13_9`, `UniversalSquare_Semigroup_SemigroupLeaves1`, `UniversalSquare_Semigroup_SemigroupLeaves2`, `UniversalSquare_Semigroup_SemigroupLeaves3`, `UniversalSquare_Semigroup_SemigroupLeaves4`, `UniversalSquare_Semigroup_SemigroupLeaves5`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ259US012`; the statements `OAI.UniversalTensorSquare.smallCert13_24` and `OAI.UniversalTensorSquare.smallCert13_30`; the proofs of `OAI.UniversalTensorSquare.smallCert13_24`, `OAI.UniversalTensorSquare.smallCert13_30`, `OAI.UniversalTensorSquare.smallSupport11_0`, `OAI.UniversalTensorSquare.smallSupport11_12`, `OAI.UniversalTensorSquare.smallSupport11_13`, `OAI.UniversalTensorSquare.smallSupport11_14`, `OAI.UniversalTensorSquare.smallSupport11_15`, `OAI.UniversalTensorSquare.smallSupport11_17`, `OAI.UniversalTensorSquare.smallSupport11_18`, `OAI.UniversalTensorSquare.smallSupport11_23`, `OAI.UniversalTensorSquare.smallSupport11_25`, `OAI.UniversalTensorSquare.smallSupport11_27`, `OAI.UniversalTensorSquare.smallSupport11_4`, `OAI.UniversalTensorSquare.smallSupport11_5`, `OAI.UniversalTensorSquare.smallSupport11_6`, `OAI.UniversalTensorSquare.smallSupport11_7`, `OAI.UniversalTensorSquare.smallSupport11_9`, `OAI.UniversalTensorSquare.smallSupport13_0`, `OAI.UniversalTensorSquare.smallSupport13_1`, `OAI.UniversalTensorSquare.smallSupport13_10`, `OAI.UniversalTensorSquare.smallSupport13_11`, `OAI.UniversalTensorSquare.smallSupport13_12`, `OAI.UniversalTensorSquare.smallSupport13_13`, `OAI.UniversalTensorSquare.smallSupport13_14`, `OAI.UniversalTensorSquare.smallSupport13_15`, `OAI.UniversalTensorSquare.smallSupport13_16`, `OAI.UniversalTensorSquare.smallSupport13_17`, `OAI.UniversalTensorSquare.smallSupport13_18`, `OAI.UniversalTensorSquare.smallSupport13_19`, `OAI.UniversalTensorSquare.smallSupport13_2`, `OAI.UniversalTensorSquare.smallSupport13_20`, `OAI.UniversalTensorSquare.smallSupport13_21`, `OAI.UniversalTensorSquare.smallSupport13_22`, `OAI.UniversalTensorSquare.smallSupport13_23`, `OAI.UniversalTensorSquare.smallSupport13_24`, `OAI.UniversalTensorSquare.smallSupport13_26`, `OAI.UniversalTensorSquare.smallSupport13_27`, `OAI.UniversalTensorSquare.smallSupport13_28`, `OAI.UniversalTensorSquare.smallSupport13_29`, `OAI.UniversalTensorSquare.smallSupport13_3`, `OAI.UniversalTensorSquare.smallSupport13_30`, `OAI.UniversalTensorSquare.smallSupport13_32`, `OAI.UniversalTensorSquare.smallSupport13_33`, `OAI.UniversalTensorSquare.smallSupport13_34`, `OAI.UniversalTensorSquare.smallSupport13_35`, `OAI.UniversalTensorSquare.smallSupport13_36`, `OAI.UniversalTensorSquare.smallSupport13_40`, `OAI.UniversalTensorSquare.smallSupport13_43`, `OAI.UniversalTensorSquare.smallSupport13_44`, `OAI.UniversalTensorSquare.smallSupport13_45`, `OAI.UniversalTensorSquare.smallSupport13_47`, `OAI.UniversalTensorSquare.smallSupport13_48`, `OAI.UniversalTensorSquare.smallSupport13_49`, `OAI.UniversalTensorSquare.smallSupport13_50`, `OAI.UniversalTensorSquare.smallSupport13_9`, `OAI.UniversalTensorSquare.smallSupports11` and `OAI.UniversalTensorSquare.smallSupports13`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ259_US.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
end OAIVecLookup
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_ChoiceCertificates13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choice certificates in degree thirteen. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_0 : Equiv.Perm (Fin 13) := Equiv.swap 1 12 * (Equiv.swap 6 3 * (Equiv.swap 6 5 * (Equiv.swap 6 7 * (Equiv.swap 5 0 * (Equiv.swap 3 9 * (Equiv.swap 2 4 * (Equiv.swap 1 11 * (Equiv.swap 0 8))))))))

def smallB13_1 : Equiv.Perm (Fin 13) := Equiv.swap 9 0 * (Equiv.swap 9 6 * (Equiv.swap 7 10 * (Equiv.swap 6 11 * (Equiv.swap 3 5 * (Equiv.swap 0 12)))))

def smallB13_2 : Equiv.Perm (Fin 13) := Equiv.swap 7 12 * (Equiv.swap 7 8 * (Equiv.swap 7 5 * (Equiv.swap 8 4 * (Equiv.swap 7 3 * (Equiv.swap 5 10 * (Equiv.swap 5 6 * (Equiv.swap 4 0 * (Equiv.swap 3 9 * (Equiv.swap 1 2 * (Equiv.swap 0 11))))))))))

def smallB13_3 : Equiv.Perm (Fin 13) := Equiv.swap 11 2 * (Equiv.swap 2 8 * (Equiv.swap 8 6 * (Equiv.swap 6 3 * (Equiv.swap 1 10 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 1 4 * (Equiv.swap 0 12))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 0. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_0 : Equiv.Perm (Fin 11) := Equiv.swap 7 0 * (Equiv.swap 7 4 * (Equiv.swap 4 9 * (Equiv.swap 4 1 * (Equiv.swap 4 5 * (Equiv.swap 2 8 * (Equiv.swap 1 6 * (Equiv.swap 0 10)))))))
def smallFlag11_0 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(1,1,1),(0,1,2),(2,2,0),(0,2,1),(4,2,2),(5,3,3)}

def smallB11_1 : Equiv.Perm (Fin 11) := Equiv.swap 7 8 * (Equiv.swap 8 0 * (Equiv.swap 7 6 * (Equiv.swap 6 1 * (Equiv.swap 0 10 * (Equiv.swap 0 3 * (Equiv.swap 3 5 * (Equiv.swap 1 9 * (Equiv.swap 0 4))))))))
def smallFlag11_1 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(4,0,2),(0,0,3),(1,1,0),(3,1,2),(0,2,1),(1,2,1),(0,2,2),(0,3,1)}

def smallB11_2 : Equiv.Perm (Fin 11) := Equiv.swap 4 9 * (Equiv.swap 5 7 * (Equiv.swap 5 2 * (Equiv.swap 4 1 * (Equiv.swap 1 8 * (Equiv.swap 2 6 * (Equiv.swap 1 3 * (Equiv.swap 0 10)))))))

def smallB11_3 : Equiv.Perm (Fin 11) := Equiv.swap 1 10 * (Equiv.swap 1 9 * (Equiv.swap 1 2 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 1 6 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 8))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 1. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_4 : Equiv.Perm (Fin 11) := Equiv.swap 0 9 * (Equiv.swap 0 5 * (Equiv.swap 5 7 * (Equiv.swap 2 3 * (Equiv.swap 3 10 * (Equiv.swap 2 4 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))))

def smallB11_5 : Equiv.Perm (Fin 11) := Equiv.swap 9 2 * (Equiv.swap 4 8 * (Equiv.swap 2 5 * (Equiv.swap 5 0 * (Equiv.swap 4 7 * (Equiv.swap 2 6 * (Equiv.swap 1 3 * (Equiv.swap 0 10)))))))

def smallB11_6 : Equiv.Perm (Fin 11) := Equiv.swap 4 0 * (Equiv.swap 0 3 * (Equiv.swap 3 10 * (Equiv.swap 4 9 * (Equiv.swap 3 6 * (Equiv.swap 0 8 * (Equiv.swap 1 5 * (Equiv.swap 0 2)))))))

def smallB11_7 : Equiv.Perm (Fin 11) := Equiv.swap 0 10 * (Equiv.swap 0 9 * (Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 1 8 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 7)))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 2. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_8 : Equiv.Perm (Fin 11) := Equiv.swap 7 8 * (Equiv.swap 4 9 * (Equiv.swap 5 0 * (Equiv.swap 4 6 * (Equiv.swap 0 10 * (Equiv.swap 0 3)))))

def smallB11_9 : Equiv.Perm (Fin 11) := Equiv.swap 8 5 * (Equiv.swap 5 4 * (Equiv.swap 5 6 * (Equiv.swap 4 2 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 10 * (Equiv.swap 0 1)))))))

def smallB11_10 : Equiv.Perm (Fin 11) := Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 4 0 * (Equiv.swap 4 5 * (Equiv.swap 1 7 * (Equiv.swap 2 9 * (Equiv.swap 1 3 * (Equiv.swap 0 10)))))))
def smallFlag11_10 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(1,0,2),(1,1,0),(0,1,1),(0,1,3),(0,2,1),(0,2,2),(2,2,2),(1,3,0)}

def smallB11_11 : Equiv.Perm (Fin 11) := Equiv.swap 7 6 * (Equiv.swap 7 8 * (Equiv.swap 6 4 * (Equiv.swap 2 1 * (Equiv.swap 4 9 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 10 * (Equiv.swap 0 5))))))))
def smallFlag11_11 : Finset (ℕ × ℕ × ℕ) := {(1,0,1),(2,0,1),(0,0,2),(0,1,0),(0,1,1),(1,1,2),(0,2,0),(0,2,3),(3,3,0)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 3. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_12 : Equiv.Perm (Fin 11) := Equiv.swap 4 2 * (Equiv.swap 2 10 * (Equiv.swap 4 9 * (Equiv.swap 5 3 * (Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 8))))))))
def smallFlag11_12 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(2,0,1),(1,1,0),(3,1,2),(0,1,3),(0,2,0),(0,2,2),(0,3,0)}

def smallB11_13 : Equiv.Perm (Fin 11) := Equiv.swap 5 10 * (Equiv.swap 5 9 * (Equiv.swap 3 4 * (Equiv.swap 5 8 * (Equiv.swap 4 7 * (Equiv.swap 3 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))))
def smallFlag11_13 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,1),(0,0,2),(1,0,3),(0,1,1),(2,1,2),(0,2,0),(1,2,0),(1,3,1)}

def smallB11_14 : Equiv.Perm (Fin 11) := Equiv.swap 8 5 * (Equiv.swap 8 6 * (Equiv.swap 5 3 * (Equiv.swap 6 9 * (Equiv.swap 5 7 * (Equiv.swap 3 0 * (Equiv.swap 3 4 * (Equiv.swap 0 10)))))))
def smallFlag11_14 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(2,0,3),(0,1,0),(1,1,1),(0,1,2),(2,2,1),(0,2,2),(2,3,0)}

def smallB11_15 : Equiv.Perm (Fin 11) := Equiv.swap 3 7 * (Equiv.swap 7 2 * (Equiv.swap 7 8 * (Equiv.swap 3 9 * (Equiv.swap 3 5 * (Equiv.swap 2 10 * (Equiv.swap 0 6))))))
def smallFlag11_15 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(0,0,1),(0,0,2),(0,0,3),(1,1,1),(0,1,2),(1,2,0),(2,3,1)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 4. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_16 : Equiv.Perm (Fin 11) := Equiv.swap 7 6 * (Equiv.swap 7 0 * (Equiv.swap 6 4 * (Equiv.swap 4 9 * (Equiv.swap 3 5 * (Equiv.swap 0 8 * (Equiv.swap 0 2))))))
def smallFlag11_16 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,2),(1,1,1),(0,1,2),(1,1,3),(2,2,0),(1,2,1),(0,3,1)}

def smallB11_17 : Equiv.Perm (Fin 11) := Equiv.swap 4 0 * (Equiv.swap 4 3 * (Equiv.swap 4 7 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 1 8 * (Equiv.swap 1 2 * (Equiv.swap 0 9)))))))

def smallB11_18 : Equiv.Perm (Fin 11) := Equiv.swap 7 2 * (Equiv.swap 7 0 * (Equiv.swap 2 10 * (Equiv.swap 2 6 * (Equiv.swap 1 9 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 8)))))))

def smallB11_19 : Equiv.Perm (Fin 11) := Equiv.swap 1 6 * (Equiv.swap 6 10 * (Equiv.swap 5 0 * (Equiv.swap 0 9 * (Equiv.swap 0 3 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 5. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_20 : Equiv.Perm (Fin 11) := Equiv.swap 5 6 * (Equiv.swap 5 0 * (Equiv.swap 6 10 * (Equiv.swap 6 7 * (Equiv.swap 5 2 * (Equiv.swap 2 8 * (Equiv.swap 0 9 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))))

def smallB11_21 : Equiv.Perm (Fin 11) := Equiv.swap 1 0 * (Equiv.swap 1 8 * (Equiv.swap 1 7 * (Equiv.swap 1 6 * (Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 10))))))))

def smallB11_22 : Equiv.Perm (Fin 11) := Equiv.swap 5 3 * (Equiv.swap 4 7 * (Equiv.swap 3 8 * (Equiv.swap 0 1 * (Equiv.swap 1 10 * (Equiv.swap 0 2)))))

def smallB11_23 : Equiv.Perm (Fin 11) := Equiv.swap 7 1 * (Equiv.swap 7 9 * (Equiv.swap 7 4 * (Equiv.swap 1 10 * (Equiv.swap 4 0 * (Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 0 8)))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts11_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 11 6. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB11_24 : Equiv.Perm (Fin 11) := Equiv.swap 7 1 * (Equiv.swap 7 4 * (Equiv.swap 1 0 * (Equiv.swap 1 6 * (Equiv.swap 4 8 * (Equiv.swap 3 2 * (Equiv.swap 2 10 * (Equiv.swap 1 5 * (Equiv.swap 0 9))))))))

def smallB11_25 : Equiv.Perm (Fin 11) := Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 2 8 * (Equiv.swap 0 6)))))

def smallB11_26 : Equiv.Perm (Fin 11) := Equiv.swap 9 1 * (Equiv.swap 1 3 * (Equiv.swap 3 0 * (Equiv.swap 1 8 * (Equiv.swap 3 7 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 6 * (Equiv.swap 0 10))))))))

def smallB11_27 : Equiv.Perm (Fin 11) := Equiv.swap 1 4 * (Equiv.swap 4 6 * (Equiv.swap 6 10 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 10. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_40 : Equiv.Perm (Fin 13) := Equiv.swap 2 12 * (Equiv.swap 2 11 * (Equiv.swap 1 7 * (Equiv.swap 7 4 * (Equiv.swap 1 8 * (Equiv.swap 2 10 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 5 * (Equiv.swap 1 6 * (Equiv.swap 0 9))))))))))

def smallB13_41 : Equiv.Perm (Fin 13) := Equiv.swap 0 3 * (Equiv.swap 3 8 * (Equiv.swap 0 2 * (Equiv.swap 8 12 * (Equiv.swap 4 7 * (Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 3 1 * (Equiv.swap 2 11 * (Equiv.swap 1 10 * (Equiv.swap 0 9))))))))))

def smallB13_42 : Equiv.Perm (Fin 13) := Equiv.swap 4 6 * (Equiv.swap 4 9 * (Equiv.swap 9 11 * (Equiv.swap 4 5 * (Equiv.swap 6 2 * (Equiv.swap 5 10 * (Equiv.swap 4 7 * (Equiv.swap 1 8 * (Equiv.swap 2 12 * (Equiv.swap 1 0 * (Equiv.swap 0 3))))))))))

def smallB13_43 : Equiv.Perm (Fin 13) := Equiv.swap 9 6 * (Equiv.swap 9 7 * (Equiv.swap 9 8 * (Equiv.swap 8 2 * (Equiv.swap 7 5 * (Equiv.swap 6 3 * (Equiv.swap 5 11 * (Equiv.swap 3 12 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 10))))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 11. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_44 : Equiv.Perm (Fin 13) := Equiv.swap 8 9 * (Equiv.swap 9 3 * (Equiv.swap 8 0 * (Equiv.swap 2 1 * (Equiv.swap 2 6 * (Equiv.swap 3 12 * (Equiv.swap 2 4 * (Equiv.swap 1 11 * (Equiv.swap 0 10))))))))

def smallB13_45 : Equiv.Perm (Fin 13) := Equiv.swap 8 1 * (Equiv.swap 9 11 * (Equiv.swap 8 5 * (Equiv.swap 5 3 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 3 10 * (Equiv.swap 3 4 * (Equiv.swap 2 7 * (Equiv.swap 1 12 * (Equiv.swap 0 6))))))))))

def smallB13_46 : Equiv.Perm (Fin 13) := Equiv.swap 6 5 * (Equiv.swap 6 11 * (Equiv.swap 6 0 * (Equiv.swap 5 3 * (Equiv.swap 4 9 * (Equiv.swap 3 12 * (Equiv.swap 2 8 * (Equiv.swap 0 10 * (Equiv.swap 0 1))))))))

def smallB13_47 : Equiv.Perm (Fin 13) := Equiv.swap 5 10 * (Equiv.swap 10 0 * (Equiv.swap 0 1 * (Equiv.swap 0 7 * (Equiv.swap 5 4 * (Equiv.swap 4 11 * (Equiv.swap 1 12 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 6)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 12. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_48 : Equiv.Perm (Fin 13) := Equiv.swap 9 7 * (Equiv.swap 9 5 * (Equiv.swap 9 2 * (Equiv.swap 5 11 * (Equiv.swap 7 1 * (Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 2 0 * (Equiv.swap 1 12 * (Equiv.swap 2 4 * (Equiv.swap 1 3 * (Equiv.swap 0 10)))))))))))

def smallB13_49 : Equiv.Perm (Fin 13) := Equiv.swap 4 12 * (Equiv.swap 4 7 * (Equiv.swap 7 9 * (Equiv.swap 6 0 * (Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 11 * (Equiv.swap 0 10)))))))))

def smallB13_50 : Equiv.Perm (Fin 13) := Equiv.swap 8 2 * (Equiv.swap 9 4 * (Equiv.swap 8 0 * (Equiv.swap 0 3 * (Equiv.swap 4 10 * (Equiv.swap 3 11 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 2 12 * (Equiv.swap 1 5 * (Equiv.swap 0 7))))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 2. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_8 : Equiv.Perm (Fin 13) := Equiv.swap 7 5 * (Equiv.swap 7 6 * (Equiv.swap 5 4 * (Equiv.swap 7 10 * (Equiv.swap 6 11 * (Equiv.swap 5 9 * (Equiv.swap 4 3 * (Equiv.swap 3 12 * (Equiv.swap 2 0 * (Equiv.swap 0 8 * (Equiv.swap 0 1))))))))))

def smallB13_9 : Equiv.Perm (Fin 13) := Equiv.swap 5 8 * (Equiv.swap 8 4 * (Equiv.swap 4 0 * (Equiv.swap 4 7 * (Equiv.swap 5 1 * (Equiv.swap 4 6 * (Equiv.swap 3 11 * (Equiv.swap 1 10 * (Equiv.swap 1 2 * (Equiv.swap 0 12)))))))))

def smallB13_10 : Equiv.Perm (Fin 13) := Equiv.swap 0 6 * (Equiv.swap 6 4 * (Equiv.swap 4 12 * (Equiv.swap 0 2 * (Equiv.swap 6 10 * (Equiv.swap 5 3 * (Equiv.swap 4 8 * (Equiv.swap 3 1 * (Equiv.swap 2 11 * (Equiv.swap 1 9 * (Equiv.swap 0 7))))))))))

def smallB13_11 : Equiv.Perm (Fin 13) := Equiv.swap 11 6 * (Equiv.swap 6 3 * (Equiv.swap 8 4 * (Equiv.swap 3 1 * (Equiv.swap 6 9 * (Equiv.swap 1 2 * (Equiv.swap 4 10 * (Equiv.swap 3 7 * (Equiv.swap 2 12 * (Equiv.swap 1 5)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 3. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_12 : Equiv.Perm (Fin 13) := Equiv.swap 9 6 * (Equiv.swap 9 2 * (Equiv.swap 2 11 * (Equiv.swap 7 4 * (Equiv.swap 6 3 * (Equiv.swap 2 0 * (Equiv.swap 4 1 * (Equiv.swap 3 12 * (Equiv.swap 2 5 * (Equiv.swap 1 10 * (Equiv.swap 0 8))))))))))

def smallB13_13 : Equiv.Perm (Fin 13) := Equiv.swap 0 8 * (Equiv.swap 8 11 * (Equiv.swap 1 10 * (Equiv.swap 1 7 * (Equiv.swap 0 9 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))))

def smallB13_14 : Equiv.Perm (Fin 13) := Equiv.swap 2 12 * (Equiv.swap 7 0 * (Equiv.swap 3 1 * (Equiv.swap 3 5 * (Equiv.swap 2 8 * (Equiv.swap 1 10 * (Equiv.swap 0 9))))))

def smallB13_15 : Equiv.Perm (Fin 13) := Equiv.swap 7 2 * (Equiv.swap 2 12 * (Equiv.swap 2 10 * (Equiv.swap 2 9 * (Equiv.swap 7 11 * (Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 2 8 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 4. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_16 : Equiv.Perm (Fin 13) := Equiv.swap 3 9 * (Equiv.swap 9 11 * (Equiv.swap 3 6 * (Equiv.swap 6 5 * (Equiv.swap 6 2 * (Equiv.swap 5 0 * (Equiv.swap 3 8 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 10))))))))))

def smallB13_17 : Equiv.Perm (Fin 13) := Equiv.swap 5 9 * (Equiv.swap 5 11 * (Equiv.swap 9 3 * (Equiv.swap 3 1 * (Equiv.swap 3 0 * (Equiv.swap 5 10 * (Equiv.swap 3 6 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 12 * (Equiv.swap 0 8))))))))))

def smallB13_18 : Equiv.Perm (Fin 13) := Equiv.swap 9 1 * (Equiv.swap 1 4 * (Equiv.swap 0 3 * (Equiv.swap 0 7 * (Equiv.swap 1 8 * (Equiv.swap 4 12 * (Equiv.swap 3 2 * (Equiv.swap 2 11 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))))))))

def smallB13_19 : Equiv.Perm (Fin 13) := Equiv.swap 4 1 * (Equiv.swap 8 0 * (Equiv.swap 1 11 * (Equiv.swap 4 9 * (Equiv.swap 4 5 * (Equiv.swap 1 6 * (Equiv.swap 2 12 * (Equiv.swap 1 3 * (Equiv.swap 0 10))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 5. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_20 : Equiv.Perm (Fin 13) := Equiv.swap 9 7 * (Equiv.swap 9 5 * (Equiv.swap 5 10 * (Equiv.swap 7 3 * (Equiv.swap 5 0 * (Equiv.swap 3 12 * (Equiv.swap 2 4 * (Equiv.swap 0 8)))))))

def smallB13_21 : Equiv.Perm (Fin 13) := Equiv.swap 4 9 * (Equiv.swap 9 7 * (Equiv.swap 7 6 * (Equiv.swap 6 1 * (Equiv.swap 5 3 * (Equiv.swap 4 2 * (Equiv.swap 3 12 * (Equiv.swap 2 10 * (Equiv.swap 1 11))))))))

def smallB13_22 : Equiv.Perm (Fin 13) := Equiv.swap 7 8 * (Equiv.swap 6 3 * (Equiv.swap 0 9 * (Equiv.swap 4 12 * (Equiv.swap 3 10 * (Equiv.swap 0 5 * (Equiv.swap 1 11 * (Equiv.swap 0 2)))))))

def smallB13_23 : Equiv.Perm (Fin 13) := Equiv.swap 7 12 * (Equiv.swap 2 11 * (Equiv.swap 7 10 * (Equiv.swap 7 5 * (Equiv.swap 5 1 * (Equiv.swap 5 3 * (Equiv.swap 1 8 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 1 4 * (Equiv.swap 0 6))))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 6. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_24 : Equiv.Perm (Fin 13) := Equiv.swap 11 12 * (Equiv.swap 8 6 * (Equiv.swap 8 9 * (Equiv.swap 6 4 * (Equiv.swap 0 3 * (Equiv.swap 4 1 * (Equiv.swap 3 7 * (Equiv.swap 0 5 * (Equiv.swap 1 10 * (Equiv.swap 0 2)))))))))

def smallB13_25 : Equiv.Perm (Fin 13) := Equiv.swap 4 0 * (Equiv.swap 0 2 * (Equiv.swap 4 11 * (Equiv.swap 2 12 * (Equiv.swap 4 9 * (Equiv.swap 2 8 * (Equiv.swap 4 7 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 0 10)))))))))

def smallB13_26 : Equiv.Perm (Fin 13) := Equiv.swap 6 5 * (Equiv.swap 6 11 * (Equiv.swap 6 4 * (Equiv.swap 5 12 * (Equiv.swap 4 9 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 1 8)))))))

def smallB13_27 : Equiv.Perm (Fin 13) := Equiv.swap 10 8 * (Equiv.swap 8 7 * (Equiv.swap 7 11 * (Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 2 6 * (Equiv.swap 1 9))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 7. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_28 : Equiv.Perm (Fin 13) := Equiv.swap 6 12 * (Equiv.swap 6 0 * (Equiv.swap 0 5 * (Equiv.swap 6 4 * (Equiv.swap 6 7 * (Equiv.swap 5 3 * (Equiv.swap 4 9 * (Equiv.swap 3 11 * (Equiv.swap 2 10 * (Equiv.swap 0 8 * (Equiv.swap 0 1))))))))))

def smallB13_29 : Equiv.Perm (Fin 13) := Equiv.swap 2 7 * (Equiv.swap 0 9 * (Equiv.swap 7 4 * (Equiv.swap 0 5 * (Equiv.swap 5 3 * (Equiv.swap 4 12 * (Equiv.swap 3 8 * (Equiv.swap 2 11 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))))))

def smallB13_30 : Equiv.Perm (Fin 13) := Equiv.swap 1 12 * (Equiv.swap 8 6 * (Equiv.swap 3 11 * (Equiv.swap 6 10 * (Equiv.swap 1 4 * (Equiv.swap 4 9 * (Equiv.swap 3 7 * (Equiv.swap 1 5)))))))

def smallB13_31 : Equiv.Perm (Fin 13) := Equiv.swap 6 12 * (Equiv.swap 6 9 * (Equiv.swap 4 11 * (Equiv.swap 6 3 * (Equiv.swap 4 2 * (Equiv.swap 4 1 * (Equiv.swap 3 0 * (Equiv.swap 2 7 * (Equiv.swap 1 5 * (Equiv.swap 0 8)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 8. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_32 : Equiv.Perm (Fin 13) := Equiv.swap 10 6 * (Equiv.swap 6 11 * (Equiv.swap 5 12 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 4)))))

def smallB13_33 : Equiv.Perm (Fin 13) := Equiv.swap 9 2 * (Equiv.swap 9 10 * (Equiv.swap 3 12 * (Equiv.swap 2 1 * (Equiv.swap 3 0 * (Equiv.swap 0 7 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 1 11 * (Equiv.swap 0 4)))))))))

def smallB13_34 : Equiv.Perm (Fin 13) := Equiv.swap 8 1 * (Equiv.swap 9 11 * (Equiv.swap 8 5 * (Equiv.swap 5 3 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 3 10 * (Equiv.swap 3 4 * (Equiv.swap 2 7 * (Equiv.swap 1 12 * (Equiv.swap 0 6))))))))))

def smallB13_35 : Equiv.Perm (Fin 13) := Equiv.swap 5 12 * (Equiv.swap 8 11 * (Equiv.swap 8 6 * (Equiv.swap 5 2 * (Equiv.swap 6 9 * (Equiv.swap 5 1 * (Equiv.swap 1 7 * (Equiv.swap 2 10 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_SmallContracts13_9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Contracts 13 9. -/

section

noncomputable section
namespace UniversalTensorSquare

def smallB13_36 : Equiv.Perm (Fin 13) := Equiv.swap 7 6 * (Equiv.swap 7 3 * (Equiv.swap 1 11 * (Equiv.swap 7 9 * (Equiv.swap 6 5 * (Equiv.swap 5 2 * (Equiv.swap 3 10 * (Equiv.swap 2 12 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 1. -/

section

noncomputable section
namespace UniversalTensorSquare
def sgT17 : Equiv.Perm (Fin 4) := Equiv.swap 2 3
def sgT67 : Equiv.Perm (Fin 6) := Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 4)))
def sgT68 : Equiv.Perm (Fin 6) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4))
def sgT71 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * (Equiv.swap 3 5 * (Equiv.swap 0 4))
def sgT88 : Equiv.Perm (Fin 6) := Equiv.swap 0 2
def sgT89 : Equiv.Perm (Fin 6) := Equiv.swap 1 3 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 1 0 * (Equiv.swap 0 2))))
def sgT92 : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT157 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgT160 : Equiv.Perm (Fin 7) := Equiv.swap 5 2 * (Equiv.swap 2 3 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 0 4))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT163 : Equiv.Perm (Fin 7) := Equiv.swap 3 0 * (Equiv.swap 3 1 * (Equiv.swap 1 5 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgT165 : Equiv.Perm (Fin 7) := Equiv.swap 1 6 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 4)))
def sgT166 : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))
def sgT167 : Equiv.Perm (Fin 7) := Equiv.swap 2 0 * (Equiv.swap 2 5 * (Equiv.swap 0 6 * (Equiv.swap 2 4 * (Equiv.swap 0 3))))
def sgT168 : Equiv.Perm (Fin 7) := Equiv.swap 1 6 * (Equiv.swap 1 4)
def sgT169 : Equiv.Perm (Fin 7) := Equiv.swap 4 2 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 6 * (Equiv.swap 0 5))))
def sgT171 : Equiv.Perm (Fin 7) := Equiv.swap 0 3 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 0 4)))
def sgT174 : Equiv.Perm (Fin 7) := Equiv.swap 5 0 * (Equiv.swap 0 3 * (Equiv.swap 3 6 * (Equiv.swap 0 4)))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT194 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))
def sgT195 : Equiv.Perm (Fin 7) := Equiv.swap 5 3 * (Equiv.swap 3 6 * (Equiv.swap 3 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgT271 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4)))
def sgT275 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 0 * (Equiv.swap 0 5))))
def sgT285 : Equiv.Perm (Fin 8) := Equiv.swap 0 3 * (Equiv.swap 1 2 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgT286 : Equiv.Perm (Fin 8) := Equiv.swap 1 0 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))
def sgT287 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))
def sgT295 : Equiv.Perm (Fin 8) := Equiv.swap 6 2 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1)))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT296 : Equiv.Perm (Fin 8) := Equiv.swap 4 2 * (Equiv.swap 2 0 * (Equiv.swap 4 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgT297 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 0 6 * (Equiv.swap 2 5 * (Equiv.swap 0 3))))
def sgT300 : Equiv.Perm (Fin 8) := Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 0 6)))))
def sgT301 : Equiv.Perm (Fin 8) := Equiv.swap 6 3 * (Equiv.swap 3 4 * (Equiv.swap 4 1 * (Equiv.swap 3 5 * (Equiv.swap 1 7 * (Equiv.swap 0 2)))))
def sgT309 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 2 4 * (Equiv.swap 0 5 * (Equiv.swap 0 1)))
def sgT310 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 0 6 * (Equiv.swap 0 1))))
def sgT311 : Equiv.Perm (Fin 8) := Equiv.swap 5 0 * (Equiv.swap 5 3 * (Equiv.swap 0 7 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))))
def sgT313 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 3 * (Equiv.swap 0 7))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 2. -/

section

noncomputable section
namespace UniversalTensorSquare
def sgT314 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 3 4 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))
def sgT315 : Equiv.Perm (Fin 8) := Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgT319 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 2 5 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgT320 : Equiv.Perm (Fin 8) := Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 0 1))))
def sgT324 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 5)))))
def sgT348 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 0 1 * (Equiv.swap 0 4 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 0 3)))))
def sgT349 : Equiv.Perm (Fin 8) := Equiv.swap 5 3 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgT350 : Equiv.Perm (Fin 8) := Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT352 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 1 * (Equiv.swap 3 5 * (Equiv.swap 1 6 * (Equiv.swap 0 4))))
def sgT353 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 1 6 * (Equiv.swap 2 5 * (Equiv.swap 1 3)))
def sgT356 : Equiv.Perm (Fin 8) := Equiv.swap 1 2 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 1 5))))
def sgT357 : Equiv.Perm (Fin 8) := Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 0 * (Equiv.swap 3 6 * (Equiv.swap 0 5 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))))
def sgT358 : Equiv.Perm (Fin 8) := Equiv.swap 6 7 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 5)))
def sgT371 : Equiv.Perm (Fin 8) := Equiv.swap 3 1 * (Equiv.swap 4 7 * (Equiv.swap 3 5 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 6)))))
def sgT372 : Equiv.Perm (Fin 8) := Equiv.swap 1 3 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4)))
def sgT373 : Equiv.Perm (Fin 8) := Equiv.swap 0 6 * (Equiv.swap 0 5 * (Equiv.swap 3 7 * (Equiv.swap 0 4 * (Equiv.swap 0 2))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT377 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))
def sgT378 : Equiv.Perm (Fin 8) := Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 3 1 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))
def sgT383 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 0 2 * (Equiv.swap 2 1 * (Equiv.swap 2 3 * (Equiv.swap 1 5 * (Equiv.swap 0 4)))))
def sgT390 : Equiv.Perm (Fin 8) := Equiv.swap 0 7 * (Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 6))))
def sgT394 : Equiv.Perm (Fin 8) := Equiv.swap 6 5 * (Equiv.swap 5 2 * (Equiv.swap 2 1 * (Equiv.swap 1 7 * (Equiv.swap 0 3))))
def sgT480 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 2 * (Equiv.swap 1 7 * (Equiv.swap 3 6 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))))
def sgT481 : Equiv.Perm (Fin 9) := Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 6 * (Equiv.swap 3 0 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))
def sgT482 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT483 : Equiv.Perm (Fin 9) := Equiv.swap 6 0 * (Equiv.swap 6 3 * (Equiv.swap 3 1 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 7 * (Equiv.swap 0 8))))))
def sgT484 : Equiv.Perm (Fin 9) := Equiv.swap 1 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8 * (Equiv.swap 1 3 * (Equiv.swap 0 2))))
def sgT487 : Equiv.Perm (Fin 9) := Equiv.swap 2 5 * (Equiv.swap 2 1 * (Equiv.swap 5 8 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 3))))))
def sgT489 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 8 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 7))))
def sgT490 : Equiv.Perm (Fin 9) := Equiv.swap 7 1 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgT495 : Equiv.Perm (Fin 9) := Equiv.swap 6 8 * (Equiv.swap 6 3 * (Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 5))))))
def sgT496 : Equiv.Perm (Fin 9) := Equiv.swap 5 7 * (Equiv.swap 3 1 * (Equiv.swap 2 4 * (Equiv.swap 1 8)))
def sgT511 : Equiv.Perm (Fin 9) := Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 0 2 * (Equiv.swap 2 7 * (Equiv.swap 0 3))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT513 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 0 2 * (Equiv.swap 3 7 * (Equiv.swap 3 1 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))))
def sgT535 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 2 7 * (Equiv.swap 1 4 * (Equiv.swap 0 6))))
def sgT536 : Equiv.Perm (Fin 9) := Equiv.swap 1 4 * (Equiv.swap 4 0 * (Equiv.swap 0 8 * (Equiv.swap 0 3 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))
def sgT537 : Equiv.Perm (Fin 9) := Equiv.swap 6 7 * (Equiv.swap 1 8 * (Equiv.swap 0 2))
def sgT541 : Equiv.Perm (Fin 9) := Equiv.swap 3 8 * (Equiv.swap 3 0 * (Equiv.swap 3 1 * (Equiv.swap 3 4 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))
def sgT548 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 1 2 * (Equiv.swap 2 0 * (Equiv.swap 1 4 * (Equiv.swap 0 7))))))
def sgT549 : Equiv.Perm (Fin 9) := Equiv.swap 4 1 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 8)))
def sgT550 : Equiv.Perm (Fin 9) := Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 0 2))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 3. -/

section

noncomputable section
namespace UniversalTensorSquare
def sgT551 : Equiv.Perm (Fin 9) := Equiv.swap 3 1 * (Equiv.swap 1 0 * (Equiv.swap 2 7 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))))
def sgT552 : Equiv.Perm (Fin 9) := Equiv.swap 1 5 * (Equiv.swap 5 8 * (Equiv.swap 5 4 * (Equiv.swap 4 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgT553 : Equiv.Perm (Fin 9) := Equiv.swap 1 3 * (Equiv.swap 1 7 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 6)))))
def sgT559 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 5 0 * (Equiv.swap 1 8 * (Equiv.swap 1 4 * (Equiv.swap 1 3 * (Equiv.swap 0 7)))))
def sgT561 : Equiv.Perm (Fin 9) := Equiv.swap 6 4 * (Equiv.swap 4 0 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 8))))
def sgT562 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))
def sgT563 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 1 * (Equiv.swap 3 4 * (Equiv.swap 4 7 * (Equiv.swap 3 5 * (Equiv.swap 1 8 * (Equiv.swap 1 0 * (Equiv.swap 0 2)))))))
def sgT564 : Equiv.Perm (Fin 9) := Equiv.swap 5 1 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 1 2 * (Equiv.swap 0 6))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT565 : Equiv.Perm (Fin 9) := Equiv.swap 3 6 * (Equiv.swap 6 5 * (Equiv.swap 5 4 * (Equiv.swap 4 8 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 0 7)))))))
def sgT569 : Equiv.Perm (Fin 9) := Equiv.swap 0 1 * (Equiv.swap 0 2 * (Equiv.swap 1 7 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 5)))))
def sgT570 : Equiv.Perm (Fin 9) := Equiv.swap 5 3 * (Equiv.swap 3 0 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 0 6))))
def sgT575 : Equiv.Perm (Fin 9) := Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 0 8 * (Equiv.swap 3 6 * (Equiv.swap 2 1 * (Equiv.swap 1 5 * (Equiv.swap 0 4))))))
def sgT577 : Equiv.Perm (Fin 9) := Equiv.swap 4 0 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 0 7 * (Equiv.swap 0 1))))
def sgT578 : Equiv.Perm (Fin 9) := Equiv.swap 3 5 * (Equiv.swap 5 1 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgT579 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 6)))))
def sgT580 : Equiv.Perm (Fin 9) := Equiv.swap 6 5 * (Equiv.swap 6 7 * (Equiv.swap 5 0 * (Equiv.swap 0 2 * (Equiv.swap 2 8 * (Equiv.swap 2 3 * (Equiv.swap 0 4))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT581 : Equiv.Perm (Fin 9) := Equiv.swap 0 4 * (Equiv.swap 0 3 * (Equiv.swap 3 7 * (Equiv.swap 4 8 * (Equiv.swap 3 5 * (Equiv.swap 0 1 * (Equiv.swap 1 6 * (Equiv.swap 0 2)))))))
def sgT582 : Equiv.Perm (Fin 9) := Equiv.swap 1 3 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 5 * (Equiv.swap 1 7))))
def sgT583 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 2 6 * (Equiv.swap 1 5 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 4))))))
def sgT584 : Equiv.Perm (Fin 9) := Equiv.swap 2 6 * (Equiv.swap 6 1 * (Equiv.swap 2 0 * (Equiv.swap 2 3 * (Equiv.swap 1 8 * (Equiv.swap 0 7)))))
def sgT614 : Equiv.Perm (Fin 9) := Equiv.swap 6 2 * (Equiv.swap 6 7 * (Equiv.swap 4 5 * (Equiv.swap 2 8)))
def sgT615 : Equiv.Perm (Fin 9) := Equiv.swap 3 4 * (Equiv.swap 4 1 * (Equiv.swap 4 5 * (Equiv.swap 3 0 * (Equiv.swap 1 8 * (Equiv.swap 1 2 * (Equiv.swap 0 7))))))
def sgT616 : Equiv.Perm (Fin 9) := Equiv.swap 4 6 * (Equiv.swap 4 5 * (Equiv.swap 0 8 * (Equiv.swap 2 7 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))
def sgT621 : Equiv.Perm (Fin 9) := Equiv.swap 5 4 * (Equiv.swap 5 6 * (Equiv.swap 4 7 * (Equiv.swap 3 0 * (Equiv.swap 0 8 * (Equiv.swap 0 2 * (Equiv.swap 0 1))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT636 : Equiv.Perm (Fin 9) := Equiv.swap 2 1 * (Equiv.swap 1 0 * (Equiv.swap 3 7 * (Equiv.swap 2 5 * (Equiv.swap 1 4 * (Equiv.swap 0 8)))))
def sgT637 : Equiv.Perm (Fin 9) := Equiv.swap 3 0 * (Equiv.swap 0 8 * (Equiv.swap 3 7 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 0 6)))))
def sgT640 : Equiv.Perm (Fin 9) := Equiv.swap 6 0 * (Equiv.swap 5 7 * (Equiv.swap 0 8 * (Equiv.swap 2 3 * (Equiv.swap 0 4))))
def sgT641 : Equiv.Perm (Fin 9) := Equiv.swap 5 2 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgT759 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 6 2 * (Equiv.swap 2 8 * (Equiv.swap 4 7 * (Equiv.swap 2 5))))
def sgT765 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 0 3 * (Equiv.swap 4 6 * (Equiv.swap 3 9 * (Equiv.swap 0 5 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgT767 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 6 * (Equiv.swap 2 4 * (Equiv.swap 2 0 * (Equiv.swap 0 3)))))
def sgT768 : Equiv.Perm (Fin 10) := Equiv.swap 8 6 * (Equiv.swap 6 9 * (Equiv.swap 0 7 * (Equiv.swap 0 4 * (Equiv.swap 1 2 * (Equiv.swap 0 3)))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT790 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 4 1 * (Equiv.swap 5 7 * (Equiv.swap 4 6 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 8 * (Equiv.swap 0 9)))))))
def sgT791 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgT792 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 6 5 * (Equiv.swap 5 0 * (Equiv.swap 3 4 * (Equiv.swap 0 8 * (Equiv.swap 1 7 * (Equiv.swap 0 2))))))
def sgT796 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 4 * (Equiv.swap 5 2 * (Equiv.swap 4 3 * (Equiv.swap 3 0 * (Equiv.swap 2 7 * (Equiv.swap 0 8 * (Equiv.swap 0 1)))))))
def sgT808 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 5 7 * (Equiv.swap 3 8 * (Equiv.swap 3 1 * (Equiv.swap 2 6 * (Equiv.swap 1 4)))))
def sgT809 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 0 * (Equiv.swap 5 1 * (Equiv.swap 1 3 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 7)))))))
def sgT814 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 4 7 * (Equiv.swap 1 5 * (Equiv.swap 1 3 * (Equiv.swap 0 6))))
def sgT816 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 3 1 * (Equiv.swap 1 9 * (Equiv.swap 3 5 * (Equiv.swap 1 4 * (Equiv.swap 0 6)))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 4. -/

section

noncomputable section
namespace UniversalTensorSquare
def sgT826 : Equiv.Perm (Fin 10) := Equiv.swap 3 6 * (Equiv.swap 6 0 * (Equiv.swap 0 4 * (Equiv.swap 4 8 * (Equiv.swap 3 7 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 5)))))))
def sgT827 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 3 5 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))
def sgT828 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 0 4 * (Equiv.swap 4 1 * (Equiv.swap 3 8 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 6))))))
def sgT829 : Equiv.Perm (Fin 10) := Equiv.swap 5 3 * (Equiv.swap 0 1 * (Equiv.swap 5 7 * (Equiv.swap 3 9 * (Equiv.swap 3 4 * (Equiv.swap 0 6 * (Equiv.swap 1 8 * (Equiv.swap 0 2)))))))
def sgT832 : Equiv.Perm (Fin 10) := Equiv.swap 2 7 * (Equiv.swap 7 3 * (Equiv.swap 2 0 * (Equiv.swap 2 4 * (Equiv.swap 4 6 * (Equiv.swap 3 1 * (Equiv.swap 2 5 * (Equiv.swap 1 9 * (Equiv.swap 0 8))))))))
def sgT833 : Equiv.Perm (Fin 10) := Equiv.swap 6 3 * (Equiv.swap 6 1 * (Equiv.swap 5 9 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 7)))))))
def sgT834 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 2 * (Equiv.swap 2 9 * (Equiv.swap 4 0 * (Equiv.swap 2 5 * (Equiv.swap 0 6)))))
def sgT835 : Equiv.Perm (Fin 10) := Equiv.swap 2 6 * (Equiv.swap 6 4 * (Equiv.swap 2 1 * (Equiv.swap 4 9 * (Equiv.swap 2 5 * (Equiv.swap 2 0 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT836 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 7 0 * (Equiv.swap 5 6 * (Equiv.swap 2 9 * (Equiv.swap 0 8 * (Equiv.swap 2 4 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))))
def sgT837 : Equiv.Perm (Fin 10) := Equiv.swap 0 5 * (Equiv.swap 5 3 * (Equiv.swap 5 2 * (Equiv.swap 0 1 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 4)))))))
def sgT838 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 7 1 * (Equiv.swap 6 4 * (Equiv.swap 1 8 * (Equiv.swap 4 0 * (Equiv.swap 0 9 * (Equiv.swap 1 5 * (Equiv.swap 0 2)))))))
def sgT839 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 8 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 5 * (Equiv.swap 0 7)))))
def sgT840 : Equiv.Perm (Fin 10) := Equiv.swap 6 9 * (Equiv.swap 6 2 * (Equiv.swap 4 0 * (Equiv.swap 0 7 * (Equiv.swap 2 8 * (Equiv.swap 0 3)))))
def sgT841 : Equiv.Perm (Fin 10) := Equiv.swap 5 4 * (Equiv.swap 5 2 * (Equiv.swap 5 1 * (Equiv.swap 4 9 * (Equiv.swap 2 7 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgT846 : Equiv.Perm (Fin 10) := Equiv.swap 1 0 * (Equiv.swap 1 8 * (Equiv.swap 5 4 * (Equiv.swap 4 3 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 9)))))))
def sgT847 : Equiv.Perm (Fin 10) := Equiv.swap 2 5 * (Equiv.swap 5 9 * (Equiv.swap 2 4 * (Equiv.swap 5 3 * (Equiv.swap 4 8 * (Equiv.swap 3 7 * (Equiv.swap 2 6))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT873 : Equiv.Perm (Fin 10) := Equiv.swap 6 1 * (Equiv.swap 2 0 * (Equiv.swap 4 8 * (Equiv.swap 1 9 * (Equiv.swap 2 5 * (Equiv.swap 1 3 * (Equiv.swap 0 7))))))
def sgT874 : Equiv.Perm (Fin 10) := Equiv.swap 3 9 * (Equiv.swap 0 8 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 0 6)))))
def sgT875 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 5 * (Equiv.swap 4 7 * (Equiv.swap 5 8 * (Equiv.swap 4 0 * (Equiv.swap 0 1 * (Equiv.swap 0 3 * (Equiv.swap 1 6 * (Equiv.swap 0 2))))))))
def sgT876 : Equiv.Perm (Fin 10) := Equiv.swap 7 8 * (Equiv.swap 3 4 * (Equiv.swap 4 9 * (Equiv.swap 3 2 * (Equiv.swap 2 1 * (Equiv.swap 1 5)))))
def sgT877 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 1 * (Equiv.swap 4 5 * (Equiv.swap 3 2 * (Equiv.swap 2 6 * (Equiv.swap 1 9)))))
def sgT878 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 6 0 * (Equiv.swap 5 3 * (Equiv.swap 0 1 * (Equiv.swap 3 7 * (Equiv.swap 1 8 * (Equiv.swap 0 4))))))
def sgT879 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 4 * (Equiv.swap 4 9 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8 * (Equiv.swap 0 2))))))
def sgT880 : Equiv.Perm (Fin 10) := Equiv.swap 8 2 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 2 3 * (Equiv.swap 3 7 * (Equiv.swap 2 4 * (Equiv.swap 1 0 * (Equiv.swap 0 5)))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT881 : Equiv.Perm (Fin 10) := Equiv.swap 4 0 * (Equiv.swap 3 7 * (Equiv.swap 1 5 * (Equiv.swap 0 6)))
def sgFlag881 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(1,0,1),(6,0,1),(0,1,0),(1,1,0),(3,1,2),(5,1,3),(2,2,1),(0,3,1)}
def sgT884 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 1 * (Equiv.swap 3 0 * (Equiv.swap 2 6 * (Equiv.swap 1 7 * (Equiv.swap 0 5)))))
def sgFlag884 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(5,0,1),(2,0,2),(1,1,0),(3,1,0),(4,1,1),(0,2,3),(0,3,1)}
def sgT885 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 3 7 * (Equiv.swap 2 1 * (Equiv.swap 1 4))))
def sgFlag885 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,2),(1,1,0),(1,1,1),(3,1,1),(4,1,3),(1,2,1),(2,3,1)}
def sgT886 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 3 * (Equiv.swap 3 0 * (Equiv.swap 3 5 * (Equiv.swap 3 1 * (Equiv.swap 1 4 * (Equiv.swap 0 9))))))
def sgFlag886 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(2,0,1),(3,1,0),(0,1,1),(0,1,2),(2,2,1),(1,3,3)}
def sgT887 : Equiv.Perm (Fin 10) := Equiv.swap 0 3 * (Equiv.swap 3 1 * (Equiv.swap 0 8 * (Equiv.swap 3 2 * (Equiv.swap 2 7 * (Equiv.swap 1 9 * (Equiv.swap 0 4))))))
def sgFlag887 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,2),(0,0,3),(0,1,0),(1,1,1),(1,2,0),(2,3,1)}
def sgT889 : Equiv.Perm (Fin 10) := Equiv.swap 2 0 * (Equiv.swap 0 9 * (Equiv.swap 4 5 * (Equiv.swap 0 6 * (Equiv.swap 2 8 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgFlag889 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(7,0,2),(0,0,3),(4,0,4),(3,1,0),(0,2,0),(6,3,0),(5,4,0)}
def sgT890 : Equiv.Perm (Fin 10) := Equiv.swap 4 9 * (Equiv.swap 4 7 * (Equiv.swap 4 3 * (Equiv.swap 4 5 * (Equiv.swap 3 6 * (Equiv.swap 1 8)))))
def sgFlag890 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(4,0,1),(0,0,2),(3,0,3),(2,0,4),(1,1,0),(2,2,0),(6,3,0),(5,4,0)}
def sgT891 : Equiv.Perm (Fin 10) := Equiv.swap 1 9 * (Equiv.swap 1 3 * (Equiv.swap 1 4 * (Equiv.swap 4 7 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 1 5 * (Equiv.swap 0 8)))))))
def sgFlag891 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(4,0,1),(2,0,2),(0,0,3),(1,0,4),(5,1,0),(0,2,0),(2,3,0),(1,4,0)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT892 : Equiv.Perm (Fin 10) := Equiv.swap 8 1 * (Equiv.swap 1 4 * (Equiv.swap 5 7 * (Equiv.swap 4 2 * (Equiv.swap 1 6 * (Equiv.swap 2 9 * (Equiv.swap 1 3))))))
def sgFlag892 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,1),(3,0,2),(4,0,3),(2,0,4),(3,1,0),(4,2,0),(1,3,0),(2,4,0)}
def sgT897 : Equiv.Perm (Fin 10) := Equiv.swap 6 7 * (Equiv.swap 5 9 * (Equiv.swap 4 1 * (Equiv.swap 1 8 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 3))))))
def sgFlag897 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,0),(0,0,2),(3,0,3),(4,0,4),(2,1,0),(0,2,0),(0,3,1),(1,4,0)}
def sgT898 : Equiv.Perm (Fin 10) := Equiv.swap 5 8 * (Equiv.swap 5 7 * (Equiv.swap 5 2 * (Equiv.swap 2 1 * (Equiv.swap 2 0 * (Equiv.swap 1 6 * (Equiv.swap 0 3))))))
def sgFlag898 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(2,0,1),(1,0,2),(3,0,4),(1,1,3),(0,2,0),(1,3,0),(4,4,0)}
def sgT899 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 4 1 * (Equiv.swap 3 5 * (Equiv.swap 2 6 * (Equiv.swap 1 8 * (Equiv.swap 0 7))))))
def sgFlag899 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(3,0,0),(0,0,1),(1,0,3),(3,0,4),(0,1,0),(2,2,0),(1,3,0),(1,4,2)}
def sgT902 : Equiv.Perm (Fin 10) := Equiv.swap 2 8 * (Equiv.swap 5 7 * (Equiv.swap 4 9 * (Equiv.swap 2 6 * (Equiv.swap 2 0 * (Equiv.swap 0 3 * (Equiv.swap 0 1))))))
def sgFlag902 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(2,0,0),(1,0,1),(0,0,4),(3,1,0),(0,2,3),(0,3,0),(1,4,2)}
def sgT903 : Equiv.Perm (Fin 10) := Equiv.swap 3 2 * (Equiv.swap 3 1 * (Equiv.swap 3 7 * (Equiv.swap 2 9 * (Equiv.swap 3 6 * (Equiv.swap 2 5 * (Equiv.swap 1 8 * (Equiv.swap 0 4)))))))
def sgFlag903 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,0),(1,0,1),(0,0,3),(0,1,0),(2,2,0),(0,3,4),(0,4,2)}
def sgT909 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 4 7 * (Equiv.swap 5 1 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 2 3 * (Equiv.swap 1 8))))))
def sgFlag909 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(1,0,1),(0,1,4),(1,2,2),(0,3,3),(0,4,0)}
def sgT915 : Equiv.Perm (Fin 10) := Equiv.swap 5 9 * (Equiv.swap 5 3 * (Equiv.swap 5 1 * (Equiv.swap 5 4 * (Equiv.swap 4 6 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 8))))))))
def sgFlag915 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(3,0,1),(4,0,2),(2,1,0),(1,1,4),(2,2,0),(0,3,0),(1,4,3)}

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLeaves5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Leaves 5. -/

section

noncomputable section
namespace UniversalTensorSquare
def sgT922 : Equiv.Perm (Fin 10) := Equiv.swap 5 0 * (Equiv.swap 4 2 * (Equiv.swap 5 7 * (Equiv.swap 4 6 * (Equiv.swap 0 1 * (Equiv.swap 2 9 * (Equiv.swap 1 8 * (Equiv.swap 0 3)))))))
def sgFlag922 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(3,0,1),(0,0,3),(0,1,0),(2,1,0),(1,2,4),(1,3,2),(2,4,0)}
def sgT932 : Equiv.Perm (Fin 10) := Equiv.swap 4 6 * (Equiv.swap 6 0 * (Equiv.swap 6 1 * (Equiv.swap 1 7 * (Equiv.swap 4 8 * (Equiv.swap 0 2 * (Equiv.swap 2 9 * (Equiv.swap 1 5 * (Equiv.swap 0 3))))))))
def sgFlag932 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,1),(1,0,3),(1,1,2),(2,1,4),(1,2,0),(2,3,0),(0,4,0)}
def sgT939 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 1 7 * (Equiv.swap 0 9 * (Equiv.swap 2 6 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))
def sgFlag939 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(1,0,3),(0,1,0),(0,2,1),(1,3,4),(1,4,2)}
def sgT940 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 2 3 * (Equiv.swap 3 8 * (Equiv.swap 2 6 * (Equiv.swap 3 5 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 9)))))))
def sgFlag940 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(6,0,0),(2,0,1),(0,0,2),(7,0,2),(0,1,0),(4,1,3),(3,2,0),(1,2,1),(5,3,0)}
def sgT941 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 5 9 * (Equiv.swap 5 6 * (Equiv.swap 3 8 * (Equiv.swap 3 2 * (Equiv.swap 2 4)))))
def sgFlag941 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(5,0,1),(3,0,2),(0,0,3),(1,1,0),(6,1,1),(2,2,0),(4,2,2),(2,3,0)}
def sgT942 : Equiv.Perm (Fin 10) := Equiv.swap 4 5 * (Equiv.swap 5 9 * (Equiv.swap 4 6 * (Equiv.swap 1 3 * (Equiv.swap 1 2 * (Equiv.swap 0 8)))))
def sgFlag942 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(1,0,2),(2,0,2),(3,1,0),(2,1,3),(3,2,0),(5,2,1),(1,3,0)}
def sgT943 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 6 3 * (Equiv.swap 3 2 * (Equiv.swap 3 0 * (Equiv.swap 2 8 * (Equiv.swap 1 4 * (Equiv.swap 0 5))))))
def sgFlag943 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(2,0,1),(0,0,2),(4,0,2),(4,1,0),(2,1,3),(3,2,0),(0,3,1)}
def sgT948 : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * (Equiv.swap 0 3 * (Equiv.swap 3 8 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))
def sgFlag948 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(2,0,0),(1,0,1),(0,0,2),(1,1,0),(5,1,3),(3,2,0),(1,2,1),(4,3,2)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT949 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 5 * (Equiv.swap 0 1 * (Equiv.swap 5 3 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 6))))))))
def sgFlag949 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(0,0,1),(1,0,1),(2,0,2),(2,1,0),(3,1,2),(1,2,0),(4,3,3)}
def sgT950 : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * (Equiv.swap 1 7 * (Equiv.swap 3 0 * (Equiv.swap 1 4 * (Equiv.swap 0 8))))
def sgFlag950 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(3,0,0),(0,0,1),(3,0,1),(2,1,0),(0,1,2),(2,2,0),(1,2,3),(0,3,2)}
def sgT951 : Equiv.Perm (Fin 10) := Equiv.swap 0 7 * (Equiv.swap 7 9 * (Equiv.swap 0 1 * (Equiv.swap 0 6 * (Equiv.swap 0 5 * (Equiv.swap 1 8 * (Equiv.swap 0 3))))))
def sgFlag951 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(3,0,0),(0,0,1),(2,0,2),(1,1,0),(2,1,3),(2,2,0),(1,2,2),(1,3,1)}
def sgT958 : Equiv.Perm (Fin 10) := Equiv.swap 6 5 * (Equiv.swap 5 4 * (Equiv.swap 6 8 * (Equiv.swap 5 7 * (Equiv.swap 4 9 * (Equiv.swap 0 3)))))
def sgFlag958 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(5,0,1),(3,0,2),(6,0,3),(1,1,0),(4,1,0),(7,1,1),(2,2,0),(0,3,0)}
def sgT959 : Equiv.Perm (Fin 10) := Equiv.swap 8 0 * (Equiv.swap 0 2 * (Equiv.swap 3 6 * (Equiv.swap 3 5 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 7)))))))
def sgFlag959 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(0,0,1),(3,0,2),(5,0,3),(2,1,0),(6,1,0),(2,1,1),(1,2,0),(4,3,0)}
def sgT960 : Equiv.Perm (Fin 10) := Equiv.swap 7 2 * (Equiv.swap 3 5 * (Equiv.swap 5 8 * (Equiv.swap 3 0 * (Equiv.swap 2 9 * (Equiv.swap 0 6 * (Equiv.swap 0 1))))))
def sgFlag960 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(5,0,0),(3,0,1),(1,0,2),(4,0,3),(0,1,0),(2,1,1),(3,2,0),(0,3,0)}
def sgT961 : Equiv.Perm (Fin 10) := Equiv.swap 8 5 * (Equiv.swap 5 2 * (Equiv.swap 5 0 * (Equiv.swap 5 6 * (Equiv.swap 0 1 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 3)))))))
def sgFlag961 : Finset (ℕ × ℕ × ℕ) := {(3,0,0),(0,0,1),(4,0,1),(0,0,3),(1,1,0),(2,1,0),(2,1,1),(4,2,2),(1,3,0)}
def sgT964 : Equiv.Perm (Fin 10) := Equiv.swap 0 6 * (Equiv.swap 6 5 * (Equiv.swap 6 1 * (Equiv.swap 5 2 * (Equiv.swap 2 9 * (Equiv.swap 1 7 * (Equiv.swap 0 8))))))
def sgFlag964 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(1,0,0),(0,0,1),(4,0,2),(2,1,0),(5,1,1),(1,1,3),(1,2,0),(3,3,1)}

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT975 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 5 8 * (Equiv.swap 4 3 * (Equiv.swap 3 7 * (Equiv.swap 1 9 * (Equiv.swap 0 2)))))
def sgFlag975 : Finset (ℕ × ℕ × ℕ) := {(2,0,0),(4,0,0),(0,0,1),(6,0,1),(5,0,2),(1,1,0),(2,1,0),(3,1,1),(0,2,0),(1,2,2)}
def sgT976 : Equiv.Perm (Fin 10) := Equiv.swap 8 7 * (Equiv.swap 7 1 * (Equiv.swap 1 4 * (Equiv.swap 1 2 * (Equiv.swap 4 9 * (Equiv.swap 1 0 * (Equiv.swap 2 6 * (Equiv.swap 1 3 * (Equiv.swap 0 5))))))))
def sgFlag976 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(1,0,1),(5,0,1),(2,0,2),(3,1,0),(1,1,1),(0,2,0),(2,2,2)}
def sgT977 : Equiv.Perm (Fin 10) := Equiv.swap 7 3 * (Equiv.swap 3 9 * (Equiv.swap 0 4 * (Equiv.swap 4 2 * (Equiv.swap 3 6 * (Equiv.swap 2 8 * (Equiv.swap 0 5 * (Equiv.swap 0 1)))))))
def sgFlag977 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,0),(2,0,1),(1,0,2),(2,1,0),(0,1,1),(3,1,1),(3,2,0),(4,2,0)}
def sgT982 : Equiv.Perm (Fin 10) := Equiv.swap 1 7 * (Equiv.swap 7 9 * (Equiv.swap 3 6 * (Equiv.swap 3 4 * (Equiv.swap 1 8 * (Equiv.swap 0 5)))))
def sgFlag982 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(4,0,1),(1,0,2),(3,1,0),(1,1,1),(2,1,1),(2,2,0)}
def sgT998 : Equiv.Perm (Fin 10) := Equiv.swap 8 9 * (Equiv.swap 3 7 * (Equiv.swap 3 6 * (Equiv.swap 3 2 * (Equiv.swap 2 0 * (Equiv.swap 0 4 * (Equiv.swap 0 1))))))
def sgFlag998 : Finset (ℕ × ℕ × ℕ) := {(1,0,0),(7,0,0),(3,0,1),(0,0,2),(1,0,3),(5,0,4),(4,1,0),(0,2,0),(2,3,0),(6,4,0)}
def sgT999 : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * (Equiv.swap 6 1 * (Equiv.swap 5 7 * (Equiv.swap 2 4 * (Equiv.swap 1 8))))
def sgFlag999 : Finset (ℕ × ℕ × ℕ) := {(0,0,0),(5,0,0),(0,0,1),(6,0,2),(1,0,3),(2,0,4),(1,1,0),(4,2,0),(3,3,0),(2,4,0)}
def sgT1000 : Equiv.Perm (Fin 10) := Equiv.swap 7 5 * (Equiv.swap 0 2 * (Equiv.swap 5 4 * (Equiv.swap 4 9 * (Equiv.swap 0 6 * (Equiv.swap 2 8 * (Equiv.swap 0 3 * (Equiv.swap 0 1)))))))
def sgT1001 : Equiv.Perm (Fin 10) := Equiv.swap 4 3 * (Equiv.swap 6 7 * (Equiv.swap 3 9 * (Equiv.swap 4 8 * (Equiv.swap 3 1 * (Equiv.swap 1 0 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT1006 : Equiv.Perm (Fin 10) := Equiv.swap 1 0 * (Equiv.swap 1 8 * (Equiv.swap 1 7 * (Equiv.swap 1 4 * (Equiv.swap 4 6 * (Equiv.swap 0 9 * (Equiv.swap 0 3 * (Equiv.swap 1 5 * (Equiv.swap 0 2))))))))
def sgT1007 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 4 9 * (Equiv.swap 4 1 * (Equiv.swap 3 2 * (Equiv.swap 2 8 * (Equiv.swap 1 0 * (Equiv.swap 0 6))))))
def sgT1008 : Equiv.Perm (Fin 10) := Equiv.swap 0 4 * (Equiv.swap 6 9 * (Equiv.swap 0 3 * (Equiv.swap 4 8 * (Equiv.swap 3 1 * (Equiv.swap 1 7 * (Equiv.swap 1 2 * (Equiv.swap 0 5)))))))
def sgT1015 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 7 0 * (Equiv.swap 0 8 * (Equiv.swap 3 6 * (Equiv.swap 2 4 * (Equiv.swap 0 5)))))
def sgT1016 : Equiv.Perm (Fin 10) := Equiv.swap 7 6 * (Equiv.swap 6 3 * (Equiv.swap 5 0 * (Equiv.swap 3 2 * (Equiv.swap 3 4 * (Equiv.swap 2 1 * (Equiv.swap 1 9 * (Equiv.swap 0 8)))))))
def sgT1023 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 5 8 * (Equiv.swap 5 6 * (Equiv.swap 3 4 * (Equiv.swap 2 7))))
def sgT1032 : Equiv.Perm (Fin 10) := Equiv.swap 1 3 * (Equiv.swap 3 9 * (Equiv.swap 5 8 * (Equiv.swap 3 0 * (Equiv.swap 1 7 * (Equiv.swap 0 6)))))
def sgT1033 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 4 9 * (Equiv.swap 2 8 * (Equiv.swap 4 6 * (Equiv.swap 1 7 * (Equiv.swap 2 5 * (Equiv.swap 1 0 * (Equiv.swap 0 3)))))))

end UniversalTensorSquare
end
end

section

noncomputable section
namespace UniversalTensorSquare
def sgT1038 : Equiv.Perm (Fin 10) := Equiv.swap 2 4 * (Equiv.swap 0 8 * (Equiv.swap 2 7 * (Equiv.swap 4 1 * (Equiv.swap 2 5 * (Equiv.swap 2 3 * (Equiv.swap 1 9 * (Equiv.swap 0 6)))))))
def sgT1040 : Equiv.Perm (Fin 10) := Equiv.swap 4 1 * (Equiv.swap 5 8 * (Equiv.swap 5 2 * (Equiv.swap 4 7 * (Equiv.swap 1 9 * (Equiv.swap 2 0 * (Equiv.swap 1 3 * (Equiv.swap 0 6)))))))
def sgT1063 : Equiv.Perm (Fin 10) := Equiv.swap 7 4 * (Equiv.swap 3 9 * (Equiv.swap 4 8 * (Equiv.swap 3 0 * (Equiv.swap 0 6 * (Equiv.swap 0 1)))))
def sgT1064 : Equiv.Perm (Fin 10) := Equiv.swap 7 9 * (Equiv.swap 5 8 * (Equiv.swap 4 2 * (Equiv.swap 2 6 * (Equiv.swap 0 3))))
def sgT1065 : Equiv.Perm (Fin 10) := Equiv.swap 2 9 * (Equiv.swap 2 8 * (Equiv.swap 2 7 * (Equiv.swap 2 0 * (Equiv.swap 0 6 * (Equiv.swap 2 1 * (Equiv.swap 1 4 * (Equiv.swap 0 3)))))))

end UniversalTensorSquare
end
end

end OAI
end


