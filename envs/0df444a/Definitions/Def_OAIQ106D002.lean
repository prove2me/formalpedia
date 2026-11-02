-- Prove2me | Definitions.Def_OAIQ106D002
-- name    : OAIQ106D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T11:55:19.235256+00:00
-- url     : https://prove2.me/theorems/f6f93eb8-1df9-4403-990a-18895824f899
-- title:
--   Definitions bundle OAIQ106D002 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4430 declarations of OpenAI's Lean: 4423 definitions, 2 inductive types or structures and 5 theorems. The definitions and types are `OAI.MUB6.Certificate.GramFunctions.Block0.decimalExponent`, `OAI.MUB6.Certificate.GramFunctions.Block1.decimalExponent`, `OAI.MUB6.Certificate.GramFunctions.Block2.decimalExponent`, `OAI.MUB6.Certificate.GramFunctions.Block3.decimalExponent`, `OAI.MUB6.Certificate.GramFunctions.Block4.decimalExponent`, `OAI.MUB6.Certificate.GramFunctions.Block5.decimalExponent`, `OAI.MUB6.Certificate.GramPolynomial.compareRows`, `OAI.MUB6.Certificate.Integer.Combination`, `OAI.MUB6.Certificate.MixedData.expr2424`, `OAI.MUB6.Certificate.MixedData.expr2425`, `OAI.MUB6.Certificate.MixedData.expr2426`, `OAI.MUB6.Certificate.MixedData.expr2427`, `OAI.MUB6.Certificate.MixedData.expr2428`, `OAI.MUB6.Certificate.MixedData.expr2429`, `OAI.MUB6.Certificate.MixedData.expr2430`, `OAI.MUB6.Certificate.MixedData.expr2431`, `OAI.MUB6.Certificate.MixedData.expr2432`, `OAI.MUB6.Certificate.MixedData.expr2433`, `OAI.MUB6.Certificate.MixedData.expr2434`, `OAI.MUB6.Certificate.MixedData.expr2435`, `OAI.MUB6.Certificate.MixedData.expr2436`, `OAI.MUB6.Certificate.MixedData.expr2437`, `OAI.MUB6.Certificate.MixedData.expr2438`, `OAI.MUB6.Certificate.MixedData.expr2439`, `OAI.MUB6.Certificate.MixedData.expr2440`, `OAI.MUB6.Certificate.MixedData.expr2441`, `OAI.MUB6.Certificate.MixedData.expr2442`, `OAI.MUB6.Certificate.MixedData.expr2443`, `OAI.MUB6.Certificate.MixedData.expr2444`, `OAI.MUB6.Certificate.MixedData.expr2445`, `OAI.MUB6.Certificate.MixedData.expr2446`, `OAI.MUB6.Certificate.MixedData.expr2447`, `OAI.MUB6.Certificate.MixedData.expr2448`, `OAI.MUB6.Certificate.MixedData.expr2449`, `OAI.MUB6.Certificate.MixedData.expr2450`, `OAI.MUB6.Certificate.MixedData.expr2451`, `OAI.MUB6.Certificate.MixedData.expr2452`, `OAI.MUB6.Certificate.MixedData.rawCombination`, `OAI.MUB6.Certificate.MixedData.residualCombination`, `OAI.MUB6.Certificate.MixedData.targetCombination` and 4385 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_Algebra`, `MutuallyUnbiased_Certificate_Gram`, `MutuallyUnbiased_Certificate_GramPolynomial`, `MutuallyUnbiased_Certificate_Integer`, `MutuallyUnbiased_GramFunctions_Block0`, `MutuallyUnbiased_GramFunctions_Block1`, `MutuallyUnbiased_GramFunctions_Block2`, `MutuallyUnbiased_GramFunctions_Block3`, `MutuallyUnbiased_GramFunctions_Block4`, `MutuallyUnbiased_GramFunctions_Block5`, `MutuallyUnbiased_MixedData_Expression`, `MutuallyUnbiased_MixedMerge_Block75`, `MutuallyUnbiased_MixedMerge_Block76`, `MutuallyUnbiased_MixedSemantics_Code`, `MutuallyUnbiased_MixedSemantics_Nodes0`, `MutuallyUnbiased_MixedSemantics_Nodes1`, `MutuallyUnbiased_MixedSemantics_Nodes10`, `MutuallyUnbiased_MixedSemantics_Nodes11`, `MutuallyUnbiased_MixedSemantics_Nodes12`, `MutuallyUnbiased_MixedSemantics_Nodes13`, `MutuallyUnbiased_MixedSemantics_Nodes14`, `MutuallyUnbiased_MixedSemantics_Nodes15`, `MutuallyUnbiased_MixedSemantics_Nodes16`, `MutuallyUnbiased_MixedSemantics_Nodes17`, `MutuallyUnbiased_MixedSemantics_Nodes18`, `MutuallyUnbiased_MixedSemantics_Nodes19`, `MutuallyUnbiased_MixedSemantics_Nodes2`, `MutuallyUnbiased_MixedSemantics_Nodes20`, `MutuallyUnbiased_MixedSemantics_Nodes21`, `MutuallyUnbiased_MixedSemantics_Nodes22`, `MutuallyUnbiased_MixedSemantics_Nodes23`, `MutuallyUnbiased_MixedSemantics_Nodes24`, `MutuallyUnbiased_MixedSemantics_Nodes25`, `MutuallyUnbiased_MixedSemantics_Nodes26`, `MutuallyUnbiased_MixedSemantics_Nodes27`, `MutuallyUnbiased_MixedSemantics_Nodes28`, `MutuallyUnbiased_MixedSemantics_Nodes29`, `MutuallyUnbiased_MixedSemantics_Nodes3`, `MutuallyUnbiased_MixedSemantics_Nodes30`, `MutuallyUnbiased_MixedSemantics_Nodes31`, `MutuallyUnbiased_MixedSemantics_Nodes32`, `MutuallyUnbiased_MixedSemantics_Nodes33`, `MutuallyUnbiased_MixedSemantics_Nodes34`, `MutuallyUnbiased_MixedSemantics_Nodes35`, `MutuallyUnbiased_MixedSemantics_Nodes36`, `MutuallyUnbiased_MixedSemantics_Nodes37`, `MutuallyUnbiased_MixedSemantics_Nodes38`, `MutuallyUnbiased_MixedSemantics_Nodes39`, `MutuallyUnbiased_MixedSemantics_Nodes40`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D071`, `OAIQ106D072`, `OAIQ106D073`, `OAIQ106D074`, `OAIQ106D075`, `OAIQ106D079`, `OAIQ106D080`, `OAIQ106D082`, `OAIQ106D083`, `OAIQ106D084`, `OAIQ106D085`, `OAIQ106D086`, `OAIQ106D087`, `OAIQ106D088`, `OAIQ106D089`, `OAIQ106D090`, `OAIQ106D091`, `OAIQ106D092`, `OAIQ106D093`, `OAIQ106D094`, `OAIQ106D095`, `OAIQ106D097`, `OAIQ106D098`, `OAIQ106D099`, `OAIQ106D100`, `OAIQ106D101`, `OAIQ106D102`, `OAIQ106D103`, `OAIQ106D106`, `OAIQ106D107`, `OAIQ106D108`, `OAIQ106D110`, `OAIQ106D112`, `OAIQ106D113`, `OAIQ106D114`, `OAIQ106D115`, `OAIQ106D116`, `OAIQ106D118`, `OAIQ106D124`, `OAIQ106D125`, `OAIQ106D126`, `OAIQ106D127`, `OAIQ106D128`, `OAIQ106D130`, `OAIQ106D131`, `OAIQ106D132`, `OAIQ106D133`, `OAIQ106D134`, `OAIQ106D135`, `OAIQ106D136`, `OAIQ106D137`, `OAIQ106D138`, `OAIQ106D139`, `OAIQ106D140` and `OAIQ106D267`; the statement `OAI.MUB6.Certificate.GramData.Block4.positiveDefinite`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact-certificate algebra

These lemmas interpret finite rational coefficient lists over real moment vectors.
They do not assert that any particular list is a true Hadamard or MUB relation.
Such relations must be proved from the mathematical moment definitions.
-/
namespace MUB6.Certificate

open scoped BigOperators

abbrev Sparse (ι : Type*) := List (ι × ℚ)

namespace Sparse

variable {ι : Type*}

/-- Evaluate a sparse rational linear form on a real vector. Repeated keys add. -/
noncomputable def eval (v : Sparse ι) (x : ι → ℝ) : ℝ :=
  (v.map fun p => (p.2 : ℝ) * x p.1).sum

/-- The exact coefficient at one key, including all repeated occurrences. -/
def coeff [DecidableEq ι] (v : Sparse ι) (i : ι) : ℚ :=
  (v.map fun p => if p.1 = i then p.2 else 0).sum

@[simp] theorem eval_nil (x : ι → ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (p : ι × ℚ) (v : Sparse ι) (x : ι → ℝ) :
    eval (p :: v) x = (p.2 : ℝ) * x p.1 + eval v x := rfl

@[simp] theorem eval_append (v w : Sparse ι) (x : ι → ℝ) :
    eval (v ++ w) x = eval v x + eval w x := by
  simp [eval]

@[simp] theorem coeff_nil [DecidableEq ι] (i : ι) : coeff [] i = 0 := rfl

@[simp] theorem coeff_cons [DecidableEq ι] (p : ι × ℚ) (v : Sparse ι) (i : ι) :
    coeff (p :: v) i = (if p.1 = i then p.2 else 0) + coeff v i := rfl

end Sparse

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact rational Gram witnesses

A unit lower triangular matrix and a positive rational diagonal certify a real
matrix's positive definiteness. The large numerical checks can therefore be
split into separate rational identities for individual matrix entries.
-/
namespace MUB6.Certificate

open Matrix
open scoped BigOperators

/-- Interpret a rational matrix as a real matrix. -/
def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => A i j

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Integer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer coefficient checking after denominator clearing. The arithmetic
checker uses only integer operations; its interpretation remains over arbitrary
real moment vectors. -/
namespace MUB6.Certificate.Integer

open scoped BigOperators

inductive Combination (κ : Type*) where
  | leaf : κ → Combination κ
  | add : Combination κ → Combination κ → Combination κ
  | scale : ℤ → Combination κ → Combination κ

end MUB6.Certificate.Integer

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite auxiliary Gram products interpreted as sparse normalized keys. -/
namespace MUB6.Certificate.GramPolynomial

open scoped BigOperators

def compareRows : List (ℤ × ℤ) → List (ℤ × ℤ) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
      (compare a.1 b.1).then ((compare a.2 b.2).then (compareRows as bs))

end MUB6.Certificate.GramPolynomial

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

def decimalExponent : ℕ := 14

end MUB6.Certificate.GramFunctions.Block0

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

def decimalExponent : ℕ := 13

end MUB6.Certificate.GramFunctions.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block2

def decimalExponent : ℕ := 13

end MUB6.Certificate.GramFunctions.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block3

def decimalExponent : ℕ := 14

end MUB6.Certificate.GramFunctions.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block4

def decimalExponent : ℕ := 14

end MUB6.Certificate.GramFunctions.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramFunctions_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramFunctions.Block5

def decimalExponent : ℕ := 15

end MUB6.Certificate.GramFunctions.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Expression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def rawCombination : Integer.Combination (Fin 29) := (.add (.add (.add (.add (.leaf 0) (.leaf 1)) (.add (.leaf 2) (.add (.leaf 3) (.leaf 4)))) (.add (.add (.leaf 5) (.add (.leaf 6) (.leaf 7))) (.add (.leaf 8) (.add (.leaf 9) (.leaf 10))))) (.add (.add (.add (.leaf 11) (.add (.leaf 12) (.leaf 13))) (.add (.leaf 14) (.add (.leaf 15) (.leaf 16)))) (.add (.add (.leaf 17) (.add (.leaf 18) (.leaf 19))) (.add (.leaf 20) (.add (.leaf 21) (.leaf 22))))))

def residualCombination : Integer.Combination (Fin 29) := (.add (.add (.leaf 23) (.add (.leaf 24) (.leaf 25))) (.add (.leaf 26) (.add (.leaf 27) (.leaf 28))))

def targetCombination : Integer.Combination (Fin 29) := .add rawCombination (.scale (-1) residualCombination)

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def expr2424 : Integer.Combination (Fin 29) := .add (.leaf 0) (.leaf 1)

def expr2425 : Integer.Combination (Fin 29) := .add (.leaf 3) (.leaf 4)

def expr2426 : Integer.Combination (Fin 29) := .add (.leaf 2) expr2425

def expr2427 : Integer.Combination (Fin 29) := .add expr2424 expr2426

def expr2428 : Integer.Combination (Fin 29) := .add (.leaf 6) (.leaf 7)

def expr2429 : Integer.Combination (Fin 29) := .add (.leaf 5) expr2428

def expr2430 : Integer.Combination (Fin 29) := .add (.leaf 9) (.leaf 10)

def expr2431 : Integer.Combination (Fin 29) := .add (.leaf 8) expr2430

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

def expr2432 : Integer.Combination (Fin 29) := .add expr2429 expr2431

def expr2433 : Integer.Combination (Fin 29) := .add expr2427 expr2432

def expr2434 : Integer.Combination (Fin 29) := .add (.leaf 12) (.leaf 13)

def expr2435 : Integer.Combination (Fin 29) := .add (.leaf 11) expr2434

def expr2436 : Integer.Combination (Fin 29) := .add (.leaf 15) (.leaf 16)

def expr2437 : Integer.Combination (Fin 29) := .add (.leaf 14) expr2436

def expr2438 : Integer.Combination (Fin 29) := .add expr2435 expr2437

def expr2439 : Integer.Combination (Fin 29) := .add (.leaf 18) (.leaf 19)

def expr2440 : Integer.Combination (Fin 29) := .add (.leaf 17) expr2439

def expr2441 : Integer.Combination (Fin 29) := .add (.leaf 21) (.leaf 22)

def expr2442 : Integer.Combination (Fin 29) := .add (.leaf 20) expr2441

def expr2443 : Integer.Combination (Fin 29) := .add expr2440 expr2442

def expr2444 : Integer.Combination (Fin 29) := .add expr2438 expr2443

def expr2445 : Integer.Combination (Fin 29) := .add expr2433 expr2444

def expr2446 : Integer.Combination (Fin 29) := .add (.leaf 24) (.leaf 25)

def expr2447 : Integer.Combination (Fin 29) := .add (.leaf 23) expr2446

def expr2448 : Integer.Combination (Fin 29) := .add (.leaf 27) (.leaf 28)

def expr2449 : Integer.Combination (Fin 29) := .add (.leaf 26) expr2448

def expr2450 : Integer.Combination (Fin 29) := .add expr2447 expr2449

def expr2451 : Integer.Combination (Fin 29) := .scale (-1) expr2450

def expr2452 : Integer.Combination (Fin 29) := .add expr2445 expr2451

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Code
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

/-- A finite integer mixed-moment descriptor, retaining every index size. -/
structure Code where
  rows : ℕ
  factors : ℕ
  labels : ℕ
  matrix : Matrix (Fin rows) (Fin factors) ℤ
  label : Fin factors → Fin labels

/-- Pair coordinates and all elementary mixed nodes share one ambient space.
The numerical certificate is reindexed into this space separately. -/
abbrev Master := Fin 909 ⊕ Fin 5502

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node0 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def node0Labels : Fin 2 → Fin 1 := ![0, 0]

def node1 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def node1Labels : Fin 2 → Fin 1 := ![0, 0]

def node2 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def node2Labels : Fin 2 → Fin 1 := ![0, 0]

def node3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def node3Labels : Fin 2 → Fin 1 := ![0, 0]

def node4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def node4Labels : Fin 2 → Fin 1 := ![0, 0]

def node5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def node5Labels : Fin 2 → Fin 1 := ![0, 0]

def node6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def node6Labels : Fin 2 → Fin 1 := ![0, 0]

def node7 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def node7Labels : Fin 2 → Fin 1 := ![0, 0]

def node8 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node8Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node9 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node9Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node10 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node10Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node11 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node11Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node12 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node12Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node13 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node13Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node14 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node14Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node15 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node15Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node16 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node16Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node17 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node17Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node18 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node18Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node19 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node19Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node20 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def node20Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node21 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node21Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node22 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node22Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node23 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node23Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node24 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node24Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node25 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node25Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node26 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node26Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node27 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node27Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node28 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node28Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node29 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node29Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node30 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node30Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node31 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node31Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node32 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node32Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node33 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node33Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node34 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node34Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node35 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def node35Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node36 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node36Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node37 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def node37Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node38 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def node38Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node39 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def node39Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node40 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def node40Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node41 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def node41Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node42 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def node42Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node43 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node43Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node44 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node44Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node45 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node45Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node46 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node46Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node47 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node47Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node48 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node48Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node49 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node49Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node50 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node50Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node51 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node51Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node52 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node52Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node53 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node53Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node54 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node54Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node55 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node55Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node56 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node56Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node57 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def node57Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node58 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node58Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node59 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node59Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node60 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node60Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node61 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node61Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node62 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node62Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node63 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node63Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def codeChunk0 : Array Code := #[⟨4, 2, 1, node0, node0Labels⟩, ⟨3, 2, 1, node1, node1Labels⟩, ⟨2, 2, 1, node2, node2Labels⟩, ⟨5, 2, 1, node3, node3Labels⟩, ⟨4, 2, 1, node4, node4Labels⟩, ⟨3, 2, 1, node5, node5Labels⟩, ⟨2, 2, 1, node6, node6Labels⟩, ⟨4, 2, 1, node7, node7Labels⟩, ⟨6, 3, 1, node8, node8Labels⟩, ⟨5, 3, 1, node9, node9Labels⟩, ⟨6, 3, 1, node10, node10Labels⟩, ⟨5, 3, 1, node11, node11Labels⟩, ⟨5, 3, 1, node12, node12Labels⟩, ⟨4, 3, 1, node13, node13Labels⟩, ⟨5, 3, 1, node14, node14Labels⟩, ⟨5, 3, 1, node15, node15Labels⟩, ⟨4, 3, 1, node16, node16Labels⟩, ⟨4, 3, 1, node17, node17Labels⟩, ⟨4, 3, 1, node18, node18Labels⟩, ⟨4, 3, 1, node19, node19Labels⟩, ⟨3, 3, 1, node20, node20Labels⟩, ⟨6, 3, 1, node21, node21Labels⟩, ⟨6, 3, 1, node22, node22Labels⟩, ⟨5, 3, 1, node23, node23Labels⟩, ⟨5, 3, 1, node24, node24Labels⟩, ⟨4, 3, 1, node25, node25Labels⟩, ⟨5, 3, 1, node26, node26Labels⟩, ⟨5, 3, 1, node27, node27Labels⟩, ⟨4, 3, 1, node28, node28Labels⟩, ⟨4, 3, 1, node29, node29Labels⟩, ⟨4, 3, 1, node30, node30Labels⟩, ⟨4, 3, 1, node31, node31Labels⟩, ⟨4, 3, 1, node32, node32Labels⟩, ⟨4, 3, 1, node33, node33Labels⟩, ⟨4, 3, 1, node34, node34Labels⟩, ⟨3, 3, 1, node35, node35Labels⟩, ⟨4, 3, 1, node36, node36Labels⟩, ⟨3, 3, 1, node37, node37Labels⟩, ⟨3, 3, 1, node38, node38Labels⟩, ⟨3, 3, 1, node39, node39Labels⟩, ⟨3, 3, 1, node40, node40Labels⟩, ⟨3, 3, 1, node41, node41Labels⟩, ⟨2, 3, 1, node42, node42Labels⟩, ⟨6, 3, 1, node43, node43Labels⟩, ⟨6, 3, 1, node44, node44Labels⟩, ⟨5, 3, 1, node45, node45Labels⟩, ⟨5, 3, 1, node46, node46Labels⟩, ⟨5, 3, 1, node47, node47Labels⟩, ⟨5, 3, 1, node48, node48Labels⟩, ⟨4, 3, 1, node49, node49Labels⟩, ⟨5, 3, 1, node50, node50Labels⟩, ⟨5, 3, 1, node51, node51Labels⟩, ⟨4, 3, 1, node52, node52Labels⟩, ⟨4, 3, 1, node53, node53Labels⟩, ⟨4, 3, 1, node54, node54Labels⟩, ⟨4, 3, 1, node55, node55Labels⟩, ⟨4, 3, 1, node56, node56Labels⟩, ⟨3, 3, 1, node57, node57Labels⟩, ⟨6, 3, 1, node58, node58Labels⟩, ⟨5, 3, 1, node59, node59Labels⟩, ⟨5, 3, 1, node60, node60Labels⟩, ⟨6, 3, 1, node61, node61Labels⟩, ⟨5, 3, 1, node62, node62Labels⟩, ⟨6, 3, 1, node63, node63Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node64 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node64Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node65 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node65Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node66 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node66Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node67 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node67Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node68 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node68Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node69 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node69Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node70 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def node70Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node71 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def node71Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node72 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node72Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node73 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node73Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node74 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node74Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node75 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node75Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node76 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node76Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node77 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node77Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node78 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node78Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node79 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node79Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node80 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node80Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node81 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node81Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node82 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def node82Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node83 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node83Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node84 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node84Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node85 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node85Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node86 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node86Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node87 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node87Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node88 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node88Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node89 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node89Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node90 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node90Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node91 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node91Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node92 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node92Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node93 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node93Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node94 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node94Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node95 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node95Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node96 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node96Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node97 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node97Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node98 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node98Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node99 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node99Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node100 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def node100Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node102Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node104 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def node104Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node105 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node106 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node106Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node107 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def node107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node108Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node110 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node110Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node111 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node112 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def node112Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node113 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def node113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node114Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node116 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node116Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node117 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node118Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node120Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node122Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node123Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node124Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node126Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node127 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def codeChunk1 : Array Code := #[⟨5, 3, 1, node64, node64Labels⟩, ⟨6, 3, 1, node65, node65Labels⟩, ⟨5, 3, 1, node66, node66Labels⟩, ⟨5, 3, 1, node67, node67Labels⟩, ⟨5, 3, 1, node68, node68Labels⟩, ⟨5, 3, 1, node69, node69Labels⟩, ⟨4, 3, 1, node70, node70Labels⟩, ⟨4, 3, 1, node71, node71Labels⟩, ⟨4, 3, 1, node72, node72Labels⟩, ⟨4, 3, 1, node73, node73Labels⟩, ⟨5, 3, 1, node74, node74Labels⟩, ⟨4, 3, 1, node75, node75Labels⟩, ⟨4, 3, 1, node76, node76Labels⟩, ⟨6, 3, 1, node77, node77Labels⟩, ⟨5, 3, 1, node78, node78Labels⟩, ⟨6, 3, 1, node79, node79Labels⟩, ⟨5, 3, 1, node80, node80Labels⟩, ⟨5, 3, 1, node81, node81Labels⟩, ⟨4, 3, 1, node82, node82Labels⟩, ⟨5, 3, 1, node83, node83Labels⟩, ⟨5, 3, 1, node84, node84Labels⟩, ⟨4, 3, 1, node85, node85Labels⟩, ⟨4, 3, 1, node86, node86Labels⟩, ⟨5, 3, 1, node87, node87Labels⟩, ⟨4, 3, 1, node88, node88Labels⟩, ⟨5, 3, 1, node89, node89Labels⟩, ⟨4, 3, 1, node90, node90Labels⟩, ⟨6, 3, 1, node91, node91Labels⟩, ⟨5, 3, 1, node92, node92Labels⟩, ⟨5, 3, 1, node93, node93Labels⟩, ⟨4, 3, 1, node94, node94Labels⟩, ⟨5, 3, 1, node95, node95Labels⟩, ⟨4, 3, 1, node96, node96Labels⟩, ⟨4, 3, 1, node97, node97Labels⟩, ⟨4, 3, 1, node98, node98Labels⟩, ⟨4, 3, 1, node99, node99Labels⟩, ⟨3, 3, 1, node100, node100Labels⟩, ⟨5, 3, 1, node101, node101Labels⟩, ⟨4, 3, 1, node102, node102Labels⟩, ⟨4, 3, 1, node103, node103Labels⟩, ⟨3, 3, 1, node104, node104Labels⟩, ⟨4, 3, 1, node105, node105Labels⟩, ⟨4, 3, 1, node106, node106Labels⟩, ⟨3, 3, 1, node107, node107Labels⟩, ⟨5, 3, 1, node108, node108Labels⟩, ⟨4, 3, 1, node109, node109Labels⟩, ⟨4, 3, 1, node110, node110Labels⟩, ⟨4, 3, 1, node111, node111Labels⟩, ⟨3, 3, 1, node112, node112Labels⟩, ⟨3, 3, 1, node113, node113Labels⟩, ⟨6, 3, 1, node114, node114Labels⟩, ⟨5, 3, 1, node115, node115Labels⟩, ⟨5, 3, 1, node116, node116Labels⟩, ⟨5, 3, 1, node117, node117Labels⟩, ⟨6, 3, 1, node118, node118Labels⟩, ⟨5, 3, 1, node119, node119Labels⟩, ⟨6, 3, 1, node120, node120Labels⟩, ⟨5, 3, 1, node121, node121Labels⟩, ⟨5, 3, 1, node122, node122Labels⟩, ⟨5, 3, 1, node123, node123Labels⟩, ⟨5, 3, 1, node124, node124Labels⟩, ⟨6, 3, 1, node125, node125Labels⟩, ⟨5, 3, 1, node126, node126Labels⟩, ⟨5, 3, 1, node127, node127Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node641 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node642 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node643 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def node643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node644 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node645 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node646 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node647 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node648 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node649 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node650 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def node650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node652 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node653 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node654 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def node654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node655 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, 0, -2], ![3, -3, 0]]
def node655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node657 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node659 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node660 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def node661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node663 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node664 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node665 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node667 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node668 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node669 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node670 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node671 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node672 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node673 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![4, 0, -4]]
def node673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node676 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node677 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node678 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node679 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node680 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def node680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node684 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node685 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node686 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def node686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node687 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node688 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node689 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node690 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node691 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def node691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node693 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![3, 0, -3]]
def node693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node694 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def node694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node695 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, -1, -1], ![2, 2, -4]]
def node695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node696 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, 0, -2], ![2, 1, -3]]
def node696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node697 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, -1, 5], ![4, 1, -5]]
def node697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node701 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk10 : Array Code := #[⟨5, 3, 2, node640, node640Labels⟩, ⟨4, 3, 2, node641, node641Labels⟩, ⟨4, 3, 2, node642, node642Labels⟩, ⟨3, 3, 2, node643, node643Labels⟩, ⟨5, 3, 2, node644, node644Labels⟩, ⟨4, 3, 2, node645, node645Labels⟩, ⟨5, 3, 2, node646, node646Labels⟩, ⟨4, 3, 2, node647, node647Labels⟩, ⟨4, 3, 2, node648, node648Labels⟩, ⟨4, 3, 2, node649, node649Labels⟩, ⟨3, 3, 2, node650, node650Labels⟩, ⟨5, 3, 2, node651, node651Labels⟩, ⟨4, 3, 2, node652, node652Labels⟩, ⟨4, 3, 2, node653, node653Labels⟩, ⟨3, 3, 2, node654, node654Labels⟩, ⟨3, 3, 2, node655, node655Labels⟩, ⟨6, 3, 2, node656, node656Labels⟩, ⟨5, 3, 2, node657, node657Labels⟩, ⟨6, 3, 2, node658, node658Labels⟩, ⟨5, 3, 2, node659, node659Labels⟩, ⟨5, 3, 2, node660, node660Labels⟩, ⟨4, 3, 2, node661, node661Labels⟩, ⟨6, 3, 2, node662, node662Labels⟩, ⟨5, 3, 2, node663, node663Labels⟩, ⟨5, 3, 2, node664, node664Labels⟩, ⟨4, 3, 2, node665, node665Labels⟩, ⟨6, 3, 2, node666, node666Labels⟩, ⟨5, 3, 2, node667, node667Labels⟩, ⟨5, 3, 2, node668, node668Labels⟩, ⟨4, 3, 2, node669, node669Labels⟩, ⟨4, 3, 2, node670, node670Labels⟩, ⟨4, 3, 2, node671, node671Labels⟩, ⟨4, 3, 2, node672, node672Labels⟩, ⟨3, 3, 2, node673, node673Labels⟩, ⟨6, 3, 2, node674, node674Labels⟩, ⟨5, 3, 2, node675, node675Labels⟩, ⟨4, 3, 2, node676, node676Labels⟩, ⟨5, 3, 2, node677, node677Labels⟩, ⟨4, 3, 2, node678, node678Labels⟩, ⟨4, 3, 2, node679, node679Labels⟩, ⟨3, 3, 2, node680, node680Labels⟩, ⟨5, 3, 2, node681, node681Labels⟩, ⟨5, 3, 2, node682, node682Labels⟩, ⟨4, 3, 2, node683, node683Labels⟩, ⟨4, 3, 2, node684, node684Labels⟩, ⟨4, 3, 2, node685, node685Labels⟩, ⟨3, 3, 2, node686, node686Labels⟩, ⟨5, 3, 2, node687, node687Labels⟩, ⟨4, 3, 2, node688, node688Labels⟩, ⟨4, 3, 2, node689, node689Labels⟩, ⟨4, 3, 2, node690, node690Labels⟩, ⟨3, 3, 2, node691, node691Labels⟩, ⟨4, 3, 2, node692, node692Labels⟩, ⟨3, 3, 2, node693, node693Labels⟩, ⟨3, 3, 2, node694, node694Labels⟩, ⟨3, 3, 2, node695, node695Labels⟩, ⟨3, 3, 2, node696, node696Labels⟩, ⟨2, 3, 2, node697, node697Labels⟩, ⟨6, 3, 2, node698, node698Labels⟩, ⟨6, 3, 2, node699, node699Labels⟩, ⟨6, 3, 2, node700, node700Labels⟩, ⟨5, 3, 2, node701, node701Labels⟩, ⟨6, 3, 2, node702, node702Labels⟩, ⟨6, 3, 2, node703, node703Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node705 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node706 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node711 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node714 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node716 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node717 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node718 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def node718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

set_option maxHeartbeats 1000000 in
def node721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node722 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node723 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def node723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node725 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node726 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def node726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def node727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def node728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node729 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node731 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node733 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def node735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node738 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node739 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def node740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node741 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def node741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node742 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node743 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node747 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def node747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node750 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node752 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node753 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node755 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node757 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node758 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node759 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def node759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node762 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node763 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node764 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node765 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def node765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk11 : Array Code := #[⟨6, 3, 2, node704, node704Labels⟩, ⟨5, 3, 2, node705, node705Labels⟩, ⟨5, 3, 2, node706, node706Labels⟩, ⟨5, 3, 2, node707, node707Labels⟩, ⟨5, 3, 2, node708, node708Labels⟩, ⟨6, 3, 2, node709, node709Labels⟩, ⟨6, 3, 2, node710, node710Labels⟩, ⟨5, 3, 2, node711, node711Labels⟩, ⟨6, 3, 2, node712, node712Labels⟩, ⟨6, 3, 2, node713, node713Labels⟩, ⟨5, 3, 2, node714, node714Labels⟩, ⟨5, 3, 2, node715, node715Labels⟩, ⟨5, 3, 2, node716, node716Labels⟩, ⟨5, 3, 2, node717, node717Labels⟩, ⟨4, 3, 2, node718, node718Labels⟩, ⟨6, 3, 2, node719, node719Labels⟩, ⟨5, 3, 2, node720, node720Labels⟩, ⟨5, 3, 2, node721, node721Labels⟩, ⟨5, 3, 2, node722, node722Labels⟩, ⟨4, 3, 2, node723, node723Labels⟩, ⟨5, 3, 2, node724, node724Labels⟩, ⟨5, 3, 2, node725, node725Labels⟩, ⟨4, 3, 2, node726, node726Labels⟩, ⟨4, 3, 2, node727, node727Labels⟩, ⟨4, 3, 2, node728, node728Labels⟩, ⟨4, 3, 2, node729, node729Labels⟩, ⟨6, 3, 2, node730, node730Labels⟩, ⟨5, 3, 2, node731, node731Labels⟩, ⟨6, 3, 2, node732, node732Labels⟩, ⟨5, 3, 2, node733, node733Labels⟩, ⟨5, 3, 2, node734, node734Labels⟩, ⟨4, 3, 2, node735, node735Labels⟩, ⟨6, 3, 2, node736, node736Labels⟩, ⟨5, 3, 2, node737, node737Labels⟩, ⟨5, 3, 2, node738, node738Labels⟩, ⟨5, 3, 2, node739, node739Labels⟩, ⟨4, 3, 2, node740, node740Labels⟩, ⟨4, 3, 2, node741, node741Labels⟩, ⟨4, 3, 2, node742, node742Labels⟩, ⟨4, 3, 2, node743, node743Labels⟩, ⟨6, 3, 2, node744, node744Labels⟩, ⟨6, 3, 2, node745, node745Labels⟩, ⟨6, 3, 2, node746, node746Labels⟩, ⟨5, 3, 2, node747, node747Labels⟩, ⟨6, 3, 2, node748, node748Labels⟩, ⟨6, 3, 2, node749, node749Labels⟩, ⟨5, 3, 2, node750, node750Labels⟩, ⟨6, 3, 2, node751, node751Labels⟩, ⟨5, 3, 2, node752, node752Labels⟩, ⟨5, 3, 2, node753, node753Labels⟩, ⟨6, 3, 2, node754, node754Labels⟩, ⟨5, 3, 2, node755, node755Labels⟩, ⟨6, 3, 2, node756, node756Labels⟩, ⟨5, 3, 2, node757, node757Labels⟩, ⟨5, 3, 2, node758, node758Labels⟩, ⟨4, 3, 2, node759, node759Labels⟩, ⟨6, 3, 2, node760, node760Labels⟩, ⟨6, 3, 2, node761, node761Labels⟩, ⟨5, 3, 2, node762, node762Labels⟩, ⟨5, 3, 2, node763, node763Labels⟩, ⟨5, 3, 2, node764, node764Labels⟩, ⟨4, 3, 2, node765, node765Labels⟩, ⟨6, 3, 2, node766, node766Labels⟩, ⟨5, 3, 2, node767, node767Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node768 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node769 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node770 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def node770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node771 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node772 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node773 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def node773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node774 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def node774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node775 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node785 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node787 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node789 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node790 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node791 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node794 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node797 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![4, -3, -1]]
def node797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node801 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def node801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node809 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node811 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node812 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node813 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node814 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node815 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node816 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node817 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def node817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node819 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def node820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node826 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node828 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node829 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk12 : Array Code := #[⟨5, 3, 2, node768, node768Labels⟩, ⟨5, 3, 2, node769, node769Labels⟩, ⟨4, 3, 2, node770, node770Labels⟩, ⟨5, 3, 2, node771, node771Labels⟩, ⟨4, 3, 2, node772, node772Labels⟩, ⟨4, 3, 2, node773, node773Labels⟩, ⟨4, 3, 2, node774, node774Labels⟩, ⟨4, 3, 2, node775, node775Labels⟩, ⟨6, 3, 2, node776, node776Labels⟩, ⟨6, 3, 2, node777, node777Labels⟩, ⟨6, 3, 2, node778, node778Labels⟩, ⟨5, 3, 2, node779, node779Labels⟩, ⟨6, 3, 2, node780, node780Labels⟩, ⟨5, 3, 2, node781, node781Labels⟩, ⟨6, 3, 2, node782, node782Labels⟩, ⟨6, 3, 2, node783, node783Labels⟩, ⟨6, 3, 2, node784, node784Labels⟩, ⟨5, 3, 2, node785, node785Labels⟩, ⟨6, 3, 2, node786, node786Labels⟩, ⟨5, 3, 2, node787, node787Labels⟩, ⟨5, 3, 2, node788, node788Labels⟩, ⟨5, 3, 2, node789, node789Labels⟩, ⟨5, 3, 2, node790, node790Labels⟩, ⟨4, 3, 2, node791, node791Labels⟩, ⟨6, 3, 2, node792, node792Labels⟩, ⟨6, 3, 2, node793, node793Labels⟩, ⟨5, 3, 2, node794, node794Labels⟩, ⟨5, 3, 2, node795, node795Labels⟩, ⟨5, 3, 2, node796, node796Labels⟩, ⟨4, 3, 2, node797, node797Labels⟩, ⟨6, 3, 2, node798, node798Labels⟩, ⟨5, 3, 2, node799, node799Labels⟩, ⟨5, 3, 2, node800, node800Labels⟩, ⟨4, 3, 2, node801, node801Labels⟩, ⟨6, 3, 2, node802, node802Labels⟩, ⟨6, 3, 2, node803, node803Labels⟩, ⟨5, 3, 2, node804, node804Labels⟩, ⟨6, 3, 2, node805, node805Labels⟩, ⟨5, 3, 2, node806, node806Labels⟩, ⟨5, 3, 2, node807, node807Labels⟩, ⟨5, 3, 2, node808, node808Labels⟩, ⟨4, 3, 2, node809, node809Labels⟩, ⟨5, 3, 2, node810, node810Labels⟩, ⟨5, 3, 2, node811, node811Labels⟩, ⟨4, 3, 2, node812, node812Labels⟩, ⟨4, 3, 2, node813, node813Labels⟩, ⟨4, 3, 2, node814, node814Labels⟩, ⟨4, 3, 2, node815, node815Labels⟩, ⟨4, 3, 2, node816, node816Labels⟩, ⟨3, 3, 2, node817, node817Labels⟩, ⟨6, 3, 2, node818, node818Labels⟩, ⟨5, 3, 2, node819, node819Labels⟩, ⟨4, 3, 2, node820, node820Labels⟩, ⟨6, 3, 2, node821, node821Labels⟩, ⟨6, 3, 2, node822, node822Labels⟩, ⟨5, 3, 2, node823, node823Labels⟩, ⟨5, 3, 2, node824, node824Labels⟩, ⟨5, 3, 2, node825, node825Labels⟩, ⟨4, 3, 2, node826, node826Labels⟩, ⟨5, 3, 2, node827, node827Labels⟩, ⟨4, 3, 2, node828, node828Labels⟩, ⟨4, 3, 2, node829, node829Labels⟩, ⟨4, 3, 2, node830, node830Labels⟩, ⟨4, 3, 2, node831, node831Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node832 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def node832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node834 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node835 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node836 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def node836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node837 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node838 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def node838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node839 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![4, -3, -1]]
def node839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node842 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def node842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node843 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def node843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node844 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def node844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node845 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def node845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node846 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def node846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node847 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node848 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node849 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node851 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node852 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node853 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node854 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 3, -4], ![2, -2, 0]]
def node854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node855 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def node855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node859 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![3, -1, -2]]
def node859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node860 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def node860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node861 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 3, -4], ![3, -3, 0]]
def node861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node862 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def node862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node863 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -1, -1], ![2, 1, -3]]
def node863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def node867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node871 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def node871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def node877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node883 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node889 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node890 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def node890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node893 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def node893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def node894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node895 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def node895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk13 : Array Code := #[⟨3, 3, 2, node832, node832Labels⟩, ⟨6, 3, 2, node833, node833Labels⟩, ⟨5, 3, 2, node834, node834Labels⟩, ⟨5, 3, 2, node835, node835Labels⟩, ⟨4, 3, 2, node836, node836Labels⟩, ⟨4, 3, 2, node837, node837Labels⟩, ⟨4, 3, 2, node838, node838Labels⟩, ⟨3, 3, 2, node839, node839Labels⟩, ⟨5, 3, 2, node840, node840Labels⟩, ⟨5, 3, 2, node841, node841Labels⟩, ⟨4, 3, 2, node842, node842Labels⟩, ⟨4, 3, 2, node843, node843Labels⟩, ⟨4, 3, 2, node844, node844Labels⟩, ⟨3, 3, 2, node845, node845Labels⟩, ⟨5, 3, 2, node846, node846Labels⟩, ⟨5, 3, 2, node847, node847Labels⟩, ⟨5, 3, 2, node848, node848Labels⟩, ⟨4, 3, 2, node849, node849Labels⟩, ⟨5, 3, 2, node850, node850Labels⟩, ⟨4, 3, 2, node851, node851Labels⟩, ⟨4, 3, 2, node852, node852Labels⟩, ⟨4, 3, 2, node853, node853Labels⟩, ⟨4, 3, 2, node854, node854Labels⟩, ⟨3, 3, 2, node855, node855Labels⟩, ⟨4, 3, 2, node856, node856Labels⟩, ⟨4, 3, 2, node857, node857Labels⟩, ⟨4, 3, 2, node858, node858Labels⟩, ⟨3, 3, 2, node859, node859Labels⟩, ⟨3, 3, 2, node860, node860Labels⟩, ⟨3, 3, 2, node861, node861Labels⟩, ⟨3, 3, 2, node862, node862Labels⟩, ⟨3, 3, 2, node863, node863Labels⟩, ⟨6, 3, 2, node864, node864Labels⟩, ⟨6, 3, 2, node865, node865Labels⟩, ⟨6, 3, 2, node866, node866Labels⟩, ⟨5, 3, 2, node867, node867Labels⟩, ⟨6, 3, 2, node868, node868Labels⟩, ⟨6, 3, 2, node869, node869Labels⟩, ⟨6, 3, 2, node870, node870Labels⟩, ⟨5, 3, 2, node871, node871Labels⟩, ⟨5, 3, 2, node872, node872Labels⟩, ⟨5, 3, 2, node873, node873Labels⟩, ⟨5, 3, 2, node874, node874Labels⟩, ⟨6, 3, 2, node875, node875Labels⟩, ⟨6, 3, 2, node876, node876Labels⟩, ⟨5, 3, 2, node877, node877Labels⟩, ⟨6, 3, 2, node878, node878Labels⟩, ⟨6, 3, 2, node879, node879Labels⟩, ⟨5, 3, 2, node880, node880Labels⟩, ⟨5, 3, 2, node881, node881Labels⟩, ⟨5, 3, 2, node882, node882Labels⟩, ⟨5, 3, 2, node883, node883Labels⟩, ⟨6, 3, 2, node884, node884Labels⟩, ⟨6, 3, 2, node885, node885Labels⟩, ⟨5, 3, 2, node886, node886Labels⟩, ⟨5, 3, 2, node887, node887Labels⟩, ⟨5, 3, 2, node888, node888Labels⟩, ⟨5, 3, 2, node889, node889Labels⟩, ⟨4, 3, 2, node890, node890Labels⟩, ⟨5, 3, 2, node891, node891Labels⟩, ⟨5, 3, 2, node892, node892Labels⟩, ⟨4, 3, 2, node893, node893Labels⟩, ⟨4, 3, 2, node894, node894Labels⟩, ⟨4, 3, 2, node895, node895Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node896 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def node896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node897 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def node897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node908 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node912 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node928 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def node928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node930 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node931 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node934 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def node934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node935 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node936 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def node936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node937 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def node937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node938 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node939 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node940 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node943 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def node948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node950 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def node951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node954 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node956 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node957 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node959 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk14 : Array Code := #[⟨4, 3, 2, node896, node896Labels⟩, ⟨4, 3, 2, node897, node897Labels⟩, ⟨6, 3, 2, node898, node898Labels⟩, ⟨6, 3, 2, node899, node899Labels⟩, ⟨6, 3, 2, node900, node900Labels⟩, ⟨6, 3, 2, node901, node901Labels⟩, ⟨5, 3, 2, node902, node902Labels⟩, ⟨5, 3, 2, node903, node903Labels⟩, ⟨6, 3, 2, node904, node904Labels⟩, ⟨6, 3, 2, node905, node905Labels⟩, ⟨6, 3, 2, node906, node906Labels⟩, ⟨6, 3, 2, node907, node907Labels⟩, ⟨5, 3, 2, node908, node908Labels⟩, ⟨6, 3, 2, node909, node909Labels⟩, ⟨6, 3, 2, node910, node910Labels⟩, ⟨5, 3, 2, node911, node911Labels⟩, ⟨5, 3, 2, node912, node912Labels⟩, ⟨5, 3, 2, node913, node913Labels⟩, ⟨5, 3, 2, node914, node914Labels⟩, ⟨6, 3, 2, node915, node915Labels⟩, ⟨5, 3, 2, node916, node916Labels⟩, ⟨5, 3, 2, node917, node917Labels⟩, ⟨6, 3, 2, node918, node918Labels⟩, ⟨6, 3, 2, node919, node919Labels⟩, ⟨6, 3, 2, node920, node920Labels⟩, ⟨5, 3, 2, node921, node921Labels⟩, ⟨6, 3, 2, node922, node922Labels⟩, ⟨6, 3, 2, node923, node923Labels⟩, ⟨5, 3, 2, node924, node924Labels⟩, ⟨5, 3, 2, node925, node925Labels⟩, ⟨5, 3, 2, node926, node926Labels⟩, ⟨5, 3, 2, node927, node927Labels⟩, ⟨4, 3, 2, node928, node928Labels⟩, ⟨6, 3, 2, node929, node929Labels⟩, ⟨5, 3, 2, node930, node930Labels⟩, ⟨5, 3, 2, node931, node931Labels⟩, ⟨5, 3, 2, node932, node932Labels⟩, ⟨5, 3, 2, node933, node933Labels⟩, ⟨4, 3, 2, node934, node934Labels⟩, ⟨5, 3, 2, node935, node935Labels⟩, ⟨4, 3, 2, node936, node936Labels⟩, ⟨4, 3, 2, node937, node937Labels⟩, ⟨4, 3, 2, node938, node938Labels⟩, ⟨4, 3, 2, node939, node939Labels⟩, ⟨4, 3, 2, node940, node940Labels⟩, ⟨6, 3, 2, node941, node941Labels⟩, ⟨6, 3, 2, node942, node942Labels⟩, ⟨5, 3, 2, node943, node943Labels⟩, ⟨6, 3, 2, node944, node944Labels⟩, ⟨5, 3, 2, node945, node945Labels⟩, ⟨5, 3, 2, node946, node946Labels⟩, ⟨5, 3, 2, node947, node947Labels⟩, ⟨4, 3, 2, node948, node948Labels⟩, ⟨5, 3, 2, node949, node949Labels⟩, ⟨5, 3, 2, node950, node950Labels⟩, ⟨4, 3, 2, node951, node951Labels⟩, ⟨4, 3, 2, node952, node952Labels⟩, ⟨4, 3, 2, node953, node953Labels⟩, ⟨4, 3, 2, node954, node954Labels⟩, ⟨6, 3, 2, node955, node955Labels⟩, ⟨5, 3, 2, node956, node956Labels⟩, ⟨5, 3, 2, node957, node957Labels⟩, ⟨6, 3, 2, node958, node958Labels⟩, ⟨5, 3, 2, node959, node959Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def node961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def node962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node963 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node968 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def node968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def node975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node983 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node985 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node986 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def node986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node989 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node991 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node992 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node993 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node994 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def node994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1000 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1002 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node1002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1005 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1007 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1009 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node1009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node1010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1011 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node1011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1012 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node1012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1016 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def node1016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1019 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk15 : Array Code := #[⟨5, 3, 2, node960, node960Labels⟩, ⟨4, 3, 2, node961, node961Labels⟩, ⟨4, 3, 2, node962, node962Labels⟩, ⟨4, 3, 2, node963, node963Labels⟩, ⟨6, 3, 2, node964, node964Labels⟩, ⟨6, 3, 2, node965, node965Labels⟩, ⟨6, 3, 2, node966, node966Labels⟩, ⟨6, 3, 2, node967, node967Labels⟩, ⟨5, 3, 2, node968, node968Labels⟩, ⟨5, 3, 2, node969, node969Labels⟩, ⟨5, 3, 2, node970, node970Labels⟩, ⟨6, 3, 2, node971, node971Labels⟩, ⟨6, 3, 2, node972, node972Labels⟩, ⟨6, 3, 2, node973, node973Labels⟩, ⟨6, 3, 2, node974, node974Labels⟩, ⟨5, 3, 2, node975, node975Labels⟩, ⟨6, 3, 2, node976, node976Labels⟩, ⟨6, 3, 2, node977, node977Labels⟩, ⟨6, 3, 2, node978, node978Labels⟩, ⟨5, 3, 2, node979, node979Labels⟩, ⟨6, 3, 2, node980, node980Labels⟩, ⟨6, 3, 2, node981, node981Labels⟩, ⟨5, 3, 2, node982, node982Labels⟩, ⟨5, 3, 2, node983, node983Labels⟩, ⟨5, 3, 2, node984, node984Labels⟩, ⟨5, 3, 2, node985, node985Labels⟩, ⟨4, 3, 2, node986, node986Labels⟩, ⟨6, 3, 2, node987, node987Labels⟩, ⟨6, 3, 2, node988, node988Labels⟩, ⟨5, 3, 2, node989, node989Labels⟩, ⟨6, 3, 2, node990, node990Labels⟩, ⟨5, 3, 2, node991, node991Labels⟩, ⟨5, 3, 2, node992, node992Labels⟩, ⟨5, 3, 2, node993, node993Labels⟩, ⟨4, 3, 2, node994, node994Labels⟩, ⟨6, 3, 2, node995, node995Labels⟩, ⟨6, 3, 2, node996, node996Labels⟩, ⟨5, 3, 2, node997, node997Labels⟩, ⟨6, 3, 2, node998, node998Labels⟩, ⟨5, 3, 2, node999, node999Labels⟩, ⟨5, 3, 2, node1000, node1000Labels⟩, ⟨5, 3, 2, node1001, node1001Labels⟩, ⟨4, 3, 2, node1002, node1002Labels⟩, ⟨6, 3, 2, node1003, node1003Labels⟩, ⟨5, 3, 2, node1004, node1004Labels⟩, ⟨5, 3, 2, node1005, node1005Labels⟩, ⟨5, 3, 2, node1006, node1006Labels⟩, ⟨4, 3, 2, node1007, node1007Labels⟩, ⟨5, 3, 2, node1008, node1008Labels⟩, ⟨4, 3, 2, node1009, node1009Labels⟩, ⟨4, 3, 2, node1010, node1010Labels⟩, ⟨4, 3, 2, node1011, node1011Labels⟩, ⟨4, 3, 2, node1012, node1012Labels⟩, ⟨4, 3, 2, node1013, node1013Labels⟩, ⟨6, 3, 2, node1014, node1014Labels⟩, ⟨6, 3, 2, node1015, node1015Labels⟩, ⟨5, 3, 2, node1016, node1016Labels⟩, ⟨6, 3, 2, node1017, node1017Labels⟩, ⟨6, 3, 2, node1018, node1018Labels⟩, ⟨5, 3, 2, node1019, node1019Labels⟩, ⟨6, 3, 2, node1020, node1020Labels⟩, ⟨6, 3, 2, node1021, node1021Labels⟩, ⟨5, 3, 2, node1022, node1022Labels⟩, ⟨6, 3, 2, node1023, node1023Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1027 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node1027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node1028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node1029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1030 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node1030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1031 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![4, -4, 0]]
def node1031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1036 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1037 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1040 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1041 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1044 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1045 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1046 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1047 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1048 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node1048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1049 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1050 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1051 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def node1051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1053 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1055 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node1055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1059 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1061 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node1062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1064 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def node1064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1066 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node1066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1067 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def node1067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1068 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node1068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1069 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 3, -3], ![4, -4, 0]]
def node1069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1070 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1071 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1072 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node1072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1074 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1075 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1076 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node1076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1077 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def node1077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1078 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1080 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1082 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1083 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1084 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1085 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def node1085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1086 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1087 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk16 : Array Code := #[⟨5, 3, 2, node1024, node1024Labels⟩, ⟨5, 3, 2, node1025, node1025Labels⟩, ⟨5, 3, 2, node1026, node1026Labels⟩, ⟨4, 3, 2, node1027, node1027Labels⟩, ⟨6, 3, 2, node1028, node1028Labels⟩, ⟨5, 3, 2, node1029, node1029Labels⟩, ⟨5, 3, 2, node1030, node1030Labels⟩, ⟨4, 3, 2, node1031, node1031Labels⟩, ⟨6, 3, 2, node1032, node1032Labels⟩, ⟨5, 3, 2, node1033, node1033Labels⟩, ⟨6, 3, 2, node1034, node1034Labels⟩, ⟨5, 3, 2, node1035, node1035Labels⟩, ⟨5, 3, 2, node1036, node1036Labels⟩, ⟨4, 3, 2, node1037, node1037Labels⟩, ⟨6, 3, 2, node1038, node1038Labels⟩, ⟨6, 3, 2, node1039, node1039Labels⟩, ⟨5, 3, 2, node1040, node1040Labels⟩, ⟨5, 3, 2, node1041, node1041Labels⟩, ⟨5, 3, 2, node1042, node1042Labels⟩, ⟨4, 3, 2, node1043, node1043Labels⟩, ⟨5, 3, 2, node1044, node1044Labels⟩, ⟨5, 3, 2, node1045, node1045Labels⟩, ⟨4, 3, 2, node1046, node1046Labels⟩, ⟨4, 3, 2, node1047, node1047Labels⟩, ⟨4, 3, 2, node1048, node1048Labels⟩, ⟨4, 3, 2, node1049, node1049Labels⟩, ⟨4, 3, 2, node1050, node1050Labels⟩, ⟨3, 3, 2, node1051, node1051Labels⟩, ⟨6, 3, 2, node1052, node1052Labels⟩, ⟨5, 3, 2, node1053, node1053Labels⟩, ⟨5, 3, 2, node1054, node1054Labels⟩, ⟨4, 3, 2, node1055, node1055Labels⟩, ⟨6, 3, 2, node1056, node1056Labels⟩, ⟨5, 3, 2, node1057, node1057Labels⟩, ⟨5, 3, 2, node1058, node1058Labels⟩, ⟨4, 3, 2, node1059, node1059Labels⟩, ⟨5, 3, 2, node1060, node1060Labels⟩, ⟨4, 3, 2, node1061, node1061Labels⟩, ⟨4, 3, 2, node1062, node1062Labels⟩, ⟨4, 3, 2, node1063, node1063Labels⟩, ⟨3, 3, 2, node1064, node1064Labels⟩, ⟨6, 3, 2, node1065, node1065Labels⟩, ⟨5, 3, 2, node1066, node1066Labels⟩, ⟨4, 3, 2, node1067, node1067Labels⟩, ⟨4, 3, 2, node1068, node1068Labels⟩, ⟨3, 3, 2, node1069, node1069Labels⟩, ⟨5, 3, 2, node1070, node1070Labels⟩, ⟨5, 3, 2, node1071, node1071Labels⟩, ⟨4, 3, 2, node1072, node1072Labels⟩, ⟨5, 3, 2, node1073, node1073Labels⟩, ⟨4, 3, 2, node1074, node1074Labels⟩, ⟨4, 3, 2, node1075, node1075Labels⟩, ⟨4, 3, 2, node1076, node1076Labels⟩, ⟨3, 3, 2, node1077, node1077Labels⟩, ⟨5, 3, 2, node1078, node1078Labels⟩, ⟨5, 3, 2, node1079, node1079Labels⟩, ⟨4, 3, 2, node1080, node1080Labels⟩, ⟨5, 3, 2, node1081, node1081Labels⟩, ⟨4, 3, 2, node1082, node1082Labels⟩, ⟨4, 3, 2, node1083, node1083Labels⟩, ⟨4, 3, 2, node1084, node1084Labels⟩, ⟨3, 3, 2, node1085, node1085Labels⟩, ⟨4, 3, 2, node1086, node1086Labels⟩, ⟨4, 3, 2, node1087, node1087Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1088 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node1088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1089 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def node1089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1090 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node1090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1091 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def node1091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1092 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def node1092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1093 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def node1093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1094 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def node1094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1095 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def node1095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1096 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def node1096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1098 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def node1103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1104 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def node1104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def node1109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def node1115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def node1118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node1123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def node1140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1141 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1142 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def node1142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def node1143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1144 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def node1144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1145 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def node1145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node1146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk17 : Array Code := #[⟨4, 3, 2, node1088, node1088Labels⟩, ⟨3, 3, 2, node1089, node1089Labels⟩, ⟨4, 3, 2, node1090, node1090Labels⟩, ⟨3, 3, 2, node1091, node1091Labels⟩, ⟨3, 3, 2, node1092, node1092Labels⟩, ⟨3, 3, 2, node1093, node1093Labels⟩, ⟨3, 3, 2, node1094, node1094Labels⟩, ⟨3, 3, 2, node1095, node1095Labels⟩, ⟨2, 3, 2, node1096, node1096Labels⟩, ⟨6, 3, 2, node1097, node1097Labels⟩, ⟨5, 3, 2, node1098, node1098Labels⟩, ⟨5, 3, 2, node1099, node1099Labels⟩, ⟨6, 3, 2, node1100, node1100Labels⟩, ⟨5, 3, 2, node1101, node1101Labels⟩, ⟨5, 3, 2, node1102, node1102Labels⟩, ⟨4, 3, 2, node1103, node1103Labels⟩, ⟨4, 3, 2, node1104, node1104Labels⟩, ⟨6, 3, 2, node1105, node1105Labels⟩, ⟨6, 3, 2, node1106, node1106Labels⟩, ⟨6, 3, 2, node1107, node1107Labels⟩, ⟨6, 3, 2, node1108, node1108Labels⟩, ⟨5, 3, 2, node1109, node1109Labels⟩, ⟨5, 3, 2, node1110, node1110Labels⟩, ⟨6, 3, 2, node1111, node1111Labels⟩, ⟨6, 3, 2, node1112, node1112Labels⟩, ⟨6, 3, 2, node1113, node1113Labels⟩, ⟨6, 3, 2, node1114, node1114Labels⟩, ⟨5, 3, 2, node1115, node1115Labels⟩, ⟨6, 3, 2, node1116, node1116Labels⟩, ⟨6, 3, 2, node1117, node1117Labels⟩, ⟨5, 3, 2, node1118, node1118Labels⟩, ⟨5, 3, 2, node1119, node1119Labels⟩, ⟨5, 3, 2, node1120, node1120Labels⟩, ⟨5, 3, 2, node1121, node1121Labels⟩, ⟨6, 3, 2, node1122, node1122Labels⟩, ⟨5, 3, 2, node1123, node1123Labels⟩, ⟨5, 3, 2, node1124, node1124Labels⟩, ⟨6, 3, 2, node1125, node1125Labels⟩, ⟨6, 3, 2, node1126, node1126Labels⟩, ⟨6, 3, 2, node1127, node1127Labels⟩, ⟨5, 3, 2, node1128, node1128Labels⟩, ⟨6, 3, 2, node1129, node1129Labels⟩, ⟨6, 3, 2, node1130, node1130Labels⟩, ⟨5, 3, 2, node1131, node1131Labels⟩, ⟨5, 3, 2, node1132, node1132Labels⟩, ⟨5, 3, 2, node1133, node1133Labels⟩, ⟨5, 3, 2, node1134, node1134Labels⟩, ⟨6, 3, 2, node1135, node1135Labels⟩, ⟨5, 3, 2, node1136, node1136Labels⟩, ⟨5, 3, 2, node1137, node1137Labels⟩, ⟨5, 3, 2, node1138, node1138Labels⟩, ⟨5, 3, 2, node1139, node1139Labels⟩, ⟨4, 3, 2, node1140, node1140Labels⟩, ⟨5, 3, 2, node1141, node1141Labels⟩, ⟨4, 3, 2, node1142, node1142Labels⟩, ⟨4, 3, 2, node1143, node1143Labels⟩, ⟨4, 3, 2, node1144, node1144Labels⟩, ⟨4, 3, 2, node1145, node1145Labels⟩, ⟨4, 3, 2, node1146, node1146Labels⟩, ⟨6, 3, 2, node1147, node1147Labels⟩, ⟨6, 3, 2, node1148, node1148Labels⟩, ⟨6, 3, 2, node1149, node1149Labels⟩, ⟨6, 3, 2, node1150, node1150Labels⟩, ⟨6, 3, 2, node1151, node1151Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def node1153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1154 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def node1154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node1155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def node1157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1159 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node1159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1160 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node1160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1163 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1167 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1168 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def node1168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1171 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node1171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1172 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1173 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def node1173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1174 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def node1174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def node1175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1176 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def node1176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def node1177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1179 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1181 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def node1186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1188 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1189 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1190 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def node1190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1191 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def node1191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1192 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node1192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1193 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node1193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1199 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def node1199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node1203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node1204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1209 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def node1209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1215 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk18 : Array Code := #[⟨6, 3, 2, node1152, node1152Labels⟩, ⟨5, 3, 2, node1153, node1153Labels⟩, ⟨5, 3, 2, node1154, node1154Labels⟩, ⟨5, 3, 2, node1155, node1155Labels⟩, ⟨6, 3, 2, node1156, node1156Labels⟩, ⟨5, 3, 2, node1157, node1157Labels⟩, ⟨6, 3, 2, node1158, node1158Labels⟩, ⟨5, 3, 2, node1159, node1159Labels⟩, ⟨5, 3, 2, node1160, node1160Labels⟩, ⟨6, 3, 2, node1161, node1161Labels⟩, ⟨6, 3, 2, node1162, node1162Labels⟩, ⟨5, 3, 2, node1163, node1163Labels⟩, ⟨6, 3, 2, node1164, node1164Labels⟩, ⟨5, 3, 2, node1165, node1165Labels⟩, ⟨5, 3, 2, node1166, node1166Labels⟩, ⟨5, 3, 2, node1167, node1167Labels⟩, ⟨4, 3, 2, node1168, node1168Labels⟩, ⟨6, 3, 2, node1169, node1169Labels⟩, ⟨5, 3, 2, node1170, node1170Labels⟩, ⟨5, 3, 2, node1171, node1171Labels⟩, ⟨5, 3, 2, node1172, node1172Labels⟩, ⟨4, 3, 2, node1173, node1173Labels⟩, ⟨4, 3, 2, node1174, node1174Labels⟩, ⟨4, 3, 2, node1175, node1175Labels⟩, ⟨4, 3, 2, node1176, node1176Labels⟩, ⟨4, 3, 2, node1177, node1177Labels⟩, ⟨6, 3, 2, node1178, node1178Labels⟩, ⟨5, 3, 2, node1179, node1179Labels⟩, ⟨6, 3, 2, node1180, node1180Labels⟩, ⟨5, 3, 2, node1181, node1181Labels⟩, ⟨5, 3, 2, node1182, node1182Labels⟩, ⟨6, 3, 2, node1183, node1183Labels⟩, ⟨5, 3, 2, node1184, node1184Labels⟩, ⟨5, 3, 2, node1185, node1185Labels⟩, ⟨4, 3, 2, node1186, node1186Labels⟩, ⟨6, 3, 2, node1187, node1187Labels⟩, ⟨5, 3, 2, node1188, node1188Labels⟩, ⟨5, 3, 2, node1189, node1189Labels⟩, ⟨4, 3, 2, node1190, node1190Labels⟩, ⟨4, 3, 2, node1191, node1191Labels⟩, ⟨4, 3, 2, node1192, node1192Labels⟩, ⟨4, 3, 2, node1193, node1193Labels⟩, ⟨6, 3, 2, node1194, node1194Labels⟩, ⟨6, 3, 2, node1195, node1195Labels⟩, ⟨6, 3, 2, node1196, node1196Labels⟩, ⟨6, 3, 2, node1197, node1197Labels⟩, ⟨6, 3, 2, node1198, node1198Labels⟩, ⟨5, 3, 2, node1199, node1199Labels⟩, ⟨6, 3, 2, node1200, node1200Labels⟩, ⟨6, 3, 2, node1201, node1201Labels⟩, ⟨5, 3, 2, node1202, node1202Labels⟩, ⟨5, 3, 2, node1203, node1203Labels⟩, ⟨5, 3, 2, node1204, node1204Labels⟩, ⟨5, 3, 2, node1205, node1205Labels⟩, ⟨6, 3, 2, node1206, node1206Labels⟩, ⟨6, 3, 2, node1207, node1207Labels⟩, ⟨6, 3, 2, node1208, node1208Labels⟩, ⟨5, 3, 2, node1209, node1209Labels⟩, ⟨6, 3, 2, node1210, node1210Labels⟩, ⟨5, 3, 2, node1211, node1211Labels⟩, ⟨6, 3, 2, node1212, node1212Labels⟩, ⟨6, 3, 2, node1213, node1213Labels⟩, ⟨6, 3, 2, node1214, node1214Labels⟩, ⟨5, 3, 2, node1215, node1215Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1217 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1218 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1221 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def node1221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1227 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def node1227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1230 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1231 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def node1231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1236 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1237 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1238 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1239 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node1239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1241 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node1243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def node1244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1245 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node1245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1246 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node1247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1249 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def node1249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1252 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def node1252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1253 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node1253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def node1255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1257 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node1257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def node1258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1261 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1262 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node1263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1266 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1267 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1268 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node1268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1269 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1271 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1272 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def node1272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1274 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1275 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def node1275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def node1277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1278 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def node1279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk19 : Array Code := #[⟨6, 3, 2, node1216, node1216Labels⟩, ⟨5, 3, 2, node1217, node1217Labels⟩, ⟨5, 3, 2, node1218, node1218Labels⟩, ⟨5, 3, 2, node1219, node1219Labels⟩, ⟨5, 3, 2, node1220, node1220Labels⟩, ⟨4, 3, 2, node1221, node1221Labels⟩, ⟨6, 3, 2, node1222, node1222Labels⟩, ⟨6, 3, 2, node1223, node1223Labels⟩, ⟨5, 3, 2, node1224, node1224Labels⟩, ⟨5, 3, 2, node1225, node1225Labels⟩, ⟨5, 3, 2, node1226, node1226Labels⟩, ⟨4, 3, 2, node1227, node1227Labels⟩, ⟨6, 3, 2, node1228, node1228Labels⟩, ⟨5, 3, 2, node1229, node1229Labels⟩, ⟨5, 3, 2, node1230, node1230Labels⟩, ⟨4, 3, 2, node1231, node1231Labels⟩, ⟨6, 3, 2, node1232, node1232Labels⟩, ⟨6, 3, 2, node1233, node1233Labels⟩, ⟨5, 3, 2, node1234, node1234Labels⟩, ⟨6, 3, 2, node1235, node1235Labels⟩, ⟨5, 3, 2, node1236, node1236Labels⟩, ⟨5, 3, 2, node1237, node1237Labels⟩, ⟨5, 3, 2, node1238, node1238Labels⟩, ⟨4, 3, 2, node1239, node1239Labels⟩, ⟨5, 3, 2, node1240, node1240Labels⟩, ⟨5, 3, 2, node1241, node1241Labels⟩, ⟨4, 3, 2, node1242, node1242Labels⟩, ⟨4, 3, 2, node1243, node1243Labels⟩, ⟨4, 3, 2, node1244, node1244Labels⟩, ⟨4, 3, 2, node1245, node1245Labels⟩, ⟨4, 3, 2, node1246, node1246Labels⟩, ⟨6, 3, 2, node1247, node1247Labels⟩, ⟨6, 3, 2, node1248, node1248Labels⟩, ⟨5, 3, 2, node1249, node1249Labels⟩, ⟨6, 3, 2, node1250, node1250Labels⟩, ⟨5, 3, 2, node1251, node1251Labels⟩, ⟨5, 3, 2, node1252, node1252Labels⟩, ⟨5, 3, 2, node1253, node1253Labels⟩, ⟨5, 3, 2, node1254, node1254Labels⟩, ⟨4, 3, 2, node1255, node1255Labels⟩, ⟨6, 3, 2, node1256, node1256Labels⟩, ⟨5, 3, 2, node1257, node1257Labels⟩, ⟨4, 3, 2, node1258, node1258Labels⟩, ⟨6, 3, 2, node1259, node1259Labels⟩, ⟨6, 3, 2, node1260, node1260Labels⟩, ⟨5, 3, 2, node1261, node1261Labels⟩, ⟨5, 3, 2, node1262, node1262Labels⟩, ⟨5, 3, 2, node1263, node1263Labels⟩, ⟨4, 3, 2, node1264, node1264Labels⟩, ⟨6, 3, 2, node1265, node1265Labels⟩, ⟨5, 3, 2, node1266, node1266Labels⟩, ⟨5, 3, 2, node1267, node1267Labels⟩, ⟨5, 3, 2, node1268, node1268Labels⟩, ⟨4, 3, 2, node1269, node1269Labels⟩, ⟨5, 3, 2, node1270, node1270Labels⟩, ⟨4, 3, 2, node1271, node1271Labels⟩, ⟨4, 3, 2, node1272, node1272Labels⟩, ⟨4, 3, 2, node1273, node1273Labels⟩, ⟨4, 3, 2, node1274, node1274Labels⟩, ⟨3, 3, 2, node1275, node1275Labels⟩, ⟨6, 3, 2, node1276, node1276Labels⟩, ⟨5, 3, 2, node1277, node1277Labels⟩, ⟨5, 3, 2, node1278, node1278Labels⟩, ⟨4, 3, 2, node1279, node1279Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node128Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def node129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node130 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node130Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def node131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def node132Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node133 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def node133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node134 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def node134Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node135 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def node135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node136Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node138Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node139 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def node140Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node142Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node143 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node144 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node144Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node145 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node146 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node146Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node147 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node148 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node148Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node149 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node150 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node150Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node152 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node152Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node153 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node154 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def node154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

set_option maxHeartbeats 1000000 in
def node155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node156 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node156Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node157 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node158 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def node158Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node159 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def node159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node160 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def node160Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node161 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def node161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node162 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def node162Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node164Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node166Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node168Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node170Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node172Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node173Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node174Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node175 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node176 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node176Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node177 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node178 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node178Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node179Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node180Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node181 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node182Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node183 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node184Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node185 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def node185Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node186 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def node186Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node187 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def node187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node188 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def node188Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node190 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node190Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def codeChunk2 : Array Code := #[⟨5, 3, 1, node128, node128Labels⟩, ⟨4, 3, 1, node129, node129Labels⟩, ⟨5, 3, 1, node130, node130Labels⟩, ⟨4, 3, 1, node131, node131Labels⟩, ⟨4, 3, 1, node132, node132Labels⟩, ⟨4, 3, 1, node133, node133Labels⟩, ⟨4, 3, 1, node134, node134Labels⟩, ⟨4, 3, 1, node135, node135Labels⟩, ⟨4, 3, 1, node136, node136Labels⟩, ⟨5, 3, 1, node137, node137Labels⟩, ⟨5, 3, 1, node138, node138Labels⟩, ⟨5, 3, 1, node139, node139Labels⟩, ⟨4, 3, 1, node140, node140Labels⟩, ⟨6, 3, 1, node141, node141Labels⟩, ⟨5, 3, 1, node142, node142Labels⟩, ⟨4, 3, 1, node143, node143Labels⟩, ⟨5, 3, 1, node144, node144Labels⟩, ⟨5, 3, 1, node145, node145Labels⟩, ⟨4, 3, 1, node146, node146Labels⟩, ⟨4, 3, 1, node147, node147Labels⟩, ⟨4, 3, 1, node148, node148Labels⟩, ⟨4, 3, 1, node149, node149Labels⟩, ⟨5, 3, 1, node150, node150Labels⟩, ⟨5, 3, 1, node151, node151Labels⟩, ⟨4, 3, 1, node152, node152Labels⟩, ⟨4, 3, 1, node153, node153Labels⟩, ⟨3, 3, 1, node154, node154Labels⟩, ⟨5, 3, 1, node155, node155Labels⟩, ⟨4, 3, 1, node156, node156Labels⟩, ⟨4, 3, 1, node157, node157Labels⟩, ⟨3, 3, 1, node158, node158Labels⟩, ⟨3, 3, 1, node159, node159Labels⟩, ⟨3, 3, 1, node160, node160Labels⟩, ⟨3, 3, 1, node161, node161Labels⟩, ⟨2, 3, 1, node162, node162Labels⟩, ⟨6, 3, 1, node163, node163Labels⟩, ⟨6, 3, 1, node164, node164Labels⟩, ⟨6, 3, 1, node165, node165Labels⟩, ⟨6, 3, 1, node166, node166Labels⟩, ⟨6, 3, 1, node167, node167Labels⟩, ⟨5, 3, 1, node168, node168Labels⟩, ⟨5, 3, 1, node169, node169Labels⟩, ⟨5, 3, 1, node170, node170Labels⟩, ⟨6, 3, 1, node171, node171Labels⟩, ⟨6, 3, 1, node172, node172Labels⟩, ⟨5, 3, 1, node173, node173Labels⟩, ⟨6, 3, 1, node174, node174Labels⟩, ⟨5, 3, 1, node175, node175Labels⟩, ⟨5, 3, 1, node176, node176Labels⟩, ⟨5, 3, 1, node177, node177Labels⟩, ⟨5, 3, 1, node178, node178Labels⟩, ⟨6, 3, 1, node179, node179Labels⟩, ⟨5, 3, 1, node180, node180Labels⟩, ⟨5, 3, 1, node181, node181Labels⟩, ⟨5, 3, 1, node182, node182Labels⟩, ⟨5, 3, 1, node183, node183Labels⟩, ⟨5, 3, 1, node184, node184Labels⟩, ⟨4, 3, 1, node185, node185Labels⟩, ⟨4, 3, 1, node186, node186Labels⟩, ⟨4, 3, 1, node187, node187Labels⟩, ⟨4, 3, 1, node188, node188Labels⟩, ⟨6, 3, 1, node189, node189Labels⟩, ⟨5, 3, 1, node190, node190Labels⟩, ⟨6, 3, 1, node191, node191Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1280 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1281 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node1281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1282 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def node1282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1283 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def node1283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1284 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node1284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1285 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![4, -4, 0]]
def node1285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1286 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1287 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def node1287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1288 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def node1288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1289 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def node1289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1290 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1291 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1292 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1294 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1295 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1296 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def node1296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1297 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def node1297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1298 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1300 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1301 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1302 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1303 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def node1303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1304 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def node1304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1305 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1306 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1307 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def node1307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1308 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def node1308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1309 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def node1309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1310 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def node1310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1311 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def node1311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1312 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def node1312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1313 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def node1313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1315 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1317 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1318 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1320 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1321 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1322 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1323 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def node1323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1324 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def node1324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def node1325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1332 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def node1332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def node1333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node1334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def node1336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node1337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node1338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk20 : Array Code := #[⟨5, 3, 2, node1280, node1280Labels⟩, ⟨4, 3, 2, node1281, node1281Labels⟩, ⟨4, 3, 2, node1282, node1282Labels⟩, ⟨4, 3, 2, node1283, node1283Labels⟩, ⟨4, 3, 2, node1284, node1284Labels⟩, ⟨3, 3, 2, node1285, node1285Labels⟩, ⟨5, 3, 2, node1286, node1286Labels⟩, ⟨4, 3, 2, node1287, node1287Labels⟩, ⟨4, 3, 2, node1288, node1288Labels⟩, ⟨3, 3, 2, node1289, node1289Labels⟩, ⟨5, 3, 2, node1290, node1290Labels⟩, ⟨5, 3, 2, node1291, node1291Labels⟩, ⟨4, 3, 2, node1292, node1292Labels⟩, ⟨5, 3, 2, node1293, node1293Labels⟩, ⟨4, 3, 2, node1294, node1294Labels⟩, ⟨4, 3, 2, node1295, node1295Labels⟩, ⟨4, 3, 2, node1296, node1296Labels⟩, ⟨3, 3, 2, node1297, node1297Labels⟩, ⟨5, 3, 2, node1298, node1298Labels⟩, ⟨5, 3, 2, node1299, node1299Labels⟩, ⟨4, 3, 2, node1300, node1300Labels⟩, ⟨4, 3, 2, node1301, node1301Labels⟩, ⟨4, 3, 2, node1302, node1302Labels⟩, ⟨4, 3, 2, node1303, node1303Labels⟩, ⟨3, 3, 2, node1304, node1304Labels⟩, ⟨4, 3, 2, node1305, node1305Labels⟩, ⟨4, 3, 2, node1306, node1306Labels⟩, ⟨3, 3, 2, node1307, node1307Labels⟩, ⟨3, 3, 2, node1308, node1308Labels⟩, ⟨3, 3, 2, node1309, node1309Labels⟩, ⟨3, 3, 2, node1310, node1310Labels⟩, ⟨3, 3, 2, node1311, node1311Labels⟩, ⟨3, 3, 2, node1312, node1312Labels⟩, ⟨2, 3, 2, node1313, node1313Labels⟩, ⟨6, 3, 2, node1314, node1314Labels⟩, ⟨5, 3, 2, node1315, node1315Labels⟩, ⟨6, 3, 2, node1316, node1316Labels⟩, ⟨5, 3, 2, node1317, node1317Labels⟩, ⟨5, 3, 2, node1318, node1318Labels⟩, ⟨6, 3, 2, node1319, node1319Labels⟩, ⟨5, 3, 2, node1320, node1320Labels⟩, ⟨5, 3, 2, node1321, node1321Labels⟩, ⟨5, 3, 2, node1322, node1322Labels⟩, ⟨4, 3, 2, node1323, node1323Labels⟩, ⟨4, 3, 2, node1324, node1324Labels⟩, ⟨4, 3, 2, node1325, node1325Labels⟩, ⟨6, 3, 2, node1326, node1326Labels⟩, ⟨6, 3, 2, node1327, node1327Labels⟩, ⟨6, 3, 2, node1328, node1328Labels⟩, ⟨6, 3, 2, node1329, node1329Labels⟩, ⟨6, 3, 2, node1330, node1330Labels⟩, ⟨6, 3, 2, node1331, node1331Labels⟩, ⟨5, 3, 2, node1332, node1332Labels⟩, ⟨5, 3, 2, node1333, node1333Labels⟩, ⟨5, 3, 2, node1334, node1334Labels⟩, ⟨6, 3, 2, node1335, node1335Labels⟩, ⟨5, 3, 2, node1336, node1336Labels⟩, ⟨5, 3, 2, node1337, node1337Labels⟩, ⟨5, 3, 2, node1338, node1338Labels⟩, ⟨6, 3, 2, node1339, node1339Labels⟩, ⟨5, 3, 2, node1340, node1340Labels⟩, ⟨6, 3, 2, node1341, node1341Labels⟩, ⟨5, 3, 2, node1342, node1342Labels⟩, ⟨5, 3, 2, node1343, node1343Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1344 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node1347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1348 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def node1348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1349 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -3, 0]]
def node1349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1351 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1352 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def node1352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1353 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def node1353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1369 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def node1369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1372 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def node1372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1373 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![3, -2, -1]]
def node1373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def node1374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1375 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def node1375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def node1385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node1389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node1390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node1394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node1397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node1399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node1400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node1401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![4, -3, -1]]
def node1402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node1404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1407 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node1407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk21 : Array Code := #[⟨5, 3, 2, node1344, node1344Labels⟩, ⟨6, 3, 2, node1345, node1345Labels⟩, ⟨5, 3, 2, node1346, node1346Labels⟩, ⟨5, 3, 2, node1347, node1347Labels⟩, ⟨4, 3, 2, node1348, node1348Labels⟩, ⟨4, 3, 2, node1349, node1349Labels⟩, ⟨6, 3, 2, node1350, node1350Labels⟩, ⟨5, 3, 2, node1351, node1351Labels⟩, ⟨4, 3, 2, node1352, node1352Labels⟩, ⟨4, 3, 2, node1353, node1353Labels⟩, ⟨6, 3, 2, node1354, node1354Labels⟩, ⟨5, 3, 2, node1355, node1355Labels⟩, ⟨5, 3, 2, node1356, node1356Labels⟩, ⟨6, 3, 2, node1357, node1357Labels⟩, ⟨6, 3, 2, node1358, node1358Labels⟩, ⟨5, 3, 2, node1359, node1359Labels⟩, ⟨6, 3, 2, node1360, node1360Labels⟩, ⟨5, 3, 2, node1361, node1361Labels⟩, ⟨5, 3, 2, node1362, node1362Labels⟩, ⟨5, 3, 2, node1363, node1363Labels⟩, ⟨6, 3, 2, node1364, node1364Labels⟩, ⟨5, 3, 2, node1365, node1365Labels⟩, ⟨6, 3, 2, node1366, node1366Labels⟩, ⟨5, 3, 2, node1367, node1367Labels⟩, ⟨5, 3, 2, node1368, node1368Labels⟩, ⟨4, 3, 2, node1369, node1369Labels⟩, ⟨5, 3, 2, node1370, node1370Labels⟩, ⟨5, 3, 2, node1371, node1371Labels⟩, ⟨4, 3, 2, node1372, node1372Labels⟩, ⟨4, 3, 2, node1373, node1373Labels⟩, ⟨4, 3, 2, node1374, node1374Labels⟩, ⟨4, 3, 2, node1375, node1375Labels⟩, ⟨6, 3, 2, node1376, node1376Labels⟩, ⟨6, 3, 2, node1377, node1377Labels⟩, ⟨6, 3, 2, node1378, node1378Labels⟩, ⟨6, 3, 2, node1379, node1379Labels⟩, ⟨6, 3, 2, node1380, node1380Labels⟩, ⟨6, 3, 2, node1381, node1381Labels⟩, ⟨6, 3, 2, node1382, node1382Labels⟩, ⟨6, 3, 2, node1383, node1383Labels⟩, ⟨6, 3, 2, node1384, node1384Labels⟩, ⟨5, 3, 2, node1385, node1385Labels⟩, ⟨6, 3, 2, node1386, node1386Labels⟩, ⟨6, 3, 2, node1387, node1387Labels⟩, ⟨5, 3, 2, node1388, node1388Labels⟩, ⟨5, 3, 2, node1389, node1389Labels⟩, ⟨5, 3, 2, node1390, node1390Labels⟩, ⟨5, 3, 2, node1391, node1391Labels⟩, ⟨6, 3, 2, node1392, node1392Labels⟩, ⟨6, 3, 2, node1393, node1393Labels⟩, ⟨5, 3, 2, node1394, node1394Labels⟩, ⟨6, 3, 2, node1395, node1395Labels⟩, ⟨6, 3, 2, node1396, node1396Labels⟩, ⟨5, 3, 2, node1397, node1397Labels⟩, ⟨6, 3, 2, node1398, node1398Labels⟩, ⟨5, 3, 2, node1399, node1399Labels⟩, ⟨5, 3, 2, node1400, node1400Labels⟩, ⟨5, 3, 2, node1401, node1401Labels⟩, ⟨4, 3, 2, node1402, node1402Labels⟩, ⟨6, 3, 2, node1403, node1403Labels⟩, ⟨5, 3, 2, node1404, node1404Labels⟩, ⟨6, 3, 2, node1405, node1405Labels⟩, ⟨5, 3, 2, node1406, node1406Labels⟩, ⟨5, 3, 2, node1407, node1407Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1408 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def node1408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1413 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node1413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node1415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1416 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node1416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1417 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def node1417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1418 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def node1418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1419 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node1419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1420 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node1420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1422 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def node1422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1423 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def node1423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1424 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def node1424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def node1425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def node1426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def node1427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node1428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def node1429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1430 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def node1430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1431 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node1431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1432 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![4, -4, 0]]
def node1432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![2, 1, -3]]
def node1434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def node1436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def node1437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1438 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def node1438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def node1440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1441 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node1442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1443 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def node1444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1445 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def node1445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1446 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1447 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1448 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1449 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def node1449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1450 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def node1450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1451 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node1451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1452 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def node1452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1453 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def node1453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1454 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def node1454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1455 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def node1455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1456 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 3, 1], ![4, -3, -1]]
def node1456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1458 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1459 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, -1, 0], ![3, 0, -3]]
def node1459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1460 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1461 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![1, 0, -1], ![3, -1, -2]]
def node1461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1462 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -3, 3], ![2, -1, -1], ![2, 0, -2]]
def node1462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node1466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1469 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def node1469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1471 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def node1471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk22 : Array Code := #[⟨4, 3, 2, node1408, node1408Labels⟩, ⟨6, 3, 2, node1409, node1409Labels⟩, ⟨5, 3, 2, node1410, node1410Labels⟩, ⟨5, 3, 2, node1411, node1411Labels⟩, ⟨5, 3, 2, node1412, node1412Labels⟩, ⟨4, 3, 2, node1413, node1413Labels⟩, ⟨5, 3, 2, node1414, node1414Labels⟩, ⟨5, 3, 2, node1415, node1415Labels⟩, ⟨4, 3, 2, node1416, node1416Labels⟩, ⟨4, 3, 2, node1417, node1417Labels⟩, ⟨4, 3, 2, node1418, node1418Labels⟩, ⟨4, 3, 2, node1419, node1419Labels⟩, ⟨4, 3, 2, node1420, node1420Labels⟩, ⟨6, 3, 2, node1421, node1421Labels⟩, ⟨5, 3, 2, node1422, node1422Labels⟩, ⟨5, 3, 2, node1423, node1423Labels⟩, ⟨4, 3, 2, node1424, node1424Labels⟩, ⟨5, 3, 2, node1425, node1425Labels⟩, ⟨5, 3, 2, node1426, node1426Labels⟩, ⟨5, 3, 2, node1427, node1427Labels⟩, ⟨4, 3, 2, node1428, node1428Labels⟩, ⟨4, 3, 2, node1429, node1429Labels⟩, ⟨4, 3, 2, node1430, node1430Labels⟩, ⟨4, 3, 2, node1431, node1431Labels⟩, ⟨3, 3, 2, node1432, node1432Labels⟩, ⟨5, 3, 2, node1433, node1433Labels⟩, ⟨4, 3, 2, node1434, node1434Labels⟩, ⟨5, 3, 2, node1435, node1435Labels⟩, ⟨4, 3, 2, node1436, node1436Labels⟩, ⟨4, 3, 2, node1437, node1437Labels⟩, ⟨3, 3, 2, node1438, node1438Labels⟩, ⟨5, 3, 2, node1439, node1439Labels⟩, ⟨4, 3, 2, node1440, node1440Labels⟩, ⟨5, 3, 2, node1441, node1441Labels⟩, ⟨4, 3, 2, node1442, node1442Labels⟩, ⟨4, 3, 2, node1443, node1443Labels⟩, ⟨4, 3, 2, node1444, node1444Labels⟩, ⟨3, 3, 2, node1445, node1445Labels⟩, ⟨5, 3, 2, node1446, node1446Labels⟩, ⟨4, 3, 2, node1447, node1447Labels⟩, ⟨4, 3, 2, node1448, node1448Labels⟩, ⟨4, 3, 2, node1449, node1449Labels⟩, ⟨3, 3, 2, node1450, node1450Labels⟩, ⟨4, 3, 2, node1451, node1451Labels⟩, ⟨3, 3, 2, node1452, node1452Labels⟩, ⟨3, 3, 2, node1453, node1453Labels⟩, ⟨3, 3, 2, node1454, node1454Labels⟩, ⟨3, 3, 2, node1455, node1455Labels⟩, ⟨2, 3, 2, node1456, node1456Labels⟩, ⟨6, 3, 2, node1457, node1457Labels⟩, ⟨5, 3, 2, node1458, node1458Labels⟩, ⟨4, 3, 2, node1459, node1459Labels⟩, ⟨5, 3, 2, node1460, node1460Labels⟩, ⟨4, 3, 2, node1461, node1461Labels⟩, ⟨4, 3, 2, node1462, node1462Labels⟩, ⟨6, 3, 2, node1463, node1463Labels⟩, ⟨6, 3, 2, node1464, node1464Labels⟩, ⟨5, 3, 2, node1465, node1465Labels⟩, ⟨5, 3, 2, node1466, node1466Labels⟩, ⟨6, 3, 2, node1467, node1467Labels⟩, ⟨5, 3, 2, node1468, node1468Labels⟩, ⟨4, 3, 2, node1469, node1469Labels⟩, ⟨5, 3, 2, node1470, node1470Labels⟩, ⟨4, 3, 2, node1471, node1471Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1472 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def node1472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1473 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def node1473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node1474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1476 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node1476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1478 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node1478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node1479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node1480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1481 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def node1481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1483 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def node1484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def node1485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def node1486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1487 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![3, -2, -1]]
def node1487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1490 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1494 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def node1494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1495 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def node1495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1496 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def node1496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1499 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def node1499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1500 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def node1500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node1501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node1502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1503 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1505 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1507 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1508 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1509 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node1509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1513 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node1513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1516 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node1516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1518 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node1518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1519 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node1519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1520 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node1520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1521 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def node1521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1523 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node1523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1524 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1525 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node1525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1526 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node1526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1527 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def node1527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node1529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1530 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node1530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1531 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def node1531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1532 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def node1532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1533 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node1533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1534 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def node1534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1535 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk23 : Array Code := #[⟨4, 3, 2, node1472, node1472Labels⟩, ⟨4, 3, 2, node1473, node1473Labels⟩, ⟨6, 3, 2, node1474, node1474Labels⟩, ⟨6, 3, 2, node1475, node1475Labels⟩, ⟨5, 3, 2, node1476, node1476Labels⟩, ⟨6, 3, 2, node1477, node1477Labels⟩, ⟨5, 3, 2, node1478, node1478Labels⟩, ⟨5, 3, 2, node1479, node1479Labels⟩, ⟨5, 3, 2, node1480, node1480Labels⟩, ⟨4, 3, 2, node1481, node1481Labels⟩, ⟨5, 3, 2, node1482, node1482Labels⟩, ⟨5, 3, 2, node1483, node1483Labels⟩, ⟨4, 3, 2, node1484, node1484Labels⟩, ⟨4, 3, 2, node1485, node1485Labels⟩, ⟨4, 3, 2, node1486, node1486Labels⟩, ⟨3, 3, 2, node1487, node1487Labels⟩, ⟨6, 3, 2, node1488, node1488Labels⟩, ⟨5, 3, 2, node1489, node1489Labels⟩, ⟨5, 3, 2, node1490, node1490Labels⟩, ⟨6, 3, 2, node1491, node1491Labels⟩, ⟨5, 3, 2, node1492, node1492Labels⟩, ⟨5, 3, 2, node1493, node1493Labels⟩, ⟨4, 3, 2, node1494, node1494Labels⟩, ⟨4, 3, 2, node1495, node1495Labels⟩, ⟨4, 3, 2, node1496, node1496Labels⟩, ⟨6, 3, 2, node1497, node1497Labels⟩, ⟨5, 3, 2, node1498, node1498Labels⟩, ⟨4, 3, 2, node1499, node1499Labels⟩, ⟨4, 3, 2, node1500, node1500Labels⟩, ⟨6, 3, 2, node1501, node1501Labels⟩, ⟨6, 3, 2, node1502, node1502Labels⟩, ⟨5, 3, 2, node1503, node1503Labels⟩, ⟨6, 3, 2, node1504, node1504Labels⟩, ⟨5, 3, 2, node1505, node1505Labels⟩, ⟨6, 3, 2, node1506, node1506Labels⟩, ⟨5, 3, 2, node1507, node1507Labels⟩, ⟨5, 3, 2, node1508, node1508Labels⟩, ⟨4, 3, 2, node1509, node1509Labels⟩, ⟨6, 3, 2, node1510, node1510Labels⟩, ⟨5, 3, 2, node1511, node1511Labels⟩, ⟨5, 3, 2, node1512, node1512Labels⟩, ⟨4, 3, 2, node1513, node1513Labels⟩, ⟨5, 3, 2, node1514, node1514Labels⟩, ⟨5, 3, 2, node1515, node1515Labels⟩, ⟨4, 3, 2, node1516, node1516Labels⟩, ⟨5, 3, 2, node1517, node1517Labels⟩, ⟨4, 3, 2, node1518, node1518Labels⟩, ⟨4, 3, 2, node1519, node1519Labels⟩, ⟨4, 3, 2, node1520, node1520Labels⟩, ⟨3, 3, 2, node1521, node1521Labels⟩, ⟨5, 3, 2, node1522, node1522Labels⟩, ⟨4, 3, 2, node1523, node1523Labels⟩, ⟨5, 3, 2, node1524, node1524Labels⟩, ⟨4, 3, 2, node1525, node1525Labels⟩, ⟨4, 3, 2, node1526, node1526Labels⟩, ⟨3, 3, 2, node1527, node1527Labels⟩, ⟨5, 3, 2, node1528, node1528Labels⟩, ⟨4, 3, 2, node1529, node1529Labels⟩, ⟨4, 3, 2, node1530, node1530Labels⟩, ⟨3, 3, 2, node1531, node1531Labels⟩, ⟨4, 3, 2, node1532, node1532Labels⟩, ⟨4, 3, 2, node1533, node1533Labels⟩, ⟨3, 3, 2, node1534, node1534Labels⟩, ⟨4, 3, 2, node1535, node1535Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1536 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1537 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def node1537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1538 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def node1538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1539 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def node1539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1540 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def node1540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1541 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def node1541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1543 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1544 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1546 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1547 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1548 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def node1548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def node1549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1555 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def node1555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1557 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1558 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1565 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1568 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1571 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1572 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1573 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def node1574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1575 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1576 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def node1576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1577 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def node1577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1578 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def node1578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, 0, -2], ![2, 1, -3]]
def node1579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1580Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1583Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1584 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def node1584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1585 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node1585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1586Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1589Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1590 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def node1590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1599 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk24 : Array Code := #[⟨4, 3, 2, node1536, node1536Labels⟩, ⟨3, 3, 2, node1537, node1537Labels⟩, ⟨3, 3, 2, node1538, node1538Labels⟩, ⟨3, 3, 2, node1539, node1539Labels⟩, ⟨3, 3, 2, node1540, node1540Labels⟩, ⟨2, 3, 2, node1541, node1541Labels⟩, ⟨6, 3, 2, node1542, node1542Labels⟩, ⟨5, 3, 2, node1543, node1543Labels⟩, ⟨5, 3, 2, node1544, node1544Labels⟩, ⟨6, 3, 2, node1545, node1545Labels⟩, ⟨5, 3, 2, node1546, node1546Labels⟩, ⟨5, 3, 2, node1547, node1547Labels⟩, ⟨4, 3, 2, node1548, node1548Labels⟩, ⟨4, 3, 2, node1549, node1549Labels⟩, ⟨6, 3, 2, node1550, node1550Labels⟩, ⟨6, 3, 2, node1551, node1551Labels⟩, ⟨6, 3, 2, node1552, node1552Labels⟩, ⟨6, 3, 2, node1553, node1553Labels⟩, ⟨6, 3, 2, node1554, node1554Labels⟩, ⟨5, 3, 2, node1555, node1555Labels⟩, ⟨6, 3, 2, node1556, node1556Labels⟩, ⟨5, 3, 2, node1557, node1557Labels⟩, ⟨5, 3, 2, node1558, node1558Labels⟩, ⟨5, 3, 2, node1559, node1559Labels⟩, ⟨5, 3, 2, node1560, node1560Labels⟩, ⟨6, 3, 2, node1561, node1561Labels⟩, ⟨5, 3, 2, node1562, node1562Labels⟩, ⟨6, 3, 2, node1563, node1563Labels⟩, ⟨5, 3, 2, node1564, node1564Labels⟩, ⟨5, 3, 2, node1565, node1565Labels⟩, ⟨6, 3, 2, node1566, node1566Labels⟩, ⟨6, 3, 2, node1567, node1567Labels⟩, ⟨5, 3, 2, node1568, node1568Labels⟩, ⟨5, 3, 2, node1569, node1569Labels⟩, ⟨5, 3, 2, node1570, node1570Labels⟩, ⟨5, 3, 2, node1571, node1571Labels⟩, ⟨5, 3, 2, node1572, node1572Labels⟩, ⟨5, 3, 2, node1573, node1573Labels⟩, ⟨4, 3, 2, node1574, node1574Labels⟩, ⟨5, 3, 2, node1575, node1575Labels⟩, ⟨4, 3, 2, node1576, node1576Labels⟩, ⟨4, 3, 2, node1577, node1577Labels⟩, ⟨4, 3, 2, node1578, node1578Labels⟩, ⟨4, 3, 2, node1579, node1579Labels⟩, ⟨6, 3, 2, node1580, node1580Labels⟩, ⟨6, 3, 2, node1581, node1581Labels⟩, ⟨6, 3, 2, node1582, node1582Labels⟩, ⟨6, 3, 2, node1583, node1583Labels⟩, ⟨5, 3, 2, node1584, node1584Labels⟩, ⟨5, 3, 2, node1585, node1585Labels⟩, ⟨6, 3, 2, node1586, node1586Labels⟩, ⟨6, 3, 2, node1587, node1587Labels⟩, ⟨6, 3, 2, node1588, node1588Labels⟩, ⟨6, 3, 2, node1589, node1589Labels⟩, ⟨5, 3, 2, node1590, node1590Labels⟩, ⟨5, 3, 2, node1591, node1591Labels⟩, ⟨6, 3, 2, node1592, node1592Labels⟩, ⟨6, 3, 2, node1593, node1593Labels⟩, ⟨6, 3, 2, node1594, node1594Labels⟩, ⟨6, 3, 2, node1595, node1595Labels⟩, ⟨6, 3, 2, node1596, node1596Labels⟩, ⟨6, 3, 2, node1597, node1597Labels⟩, ⟨6, 3, 2, node1598, node1598Labels⟩, ⟨5, 3, 2, node1599, node1599Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1601Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1602 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1603 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1604 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1604Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1605 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1607Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1608 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1610 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1611 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1612 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1616Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1617 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1618 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1619 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1619Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def node1620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1622Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1623 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1624 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1625 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1625Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1627 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1628 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def node1628Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1629 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def node1629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1630 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1631 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1633 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def node1633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1634 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node1634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1641 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1643 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1645 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1646 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1647 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def node1647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1648 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1649 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1650 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def node1650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1651 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def node1651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1652 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def node1652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1653 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def node1653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1655 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1656 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1657 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def node1657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1658 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1659 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def node1659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1660 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def node1660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1661 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def node1661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk25 : Array Code := #[⟨6, 3, 2, node1600, node1600Labels⟩, ⟨6, 3, 2, node1601, node1601Labels⟩, ⟨5, 3, 2, node1602, node1602Labels⟩, ⟨5, 3, 2, node1603, node1603Labels⟩, ⟨5, 3, 2, node1604, node1604Labels⟩, ⟨5, 3, 2, node1605, node1605Labels⟩, ⟨6, 3, 2, node1606, node1606Labels⟩, ⟨6, 3, 2, node1607, node1607Labels⟩, ⟨5, 3, 2, node1608, node1608Labels⟩, ⟨6, 3, 2, node1609, node1609Labels⟩, ⟨5, 3, 2, node1610, node1610Labels⟩, ⟨5, 3, 2, node1611, node1611Labels⟩, ⟨5, 3, 2, node1612, node1612Labels⟩, ⟨6, 3, 2, node1613, node1613Labels⟩, ⟨6, 3, 2, node1614, node1614Labels⟩, ⟨5, 3, 2, node1615, node1615Labels⟩, ⟨6, 3, 2, node1616, node1616Labels⟩, ⟨5, 3, 2, node1617, node1617Labels⟩, ⟨5, 3, 2, node1618, node1618Labels⟩, ⟨5, 3, 2, node1619, node1619Labels⟩, ⟨4, 3, 2, node1620, node1620Labels⟩, ⟨6, 3, 2, node1621, node1621Labels⟩, ⟨5, 3, 2, node1622, node1622Labels⟩, ⟨5, 3, 2, node1623, node1623Labels⟩, ⟨5, 3, 2, node1624, node1624Labels⟩, ⟨4, 3, 2, node1625, node1625Labels⟩, ⟨5, 3, 2, node1626, node1626Labels⟩, ⟨4, 3, 2, node1627, node1627Labels⟩, ⟨4, 3, 2, node1628, node1628Labels⟩, ⟨4, 3, 2, node1629, node1629Labels⟩, ⟨4, 3, 2, node1630, node1630Labels⟩, ⟨4, 3, 2, node1631, node1631Labels⟩, ⟨6, 3, 2, node1632, node1632Labels⟩, ⟨5, 3, 2, node1633, node1633Labels⟩, ⟨5, 3, 2, node1634, node1634Labels⟩, ⟨6, 3, 2, node1635, node1635Labels⟩, ⟨6, 3, 2, node1636, node1636Labels⟩, ⟨5, 3, 2, node1637, node1637Labels⟩, ⟨6, 3, 2, node1638, node1638Labels⟩, ⟨5, 3, 2, node1639, node1639Labels⟩, ⟨5, 3, 2, node1640, node1640Labels⟩, ⟨5, 3, 2, node1641, node1641Labels⟩, ⟨6, 3, 2, node1642, node1642Labels⟩, ⟨5, 3, 2, node1643, node1643Labels⟩, ⟨6, 3, 2, node1644, node1644Labels⟩, ⟨5, 3, 2, node1645, node1645Labels⟩, ⟨5, 3, 2, node1646, node1646Labels⟩, ⟨4, 3, 2, node1647, node1647Labels⟩, ⟨5, 3, 2, node1648, node1648Labels⟩, ⟨5, 3, 2, node1649, node1649Labels⟩, ⟨4, 3, 2, node1650, node1650Labels⟩, ⟨4, 3, 2, node1651, node1651Labels⟩, ⟨4, 3, 2, node1652, node1652Labels⟩, ⟨4, 3, 2, node1653, node1653Labels⟩, ⟨6, 3, 2, node1654, node1654Labels⟩, ⟨5, 3, 2, node1655, node1655Labels⟩, ⟨5, 3, 2, node1656, node1656Labels⟩, ⟨4, 3, 2, node1657, node1657Labels⟩, ⟨5, 3, 2, node1658, node1658Labels⟩, ⟨4, 3, 2, node1659, node1659Labels⟩, ⟨4, 3, 2, node1660, node1660Labels⟩, ⟨4, 3, 2, node1661, node1661Labels⟩, ⟨6, 3, 2, node1662, node1662Labels⟩, ⟨6, 3, 2, node1663, node1663Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1666 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node1666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1669 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node1669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1672 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node1672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1674 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node1674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1675 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node1675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1676 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node1676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1677 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def node1677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1679 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node1679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1681 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node1681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1682 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node1682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1683 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def node1683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1685 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node1685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1686 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node1686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1687 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def node1687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1688 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def node1688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1689 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node1689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1690 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1691 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1692 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node1692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1693 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node1693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1694 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node1694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1695 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def node1695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node1696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node1697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node1698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node1699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1700 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node1700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node1701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1702 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node1702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1704 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node1704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1707 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node1707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1708 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node1708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1709 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node1709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1710 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node1710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node1711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1712 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node1712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1714 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node1714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1715 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node1715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1716 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node1716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1718 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def node1718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1719 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def node1719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1720 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node1720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1721 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node1721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1722 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def node1722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1723 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node1723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1724 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node1724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1725 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node1725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1726 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node1726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1727 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node1727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk26 : Array Code := #[⟨6, 3, 2, node1664, node1664Labels⟩, ⟨6, 3, 2, node1665, node1665Labels⟩, ⟨5, 3, 2, node1666, node1666Labels⟩, ⟨6, 3, 2, node1667, node1667Labels⟩, ⟨6, 3, 2, node1668, node1668Labels⟩, ⟨5, 3, 2, node1669, node1669Labels⟩, ⟨6, 3, 2, node1670, node1670Labels⟩, ⟨6, 3, 2, node1671, node1671Labels⟩, ⟨5, 3, 2, node1672, node1672Labels⟩, ⟨6, 3, 2, node1673, node1673Labels⟩, ⟨5, 3, 2, node1674, node1674Labels⟩, ⟨5, 3, 2, node1675, node1675Labels⟩, ⟨5, 3, 2, node1676, node1676Labels⟩, ⟨4, 3, 2, node1677, node1677Labels⟩, ⟨6, 3, 2, node1678, node1678Labels⟩, ⟨5, 3, 2, node1679, node1679Labels⟩, ⟨6, 3, 2, node1680, node1680Labels⟩, ⟨5, 3, 2, node1681, node1681Labels⟩, ⟨5, 3, 2, node1682, node1682Labels⟩, ⟨4, 3, 2, node1683, node1683Labels⟩, ⟨6, 3, 2, node1684, node1684Labels⟩, ⟨5, 3, 2, node1685, node1685Labels⟩, ⟨5, 3, 2, node1686, node1686Labels⟩, ⟨4, 3, 2, node1687, node1687Labels⟩, ⟨5, 3, 2, node1688, node1688Labels⟩, ⟨5, 3, 2, node1689, node1689Labels⟩, ⟨5, 3, 2, node1690, node1690Labels⟩, ⟨5, 3, 2, node1691, node1691Labels⟩, ⟨4, 3, 2, node1692, node1692Labels⟩, ⟨4, 3, 2, node1693, node1693Labels⟩, ⟨4, 3, 2, node1694, node1694Labels⟩, ⟨4, 3, 2, node1695, node1695Labels⟩, ⟨6, 3, 2, node1696, node1696Labels⟩, ⟨6, 3, 2, node1697, node1697Labels⟩, ⟨6, 3, 2, node1698, node1698Labels⟩, ⟨6, 3, 2, node1699, node1699Labels⟩, ⟨5, 3, 2, node1700, node1700Labels⟩, ⟨6, 3, 2, node1701, node1701Labels⟩, ⟨5, 3, 2, node1702, node1702Labels⟩, ⟨6, 3, 2, node1703, node1703Labels⟩, ⟨5, 3, 2, node1704, node1704Labels⟩, ⟨6, 3, 2, node1705, node1705Labels⟩, ⟨6, 3, 2, node1706, node1706Labels⟩, ⟨5, 3, 2, node1707, node1707Labels⟩, ⟨5, 3, 2, node1708, node1708Labels⟩, ⟨5, 3, 2, node1709, node1709Labels⟩, ⟨4, 3, 2, node1710, node1710Labels⟩, ⟨6, 3, 2, node1711, node1711Labels⟩, ⟨5, 3, 2, node1712, node1712Labels⟩, ⟨6, 3, 2, node1713, node1713Labels⟩, ⟨5, 3, 2, node1714, node1714Labels⟩, ⟨5, 3, 2, node1715, node1715Labels⟩, ⟨4, 3, 2, node1716, node1716Labels⟩, ⟨6, 3, 2, node1717, node1717Labels⟩, ⟨5, 3, 2, node1718, node1718Labels⟩, ⟨4, 3, 2, node1719, node1719Labels⟩, ⟨5, 3, 2, node1720, node1720Labels⟩, ⟨5, 3, 2, node1721, node1721Labels⟩, ⟨4, 3, 2, node1722, node1722Labels⟩, ⟨5, 3, 2, node1723, node1723Labels⟩, ⟨5, 3, 2, node1724, node1724Labels⟩, ⟨4, 3, 2, node1725, node1725Labels⟩, ⟨5, 3, 2, node1726, node1726Labels⟩, ⟨4, 3, 2, node1727, node1727Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1728 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node1728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1729 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node1729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1730 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def node1730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node1731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1732 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node1732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1733 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def node1733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1734 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node1734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1735 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def node1735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1736 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node1736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1737 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node1737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1738 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node1738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1739 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node1739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1740 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node1740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1741 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def node1741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1742 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node1742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1743 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def node1743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1744 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node1744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1745 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def node1745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1746 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def node1746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1747 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def node1747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1748 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def node1748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1749 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def node1749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1750 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1751 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1752 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def node1752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1753 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1754 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def node1754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1755 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def node1755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1756 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def node1756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1757 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def node1757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1758 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -1, 4], ![3, 1, -4]]
def node1758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1765 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def node1765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1766 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node1766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1767 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node1767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1772 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1773 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1774 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1775 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1776Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1777 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1778 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node1778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1779 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node1779Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1780 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1781 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node1781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1782 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node1782Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1783 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def node1783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1788 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk27 : Array Code := #[⟨4, 3, 2, node1728, node1728Labels⟩, ⟨4, 3, 2, node1729, node1729Labels⟩, ⟨3, 3, 2, node1730, node1730Labels⟩, ⟨6, 3, 2, node1731, node1731Labels⟩, ⟨5, 3, 2, node1732, node1732Labels⟩, ⟨4, 3, 2, node1733, node1733Labels⟩, ⟨5, 3, 2, node1734, node1734Labels⟩, ⟨4, 3, 2, node1735, node1735Labels⟩, ⟨5, 3, 2, node1736, node1736Labels⟩, ⟨5, 3, 2, node1737, node1737Labels⟩, ⟨4, 3, 2, node1738, node1738Labels⟩, ⟨4, 3, 2, node1739, node1739Labels⟩, ⟨4, 3, 2, node1740, node1740Labels⟩, ⟨3, 3, 2, node1741, node1741Labels⟩, ⟨5, 3, 2, node1742, node1742Labels⟩, ⟨4, 3, 2, node1743, node1743Labels⟩, ⟨5, 3, 2, node1744, node1744Labels⟩, ⟨4, 3, 2, node1745, node1745Labels⟩, ⟨4, 3, 2, node1746, node1746Labels⟩, ⟨3, 3, 2, node1747, node1747Labels⟩, ⟨4, 3, 2, node1748, node1748Labels⟩, ⟨4, 3, 2, node1749, node1749Labels⟩, ⟨4, 3, 2, node1750, node1750Labels⟩, ⟨4, 3, 2, node1751, node1751Labels⟩, ⟨3, 3, 2, node1752, node1752Labels⟩, ⟨4, 3, 2, node1753, node1753Labels⟩, ⟨3, 3, 2, node1754, node1754Labels⟩, ⟨3, 3, 2, node1755, node1755Labels⟩, ⟨3, 3, 2, node1756, node1756Labels⟩, ⟨3, 3, 2, node1757, node1757Labels⟩, ⟨2, 3, 2, node1758, node1758Labels⟩, ⟨6, 3, 2, node1759, node1759Labels⟩, ⟨6, 3, 2, node1760, node1760Labels⟩, ⟨6, 3, 2, node1761, node1761Labels⟩, ⟨6, 3, 2, node1762, node1762Labels⟩, ⟨6, 3, 2, node1763, node1763Labels⟩, ⟨6, 3, 2, node1764, node1764Labels⟩, ⟨5, 3, 2, node1765, node1765Labels⟩, ⟨5, 3, 2, node1766, node1766Labels⟩, ⟨5, 3, 2, node1767, node1767Labels⟩, ⟨6, 3, 2, node1768, node1768Labels⟩, ⟨6, 3, 2, node1769, node1769Labels⟩, ⟨6, 3, 2, node1770, node1770Labels⟩, ⟨6, 3, 2, node1771, node1771Labels⟩, ⟨5, 3, 2, node1772, node1772Labels⟩, ⟨5, 3, 2, node1773, node1773Labels⟩, ⟨5, 3, 2, node1774, node1774Labels⟩, ⟨5, 3, 2, node1775, node1775Labels⟩, ⟨6, 3, 2, node1776, node1776Labels⟩, ⟨5, 3, 2, node1777, node1777Labels⟩, ⟨5, 3, 2, node1778, node1778Labels⟩, ⟨5, 3, 2, node1779, node1779Labels⟩, ⟨5, 3, 2, node1780, node1780Labels⟩, ⟨5, 3, 2, node1781, node1781Labels⟩, ⟨5, 3, 2, node1782, node1782Labels⟩, ⟨4, 3, 2, node1783, node1783Labels⟩, ⟨6, 3, 2, node1784, node1784Labels⟩, ⟨6, 3, 2, node1785, node1785Labels⟩, ⟨6, 3, 2, node1786, node1786Labels⟩, ⟨6, 3, 2, node1787, node1787Labels⟩, ⟨5, 3, 2, node1788, node1788Labels⟩, ⟨6, 3, 2, node1789, node1789Labels⟩, ⟨6, 3, 2, node1790, node1790Labels⟩, ⟨6, 3, 2, node1791, node1791Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1795 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1796 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1797 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1799 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def node1799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1800 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1804 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1809 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1810 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1812 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1813 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1814 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1815 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1816 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1817 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def node1817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1818 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def node1818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1819 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def node1819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1820 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def node1820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1825 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1826 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1830 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def node1830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1831 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def node1831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1832 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def node1832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1839 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def node1839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1840 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1841 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1843 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1845 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1846 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1849 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1850 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1851 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1855 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk28 : Array Code := #[⟨6, 3, 2, node1792, node1792Labels⟩, ⟨6, 3, 2, node1793, node1793Labels⟩, ⟨6, 3, 2, node1794, node1794Labels⟩, ⟨5, 3, 2, node1795, node1795Labels⟩, ⟨5, 3, 2, node1796, node1796Labels⟩, ⟨5, 3, 2, node1797, node1797Labels⟩, ⟨6, 3, 2, node1798, node1798Labels⟩, ⟨5, 3, 2, node1799, node1799Labels⟩, ⟨5, 3, 2, node1800, node1800Labels⟩, ⟨6, 3, 2, node1801, node1801Labels⟩, ⟨6, 3, 2, node1802, node1802Labels⟩, ⟨6, 3, 2, node1803, node1803Labels⟩, ⟨5, 3, 2, node1804, node1804Labels⟩, ⟨6, 3, 2, node1805, node1805Labels⟩, ⟨6, 3, 2, node1806, node1806Labels⟩, ⟨5, 3, 2, node1807, node1807Labels⟩, ⟨5, 3, 2, node1808, node1808Labels⟩, ⟨5, 3, 2, node1809, node1809Labels⟩, ⟨5, 3, 2, node1810, node1810Labels⟩, ⟨6, 3, 2, node1811, node1811Labels⟩, ⟨5, 3, 2, node1812, node1812Labels⟩, ⟨5, 3, 2, node1813, node1813Labels⟩, ⟨5, 3, 2, node1814, node1814Labels⟩, ⟨5, 3, 2, node1815, node1815Labels⟩, ⟨5, 3, 2, node1816, node1816Labels⟩, ⟨4, 3, 2, node1817, node1817Labels⟩, ⟨4, 3, 2, node1818, node1818Labels⟩, ⟨4, 3, 2, node1819, node1819Labels⟩, ⟨4, 3, 2, node1820, node1820Labels⟩, ⟨6, 3, 2, node1821, node1821Labels⟩, ⟨6, 3, 2, node1822, node1822Labels⟩, ⟨5, 3, 2, node1823, node1823Labels⟩, ⟨6, 3, 2, node1824, node1824Labels⟩, ⟨5, 3, 2, node1825, node1825Labels⟩, ⟨5, 3, 2, node1826, node1826Labels⟩, ⟨5, 3, 2, node1827, node1827Labels⟩, ⟨5, 3, 2, node1828, node1828Labels⟩, ⟨5, 3, 2, node1829, node1829Labels⟩, ⟨4, 3, 2, node1830, node1830Labels⟩, ⟨4, 3, 2, node1831, node1831Labels⟩, ⟨4, 3, 2, node1832, node1832Labels⟩, ⟨6, 3, 2, node1833, node1833Labels⟩, ⟨6, 3, 2, node1834, node1834Labels⟩, ⟨6, 3, 2, node1835, node1835Labels⟩, ⟨6, 3, 2, node1836, node1836Labels⟩, ⟨6, 3, 2, node1837, node1837Labels⟩, ⟨6, 3, 2, node1838, node1838Labels⟩, ⟨5, 3, 2, node1839, node1839Labels⟩, ⟨5, 3, 2, node1840, node1840Labels⟩, ⟨5, 3, 2, node1841, node1841Labels⟩, ⟨6, 3, 2, node1842, node1842Labels⟩, ⟨5, 3, 2, node1843, node1843Labels⟩, ⟨6, 3, 2, node1844, node1844Labels⟩, ⟨5, 3, 2, node1845, node1845Labels⟩, ⟨5, 3, 2, node1846, node1846Labels⟩, ⟨6, 3, 2, node1847, node1847Labels⟩, ⟨6, 3, 2, node1848, node1848Labels⟩, ⟨5, 3, 2, node1849, node1849Labels⟩, ⟨5, 3, 2, node1850, node1850Labels⟩, ⟨5, 3, 2, node1851, node1851Labels⟩, ⟨5, 3, 2, node1852, node1852Labels⟩, ⟨5, 3, 2, node1853, node1853Labels⟩, ⟨5, 3, 2, node1854, node1854Labels⟩, ⟨5, 3, 2, node1855, node1855Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1856 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![3, 0, -3]]
def node1856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1857 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def node1857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1858 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def node1858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1859 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, 0, -2], ![2, 1, -3]]
def node1859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node1860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node1861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def node1862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node1863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node1864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node1865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node1866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node1867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node1868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node1869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node1870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node1871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1872 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def node1872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def node1873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def node1880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def node1881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def node1882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def node1883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def node1884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def node1885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def node1886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def node1887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def node1888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def node1889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def node1891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def node1892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def node1893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def node1894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node1896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node1897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node1898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node1899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node1900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node1901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node1902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node1903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node1904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node1905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node1906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node1907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node1908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node1909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node1910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node1912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node1913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1914 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1915 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1916 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def node1916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1917 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node1919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk29 : Array Code := #[⟨4, 3, 2, node1856, node1856Labels⟩, ⟨4, 3, 2, node1857, node1857Labels⟩, ⟨4, 3, 2, node1858, node1858Labels⟩, ⟨4, 3, 2, node1859, node1859Labels⟩, ⟨6, 3, 2, node1860, node1860Labels⟩, ⟨6, 3, 2, node1861, node1861Labels⟩, ⟨6, 3, 2, node1862, node1862Labels⟩, ⟨6, 3, 2, node1863, node1863Labels⟩, ⟨6, 3, 2, node1864, node1864Labels⟩, ⟨6, 3, 2, node1865, node1865Labels⟩, ⟨6, 3, 2, node1866, node1866Labels⟩, ⟨6, 3, 2, node1867, node1867Labels⟩, ⟨6, 3, 2, node1868, node1868Labels⟩, ⟨6, 3, 2, node1869, node1869Labels⟩, ⟨6, 3, 2, node1870, node1870Labels⟩, ⟨6, 3, 2, node1871, node1871Labels⟩, ⟨5, 3, 2, node1872, node1872Labels⟩, ⟨5, 3, 2, node1873, node1873Labels⟩, ⟨6, 3, 2, node1874, node1874Labels⟩, ⟨6, 3, 2, node1875, node1875Labels⟩, ⟨6, 3, 2, node1876, node1876Labels⟩, ⟨6, 3, 2, node1877, node1877Labels⟩, ⟨6, 3, 2, node1878, node1878Labels⟩, ⟨6, 3, 2, node1879, node1879Labels⟩, ⟨5, 3, 2, node1880, node1880Labels⟩, ⟨5, 3, 2, node1881, node1881Labels⟩, ⟨6, 3, 2, node1882, node1882Labels⟩, ⟨6, 3, 2, node1883, node1883Labels⟩, ⟨6, 3, 2, node1884, node1884Labels⟩, ⟨6, 3, 2, node1885, node1885Labels⟩, ⟨6, 3, 2, node1886, node1886Labels⟩, ⟨6, 3, 2, node1887, node1887Labels⟩, ⟨6, 3, 2, node1888, node1888Labels⟩, ⟨6, 3, 2, node1889, node1889Labels⟩, ⟨6, 3, 2, node1890, node1890Labels⟩, ⟨6, 3, 2, node1891, node1891Labels⟩, ⟨6, 3, 2, node1892, node1892Labels⟩, ⟨5, 3, 2, node1893, node1893Labels⟩, ⟨5, 3, 2, node1894, node1894Labels⟩, ⟨5, 3, 2, node1895, node1895Labels⟩, ⟨6, 3, 2, node1896, node1896Labels⟩, ⟨6, 3, 2, node1897, node1897Labels⟩, ⟨6, 3, 2, node1898, node1898Labels⟩, ⟨6, 3, 2, node1899, node1899Labels⟩, ⟨6, 3, 2, node1900, node1900Labels⟩, ⟨6, 3, 2, node1901, node1901Labels⟩, ⟨6, 3, 2, node1902, node1902Labels⟩, ⟨6, 3, 2, node1903, node1903Labels⟩, ⟨6, 3, 2, node1904, node1904Labels⟩, ⟨6, 3, 2, node1905, node1905Labels⟩, ⟨6, 3, 2, node1906, node1906Labels⟩, ⟨6, 3, 2, node1907, node1907Labels⟩, ⟨6, 3, 2, node1908, node1908Labels⟩, ⟨6, 3, 2, node1909, node1909Labels⟩, ⟨6, 3, 2, node1910, node1910Labels⟩, ⟨5, 3, 2, node1911, node1911Labels⟩, ⟨6, 3, 2, node1912, node1912Labels⟩, ⟨6, 3, 2, node1913, node1913Labels⟩, ⟨5, 3, 2, node1914, node1914Labels⟩, ⟨5, 3, 2, node1915, node1915Labels⟩, ⟨5, 3, 2, node1916, node1916Labels⟩, ⟨5, 3, 2, node1917, node1917Labels⟩, ⟨5, 3, 2, node1918, node1918Labels⟩, ⟨6, 3, 2, node1919, node1919Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node192 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node192Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node193Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node194 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node194Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node195 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node195Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node196 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def node196Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node197 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def node197Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node198Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node199Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node200Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node201 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node201Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node202Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node203Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node204 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node204Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node205Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node206Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node207Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node208Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node209Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node210Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node211 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node211Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node212Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node213Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node214 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node214Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node215Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node216Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node217Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node218Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node219Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node220Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node221Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node222 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node222Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node223Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node224Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node225Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node226Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node227Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node228Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node229 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node229Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node230 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node230Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node231 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node231Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node232Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node233 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node233Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node234 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node234Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node235Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def node236Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node237 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def node237Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node238Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node239Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node240Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def node241Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node242Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node243Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node244 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node244Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node245 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node245Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node246 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node246Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def node247Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node248 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node248Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node249 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def node249Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node250 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def node250Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node251 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node251Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node252 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node252Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node253Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node254Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def node255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def node255Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def codeChunk3 : Array Code := #[⟨5, 3, 1, node192, node192Labels⟩, ⟨5, 3, 1, node193, node193Labels⟩, ⟨5, 3, 1, node194, node194Labels⟩, ⟨5, 3, 1, node195, node195Labels⟩, ⟨4, 3, 1, node196, node196Labels⟩, ⟨4, 3, 1, node197, node197Labels⟩, ⟨6, 3, 1, node198, node198Labels⟩, ⟨6, 3, 1, node199, node199Labels⟩, ⟨6, 3, 1, node200, node200Labels⟩, ⟨5, 3, 1, node201, node201Labels⟩, ⟨5, 3, 1, node202, node202Labels⟩, ⟨5, 3, 1, node203, node203Labels⟩, ⟨5, 3, 1, node204, node204Labels⟩, ⟨6, 3, 1, node205, node205Labels⟩, ⟨6, 3, 1, node206, node206Labels⟩, ⟨6, 3, 1, node207, node207Labels⟩, ⟨6, 3, 1, node208, node208Labels⟩, ⟨6, 3, 1, node209, node209Labels⟩, ⟨6, 3, 1, node210, node210Labels⟩, ⟨5, 3, 1, node211, node211Labels⟩, ⟨6, 3, 1, node212, node212Labels⟩, ⟨6, 3, 1, node213, node213Labels⟩, ⟨5, 3, 1, node214, node214Labels⟩, ⟨6, 3, 1, node215, node215Labels⟩, ⟨6, 3, 1, node216, node216Labels⟩, ⟨6, 3, 1, node217, node217Labels⟩, ⟨6, 3, 1, node218, node218Labels⟩, ⟨5, 3, 1, node219, node219Labels⟩, ⟨6, 3, 1, node220, node220Labels⟩, ⟨6, 3, 1, node221, node221Labels⟩, ⟨5, 3, 1, node222, node222Labels⟩, ⟨6, 3, 1, node223, node223Labels⟩, ⟨5, 3, 1, node224, node224Labels⟩, ⟨5, 3, 1, node225, node225Labels⟩, ⟨5, 3, 1, node226, node226Labels⟩, ⟨5, 3, 1, node227, node227Labels⟩, ⟨5, 3, 1, node228, node228Labels⟩, ⟨5, 3, 1, node229, node229Labels⟩, ⟨5, 3, 1, node230, node230Labels⟩, ⟨5, 3, 1, node231, node231Labels⟩, ⟨6, 3, 1, node232, node232Labels⟩, ⟨5, 3, 1, node233, node233Labels⟩, ⟨5, 3, 1, node234, node234Labels⟩, ⟨5, 3, 1, node235, node235Labels⟩, ⟨4, 3, 1, node236, node236Labels⟩, ⟨4, 3, 1, node237, node237Labels⟩, ⟨6, 3, 1, node238, node238Labels⟩, ⟨5, 3, 1, node239, node239Labels⟩, ⟨5, 3, 1, node240, node240Labels⟩, ⟨4, 3, 1, node241, node241Labels⟩, ⟨6, 3, 1, node242, node242Labels⟩, ⟨6, 3, 1, node243, node243Labels⟩, ⟨5, 3, 1, node244, node244Labels⟩, ⟨5, 3, 1, node245, node245Labels⟩, ⟨5, 3, 1, node246, node246Labels⟩, ⟨4, 3, 1, node247, node247Labels⟩, ⟨5, 3, 1, node248, node248Labels⟩, ⟨4, 3, 1, node249, node249Labels⟩, ⟨4, 3, 1, node250, node250Labels⟩, ⟨4, 3, 1, node251, node251Labels⟩, ⟨4, 3, 1, node252, node252Labels⟩, ⟨6, 3, 1, node253, node253Labels⟩, ⟨5, 3, 1, node254, node254Labels⟩, ⟨4, 3, 1, node255, node255Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def node1920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node1921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node1922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node1923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node1925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def node1927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1928 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1929 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node1930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node1931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1932 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def node1932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def node1933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def node1934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node1935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node1936Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def node1937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def node1938Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def node1939Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node1940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node1941Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1942Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node1943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1944Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1945 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1945Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1947 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node1947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1948 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node1948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1949 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node1949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def node1950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1951 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def node1951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1952 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def node1952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1953 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def node1953Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def node1954Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node1955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node1956Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node1957Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node1958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def node1959Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node1960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node1961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node1962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node1963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node1964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node1965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node1966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node1967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node1968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def node1969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node1970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node1971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node1972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node1973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node1974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node1975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node1976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node1977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1978 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def node1978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node1979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node1980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node1981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node1982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node1983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk30 : Array Code := #[⟨5, 3, 2, node1920, node1920Labels⟩, ⟨6, 3, 2, node1921, node1921Labels⟩, ⟨6, 3, 2, node1922, node1922Labels⟩, ⟨6, 3, 2, node1923, node1923Labels⟩, ⟨5, 3, 2, node1924, node1924Labels⟩, ⟨6, 3, 2, node1925, node1925Labels⟩, ⟨5, 3, 2, node1926, node1926Labels⟩, ⟨5, 3, 2, node1927, node1927Labels⟩, ⟨5, 3, 2, node1928, node1928Labels⟩, ⟨5, 3, 2, node1929, node1929Labels⟩, ⟨6, 3, 2, node1930, node1930Labels⟩, ⟨6, 3, 2, node1931, node1931Labels⟩, ⟨5, 3, 2, node1932, node1932Labels⟩, ⟨5, 3, 2, node1933, node1933Labels⟩, ⟨5, 3, 2, node1934, node1934Labels⟩, ⟨6, 3, 2, node1935, node1935Labels⟩, ⟨6, 3, 2, node1936, node1936Labels⟩, ⟨5, 3, 2, node1937, node1937Labels⟩, ⟨5, 3, 2, node1938, node1938Labels⟩, ⟨5, 3, 2, node1939, node1939Labels⟩, ⟨6, 3, 2, node1940, node1940Labels⟩, ⟨6, 3, 2, node1941, node1941Labels⟩, ⟨5, 3, 2, node1942, node1942Labels⟩, ⟨6, 3, 2, node1943, node1943Labels⟩, ⟨5, 3, 2, node1944, node1944Labels⟩, ⟨5, 3, 2, node1945, node1945Labels⟩, ⟨5, 3, 2, node1946, node1946Labels⟩, ⟨5, 3, 2, node1947, node1947Labels⟩, ⟨5, 3, 2, node1948, node1948Labels⟩, ⟨5, 3, 2, node1949, node1949Labels⟩, ⟨4, 3, 2, node1950, node1950Labels⟩, ⟨4, 3, 2, node1951, node1951Labels⟩, ⟨4, 3, 2, node1952, node1952Labels⟩, ⟨4, 3, 2, node1953, node1953Labels⟩, ⟨6, 3, 2, node1954, node1954Labels⟩, ⟨6, 3, 2, node1955, node1955Labels⟩, ⟨6, 3, 2, node1956, node1956Labels⟩, ⟨6, 3, 2, node1957, node1957Labels⟩, ⟨6, 3, 2, node1958, node1958Labels⟩, ⟨6, 3, 2, node1959, node1959Labels⟩, ⟨6, 3, 2, node1960, node1960Labels⟩, ⟨6, 3, 2, node1961, node1961Labels⟩, ⟨6, 3, 2, node1962, node1962Labels⟩, ⟨6, 3, 2, node1963, node1963Labels⟩, ⟨6, 3, 2, node1964, node1964Labels⟩, ⟨6, 3, 2, node1965, node1965Labels⟩, ⟨6, 3, 2, node1966, node1966Labels⟩, ⟨6, 3, 2, node1967, node1967Labels⟩, ⟨6, 3, 2, node1968, node1968Labels⟩, ⟨5, 3, 2, node1969, node1969Labels⟩, ⟨5, 3, 2, node1970, node1970Labels⟩, ⟨5, 3, 2, node1971, node1971Labels⟩, ⟨6, 3, 2, node1972, node1972Labels⟩, ⟨6, 3, 2, node1973, node1973Labels⟩, ⟨6, 3, 2, node1974, node1974Labels⟩, ⟨6, 3, 2, node1975, node1975Labels⟩, ⟨6, 3, 2, node1976, node1976Labels⟩, ⟨6, 3, 2, node1977, node1977Labels⟩, ⟨5, 3, 2, node1978, node1978Labels⟩, ⟨5, 3, 2, node1979, node1979Labels⟩, ⟨5, 3, 2, node1980, node1980Labels⟩, ⟨6, 3, 2, node1981, node1981Labels⟩, ⟨6, 3, 2, node1982, node1982Labels⟩, ⟨6, 3, 2, node1983, node1983Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node1984 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node1984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node1985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def node1986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node1987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node1988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node1989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node1990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node1991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node1992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node1993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node1994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node1995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node1996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node1997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node1998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node1999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node1999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def node2003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2004 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node2004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2005 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node2005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2007 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2018 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def node2018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2022 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2025 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2026 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2027 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node2027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2028 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2029 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node2032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2037 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node2038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2039 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2041 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![1, -1, 0], ![3, -3, 0]]
def node2041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 3, -3], ![2, -2, 0], ![2, -2, 0]]
def node2042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2045 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node2045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2047 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk31 : Array Code := #[⟨5, 3, 2, node1984, node1984Labels⟩, ⟨6, 3, 2, node1985, node1985Labels⟩, ⟨6, 3, 2, node1986, node1986Labels⟩, ⟨6, 3, 2, node1987, node1987Labels⟩, ⟨6, 3, 2, node1988, node1988Labels⟩, ⟨6, 3, 2, node1989, node1989Labels⟩, ⟨6, 3, 2, node1990, node1990Labels⟩, ⟨6, 3, 2, node1991, node1991Labels⟩, ⟨6, 3, 2, node1992, node1992Labels⟩, ⟨6, 3, 2, node1993, node1993Labels⟩, ⟨6, 3, 2, node1994, node1994Labels⟩, ⟨6, 3, 2, node1995, node1995Labels⟩, ⟨6, 3, 2, node1996, node1996Labels⟩, ⟨6, 3, 2, node1997, node1997Labels⟩, ⟨6, 3, 2, node1998, node1998Labels⟩, ⟨6, 3, 2, node1999, node1999Labels⟩, ⟨6, 3, 2, node2000, node2000Labels⟩, ⟨6, 3, 2, node2001, node2001Labels⟩, ⟨6, 3, 2, node2002, node2002Labels⟩, ⟨5, 3, 2, node2003, node2003Labels⟩, ⟨5, 3, 2, node2004, node2004Labels⟩, ⟨5, 3, 2, node2005, node2005Labels⟩, ⟨5, 3, 2, node2006, node2006Labels⟩, ⟨5, 3, 2, node2007, node2007Labels⟩, ⟨6, 3, 2, node2008, node2008Labels⟩, ⟨6, 3, 2, node2009, node2009Labels⟩, ⟨6, 3, 2, node2010, node2010Labels⟩, ⟨6, 3, 2, node2011, node2011Labels⟩, ⟨6, 3, 2, node2012, node2012Labels⟩, ⟨6, 3, 2, node2013, node2013Labels⟩, ⟨6, 3, 2, node2014, node2014Labels⟩, ⟨6, 3, 2, node2015, node2015Labels⟩, ⟨6, 3, 2, node2016, node2016Labels⟩, ⟨6, 3, 2, node2017, node2017Labels⟩, ⟨5, 3, 2, node2018, node2018Labels⟩, ⟨6, 3, 2, node2019, node2019Labels⟩, ⟨6, 3, 2, node2020, node2020Labels⟩, ⟨6, 3, 2, node2021, node2021Labels⟩, ⟨5, 3, 2, node2022, node2022Labels⟩, ⟨6, 3, 2, node2023, node2023Labels⟩, ⟨6, 3, 2, node2024, node2024Labels⟩, ⟨5, 3, 2, node2025, node2025Labels⟩, ⟨5, 3, 2, node2026, node2026Labels⟩, ⟨5, 3, 2, node2027, node2027Labels⟩, ⟨5, 3, 2, node2028, node2028Labels⟩, ⟨5, 3, 2, node2029, node2029Labels⟩, ⟨6, 3, 2, node2030, node2030Labels⟩, ⟨6, 3, 2, node2031, node2031Labels⟩, ⟨5, 3, 2, node2032, node2032Labels⟩, ⟨6, 3, 2, node2033, node2033Labels⟩, ⟨6, 3, 2, node2034, node2034Labels⟩, ⟨5, 3, 2, node2035, node2035Labels⟩, ⟨6, 3, 2, node2036, node2036Labels⟩, ⟨5, 3, 2, node2037, node2037Labels⟩, ⟨5, 3, 2, node2038, node2038Labels⟩, ⟨5, 3, 2, node2039, node2039Labels⟩, ⟨6, 3, 2, node2040, node2040Labels⟩, ⟨5, 3, 2, node2041, node2041Labels⟩, ⟨5, 3, 2, node2042, node2042Labels⟩, ⟨6, 3, 2, node2043, node2043Labels⟩, ⟨6, 3, 2, node2044, node2044Labels⟩, ⟨5, 3, 2, node2045, node2045Labels⟩, ⟨6, 3, 2, node2046, node2046Labels⟩, ⟨5, 3, 2, node2047, node2047Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2048 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node2049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2053 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2056 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def node2056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node2059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2060 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node2061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def node2063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2064 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def node2064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2065 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2066 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2068 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node2068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2079 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def node2079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2080 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def node2080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2081 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def node2081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2082 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def node2082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node2084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2087 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2090 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2092 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2094 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2096 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2099 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2101 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2102 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2103 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def node2103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2107 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2109 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def node2109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk32 : Array Code := #[⟨5, 3, 2, node2048, node2048Labels⟩, ⟨5, 3, 2, node2049, node2049Labels⟩, ⟨6, 3, 2, node2050, node2050Labels⟩, ⟨6, 3, 2, node2051, node2051Labels⟩, ⟨5, 3, 2, node2052, node2052Labels⟩, ⟨5, 3, 2, node2053, node2053Labels⟩, ⟨5, 3, 2, node2054, node2054Labels⟩, ⟨5, 3, 2, node2055, node2055Labels⟩, ⟨4, 3, 2, node2056, node2056Labels⟩, ⟨5, 3, 2, node2057, node2057Labels⟩, ⟨5, 3, 2, node2058, node2058Labels⟩, ⟨5, 3, 2, node2059, node2059Labels⟩, ⟨4, 3, 2, node2060, node2060Labels⟩, ⟨5, 3, 2, node2061, node2061Labels⟩, ⟨4, 3, 2, node2062, node2062Labels⟩, ⟨4, 3, 2, node2063, node2063Labels⟩, ⟨4, 3, 2, node2064, node2064Labels⟩, ⟨4, 3, 2, node2065, node2065Labels⟩, ⟨4, 3, 2, node2066, node2066Labels⟩, ⟨6, 3, 2, node2067, node2067Labels⟩, ⟨5, 3, 2, node2068, node2068Labels⟩, ⟨6, 3, 2, node2069, node2069Labels⟩, ⟨6, 3, 2, node2070, node2070Labels⟩, ⟨6, 3, 2, node2071, node2071Labels⟩, ⟨6, 3, 2, node2072, node2072Labels⟩, ⟨6, 3, 2, node2073, node2073Labels⟩, ⟨6, 3, 2, node2074, node2074Labels⟩, ⟨6, 3, 2, node2075, node2075Labels⟩, ⟨6, 3, 2, node2076, node2076Labels⟩, ⟨6, 3, 2, node2077, node2077Labels⟩, ⟨6, 3, 2, node2078, node2078Labels⟩, ⟨5, 3, 2, node2079, node2079Labels⟩, ⟨5, 3, 2, node2080, node2080Labels⟩, ⟨5, 3, 2, node2081, node2081Labels⟩, ⟨5, 3, 2, node2082, node2082Labels⟩, ⟨6, 3, 2, node2083, node2083Labels⟩, ⟨6, 3, 2, node2084, node2084Labels⟩, ⟨6, 3, 2, node2085, node2085Labels⟩, ⟨6, 3, 2, node2086, node2086Labels⟩, ⟨5, 3, 2, node2087, node2087Labels⟩, ⟨6, 3, 2, node2088, node2088Labels⟩, ⟨6, 3, 2, node2089, node2089Labels⟩, ⟨5, 3, 2, node2090, node2090Labels⟩, ⟨6, 3, 2, node2091, node2091Labels⟩, ⟨5, 3, 2, node2092, node2092Labels⟩, ⟨5, 3, 2, node2093, node2093Labels⟩, ⟨5, 3, 2, node2094, node2094Labels⟩, ⟨6, 3, 2, node2095, node2095Labels⟩, ⟨5, 3, 2, node2096, node2096Labels⟩, ⟨5, 3, 2, node2097, node2097Labels⟩, ⟨6, 3, 2, node2098, node2098Labels⟩, ⟨5, 3, 2, node2099, node2099Labels⟩, ⟨6, 3, 2, node2100, node2100Labels⟩, ⟨5, 3, 2, node2101, node2101Labels⟩, ⟨5, 3, 2, node2102, node2102Labels⟩, ⟨4, 3, 2, node2103, node2103Labels⟩, ⟨6, 3, 2, node2104, node2104Labels⟩, ⟨6, 3, 2, node2105, node2105Labels⟩, ⟨5, 3, 2, node2106, node2106Labels⟩, ⟨5, 3, 2, node2107, node2107Labels⟩, ⟨5, 3, 2, node2108, node2108Labels⟩, ⟨4, 3, 2, node2109, node2109Labels⟩, ⟨5, 3, 2, node2110, node2110Labels⟩, ⟨5, 3, 2, node2111, node2111Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2112 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def node2112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2113 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def node2113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2114 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def node2114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2115 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def node2115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2116 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def node2116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def node2119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2121 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def node2121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2122 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def node2122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def node2123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def node2124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def node2125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def node2126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def node2130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2134 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def node2134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def node2136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2137 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def node2137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2138 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def node2138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2143 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node2143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2146 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node2146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2149 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node2149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node2151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2152 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node2152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2153 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node2153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node2155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node2157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node2158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2159 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def node2159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2161 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def node2161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node2162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2163 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def node2163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2164 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node2164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node2165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node2166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2167 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def node2167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2168 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def node2168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2169 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def node2169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def node2170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def node2171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def node2172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def node2173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def node2174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def node2175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk33 : Array Code := #[⟨4, 3, 2, node2112, node2112Labels⟩, ⟨4, 3, 2, node2113, node2113Labels⟩, ⟨4, 3, 2, node2114, node2114Labels⟩, ⟨4, 3, 2, node2115, node2115Labels⟩, ⟨4, 3, 2, node2116, node2116Labels⟩, ⟨6, 3, 2, node2117, node2117Labels⟩, ⟨6, 3, 2, node2118, node2118Labels⟩, ⟨5, 3, 2, node2119, node2119Labels⟩, ⟨6, 3, 2, node2120, node2120Labels⟩, ⟨5, 3, 2, node2121, node2121Labels⟩, ⟨5, 3, 2, node2122, node2122Labels⟩, ⟨5, 3, 2, node2123, node2123Labels⟩, ⟨6, 3, 2, node2124, node2124Labels⟩, ⟨5, 3, 2, node2125, node2125Labels⟩, ⟨5, 3, 2, node2126, node2126Labels⟩, ⟨6, 3, 2, node2127, node2127Labels⟩, ⟨5, 3, 2, node2128, node2128Labels⟩, ⟨5, 3, 2, node2129, node2129Labels⟩, ⟨4, 3, 2, node2130, node2130Labels⟩, ⟨6, 3, 2, node2131, node2131Labels⟩, ⟨5, 3, 2, node2132, node2132Labels⟩, ⟨5, 3, 2, node2133, node2133Labels⟩, ⟨4, 3, 2, node2134, node2134Labels⟩, ⟨5, 3, 2, node2135, node2135Labels⟩, ⟨4, 3, 2, node2136, node2136Labels⟩, ⟨4, 3, 2, node2137, node2137Labels⟩, ⟨4, 3, 2, node2138, node2138Labels⟩, ⟨6, 3, 2, node2139, node2139Labels⟩, ⟨6, 3, 2, node2140, node2140Labels⟩, ⟨6, 3, 2, node2141, node2141Labels⟩, ⟨6, 3, 2, node2142, node2142Labels⟩, ⟨5, 3, 2, node2143, node2143Labels⟩, ⟨6, 3, 2, node2144, node2144Labels⟩, ⟨6, 3, 2, node2145, node2145Labels⟩, ⟨5, 3, 2, node2146, node2146Labels⟩, ⟨6, 3, 2, node2147, node2147Labels⟩, ⟨6, 3, 2, node2148, node2148Labels⟩, ⟨5, 3, 2, node2149, node2149Labels⟩, ⟨6, 3, 2, node2150, node2150Labels⟩, ⟨5, 3, 2, node2151, node2151Labels⟩, ⟨5, 3, 2, node2152, node2152Labels⟩, ⟨5, 3, 2, node2153, node2153Labels⟩, ⟨6, 3, 2, node2154, node2154Labels⟩, ⟨5, 3, 2, node2155, node2155Labels⟩, ⟨6, 3, 2, node2156, node2156Labels⟩, ⟨5, 3, 2, node2157, node2157Labels⟩, ⟨5, 3, 2, node2158, node2158Labels⟩, ⟨4, 3, 2, node2159, node2159Labels⟩, ⟨6, 3, 2, node2160, node2160Labels⟩, ⟨5, 3, 2, node2161, node2161Labels⟩, ⟨5, 3, 2, node2162, node2162Labels⟩, ⟨4, 3, 2, node2163, node2163Labels⟩, ⟨5, 3, 2, node2164, node2164Labels⟩, ⟨5, 3, 2, node2165, node2165Labels⟩, ⟨5, 3, 2, node2166, node2166Labels⟩, ⟨4, 3, 2, node2167, node2167Labels⟩, ⟨4, 3, 2, node2168, node2168Labels⟩, ⟨4, 3, 2, node2169, node2169Labels⟩, ⟨6, 3, 2, node2170, node2170Labels⟩, ⟨6, 3, 2, node2171, node2171Labels⟩, ⟨6, 3, 2, node2172, node2172Labels⟩, ⟨6, 3, 2, node2173, node2173Labels⟩, ⟨6, 3, 2, node2174, node2174Labels⟩, ⟨6, 3, 2, node2175, node2175Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def node2176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def node2177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def node2178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def node2179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2180 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def node2180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def node2181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def node2182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def node2183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2184 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def node2184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def node2185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2186 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def node2186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node2188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node2189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def node2193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node2194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2197 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def node2197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node2198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node2199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2200 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def node2200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2203 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def node2203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2205 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def node2205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2206 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def node2206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2207 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def node2207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2208 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def node2208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2210 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def node2210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2212 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def node2212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2215 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def node2215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2216 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def node2216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2217 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def node2217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2218 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def node2218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def node2220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2221 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def node2221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2222 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def node2222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2223 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def node2223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2224 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2226 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def node2226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2228 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def node2228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def node2229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def node2230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def node2231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def node2232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def node2233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def node2234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2235 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def node2235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node2236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def node2237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node2238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def node2239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk34 : Array Code := #[⟨6, 3, 2, node2176, node2176Labels⟩, ⟨6, 3, 2, node2177, node2177Labels⟩, ⟨6, 3, 2, node2178, node2178Labels⟩, ⟨6, 3, 2, node2179, node2179Labels⟩, ⟨5, 3, 2, node2180, node2180Labels⟩, ⟨6, 3, 2, node2181, node2181Labels⟩, ⟨6, 3, 2, node2182, node2182Labels⟩, ⟨6, 3, 2, node2183, node2183Labels⟩, ⟨5, 3, 2, node2184, node2184Labels⟩, ⟨5, 3, 2, node2185, node2185Labels⟩, ⟨5, 3, 2, node2186, node2186Labels⟩, ⟨6, 3, 2, node2187, node2187Labels⟩, ⟨6, 3, 2, node2188, node2188Labels⟩, ⟨6, 3, 2, node2189, node2189Labels⟩, ⟨6, 3, 2, node2190, node2190Labels⟩, ⟨6, 3, 2, node2191, node2191Labels⟩, ⟨6, 3, 2, node2192, node2192Labels⟩, ⟨5, 3, 2, node2193, node2193Labels⟩, ⟨6, 3, 2, node2194, node2194Labels⟩, ⟨6, 3, 2, node2195, node2195Labels⟩, ⟨6, 3, 2, node2196, node2196Labels⟩, ⟨5, 3, 2, node2197, node2197Labels⟩, ⟨6, 3, 2, node2198, node2198Labels⟩, ⟨6, 3, 2, node2199, node2199Labels⟩, ⟨5, 3, 2, node2200, node2200Labels⟩, ⟨6, 3, 2, node2201, node2201Labels⟩, ⟨6, 3, 2, node2202, node2202Labels⟩, ⟨5, 3, 2, node2203, node2203Labels⟩, ⟨6, 3, 2, node2204, node2204Labels⟩, ⟨5, 3, 2, node2205, node2205Labels⟩, ⟨5, 3, 2, node2206, node2206Labels⟩, ⟨5, 3, 2, node2207, node2207Labels⟩, ⟨4, 3, 2, node2208, node2208Labels⟩, ⟨6, 3, 2, node2209, node2209Labels⟩, ⟨5, 3, 2, node2210, node2210Labels⟩, ⟨6, 3, 2, node2211, node2211Labels⟩, ⟨5, 3, 2, node2212, node2212Labels⟩, ⟨6, 3, 2, node2213, node2213Labels⟩, ⟨6, 3, 2, node2214, node2214Labels⟩, ⟨5, 3, 2, node2215, node2215Labels⟩, ⟨5, 3, 2, node2216, node2216Labels⟩, ⟨5, 3, 2, node2217, node2217Labels⟩, ⟨4, 3, 2, node2218, node2218Labels⟩, ⟨6, 3, 2, node2219, node2219Labels⟩, ⟨5, 3, 2, node2220, node2220Labels⟩, ⟨5, 3, 2, node2221, node2221Labels⟩, ⟨4, 3, 2, node2222, node2222Labels⟩, ⟨5, 3, 2, node2223, node2223Labels⟩, ⟨5, 3, 2, node2224, node2224Labels⟩, ⟨5, 3, 2, node2225, node2225Labels⟩, ⟨4, 3, 2, node2226, node2226Labels⟩, ⟨5, 3, 2, node2227, node2227Labels⟩, ⟨4, 3, 2, node2228, node2228Labels⟩, ⟨4, 3, 2, node2229, node2229Labels⟩, ⟨4, 3, 2, node2230, node2230Labels⟩, ⟨6, 3, 2, node2231, node2231Labels⟩, ⟨6, 3, 2, node2232, node2232Labels⟩, ⟨6, 3, 2, node2233, node2233Labels⟩, ⟨6, 3, 2, node2234, node2234Labels⟩, ⟨5, 3, 2, node2235, node2235Labels⟩, ⟨6, 3, 2, node2236, node2236Labels⟩, ⟨6, 3, 2, node2237, node2237Labels⟩, ⟨6, 3, 2, node2238, node2238Labels⟩, ⟨5, 3, 2, node2239, node2239Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2242 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def node2242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2244 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def node2244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2245 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def node2245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2246 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def node2246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def node2247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def node2248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2249 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def node2249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def node2250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2251 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def node2251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2253 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def node2253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2254 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def node2254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2255 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def node2255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2256 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def node2256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2257 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def node2257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2258 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def node2258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2259 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def node2259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2260 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def node2260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2261 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def node2261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2262 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def node2262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2263 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def node2263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2264 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def node2264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2265 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def node2265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2266 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def node2266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2267 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def node2267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2268 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def node2268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def node2269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2270 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def node2270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def node2271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def node2272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2273 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def node2273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2274 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def node2274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2275 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def node2275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2276 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def node2276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2277 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def node2277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2278 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def node2278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2279 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def node2279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2280 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def node2280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2281 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def node2281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2282 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def node2282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2283 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def node2283Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2284 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def node2284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2285 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def node2285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2286 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def node2286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2287 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def node2287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2288 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def node2288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2289 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def node2289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2290 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2291 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2292 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def node2292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2293 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def node2293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2294 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def node2294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def node2300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node2301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk35 : Array Code := #[⟨6, 3, 2, node2240, node2240Labels⟩, ⟨6, 3, 2, node2241, node2241Labels⟩, ⟨5, 3, 2, node2242, node2242Labels⟩, ⟨6, 3, 2, node2243, node2243Labels⟩, ⟨5, 3, 2, node2244, node2244Labels⟩, ⟨5, 3, 2, node2245, node2245Labels⟩, ⟨5, 3, 2, node2246, node2246Labels⟩, ⟨4, 3, 2, node2247, node2247Labels⟩, ⟨6, 3, 2, node2248, node2248Labels⟩, ⟨5, 3, 2, node2249, node2249Labels⟩, ⟨6, 3, 2, node2250, node2250Labels⟩, ⟨5, 3, 2, node2251, node2251Labels⟩, ⟨6, 3, 2, node2252, node2252Labels⟩, ⟨5, 3, 2, node2253, node2253Labels⟩, ⟨5, 3, 2, node2254, node2254Labels⟩, ⟨4, 3, 2, node2255, node2255Labels⟩, ⟨5, 3, 2, node2256, node2256Labels⟩, ⟨5, 3, 2, node2257, node2257Labels⟩, ⟨4, 3, 2, node2258, node2258Labels⟩, ⟨5, 3, 2, node2259, node2259Labels⟩, ⟨5, 3, 2, node2260, node2260Labels⟩, ⟨4, 3, 2, node2261, node2261Labels⟩, ⟨5, 3, 2, node2262, node2262Labels⟩, ⟨5, 3, 2, node2263, node2263Labels⟩, ⟨4, 3, 2, node2264, node2264Labels⟩, ⟨4, 3, 2, node2265, node2265Labels⟩, ⟨4, 3, 2, node2266, node2266Labels⟩, ⟨4, 3, 2, node2267, node2267Labels⟩, ⟨3, 3, 2, node2268, node2268Labels⟩, ⟨6, 3, 2, node2269, node2269Labels⟩, ⟨5, 3, 2, node2270, node2270Labels⟩, ⟨5, 3, 2, node2271, node2271Labels⟩, ⟨5, 3, 2, node2272, node2272Labels⟩, ⟨4, 3, 2, node2273, node2273Labels⟩, ⟨5, 3, 2, node2274, node2274Labels⟩, ⟨5, 3, 2, node2275, node2275Labels⟩, ⟨4, 3, 2, node2276, node2276Labels⟩, ⟨5, 3, 2, node2277, node2277Labels⟩, ⟨4, 3, 2, node2278, node2278Labels⟩, ⟨4, 3, 2, node2279, node2279Labels⟩, ⟨4, 3, 2, node2280, node2280Labels⟩, ⟨3, 3, 2, node2281, node2281Labels⟩, ⟨4, 3, 2, node2282, node2282Labels⟩, ⟨5, 3, 2, node2283, node2283Labels⟩, ⟨4, 3, 2, node2284, node2284Labels⟩, ⟨3, 3, 2, node2285, node2285Labels⟩, ⟨4, 3, 2, node2286, node2286Labels⟩, ⟨4, 3, 2, node2287, node2287Labels⟩, ⟨4, 3, 2, node2288, node2288Labels⟩, ⟨3, 3, 2, node2289, node2289Labels⟩, ⟨4, 3, 2, node2290, node2290Labels⟩, ⟨4, 3, 2, node2291, node2291Labels⟩, ⟨3, 3, 2, node2292, node2292Labels⟩, ⟨3, 3, 2, node2293, node2293Labels⟩, ⟨3, 3, 2, node2294, node2294Labels⟩, ⟨6, 3, 2, node2295, node2295Labels⟩, ⟨6, 3, 2, node2296, node2296Labels⟩, ⟨6, 3, 2, node2297, node2297Labels⟩, ⟨6, 3, 2, node2298, node2298Labels⟩, ⟨6, 3, 2, node2299, node2299Labels⟩, ⟨5, 3, 2, node2300, node2300Labels⟩, ⟨5, 3, 2, node2301, node2301Labels⟩, ⟨6, 3, 2, node2302, node2302Labels⟩, ⟨6, 3, 2, node2303, node2303Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def node2306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node2307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2310 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node2310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node2311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node2313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node2314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2315 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def node2315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def node2325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2326 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node2326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2327 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2335 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2336 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2341 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2342 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2343 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2344 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def node2344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2345 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2346 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def node2346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2352 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2355 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def node2355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2356 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2357 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2358 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2363 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def node2363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2365 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk36 : Array Code := #[⟨6, 3, 2, node2304, node2304Labels⟩, ⟨6, 3, 2, node2305, node2305Labels⟩, ⟨5, 3, 2, node2306, node2306Labels⟩, ⟨5, 3, 2, node2307, node2307Labels⟩, ⟨6, 3, 2, node2308, node2308Labels⟩, ⟨5, 3, 2, node2309, node2309Labels⟩, ⟨5, 3, 2, node2310, node2310Labels⟩, ⟨5, 3, 2, node2311, node2311Labels⟩, ⟨5, 3, 2, node2312, node2312Labels⟩, ⟨5, 3, 2, node2313, node2313Labels⟩, ⟨5, 3, 2, node2314, node2314Labels⟩, ⟨4, 3, 2, node2315, node2315Labels⟩, ⟨6, 3, 2, node2316, node2316Labels⟩, ⟨6, 3, 2, node2317, node2317Labels⟩, ⟨6, 3, 2, node2318, node2318Labels⟩, ⟨6, 3, 2, node2319, node2319Labels⟩, ⟨6, 3, 2, node2320, node2320Labels⟩, ⟨6, 3, 2, node2321, node2321Labels⟩, ⟨6, 3, 2, node2322, node2322Labels⟩, ⟨6, 3, 2, node2323, node2323Labels⟩, ⟨6, 3, 2, node2324, node2324Labels⟩, ⟨5, 3, 2, node2325, node2325Labels⟩, ⟨5, 3, 2, node2326, node2326Labels⟩, ⟨5, 3, 2, node2327, node2327Labels⟩, ⟨6, 3, 2, node2328, node2328Labels⟩, ⟨5, 3, 2, node2329, node2329Labels⟩, ⟨6, 3, 2, node2330, node2330Labels⟩, ⟨6, 3, 2, node2331, node2331Labels⟩, ⟨6, 3, 2, node2332, node2332Labels⟩, ⟨6, 3, 2, node2333, node2333Labels⟩, ⟨5, 3, 2, node2334, node2334Labels⟩, ⟨5, 3, 2, node2335, node2335Labels⟩, ⟨5, 3, 2, node2336, node2336Labels⟩, ⟨5, 3, 2, node2337, node2337Labels⟩, ⟨6, 3, 2, node2338, node2338Labels⟩, ⟨5, 3, 2, node2339, node2339Labels⟩, ⟨5, 3, 2, node2340, node2340Labels⟩, ⟨5, 3, 2, node2341, node2341Labels⟩, ⟨5, 3, 2, node2342, node2342Labels⟩, ⟨5, 3, 2, node2343, node2343Labels⟩, ⟨4, 3, 2, node2344, node2344Labels⟩, ⟨4, 3, 2, node2345, node2345Labels⟩, ⟨4, 3, 2, node2346, node2346Labels⟩, ⟨6, 3, 2, node2347, node2347Labels⟩, ⟨6, 3, 2, node2348, node2348Labels⟩, ⟨6, 3, 2, node2349, node2349Labels⟩, ⟨6, 3, 2, node2350, node2350Labels⟩, ⟨6, 3, 2, node2351, node2351Labels⟩, ⟨5, 3, 2, node2352, node2352Labels⟩, ⟨6, 3, 2, node2353, node2353Labels⟩, ⟨6, 3, 2, node2354, node2354Labels⟩, ⟨5, 3, 2, node2355, node2355Labels⟩, ⟨5, 3, 2, node2356, node2356Labels⟩, ⟨5, 3, 2, node2357, node2357Labels⟩, ⟨5, 3, 2, node2358, node2358Labels⟩, ⟨5, 3, 2, node2359, node2359Labels⟩, ⟨5, 3, 2, node2360, node2360Labels⟩, ⟨6, 3, 2, node2361, node2361Labels⟩, ⟨5, 3, 2, node2362, node2362Labels⟩, ⟨4, 3, 2, node2363, node2363Labels⟩, ⟨6, 3, 2, node2364, node2364Labels⟩, ⟨5, 3, 2, node2365, node2365Labels⟩, ⟨6, 3, 2, node2366, node2366Labels⟩, ⟨5, 3, 2, node2367, node2367Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2369 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def node2369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2376 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node2376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node2385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node2386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node2387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2388 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node2391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2393 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node2393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2394 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node2394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2395 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node2395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node2397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2399 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node2401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2403 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2406 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2407 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def node2407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2408 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def node2408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2409 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def node2409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2410 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def node2410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2411 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def node2411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def node2412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def node2413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def node2414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def node2415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def node2416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def node2417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def node2418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def node2419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def node2420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def node2421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def node2422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def node2423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def node2424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def node2425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def node2426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def node2427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def node2428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def node2429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def node2430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def node2431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk37 : Array Code := #[⟨5, 3, 2, node2368, node2368Labels⟩, ⟨4, 3, 2, node2369, node2369Labels⟩, ⟨6, 3, 2, node2370, node2370Labels⟩, ⟨6, 3, 2, node2371, node2371Labels⟩, ⟨6, 3, 2, node2372, node2372Labels⟩, ⟨6, 3, 2, node2373, node2373Labels⟩, ⟨6, 3, 2, node2374, node2374Labels⟩, ⟨6, 3, 2, node2375, node2375Labels⟩, ⟨5, 3, 2, node2376, node2376Labels⟩, ⟨6, 3, 2, node2377, node2377Labels⟩, ⟨6, 3, 2, node2378, node2378Labels⟩, ⟨6, 3, 2, node2379, node2379Labels⟩, ⟨6, 3, 2, node2380, node2380Labels⟩, ⟨6, 3, 2, node2381, node2381Labels⟩, ⟨6, 3, 2, node2382, node2382Labels⟩, ⟨6, 3, 2, node2383, node2383Labels⟩, ⟨6, 3, 2, node2384, node2384Labels⟩, ⟨5, 3, 2, node2385, node2385Labels⟩, ⟨5, 3, 2, node2386, node2386Labels⟩, ⟨5, 3, 2, node2387, node2387Labels⟩, ⟨5, 3, 2, node2388, node2388Labels⟩, ⟨6, 3, 2, node2389, node2389Labels⟩, ⟨6, 3, 2, node2390, node2390Labels⟩, ⟨5, 3, 2, node2391, node2391Labels⟩, ⟨6, 3, 2, node2392, node2392Labels⟩, ⟨5, 3, 2, node2393, node2393Labels⟩, ⟨5, 3, 2, node2394, node2394Labels⟩, ⟨5, 3, 2, node2395, node2395Labels⟩, ⟨6, 3, 2, node2396, node2396Labels⟩, ⟨5, 3, 2, node2397, node2397Labels⟩, ⟨6, 3, 2, node2398, node2398Labels⟩, ⟨5, 3, 2, node2399, node2399Labels⟩, ⟨5, 3, 2, node2400, node2400Labels⟩, ⟨5, 3, 2, node2401, node2401Labels⟩, ⟨6, 3, 2, node2402, node2402Labels⟩, ⟨5, 3, 2, node2403, node2403Labels⟩, ⟨5, 3, 2, node2404, node2404Labels⟩, ⟨5, 3, 2, node2405, node2405Labels⟩, ⟨5, 3, 2, node2406, node2406Labels⟩, ⟨4, 3, 2, node2407, node2407Labels⟩, ⟨4, 3, 2, node2408, node2408Labels⟩, ⟨4, 3, 2, node2409, node2409Labels⟩, ⟨4, 3, 2, node2410, node2410Labels⟩, ⟨4, 3, 2, node2411, node2411Labels⟩, ⟨6, 3, 2, node2412, node2412Labels⟩, ⟨6, 3, 2, node2413, node2413Labels⟩, ⟨6, 3, 2, node2414, node2414Labels⟩, ⟨6, 3, 2, node2415, node2415Labels⟩, ⟨6, 3, 2, node2416, node2416Labels⟩, ⟨6, 3, 2, node2417, node2417Labels⟩, ⟨6, 3, 2, node2418, node2418Labels⟩, ⟨6, 3, 2, node2419, node2419Labels⟩, ⟨6, 3, 2, node2420, node2420Labels⟩, ⟨5, 3, 2, node2421, node2421Labels⟩, ⟨6, 3, 2, node2422, node2422Labels⟩, ⟨6, 3, 2, node2423, node2423Labels⟩, ⟨6, 3, 2, node2424, node2424Labels⟩, ⟨6, 3, 2, node2425, node2425Labels⟩, ⟨6, 3, 2, node2426, node2426Labels⟩, ⟨6, 3, 2, node2427, node2427Labels⟩, ⟨6, 3, 2, node2428, node2428Labels⟩, ⟨6, 3, 2, node2429, node2429Labels⟩, ⟨6, 3, 2, node2430, node2430Labels⟩, ⟨6, 3, 2, node2431, node2431Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def node2432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def node2433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def node2434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def node2435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def node2436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def node2439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2442 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def node2442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2443 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def node2443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def node2444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def node2445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def node2446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2447 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def node2447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def node2448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def node2449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def node2450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def node2451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def node2453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def node2454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def node2455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def node2456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def node2457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def node2460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def node2463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def node2464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def node2465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def node2466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2467 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2468 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def node2469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def node2470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def node2471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def node2472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def node2473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def node2474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def node2475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def node2476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def node2477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def node2478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def node2479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def node2480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def node2481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def node2483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def node2484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2485 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2486 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2487 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def node2487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2488 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2489 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def node2490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def node2491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2492 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def node2492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def node2493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def node2494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def codeChunk38 : Array Code := #[⟨6, 3, 2, node2432, node2432Labels⟩, ⟨6, 3, 2, node2433, node2433Labels⟩, ⟨5, 3, 2, node2434, node2434Labels⟩, ⟨5, 3, 2, node2435, node2435Labels⟩, ⟨6, 3, 2, node2436, node2436Labels⟩, ⟨6, 3, 2, node2437, node2437Labels⟩, ⟨6, 3, 2, node2438, node2438Labels⟩, ⟨6, 3, 2, node2439, node2439Labels⟩, ⟨6, 3, 2, node2440, node2440Labels⟩, ⟨6, 3, 2, node2441, node2441Labels⟩, ⟨5, 3, 2, node2442, node2442Labels⟩, ⟨5, 3, 2, node2443, node2443Labels⟩, ⟨6, 3, 2, node2444, node2444Labels⟩, ⟨6, 3, 2, node2445, node2445Labels⟩, ⟨6, 3, 2, node2446, node2446Labels⟩, ⟨5, 3, 2, node2447, node2447Labels⟩, ⟨6, 3, 2, node2448, node2448Labels⟩, ⟨6, 3, 2, node2449, node2449Labels⟩, ⟨6, 3, 2, node2450, node2450Labels⟩, ⟨6, 3, 2, node2451, node2451Labels⟩, ⟨6, 3, 2, node2452, node2452Labels⟩, ⟨6, 3, 2, node2453, node2453Labels⟩, ⟨6, 3, 2, node2454, node2454Labels⟩, ⟨6, 3, 2, node2455, node2455Labels⟩, ⟨6, 3, 2, node2456, node2456Labels⟩, ⟨6, 3, 2, node2457, node2457Labels⟩, ⟨6, 3, 2, node2458, node2458Labels⟩, ⟨6, 3, 2, node2459, node2459Labels⟩, ⟨6, 3, 2, node2460, node2460Labels⟩, ⟨6, 3, 2, node2461, node2461Labels⟩, ⟨6, 3, 2, node2462, node2462Labels⟩, ⟨6, 3, 2, node2463, node2463Labels⟩, ⟨6, 3, 2, node2464, node2464Labels⟩, ⟨5, 3, 2, node2465, node2465Labels⟩, ⟨5, 3, 2, node2466, node2466Labels⟩, ⟨5, 3, 2, node2467, node2467Labels⟩, ⟨5, 3, 2, node2468, node2468Labels⟩, ⟨6, 3, 2, node2469, node2469Labels⟩, ⟨6, 3, 2, node2470, node2470Labels⟩, ⟨6, 3, 2, node2471, node2471Labels⟩, ⟨6, 3, 2, node2472, node2472Labels⟩, ⟨6, 3, 2, node2473, node2473Labels⟩, ⟨6, 3, 2, node2474, node2474Labels⟩, ⟨6, 3, 2, node2475, node2475Labels⟩, ⟨6, 3, 2, node2476, node2476Labels⟩, ⟨6, 3, 2, node2477, node2477Labels⟩, ⟨6, 3, 2, node2478, node2478Labels⟩, ⟨6, 3, 2, node2479, node2479Labels⟩, ⟨6, 3, 2, node2480, node2480Labels⟩, ⟨6, 3, 2, node2481, node2481Labels⟩, ⟨5, 3, 2, node2482, node2482Labels⟩, ⟨6, 3, 2, node2483, node2483Labels⟩, ⟨6, 3, 2, node2484, node2484Labels⟩, ⟨5, 3, 2, node2485, node2485Labels⟩, ⟨5, 3, 2, node2486, node2486Labels⟩, ⟨5, 3, 2, node2487, node2487Labels⟩, ⟨5, 3, 2, node2488, node2488Labels⟩, ⟨5, 3, 2, node2489, node2489Labels⟩, ⟨6, 3, 2, node2490, node2490Labels⟩, ⟨6, 3, 2, node2491, node2491Labels⟩, ⟨5, 3, 2, node2492, node2492Labels⟩, ⟨6, 3, 2, node2493, node2493Labels⟩, ⟨6, 3, 2, node2494, node2494Labels⟩, ⟨5, 3, 2, node2495, node2495Labels⟩]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def node2496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2497 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2498 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def node2498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2499 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def node2500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def node2501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def node2502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def node2503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2504 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2505 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2506 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def node2506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def node2507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def node2508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2509 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def node2510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2511 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2512 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2513 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2514 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def node2514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def node2515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2516 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def node2516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2517 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def node2517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2518 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def node2518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2519 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def node2519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2520 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def node2520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2521 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def node2521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2522 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def node2522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2523 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def node2523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def node2524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def node2525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def node2526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def node2527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def node2528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def node2529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def node2530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2531 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def node2531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2532 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def node2532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def node2533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def node2534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def node2535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def node2536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def node2537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2538 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def node2538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def node2539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def node2540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def node2541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def node2542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def node2543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def node2544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def node2545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def node2546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def node2547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def node2548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def node2549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def node2550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def node2551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def node2552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def node2553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def node2554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def node2555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def node2556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Nodes40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def node2560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

end MUB6.Certificate.MixedSemantics

end OAI
end


