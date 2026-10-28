-- Prove2me | Definitions.Def_OAIQ084L015
-- name    : OAIQ084L015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:29:33.084448+00:00
-- url     : https://prove2.me/theorems/7f2ff565-d7fc-4c69-b567-47bd69312c46
-- title:
--   Definitions bundle OAIQ084L015 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 39 declarations of OpenAI's Lean: 39 definitions. The definitions and types are `OAI.LaughlinFock.fourHighestCache_20_4`, `OAI.LaughlinFock.fourHighestCache_20_5`, `OAI.LaughlinFock.fourHighestCache_20_6`, `OAI.LaughlinFock.fourHighestCache_20_7`, `OAI.LaughlinFock.fourHighestCache_20_8`, `OAI.LaughlinFock.fourHighestCache_20_9`, `OAI.LaughlinFock.fourHighestCache_21_0`, `OAI.LaughlinFock.fourHighestCache_21_1`, `OAI.LaughlinFock.fourHighestCache_21_10`, `OAI.LaughlinFock.fourHighestCache_21_11`, `OAI.LaughlinFock.fourHighestCache_21_12`, `OAI.LaughlinFock.rowEntryData_3`, `OAI.LaughlinFock.rowEntryData_4`, `OAI.LaughlinFock.rowEntryData_5`, `OAI.LaughlinFock.rowEntryData_6`, `OAI.LaughlinFock.rowEntryList_3`, `OAI.LaughlinFock.rowEntryList_4`, `OAI.LaughlinFock.rowEntryList_5`, `OAI.LaughlinFock.rowEntryList_6`, `OAI.LaughlinFock.rowThreeBody`, `OAI.LaughlinFock.rowThreeLevelTrace`, `OAI.LaughlinFock.rowThreePrewedge`, `OAI.LaughlinFock.rowThreeTrace`, `OAI.LaughlinFock.rowToNumeric`, `OAI.LaughlinFock.rowTwoBody`, `OAI.LaughlinFock.rowsEta`, `OAI.LaughlinFock.rowsThreeTrace`, `OAI.LaughlinFock.sectorAverage`, `OAI.LaughlinFock.sectorHamiltonian`, `OAI.LaughlinFock.shortNumericFourTrace`, `OAI.LaughlinFock.shortNumericRowTerm`, `OAI.LaughlinFock.shortNumericRowsFourTrace`, `OAI.LaughlinFock.singletonSectorEquiv`, `OAI.LaughlinFock.sourceRowFourP`, `OAI.LaughlinFock.sourceRowP`, `OAI.LaughlinFock.sourceRowT`, `OAI.LaughlinFock.sourceRowThreeKernel`, `OAI.LaughlinFock.sphericalRowAmplitude`, `OAI.LaughlinFock.sphericalThreeCoefficient`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_Certificate20`, `LaughlinFock_Certificate21`, `LaughlinFock_CreationRows`, `LaughlinFock_EntryEnumeration`, `LaughlinFock_FasterTrace`, `LaughlinFock_FiniteComparison`, `LaughlinFock_FockRotations`, `LaughlinFock_FourTraces`, `LaughlinFock_Model`, `LaughlinFock_NormalOrdering`, `LaughlinFock_NumericTrace`, `LaughlinFock_RowTraces`, `LaughlinFock_ThreeTraces`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L000` and `OAIQ084L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L022` and `OAIQ084L035`; the statements `OAI.LaughlinFock.fockInequality_eventual_of_certificates`, `OAI.LaughlinFock.fourYNumber_12_11_1`, `OAI.LaughlinFock.fourYNumber_12_11_11`, `OAI.LaughlinFock.fourYNumber_12_11_3`, `OAI.LaughlinFock.fourYNumber_12_11_5`, `OAI.LaughlinFock.fourYNumber_12_11_7`, `OAI.LaughlinFock.fourYNumber_12_11_9`, `OAI.LaughlinFock.fourYNumber_12_1_1`, `OAI.LaughlinFock.fourYNumber_12_3_3`, `OAI.LaughlinFock.fourYNumber_12_7_1`, `OAI.LaughlinFock.fourYNumber_12_7_7`, `OAI.LaughlinFock.fourYNumber_12_9_1`, `OAI.LaughlinFock.fourYNumber_12_9_3`, `OAI.LaughlinFock.fourYNumber_12_9_7`, `OAI.LaughlinFock.fourYNumber_12_9_9`, `OAI.LaughlinFock.fourYNumber_5_3_1`, `OAI.LaughlinFock.fourYNumber_5_3_3`, `OAI.LaughlinFock.fourYNumber_5_5_3`, `OAI.LaughlinFock.fourYNumber_7_1_1`, `OAI.LaughlinFock.fourYNumber_7_3_1`, `OAI.LaughlinFock.fourYNumber_7_3_3`, `OAI.LaughlinFock.fourYNumber_7_5_5`, `OAI.LaughlinFock.fourYNumber_7_7_1`, `OAI.LaughlinFock.fourYNumber_7_7_5` and `OAI.LaughlinFock.fourYNumber_7_7_7`; the proofs of `OAI.LaughlinFock.fourYNumber_12_11_1`, `OAI.LaughlinFock.fourYNumber_12_11_11`, `OAI.LaughlinFock.fourYNumber_12_11_3`, `OAI.LaughlinFock.fourYNumber_12_11_5`, `OAI.LaughlinFock.fourYNumber_12_11_7`, `OAI.LaughlinFock.fourYNumber_12_11_9`, `OAI.LaughlinFock.fourYNumber_12_1_1`, `OAI.LaughlinFock.fourYNumber_12_3_3`, `OAI.LaughlinFock.fourYNumber_12_7_1`, `OAI.LaughlinFock.fourYNumber_12_7_7`, `OAI.LaughlinFock.fourYNumber_12_9_1`, `OAI.LaughlinFock.fourYNumber_12_9_3`, `OAI.LaughlinFock.fourYNumber_12_9_7`, `OAI.LaughlinFock.fourYNumber_12_9_9`, `OAI.LaughlinFock.fourYNumber_5_3_1`, `OAI.LaughlinFock.fourYNumber_5_3_3`, `OAI.LaughlinFock.fourYNumber_5_5_3`, `OAI.LaughlinFock.fourYNumber_7_1_1`, `OAI.LaughlinFock.fourYNumber_7_3_1`, `OAI.LaughlinFock.fourYNumber_7_3_3`, `OAI.LaughlinFock.fourYNumber_7_5_5`, `OAI.LaughlinFock.fourYNumber_7_7_1`, `OAI.LaughlinFock.fourYNumber_7_7_5`, `OAI.LaughlinFock.fourYNumber_7_7_7` and `OAI.LaughlinFock.thm_fock`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L000
import Definitions.Def_OAIQ084L001

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model. -/
noncomputable section

namespace LaughlinFock

open scoped BigOperators Matrix ComplexConjugate ComplexOrder


def sectorHamiltonian (Q n : ℕ) :
    Matrix (SectorOccupation Q n) (SectorOccupation Q n) ℂ :=
  (hamiltonian Q).submatrix Subtype.val Subtype.val


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal Ordering. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
open Filter Topology
open Filter Topology
open Filter Topology
open scoped Kronecker
open scoped Matrix ComplexOrder Kronecker BigOperators



def singletonSectorEquiv (Q : ℕ) : Orbital Q ≃ SectorOccupation Q 1 :=
  Equiv.ofBijective (fun j => ⟨{j}, Finset.card_singleton j⟩)
    ⟨by intro i j h; simpa only [Subtype.mk.injEq, Finset.singleton_inj] using h,
      by intro S; obtain ⟨j,hj⟩ := Finset.card_eq_one.mp S.property
         exact ⟨j, Subtype.ext hj.symm⟩⟩

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CreationRows
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Creation Rows. -/
noncomputable section
namespace LaughlinFock
open scoped Matrix ComplexOrder Kronecker BigOperators



def rowTwoBody (Q t : ℕ) (ℓ : ℝ) : FockMatrix Q :=
  ℓ^2 • ((pairAnnihilator Q t)ᴴ * pairAnnihilator Q t)

 
def rowThreeBody {β : Type*} [Fintype β] (Q t : ℕ) (ℓ : ℝ)
    (p : β → ℕ) (i j : β → Orbital Q) (a : β → ℝ) : FockMatrix Q :=
  (∑ b, (ℓ*a b) •
    ((annihilator Q (i b) * pairAnnihilator Q t)ᴴ *
      (annihilator Q (j b) * pairAnnihilator Q (p b)) +
    (annihilator Q (j b) * pairAnnihilator Q (p b))ᴴ *
      (annihilator Q (i b) * pairAnnihilator Q t))) +
    ∑ b, ∑ c, (a b*a c) •
      (if i b = i c then
        (annihilator Q (j b) * pairAnnihilator Q (p b))ᴴ *
          (annihilator Q (j c) * pairAnnihilator Q (p c)) else 0)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

def rowThreePrewedge {β : Type*} [Fintype β] (Q : ℕ) (t : PairLabel Q) (ℓ : ℝ)
    (p : β → PairLabel Q) (i j : β → Orbital Q) (a : β → ℝ) :
    Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  (∑ b, (ℓ*a b : ℂ) •
    (Matrix.single (t,i b) (p b,j b) 1 + Matrix.single (p b,j b) (t,i b) 1)) +
  ∑ b, ∑ c, (a b*a c : ℂ) •
    (if i b = i c then Matrix.single (p b,j b) (p c,j c) 1 else 0)



def sphericalThreeCoefficient (Q z T p : ℕ) : ℝ :=
  if z ≤ T then coupledCoefficient (2*Q-2) Q z (T-z) p else 0



def rowThreeTrace (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*sphericalThreeCoefficient Q z T (rowP b) else 0
    2*ℓ*sphericalThreeCoefficient Q z T t*X + X^2
  else 0


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_EntryEnumeration
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entry Enumeration. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def rowEntryList_3 : List (RowEntry 3) := [⟨(⟨0, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨4, by decide⟩), by decide⟩]

def rowEntryData_3 : Finset (RowEntry 3) := ⟨rowEntryList_3, by decide⟩

def rowEntryList_4 : List (RowEntry 4) := [⟨(⟨0, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨5, by decide⟩), by decide⟩]

def rowEntryData_4 : Finset (RowEntry 4) := ⟨rowEntryList_4, by decide⟩

def rowEntryList_5 : List (RowEntry 5) := [⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨6, by decide⟩), by decide⟩]

def rowEntryData_5 : Finset (RowEntry 5) := ⟨rowEntryList_5, by decide⟩

def rowEntryList_6 : List (RowEntry 6) := [⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨7, by decide⟩), by decide⟩]

def rowEntryData_6 : Finset (RowEntry 6) := ⟨rowEntryList_6, by decide⟩

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 
def rowsEta {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) : ℝ :=
  ∑ i, (rows i).ell ^ 2

 
def rowsThreeTrace {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (Q z : ℕ) : ℝ :=
  ∑ i, rowThreeTrace Q z (rows i).t.val (rows i).ell (rows i).alpha


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NumericTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def rowToNumeric (t : Fin 8) (b : RowEntry t.val) : NumericRowEntry :=
  ⟨rowP b, rowJ b, rowI b, certificateAlphaData t b.val.1 b.val.2⟩

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FasterTrace
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faster Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def shortNumericRowTerm (D t r s : ℕ) (b c : NumericRowEntry) : ℤ :=
  if D ≤ b.p+b.j+c.i then
    let x := memoIntegerCopyPolynomial D (b.p+b.j+c.i) r b.p b.j c.i
    if x = 0 then 0 else
    let y := memoIntegerCopyPolynomial D (b.p+b.j+c.i) s c.p c.j b.i
    if y = 0 then 0 else
    b.a*c.a * (numericRowFactor D t b c : ℤ) * x * y
  else 0

def shortNumericFourTrace (D : ℕ) (t : Fin 8) (r s : ℕ) : ℤ :=
  -(directIntegerSum (fun b => directIntegerSum (shortNumericRowTerm D t.val r s b)
    (numericRowData t)) (numericRowData t))

def shortNumericRowsFourTrace (D r s : ℕ) : ℤ :=
  shortNumericFourTrace D 0 r s + shortNumericFourTrace D 1 r s +
  shortNumericFourTrace D 2 r s + shortNumericFourTrace D 3 r s +
  shortNumericFourTrace D 4 r s + shortNumericFourTrace D 5 r s +
  shortNumericFourTrace D 6 r s + shortNumericFourTrace D 7 r s

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate20
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate20. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_20_4 : List (Occupation 24 × List ℚ) := [
  ({0,3,5,13}, [0, 2048759585832960000, 396696096276480000, 44063395504128000, 41427123978240000, 16947459809280000, -27618082652160000, -313841848320000, 51218989645824000, 0]),
  ({0,3,6,12}, [0, -1843883627249664000, -248562743869440000, -69484585218048000, -16425999507456000, -4953872867328000, 8473729904640000, 8473729904640000, -38414242234368000, 0]),
  ({0,3,7,11}, [0, 1639007668666368000, 140601148047360000, 43686785286144000, 12746807377920000, -5620183252992000, 3515028701184000, -11298306539520000, 25609494822912000, 0]),
  ({0,3,8,10}, [0, -682919861944320000, -105450861035520000, -8662035013632000, -10718906204160000, 6807953940480000, -5021469573120000, 7532204359680000, -12804747411456000, 0])
]

def fourHighestCache_20_5 : List (Occupation 24 × List ℚ) := [
  ({0,4,5,12}, [0, -546335889555456000, -261116417802240000, 9540792188928000, -3012881743872000, -10718906204160000, 11298306539520000, -3766102179840000, -8536498274304000, 0]),
  ({0,4,6,11}, [0, 887795820527616000, 213412456857600000, 10356780994560000, -4142712397824000, 9560105533440000, -8222656425984000, 1569209241600000, 8536498274304000, 0]),
  ({0,4,7,10}, [0, -1707299654860800000, -123026004541440000, -8097119686656000, -376610217984000, -1883051089920000, 1318135762944000, 2510734786560000, -8536498274304000, 0]),
  ({0,4,8,9}, [0, 1639007668666368000, 140601148047360000, -12553673932800000, 9038645231616000, -4461382582272000, 3263955222528000, -5021469573120000, 8536498274304000, 0])
]

def fourHighestCache_20_6 : List (Occupation 24 × List ℚ) := [
  ({0,5,6,10}, [0, 341459930972160000, -47703960944640000, -12239832084480000, 7677054443520000, -5794003353600000, 4079944028160000, -2196892938240000, 0, 0]),
  ({0,5,7,9}, [0, 204875958583296000, -12553673932800000, 18767742529536000, -8372334845952000, 4924902850560000, -3075650113536000, 1569209241600000, 0, 0]),
  ({0,6,7,8}, [0, -682919861944320000, 55236165304320000, -20713561989120000, 7821904527360000, -3737132163072000, 2008587829248000, -941525544960000, 0, 0]),
  ({1,2,3,15}, [0, -2390219516805120000, -509679161671680000, 20399720140800000, 62140685967360000, -376610217984000, -18893279268864000, 7218362511360000, 21341245685760000, 0])
]

def fourHighestCache_20_7 : List (Occupation 24 × List ℚ) := [
  ({1,2,4,14}, [0, 2390219516805120000, 509679161671680000, -20399720140800000, -62140685967360000, 376610217984000, 18893279268864000, -7218362511360000, -21341245685760000, 0]),
  ({1,2,5,13}, [0, -2731679447777280000, -341459930972160000, 47703960944640000, 33141699182592000, -753220435968000, -10042939146240000, 1883051089920000, 17072996548608000, 0]),
  ({1,2,6,12}, [0, 2390219516805120000, 228476865576960000, -63584358469632000, -11153456455680000, 2027901173760000, 2196892938240000, 2510734786560000, -12804747411456000, 0]),
  ({1,2,7,11}, [0, -1707299654860800000, -123026004541440000, 48143339532288000, 3331551928320000, -3041851760640000, 1569209241600000, -3766102179840000, 8536498274304000, 0])
]

def fourHighestCache_20_8 : List (Occupation 24 × List ℚ) := [
  ({1,2,8,10}, [0, 956087806722048000, 35150287011840000, -21215708946432000, -1680260972544000, 2346571358208000, -1757514350592000, 2510734786560000, -4268249137152000, 0]),
  ({1,3,4,13}, [0, 341459930972160000, -168219230699520000, -27304240803840000, 28998986784768000, 376610217984000, -8850340122624000, 5335311421440000, 4268249137152000, 0]),
  ({1,3,5,12}, [0, 341459930972160000, 112983065395200000, 15880397524992000, -21988242726912000, -1274680737792000, 7846046208000000, -4393785876480000, -4268249137152000, 0]),
  ({1,3,6,11}, [0, -682919861944320000, -105450861035520000, 15441018937344000, 7821904527360000, 1013950586880000, -3766102179840000, 1255367393280000, 4268249137152000, 0])
]

def fourHighestCache_20_9 : List (Occupation 24 × List ℚ) := [
  ({1,3,7,10}, [0, 751211848138752000, 87875717529600000, -26927630585856000, -1651290955776000, 695280402432000, 188305108992000, 1255367393280000, -4268249137152000, 0]),
  ({1,3,8,9}, [0, -956087806722048000, -35150287011840000, 21215708946432000, 1680260972544000, -2346571358208000, 1757514350592000, -2510734786560000, 4268249137152000, 0]),
  ({1,4,5,11}, [0, -341459930972160000, 47703960944640000, -19897573183488000, 7155594141696000, 1158800670720000, -3075650113536000, 2196892938240000, 0, 0]),
  ({1,4,6,10}, [0, 478043903361024000, -42682491371520000, 9980170776576000, -3157731827712000, -1883051089920000, 2824576634880000, -1883051089920000, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate21
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_21_0 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,19}, [350337889177436160000, 122618261212102656000, 80285766269829120000, 45981847954538496000, 20436376868683776000, 3649353012264960000, -4379223614717952000, -3649353012264960000, 5838964819623936000, 24085729880948736000, 51090942171709440000]),
  ({0,1,3,18}, [-350337889177436160000, -122618261212102656000, -80285766269829120000, -45981847954538496000, -20436376868683776000, -3649353012264960000, 4379223614717952000, 3649353012264960000, -5838964819623936000, -24085729880948736000, -51090942171709440000]),
  ({0,1,4,17}, [622822914093219840000, 172095805209968640000, 85364982743040000000, 37287424462159872000, 12753528421810176000, 1664617163489280000, -2432902008176640000, -2304854534062080000, 2970701399457792000, 18003474860507136000, 51090942171709440000]),
  ({0,1,5,16}, [-622822914093219840000, -172095805209968640000, -76366509268008960000, -27839027313377280000, -6462631340605440000, -7532204359680000, 866203501363200000, 1039444201635840000, -512189896458240000, -12164510040883200000, -51090942171709440000])
]

def fourHighestCache_21_1 : List (Occupation 24 × List ℚ) := [
  ({0,1,6,15}, [817455074747351040000, 182851793035591680000, 61636028275261440000, 18058459952332800000, 2881068167577600000, -547967867166720000, -222200028610560000, -217492400885760000, -640237370572800000, 7298706024529920000, 51090942171709440000]),
  ({0,1,7,14}, [-817455074747351040000, -182851793035591680000, -48138318062714880000, -10184795661680640000, -964875378475008000, 382259371253760000, 117753461489664000, -151585612738560000, 776821342961664000, -3406062811447296000, -51090942171709440000]),
  ({0,1,8,13}, [934234371139829760000, 179471339718967296000, 35491746942812160000, 5202242477752320000, 40673903542272000, -109216963215360000, -110221257129984000, 173240700272640000, -401215418892288000, 486580401635328000, 51090942171709440000]),
  ({0,1,9,12}, [-934234371139829760000, -179471339718967296000, -25850525362421760000, -2277738598367232000, 190159190065152000, 19989311569920000, 33894919618560000, -22596613079040000, -76828484468736000, 1459741204905984000, -51090942171709440000])
]

def fourHighestCache_21_10 : List (Occupation 24 × List ℚ) := [
  ({1,3,7,11}, [0, 0, -3213740526796800000, 224961836875776000, 175210661412864000, -38240422133760000, 16068702633984000, -45193226158080000, 68291986194432000, 0, 0]),
  ({1,3,8,10}, [-38926432130826240000, 2765825440874496000, 1282985475932160000, -61513002270720000, -119240589017088000, 48669628170240000, -26362715258880000, 30128817438720000, -34145993097216000, 0, 0]),
  ({1,4,5,12}, [311411457046609920000, 7375534508998656000, -1024379792916480000, 309322525704192000, -42064464347136000, -91255552819200000, 69045206630400000, -15064408719360000, -25609494822912000, 0, 0]),
  ({1,4,6,11}, [-194632160654131200000, -10755987825623040000, 268648622161920000, -5272543051776000, -13036507545600000, 77494794854400000, -51470063124480000, 6590678814720000, 25609494822912000, 0, 0])
]

def fourHighestCache_21_11 : List (Occupation 24 × List ℚ) := [
  ({1,4,7,10}, [350337889177436160000, 4609709068124160000, 263627152588800000, -79088145776640000, -22944253280256000, -14774708551680000, 9038645231616000, 11298306539520000, -25609494822912000, 0, 0]),
  ({1,4,8,9}, [-311411457046609920000, -7375534508998656000, 381631687557120000, -84360688828416000, 94905774931968000, -35053720289280000, 19332657856512000, -22596613079040000, 25609494822912000, 0, 0]),
  ({1,5,6,10}, [-155705728523304960000, 6146278757498880000, 110472330608640000, -140601148047360000, 72135341752320000, -47655677583360000, 26362715258880000, -10356780994560000, 0, 0, 0]),
  ({1,5,7,9}, [0, 0, -642748105359360000, 224961836875776000, -80652526682112000, 40558023475200000, -20085878292480000, 7532204359680000, 0, 0, 0])
]

def fourHighestCache_21_12 : List (Occupation 24 × List ℚ) := [
  ({1,6,7,8}, [116779296392478720000, -3380453316624384000, 851139092643840000, -258354609537024000, 79783426179072000, -31722168360960000, 13557967847424000, -4707627724800000, 0, 0, 0]),
  ({2,3,4,13}, [194632160654131200000, 10755987825623040000, -268648622161920000, -444651130699776000, 124281371934720000, 24479664168960000, -34899213533184000, 12239832084480000, 8536498274304000, 0, 0]),
  ({2,3,5,12}, [-194632160654131200000, -10755987825623040000, 268648622161920000, 444651130699776000, -124281371934720000, -24479664168960000, 34899213533184000, -12239832084480000, -8536498274304000, 0, 0]),
  ({2,3,6,11}, [311411457046609920000, 7375534508998656000, -1024379792916480000, -140601148047360000, 69180400041984000, 10718906204160000, -17324070027264000, 3766102179840000, 8536498274304000, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FockRotations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fock Rotations. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def sectorAverage (Q k : ℕ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ →ₗ[ℂ]
      Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ :=
  rotationAverageLinear (fockRotationGenerator Q) (fockRotationGenerator_skew Q) (.sector k)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 
def sourceRowP {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : PairLabel Q :=
  ⟨rowP b, by have := (rowEntry_bounds b).1; omega⟩

def sourceRowT {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7) : PairLabel Q :=
  ⟨t, by omega⟩

 
def sourceRowThreeKernel {Q t : ℕ} (hQ : 8 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ :=
  rowThreePrewedge Q (sourceRowT hQ ht) ℓ (sourceRowP hQ) (sourceRowI hQ) (sourceRowJ hQ) a


def sphericalRowAmplitude (Q z t T : ℕ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ b : RowEntry t, if rowP b+rowJ b=T then
    a b*sphericalThreeCoefficient Q z T (rowP b) else 0


def rowThreeLevelTrace (Q z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) (T : ℕ) : ℝ :=
  if z ≤ T ∧ t ≤ T then
    2*ℓ*sphericalThreeCoefficient Q z T t*sphericalRowAmplitude Q z t T a +
      (sphericalRowAmplitude Q z t T a)^2
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def sourceRowFourP {Q t : ℕ} (hQ : 8 ≤ Q) (b : RowEntry t) : Fin (2*Q-2+1) :=
  ⟨rowP b, by have := (rowEntry_bounds b).1; omega⟩


end LaughlinFock
end

end OAI
end


