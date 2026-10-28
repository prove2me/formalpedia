-- Prove2me | Definitions.Def_OAIQ084L020
-- name    : OAIQ084L020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:30:41.017215+00:00
-- url     : https://prove2.me/theorems/acc3fefa-dfca-4acd-b1d1-325844cbfda7
-- title:
--   Definitions bundle OAIQ084L020 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 32 definitions and 1 instance. The definitions and types are `OAI.LaughlinFock.fourHighestCache_23_16`, `OAI.LaughlinFock.fourHighestCache_23_17`, `OAI.LaughlinFock.fourHighestCache_23_18`, `OAI.LaughlinFock.fourHighestCache_23_19`, `OAI.LaughlinFock.fourHighestCache_23_2`, `OAI.LaughlinFock.fourHighestCache_23_20`, `OAI.LaughlinFock.fourHighestCache_23_3`, `OAI.LaughlinFock.fourHighestCache_23_4`, `OAI.LaughlinFock.numericFourTrace`, `OAI.LaughlinFock.numericRowTerm`, `OAI.LaughlinFock.numericRowsFourTrace`, `OAI.LaughlinFock.orbitalDelta`, `OAI.LaughlinFock.orderedFourColumn`, `OAI.LaughlinFock.oscillatorCoefficient`, `OAI.LaughlinFock.pairPartialAnnihilator`, `OAI.LaughlinFock.planarFourComparison`, `OAI.LaughlinFock.planarLocalCopyMatrix`, `OAI.LaughlinFock.planarRowFourTrace`, `OAI.LaughlinFock.planarRowThreeTrace`, `OAI.LaughlinFock.planarRowsThreeTrace`, `OAI.LaughlinFock.rationalThreeTrace`, `OAI.LaughlinFock.rotationCrossAverage`, `OAI.LaughlinFock.rowEntryData_0`, `OAI.LaughlinFock.rowEntryData_1`, `OAI.LaughlinFock.rowEntryData_2`, `OAI.LaughlinFock.rowEntryData_7`, `OAI.LaughlinFock.rowEntryList_0`, `OAI.LaughlinFock.rowEntryList_1`, `OAI.LaughlinFock.rowEntryList_2`, `OAI.LaughlinFock.rowEntryList_7`, `OAI.LaughlinFock.swap23`, `OAI.LaughlinFock.wedgeAnnihilator`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinFock_Averaging`, `LaughlinFock_Certificate23`, `LaughlinFock_CrossOrbit`, `LaughlinFock_EntryEnumeration`, `LaughlinFock_FermionOperators`, `LaughlinFock_FiniteComparison`, `LaughlinFock_FiniteCoupling`, `LaughlinFock_FourTraces`, `LaughlinFock_NormalOrdering`, `LaughlinFock_NumericTrace`, `LaughlinFock_RationalThree`, `LaughlinFock_RelativeTransfer`, `LaughlinFock_RowTraces`, `LaughlinFock_SwapCompression`, `LaughlinFock_ThreeGram`.
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L000` and `OAIQ084L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ084L022`, `OAIQ084L023`, `OAIQ084L029` and `OAIQ084L035`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L000
import Definitions.Def_OAIQ084L001

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FermionOperators
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fermion Operators. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial


def orbitalDelta (Q : ℕ) (i j : Orbital Q) : FockMatrix Q := if i=j then 1 else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NormalOrdering
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
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



def wedgeAnnihilator (Q k : ℕ) (v : SectorOccupation Q k → ℂ) : FockMatrix Q :=
  ∑ A, star (v A) • basisAnnihilator Q A.val


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeGram
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Gram. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder


def pairPartialAnnihilator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) (k : Orbital Q) :
    FockMatrix Q := ∑ i, a k i • annihilator Q i


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Averaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open NormedSpace MeasureTheory Topology

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)

attribute [local instance] OAI.LaughlinFock.averagingRotationMeasurableSpace
attribute [local instance] OAI.LaughlinFock.averagingRotationBorelSpace
instance rotationHaar_leftInvariant : (rotationHaar X hX).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _


end
end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteCoupling
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology



def oscillatorCoefficient (r : ℝ) (z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => (-1 : ℝ)^(z-p) * Real.sqrt ((z.choose p : ℝ) * (1-r)^(z-p) * r^p)
  | k+1, p =>
      ((if p = 0 then 0 else Real.sqrt ((p : ℝ)*(1-r)) * oscillatorCoefficient r z k (p-1)) +
        Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * Real.sqrt r * oscillatorCoefficient r z k p) /
        Real.sqrt (k+1 : ℕ)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SwapCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swap Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators


def swap23 : CubeVector →ₗ[ℝ] CubeVector where
  toFun f i j k := f i k j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


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



def planarRowThreeTrace (z t : ℕ) (ℓ : ℝ) (a : RowEntry t → ℝ) : ℝ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*planarThreeCoefficient z T (rowP b) else 0
    2*ℓ*planarThreeCoefficient z T t*X + X^2
  else 0



def planarRowFourTrace (D t : ℕ) (a : RowEntry t → ℝ) : Matrix (CopyLabel D) (CopyLabel D) ℝ :=
  fun r s => -(∑ b : RowEntry t, ∑ c : RowEntry t,
    a b*a c*planarCopyCoefficient D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) *
      planarCopyCoefficient D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b))



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
def rowEntryList_0 : List (RowEntry 0) := [⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩]

def rowEntryData_0 : Finset (RowEntry 0) := ⟨rowEntryList_0, by decide⟩

def rowEntryList_1 : List (RowEntry 1) := [⟨(⟨0, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩]

def rowEntryData_1 : Finset (RowEntry 1) := ⟨rowEntryList_1, by decide⟩

def rowEntryList_2 : List (RowEntry 2) := [⟨(⟨0, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩]

def rowEntryData_2 : Finset (RowEntry 2) := ⟨rowEntryList_2, by decide⟩

def rowEntryList_7 : List (RowEntry 7) := [⟨(⟨0, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨0, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨1, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨2, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨3, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨4, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨5, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨6, by decide⟩, ⟨8, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨0, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨1, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨2, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨3, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨4, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨5, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨6, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨7, by decide⟩), by decide⟩, ⟨(⟨7, by decide⟩, ⟨8, by decide⟩), by decide⟩]

def rowEntryData_7 : Finset (RowEntry 7) := ⟨rowEntryList_7, by decide⟩

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RelativeTransfer
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Transfer. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



def planarFourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (2 : ℂ) • targetCopy D -
    Matrix.of (fun r s => ((∑ i, planarRowFourTrace D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ)) +
      (ε : ℂ) • 1

def planarLocalCopyMatrix (D : ℕ) : Matrix (CopyLabel D) (FourHighestShell 24 D) ℂ := fun r b =>
  planarCopyCoefficient D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val

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


def planarRowsThreeTrace {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (z : ℕ) : ℝ :=
  ∑ i, planarRowThreeTrace z (rows i).t.val (rows i).ell (rows i).alpha

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalThree
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Three. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def rationalThreeTrace (z t : ℕ) (ell : ℚ) (a : RowEntry t → ℚ) : ℚ :=
  ∑ T ∈ Finset.range 16, if z ≤ T ∧ t ≤ T then
    let X := ∑ b : RowEntry t, if rowP b+rowJ b=T then
      a b*rationalCoupling 2 z (T-z) (rowP b) else 0
    rationalCouplingWeight 2 z (T-z) t * X *
      (X+2*ell*rationalCoupling 2 z (T-z) t)
  else 0

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_NumericTrace
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def numericRowTerm (D t r s : ℕ) (b c : NumericRowEntry) : ℤ :=
  if D ≤ b.p+b.j+c.i then
    b.a*c.a * (numericRowFactor D t b c : ℤ) *
      memoIntegerCopyPolynomial D (b.p+b.j+c.i) r b.p b.j c.i *
      memoIntegerCopyPolynomial D (b.p+b.j+c.i) s c.p c.j b.i
  else 0

def numericFourTrace (D : ℕ) (t : Fin 8) (r s : ℕ) : ℤ :=
  -(((numericRowData t).map (fun b => ((numericRowData t).map (fun c =>
    numericRowTerm D t.val r s b c)).sum)).sum)

def numericRowsFourTrace (D r s : ℕ) : ℤ :=
  ∑ t : Fin 8, numericFourTrace D t r s

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def fourHighestCache_23_2 : List (Occupation 24 × List ℚ) := [
  ({0,1,10,13}, [539520349333251686400000, 102765780825381273600000, 16132445168745185280000, 1623837809085972480000, 28155379896483840000, -37035848836546560000, 6033295692103680000, -7908814577664000000, 3841424223436800000, 43792236147179520000, -715273190403932160000, 25852016738884976640000]),
  ({0,1,11,12}, [-539520349333251686400000, -102765780825381273600000, -13673933665745633280000, -915208022927278080000, 59157933040926720000, 2313545539092480000, 10688197986385920000, -17399392070860800000, 42255666457804800000, -160571532539658240000, 1124000727777607680000, -25852016738884976640000]),
  ({0,2,3,19}, [-143872093155533783040000, -29895499876474552320000, -6422861301586329600000, 2861092761615728640000, 4373384649898328064000, 2408572988094873600000, 14597412049059840000, -1021818843434188800000, -175168944588718080000, 1818837541312856064000, 2963274645959147520000, 0]),
  ({0,2,4,18}, [0, 0, -4130299325039247360000, -4818682545879121920000, -3897969988005789696000, -1960662923642142720000, -39950811923742720000, 860479026049843200000, 208973477754961920000, -1611554290216206336000, -2861092761615728640000, 0])
]

def fourHighestCache_23_3 : List (Occupation 24 × List ℚ) := [
  ({0,2,5,17}, [-107904069866650337280000, -9342343711398297600000, 6455129265063198720000, 5917585968730275840000, 2947140664220712960000, 921173528780144640000, -15365696893747200000, -397971549548052480000, -227412314027458560000, 919636959090769920000, 2452365224242053120000, 0]),
  ({0,2,6,16}, [0, 0, -6883832208398745600000, -5007650488854773760000, -2042372276535951360000, -298275292643328000000, 86951767128145920000, 80986261275279360000, 184388362724966400000, -350337889177436160000, -2043637686868377600000, 0]),
  ({0,2,7,15}, [-71936046577766891520000, 0, 7507679502284881920000, 3718408261834506240000, 1144247293096427520000, 81777142733045760000, -102023708051865600000, 26204538967326720000, -87840567242588160000, 0, 1634910149494702080000, 0]),
  ({0,2,8,14}, [0, 0, -6195448987558871040000, -2692793187403038720000, -493763111712718848000, -13919513656688640000, 57576170125393920000, -13497710212546560000, -7170658550415360000, 163491014949470208000, -1226182612121026560000, 0])
]

def fourHighestCache_23_4 : List (Occupation 24 × List ℚ) := [
  ({0,2,9,13}, [-35968023288883445760000, 1868468742279659520000, 4282419724287344640000, 1664330939723612160000, 195885519459581952000, -27341901825638400000, -3027946152591360000, -20721094193479680000, 55316508817489920000, -186846874227965952000, 817455074747351040000, 0]),
  ({0,2,10,12}, [0, 0, -2458511502999552000000, -708629786158694400000, -87313312937410560000, 34722303297454080000, -16721493678489600000, 25308206648524800000, -46097090681241600000, 116779296392478720000, -408727537373675520000, 0]),
  ({0,3,4,17}, [251776163022184120320000, 39237843587872849920000, 8228330686601625600000, 858686361412239360000, 475414661892538368000, 591579330409267200000, 80669908692172800000, -301167659117445120000, -15365696893747200000, 484634080028786688000, 306545653030256640000, 0]),
  ({0,3,5,16}, [-143872093155533783040000, -29895499876474552320000, -9176394184945827840000, -1863105812775567360000, -452384193842380800000, -383283751046676480000, -88804689400627200000, 228406565002936320000, 46097090681241600000, -423324949422735360000, -306545653030256640000, 0])
]

def fourHighestCache_23_16 : List (Occupation 24 × List ℚ) := [
  ({2,3,7,12}, [-179840116444417228800000, -9342343711398297600000, 440995500850544640000, 150478378697687040000, -36254006024011776000, -1625217940684800000, -338949196185600000, 2583546095370240000, -768284844687360000, -2919482409811968000, 0, 0]),
  ({2,3,8,11}, [215808139733300674560000, 7473874969118638080000, -740626590278615040000, -56732563237109760000, 29800413328637952000, -2466507227627520000, -338949196185600000, 210901722071040000, -1280474741145600000, 2919482409811968000, 0, 0]),
  ({2,3,9,10}, [-215808139733300674560000, -7473874969118638080000, 1035647970638561280000, -31002553144442880000, -12843914874126336000, -133841477468160000, 2056291790192640000, -1898115498639360000, 2304854534062080000, -2919482409811968000, 0, 0]),
  ({2,4,5,13}, [-71936046577766891520000, 0, 722187754006118400000, -94694873209896960000, -31318905727549440000, 24110586155335680000, -4496726002728960000, -3321702122618880000, 3329234326978560000, 0, 0, 0])
]

def fourHighestCache_23_17 : List (Occupation 24 × List ℚ) := [
  ({2,4,6,12}, [0, 0, -491702300599910400000, 74237406169006080000, 23030468050157568000, -18508364312739840000, 2801980021800960000, 3374427553136640000, -3073139378749440000, 0, 0, 0]),
  ({2,4,7,11}, [-35968023288883445760000, 1868468742279659520000, 299631089428070400000, -93745815460577280000, 6453592695373824000, 4091725168312320000, 677898392371200000, -2794447817441280000, 2048759585832960000, 0, 0, 0]),
  ({2,4,8,10}, [0, 0, -295021380359946240000, 87735116381552640000, -16956498454511616000, 2600348705095680000, -1717342594007040000, 1687213776568320000, -1024379792916480000, 0, 0, 0]),
  ({2,5,6,11}, [107904069866650337280000, -1868468742279659520000, -38414242234368000000, 39965876332462080000, -21195623068139520000, 8814417301831680000, -1785132433244160000, -632705166213120000, 768284844687360000, 0, 0, 0])
]

def fourHighestCache_23_18 : List (Occupation 24 × List ℚ) := [
  ({2,5,7,10}, [-71936046577766891520000, 0, 132144993286225920000, -27206322147164160000, 11705045574942720000, -4952134666321920000, 564915326976000000, 896332318801920000, -768284844687360000, 0, 0, 0]),
  ({2,5,8,9}, [107904069866650337280000, -1868468742279659520000, 109096447945605120000, -30897102283407360000, 6516863211995136000, -1051611608678400000, 1197620493189120000, -1265410332426240000, 768284844687360000, 0, 0, 0]),
  ({2,6,7,9}, [-35968023288883445760000, 1868468742279659520000, -192071211171840000000, 34482431558615040000, -8984413360226304000, 2715069971496960000, -768284844687360000, 158176291553280000, 0, 0, 0, 0]),
  ({3,4,5,12}, [71936046577766891520000, 0, -230485453406208000000, 20457467040890880000, 8288437677391872000, -5602221842595840000, 1694745980928000000, -52725430517760000, -256094948229120000, 0, 0, 0])
]

def fourHighestCache_23_19 : List (Occupation 24 × List ℚ) := [
  ({3,4,6,11}, [-71936046577766891520000, 0, 230485453406208000000, -20457467040890880000, -8288437677391872000, 5602221842595840000, -1694745980928000000, 52725430517760000, 256094948229120000, 0, 0, 0]),
  ({3,4,7,10}, [107904069866650337280000, -1868468742279659520000, -136754702354350080000, 33217021226188800000, -1202139815804928000, -1739939207086080000, 474528874659840000, 210901722071040000, -256094948229120000, 0, 0, 0]),
  ({3,4,8,9}, [-107904069866650337280000, 1868468742279659520000, 185924932414341120000, -56838014098145280000, 10439635242516480000, -1548737096417280000, 519722100817920000, -421803444142080000, 256094948229120000, 0, 0, 0]),
  ({3,5,6,10}, [-35968023288883445760000, 1868468742279659520000, -93730751051857920000, -12759554185297920000, 9490577493196800000, -3862282635509760000, 1220217106268160000, -263627152588800000, 0, 0, 0, 0])
]

def fourHighestCache_23_20 : List (Occupation 24 × List ℚ) := [
  ({3,5,7,9}, [0, 0, -49170230059991040000, 23620992871956480000, -9237495426711552000, 3288676303503360000, -994250975477760000, 210901722071040000, 0, 0, 0, 0]),
  ({3,6,7,8}, [35968023288883445760000, -1868468742279659520000, 192071211171840000000, -34482431558615040000, 8984413360226304000, -2715069971496960000, 768284844687360000, -158176291553280000, 0, 0, 0, 0]),
  ({4,5,6,9}, [35968023288883445760000, -1868468742279659520000, 142900981111848960000, -10861438686658560000, -253082066485248000, 573606332006400000, -225966130790400000, 52725430517760000, 0, 0, 0, 0]),
  ({4,5,7,8}, [-35968023288883445760000, 1868468742279659520000, -142900981111848960000, 10861438686658560000, 253082066485248000, -573606332006400000, 225966130790400000, -52725430517760000, 0, 0, 0, 0])
]

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_CrossOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cross Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Elementwise ComplexOrder
open MeasureTheory Topology

section
variable {J σ : Type*} {I : J → Type*}
  [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  (X : σ → ∀ j, Matrix (I j) (I j) ℂ)
  (hX : ∀ s j, (X s j)ᴴ = -X s j)


local instance crossOrbitRotationMeasurableSpace_r7f2a4f_1 : MeasurableSpace (rotationGroup X hX) := borel _
local instance crossOrbitRotationBorelSpace_r7f2a4f_1 : BorelSpace (rotationGroup X hX) := ⟨rfl⟩
def rotationCrossAverage (i j : J) (M : Matrix (I i) (I j) ℂ) : Matrix (I i) (I j) ℂ :=
  ∫ g, rotationEvaluation X hX i g * M * (rotationEvaluation X hX j g)ᴴ ∂rotationHaar X hX

end


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourTraces
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def orderedFourColumn (Q : ℕ) (p : Fin (2*Q-2+1)) (j k : Orbital Q) : FourUncoupled Q → ℂ :=
  if h : j < k then Pi.single (p,⟨(j,k),h⟩) 1
  else if h : k < j then Pi.single (p,⟨(k,j),h⟩) (-1) else 0


end LaughlinFock
end

end OAI
end


