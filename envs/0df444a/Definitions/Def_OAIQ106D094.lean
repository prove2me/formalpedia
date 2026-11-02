-- Prove2me | Definitions.Def_OAIQ106D094
-- name    : OAIQ106D094
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T12:59:46.420277+00:00
-- url     : https://prove2.me/theorems/19b2266d-3365-4aee-9938-99d040f53339
-- title:
--   Definitions bundle OAIQ106D094 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 737 declarations of OpenAI's Lean: 737 definitions. The definitions and types are `OAI.MUB6.Certificate.GramEntries.Block5.entry10_1`, `OAI.MUB6.Certificate.GramEntries.Block5.entry10_3`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_10`, `OAI.MUB6.Certificate.GramEntries.Block5.entry11_5`, `OAI.MUB6.Certificate.GramEntries.Block5.entry2_2`, `OAI.MUB6.Certificate.GramEntries.Block5.entry5_2`, `OAI.MUB6.Certificate.GramPolynomial.keyLess`, `OAI.MUB6.Certificate.GramRows.key104`, `OAI.MUB6.Certificate.GramRows.key1061`, `OAI.MUB6.Certificate.GramRows.key1062`, `OAI.MUB6.Certificate.GramRows.key12`, `OAI.MUB6.Certificate.GramRows.key1275`, `OAI.MUB6.Certificate.GramRows.key129`, `OAI.MUB6.Certificate.GramRows.key130`, `OAI.MUB6.Certificate.GramRows.key1328`, `OAI.MUB6.Certificate.GramRows.key1349`, `OAI.MUB6.Certificate.GramRows.key1381`, `OAI.MUB6.Certificate.GramRows.key140`, `OAI.MUB6.Certificate.GramRows.key1404`, `OAI.MUB6.Certificate.GramRows.key1413`, `OAI.MUB6.Certificate.GramRows.key1414`, `OAI.MUB6.Certificate.GramRows.key1446`, `OAI.MUB6.Certificate.GramRows.key145`, `OAI.MUB6.Certificate.GramRows.key1470`, `OAI.MUB6.Certificate.GramRows.key1521`, `OAI.MUB6.Certificate.GramRows.key1558`, `OAI.MUB6.Certificate.GramRows.key1584`, `OAI.MUB6.Certificate.GramRows.key1595`, `OAI.MUB6.Certificate.GramRows.key1608`, `OAI.MUB6.Certificate.GramRows.key1611`, `OAI.MUB6.Certificate.GramRows.key1616`, `OAI.MUB6.Certificate.GramRows.key1626`, `OAI.MUB6.Certificate.GramRows.key1635`, `OAI.MUB6.Certificate.GramRows.key1643`, `OAI.MUB6.Certificate.GramRows.key1644`, `OAI.MUB6.Certificate.GramRows.key1675`, `OAI.MUB6.Certificate.GramRows.key1676`, `OAI.MUB6.Certificate.GramRows.key168`, `OAI.MUB6.Certificate.GramRows.key1694`, `OAI.MUB6.Certificate.GramRows.key1698` and 697 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Certificate_GramPolynomial`, `MutuallyUnbiased_GramEntries_Block5Data`, `MutuallyUnbiased_GramKeys_Block0`, `MutuallyUnbiased_GramKeys_Block1`, `MutuallyUnbiased_GramKeys_Block10`, `MutuallyUnbiased_GramKeys_Block11`, `MutuallyUnbiased_GramKeys_Block12`, `MutuallyUnbiased_GramKeys_Block13`, `MutuallyUnbiased_GramKeys_Block14`, `MutuallyUnbiased_GramKeys_Block15`, `MutuallyUnbiased_GramKeys_Block16`, `MutuallyUnbiased_GramKeys_Block17`, `MutuallyUnbiased_GramKeys_Block18`, `MutuallyUnbiased_GramKeys_Block2`, `MutuallyUnbiased_GramKeys_Block23`, `MutuallyUnbiased_GramKeys_Block24`, `MutuallyUnbiased_GramKeys_Block3`, `MutuallyUnbiased_GramKeys_Block4`, `MutuallyUnbiased_GramKeys_Block5`, `MutuallyUnbiased_GramKeys_Block6`, `MutuallyUnbiased_GramKeys_Block7`, `MutuallyUnbiased_GramKeys_Block8`, `MutuallyUnbiased_GramKeys_Block9`, `MutuallyUnbiased_GramRows_Block0`, `MutuallyUnbiased_GramRows_Block107`, `MutuallyUnbiased_GramRows_Block108`, `MutuallyUnbiased_GramRows_Block109`, `MutuallyUnbiased_GramRows_Block110`, `MutuallyUnbiased_GramRows_Block130`, `MutuallyUnbiased_GramRows_Block132`, `MutuallyUnbiased_GramRows_Block150`, `MutuallyUnbiased_GramRows_Block151`, `MutuallyUnbiased_GramRows_Block152`, `MutuallyUnbiased_GramRows_Block153`, `MutuallyUnbiased_GramRows_Block154`, `MutuallyUnbiased_GramRows_Block169`, `MutuallyUnbiased_GramRows_Block171`, `MutuallyUnbiased_GramRows_Block175`, `MutuallyUnbiased_GramRows_Block176`, `MutuallyUnbiased_GramRows_Block179`, `MutuallyUnbiased_GramRows_Block181`, `MutuallyUnbiased_GramRows_Block182`, `MutuallyUnbiased_MixedMoments_MixedMoments`, `MutuallyUnbiased_MixedSemantics_Values18`, `MutuallyUnbiased_MixedSemantics_Values19`, `MutuallyUnbiased_Moments_AuxiliaryGram`, `MutuallyUnbiased_Moments_GramNormalization`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`; the bundles `OAIQ106D000`, `OAIQ106D001` and `OAIQ106D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106D151`, `OAIQ106D152`, `OAIQ106D153`, `OAIQ106D154`, `OAIQ106D155`, `OAIQ106D156`, `OAIQ106D157`, `OAIQ106D158`, `OAIQ106D159`, `OAIQ106D160`, `OAIQ106D162`, `OAIQ106D163`, `OAIQ106D164`, `OAIQ106D165`, `OAIQ106D166`, `OAIQ106D167`, `OAIQ106D168`, `OAIQ106D169`, `OAIQ106D170`, `OAIQ106D171`, `OAIQ106D172`, `OAIQ106D173`, `OAIQ106D174`, `OAIQ106D178`, `OAIQ106D179`, `OAIQ106D180`, `OAIQ106D181`, `OAIQ106D182`, `OAIQ106D185` and `OAIQ106D186`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D002

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def mixedIntegrand {p n l : ℕ} (B : Fin 7 → Basis) (A : Matrix (Fin p) (Fin n) ℤ)
    (label : Fin n → Fin l) (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) : ℂ :=
  ∏ j, rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)

/-- The real mixed moment with uniform reference, row injection, and injection
of the distinct matrix labels into the six nonreference bases. -/
def mixedMoment {p n l : ℕ} (B : Fin 7 → Basis) (A : Matrix (Fin p) (Fin n) ℤ)
    (label : Fin n → Fin l) : ℝ :=
  average (fun r : Fin 7 => average (fun ρ : Fin p ↪ Coord =>
    average (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AuxiliaryGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Auxiliary-column Gram matrices

The functions in manuscript §4 are interpreted, with the same sampled
column in all factors. Real Gram forms are nonnegative for any real positive
semidefinite coefficient matrix. No numerical certificate is assumed here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

/-- The character of the shared sampled column, before any Fourier average. -/
def auxiliaryCharacter (B : Fin 7 → Basis) (a : Charge) (ω : AuxiliarySample) : ℂ :=
  character (fun i => relativeMatrix B ω.1 (ω.2.2.1 0) (ω.2.1 i) ω.2.2.2) a

/-- One Fourier factor, labelled `s`, multiplied by the inverse character of
the same auxiliary column used by all factors. -/
def elementaryAuxiliary (B : Fin 7 → Basis) (s : Coord) (a : Charge)
    (ω : AuxiliarySample) : ℂ :=
  rowFourier (relativeMatrix B ω.1 (ω.2.2.1 s)) ω.2.1 a * auxiliaryCharacter B (-a) ω

/-- Manuscript `F₀` and `F₁`; the latter averages the five nonzero labels. -/
def auxiliaryF (B : Fin 7 → Basis) (t : Fin 2) (a : Charge) : AuxiliarySample → ℂ :=
  if t = 0 then elementaryAuxiliary B 0 a
  else fun ω => (5 : ℂ)⁻¹ * ∑ s : Fin 5, elementaryAuxiliary B s.succ a ω

/-- The three charges produced by integrating out the shared column. -/
def gramCharges (a v : Charge) : Matrix Coord (Fin 3) ℤ :=
  fun i => ![a i, -v i, v i - a i]

def gramLabels (s t : Coord) : Fin 3 → Coord := ![s, t, 0]

/-- The exact mixed-moment expression for a pair of auxiliary functions. -/
def auxiliaryMixedEntry (B : Fin 7 → Basis) (s t : Fin 2) (a v : Charge) : ℝ :=
  if s = 1 ∧ t = 1 then
    (1 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 1) +
    (4 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 2)
  else mixedMoment B (gramCharges a v)
    (gramLabels (Fin.castLE (by decide : 2 ≤ 6) s) (Fin.castLE (by decide : 2 ≤ 6) t))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

def rowOrder (a v : Charge) : List Coord :=
  (List.finRange 6).insertionSort (fun i j => (compare (a i) (a j) |>.then (compare (v i) (v j))) != .gt)

def orderedKey (s t : Fin 2) (a v : Charge) : Key :=
  ⟨s, t, (rowOrder a v).map (fun i => (a i, v i))⟩

def normalize (s t : Fin 2) (a v : Charge) : Key :=
  if (compare s.val t.val |>.then (compare (List.ofFn a) (List.ofFn v))) == .gt then
    orderedKey t s v a
  else orderedKey s t a v

end MUB6.GramNormalization

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

open GramFunctions GramNormalization
open scoped BigOperators

def keyLess (a b : Key) : Bool :=
  (compare a.leftTag.val b.leftTag.val |>.then
    (compare a.rightTag.val b.rightTag.val) |>.then (compareRows a.rows b.rows)) == .lt

end MUB6.Certificate.GramPolynomial

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key12 : Key := ⟨0, 0, [(-3, -3), (0, 0), (0, 1), (1, 0), (1, 0), (1, 2)]⟩
def key38 : Key := ⟨0, 0, [(-3, -2), (0, 0), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key99 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 0), (1, 0), (2, 3)]⟩
def key104 : Key := ⟨0, 0, [(-3, 0), (0, -2), (0, -1), (0, 1), (1, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key129 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 0), (1, 3)]⟩
def key130 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, -1), (1, -1), (1, 1), (1, 2)]⟩
def key140 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 0), (1, -1), (1, -1), (1, 3)]⟩
def key145 : Key := ⟨0, 0, [(-3, 0), (0, -1), (0, 2), (1, -1), (1, -1), (1, 1)]⟩
def key168 : Key := ⟨0, 0, [(-3, 1), (0, -3), (0, 0), (1, 0), (1, 0), (1, 2)]⟩
def key188 : Key := ⟨0, 0, [(-3, 1), (0, 0), (0, 0), (1, -3), (1, 0), (1, 2)]⟩
def key207 : Key := ⟨0, 0, [(-2, -3), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 1)]⟩
def key222 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key224 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 0), (0, 1), (0, 1), (2, 1)]⟩
def key230 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 1), (0, 1), (0, 1), (2, 0)]⟩
def key231 : Key := ⟨0, 0, [(-2, -3), (0, 0), (0, 1), (0, 1), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1328 : Key := ⟨0, 1, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key1349 : Key := ⟨0, 1, [(-2, -2), (-1, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key1381 : Key := ⟨0, 1, [(-2, -2), (0, 1), (0, 1), (0, 1), (1, -1), (1, 0)]⟩
def key1404 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, -1), (0, 0), (0, 2), (3, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1413 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, 0), (0, 2), (1, -1), (2, 1)]⟩
def key1414 : Key := ⟨0, 1, [(-2, -1), (-1, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩
def key1446 : Key := ⟨0, 1, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key1470 : Key := ⟨0, 1, [(-2, -1), (-1, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key1521 : Key := ⟨0, 1, [(-2, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1558 : Key := ⟨0, 1, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key1584 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, -1), (0, -1), (1, 3), (2, 0)]⟩
def key1595 : Key := ⟨0, 1, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key1608 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 0), (2, 2)]⟩
def key1611 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -3), (0, 2), (1, 0), (2, 1)]⟩
def key1616 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 3)]⟩
def key1626 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 2)]⟩
def key1635 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 2)]⟩
def key1643 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key1644 : Key := ⟨0, 1, [(-2, 0), (-1, 0), (0, 2), (1, -2), (1, -1), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1675 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key1676 : Key := ⟨0, 1, [(-2, 0), (-1, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key1694 : Key := ⟨0, 1, [(-2, 0), (-1, 2), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key1698 : Key := ⟨0, 1, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key1713 : Key := ⟨0, 1, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 0), (1, 3)]⟩
def key1750 : Key := ⟨0, 1, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 3), (2, -3)]⟩
def key1784 : Key := ⟨0, 1, [(-2, 1), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1802 : Key := ⟨0, 1, [(-2, 1), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key1812 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 2)]⟩
def key1830 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key1833 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key1834 : Key := ⟨0, 1, [(-2, 1), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key1843 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key1846 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key1849 : Key := ⟨0, 1, [(-2, 1), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1931 : Key := ⟨0, 1, [(-2, 2), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key1986 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key1987 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key1988 : Key := ⟨0, 1, [(-1, -3), (-1, 0), (0, 0), (0, 0), (1, 1), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2314 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, 0), (0, 0), (1, -3), (1, 1)]⟩
def key2315 : Key := ⟨0, 1, [(-1, 0), (-1, 2), (0, 0), (0, 1), (1, -2), (1, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key258 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (0, 0), (1, 2), (2, 0)]⟩
def key264 : Key := ⟨0, 0, [(-2, -2), (-1, 0), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key276 : Key := ⟨0, 0, [(-2, -2), (-1, 1), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key279 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 0), (2, 3)]⟩
def key280 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key283 : Key := ⟨0, 0, [(-2, -2), (0, -1), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key292 : Key := ⟨0, 0, [(-2, -2), (0, 0), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key332 : Key := ⟨0, 0, [(-2, -1), (-1, 0), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key345 : Key := ⟨0, 0, [(-2, -1), (-1, 1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key349 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key352 : Key := ⟨0, 0, [(-2, -1), (0, -2), (0, 0), (0, 1), (0, 2), (2, 0)]⟩
def key361 : Key := ⟨0, 0, [(-2, -1), (0, -1), (0, 0), (0, 0), (0, 1), (2, 1)]⟩
def key369 : Key := ⟨0, 0, [(-2, -1), (0, 0), (0, 0), (0, 1), (0, 2), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2957 : Key := ⟨1, 1, [(-2, 1), (-1, -1), (0, -1), (1, -1), (1, 0), (1, 2)]⟩
def key3041 : Key := ⟨1, 1, [(-1, -3), (-1, 0), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩
def key3049 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 3), (2, 0)]⟩
def key3056 : Key := ⟨1, 1, [(-1, -2), (-1, -1), (-1, 1), (0, 0), (1, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key3114 : Key := ⟨1, 1, [(-1, -1), (-1, 0), (-1, 2), (0, -1), (1, 1), (2, -1)]⟩
def key3134 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -2), (1, -1), (2, 2)]⟩
def key3136 : Key := ⟨1, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, -2), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key401 : Key := ⟨0, 0, [(-2, 0), (-1, -2), (0, 0), (1, -1), (1, 1), (1, 2)]⟩
def key422 : Key := ⟨0, 0, [(-2, 0), (-1, -1), (0, 0), (1, -2), (1, 1), (1, 2)]⟩
def key431 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -3), (0, 1), (1, 2), (2, 0)]⟩
def key434 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (0, -1), (1, 0), (2, 3)]⟩
def key446 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -2), (1, -1), (1, 1), (1, 2)]⟩
def key447 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, -1), (1, 1), (2, 1)]⟩
def key451 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (0, 1), (1, 1), (2, -1)]⟩
def key454 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, -1), (1, -2), (1, 1), (1, 2)]⟩
def key455 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -2)]⟩
def key462 : Key := ⟨0, 0, [(-2, 0), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 2)]⟩
def key484 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key485 : Key := ⟨0, 0, [(-2, 0), (-1, 1), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key494 : Key := ⟨0, 0, [(-2, 0), (0, -3), (0, 0), (0, 0), (0, 3), (2, 0)]⟩
def key506 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key507 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 0), (1, 0), (1, 3)]⟩
def key509 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, -1), (0, 1), (0, 2), (2, 0)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key520 : Key := ⟨0, 0, [(-2, 0), (0, -2), (0, 0), (0, 1), (0, 2), (2, -1)]⟩
def key530 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (0, 1), (2, 1)]⟩
def key533 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, -1), (0, 0), (1, 0), (1, 2)]⟩
def key539 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 0), (1, -1), (1, 2)]⟩
def key541 : Key := ⟨0, 0, [(-2, 0), (0, -1), (0, 0), (0, 1), (0, 2), (2, -2)]⟩
def key548 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 0), (0, 0), (0, 3), (2, -3)]⟩
def key559 : Key := ⟨0, 0, [(-2, 0), (0, 0), (0, 1), (0, 1), (0, 1), (2, -3)]⟩
def key577 : Key := ⟨0, 0, [(-2, 1), (-1, -2), (0, 1), (1, -1), (1, 0), (1, 1)]⟩
def key588 : Key := ⟨0, 0, [(-2, 1), (-1, -1), (0, 1), (1, -2), (1, 0), (1, 1)]⟩
def key608 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (0, 0), (1, 2), (2, -3)]⟩
def key610 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 0), (1, -2), (1, -1), (1, 2)]⟩
def key611 : Key := ⟨0, 0, [(-2, 1), (-1, 0), (0, 1), (1, -2), (1, -1), (1, 1)]⟩
def key613 : Key := ⟨0, 0, [(-2, 1), (-1, 1), (0, -2), (1, -1), (1, 0), (1, 1)]⟩
def key614 : Key := ⟨0, 0, [(-2, 1), (-1, 1), (0, -1), (1, -2), (1, 0), (1, 1)]⟩
def key616 : Key := ⟨0, 0, [(-2, 1), (-1, 1), (0, 0), (1, -2), (1, -1), (1, 1)]⟩
def key626 : Key := ⟨0, 0, [(-2, 1), (0, -2), (0, -1), (0, 0), (0, 0), (2, 2)]⟩
def key634 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key636 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, -1), (0, 0), (1, 0), (1, 1)]⟩
def key639 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 0), (0, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key640 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key641 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 0), (1, -2), (1, 2)]⟩
def key642 : Key := ⟨0, 0, [(-2, 1), (0, -1), (0, 0), (0, 0), (1, -1), (1, 1)]⟩
def key648 : Key := ⟨0, 0, [(-2, 1), (0, 0), (0, 0), (0, 1), (0, 1), (2, -3)]⟩
def key667 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, -1), (0, 0), (0, 1), (2, 0)]⟩
def key671 : Key := ⟨0, 0, [(-2, 2), (0, -2), (0, 0), (0, 0), (0, 1), (2, -1)]⟩
def key677 : Key := ⟨0, 0, [(-2, 2), (0, -1), (0, 0), (0, 0), (0, 1), (2, -2)]⟩
def key690 : Key := ⟨0, 0, [(-2, 3), (0, -1), (0, 0), (0, 0), (0, 0), (2, -2)]⟩
def key701 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (-1, 2), (0, 0), (1, 1), (2, 0)]⟩
def key702 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 0), (0, 1), (2, 2)]⟩
def key703 : Key := ⟨0, 0, [(-1, -3), (-1, 0), (0, 0), (0, 0), (0, 2), (2, 1)]⟩
def key726 : Key := ⟨0, 0, [(-1, -2), (-1, -1), (0, 0), (0, 1), (1, 0), (1, 2)]⟩
def key737 : Key := ⟨0, 0, [(-1, -2), (-1, 1), (0, -1), (0, 0), (0, 0), (2, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key899 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, -2), (0, -1), (1, 0), (1, 2)]⟩
def key915 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 2)]⟩
def key919 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (0, 0), (0, 2), (1, -2), (1, -1)]⟩
def key925 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, -1), (0, 1), (2, 0)]⟩
def key926 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 1)]⟩
def key941 : Key := ⟨0, 0, [(-1, 0), (-1, 2), (0, 0), (0, 1), (1, -2), (1, -1)]⟩
def key961 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, -1), (1, 0), (1, 0)]⟩
def key963 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -2), (0, 0), (1, -1), (1, 0)]⟩
def key965 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, -1), (0, 0), (1, -2), (1, 0)]⟩
def key967 : Key := ⟨0, 0, [(-1, 1), (-1, 2), (0, 0), (0, 0), (1, -2), (1, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1061 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, -1), (2, 1)]⟩
def key1062 : Key := ⟨0, 1, [(-3, -1), (0, -1), (0, 0), (0, 2), (1, 1), (2, -1)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key1275 : Key := ⟨0, 1, [(-2, -3), (0, 0), (0, 0), (0, 0), (0, 3), (2, 0)]⟩

end MUB6.Certificate.GramRows

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

def entry2_2 : Integer.Sparse Key := [(key2608, 240), (key2614, 480), (key2624, 480), (key2630, 480), (key2638, 640), (key2657, 320), (key2659, 240), (key2663, 240), (key2669, 480), (key2698, 640), (key2704, 576), (key2724, 720), (key2752, 480), (key2757, 320), (key2778, 320), (key2784, 384), (key2792, 480), (key2801, 480), (key2807, 480), (key2827, 640), (key2851, 480), (key2858, 576), (key2868, 576), (key2918, 384), (key2919, 480), (key2922, 480), (key3007, 240), (key3009, 160), (key3011, 320), (key3016, 240), (key3021, 384), (key3022, 480), (key3025, 480)]

def entry5_2 : Integer.Sparse Key := [(key2378, 480), (key2383, 192), (key2390, 320), (key2394, 480), (key2406, 480), (key2411, 192), (key2437, 320), (key2443, 480), (key2472, 384), (key2480, 480), (key2484, 384), (key2503, 480), (key2509, 384), (key2524, 480), (key2569, 96), (key2571, 240), (key2576, 240), (key2580, 160), (key2587, 480), (key2593, 288), (key2598, 160), (key2600, 480), (key2766, 480), (key2772, 288), (key2843, 576), (key2880, 384), (key2887, 480), (key2889, 576), (key2910, 720), (key2929, 160), (key2931, 480), (key2966, 480), (key2968, 576), (key2989, 720), (key2995, 480), (key3002, 320)]

def entry10_1 : Integer.Sparse Key := [(key222, 2880), (key494, 8640), (key548, 2880)]

def entry10_3 : Integer.Sparse Key := [(key1275, 2880), (key1698, 8640), (key1750, 2880)]

def entry11_5 : Integer.Sparse Key := [(key1256, 960), (key1261, 480), (key1265, 480), (key1268, 960), (key1531, 960), (key1536, 480), (key1609, 960), (key1642, 480), (key1648, 960), (key1651, 960), (key1674, 960), (key1765, 480), (key1768, 960), (key1806, 960), (key1809, 960), (key1832, 960), (key1837, 960), (key1848, 480)]

def entry11_10 : Integer.Sparse Key := [(key280, 720), (key283, 1440), (key292, 720), (key349, 720), (key352, 1440), (key369, 720), (key506, 1440), (key509, 1440), (key520, 1440), (key541, 1440), (key667, 1440), (key671, 720), (key677, 720)]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2067 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 0), (0, 3), (2, -1)]⟩
def key2068 : Key := ⟨0, 1, [(-1, -2), (-1, 0), (0, 0), (0, 0), (1, -1), (1, 3)]⟩
def key2114 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 0), (0, 2), (2, 1)]⟩
def key2115 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key2116 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 0), (1, 0), (1, 3)]⟩
def key2117 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 0), (1, 1), (1, 2)]⟩
def key2118 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key2119 : Key := ⟨0, 1, [(-1, -1), (-1, -1), (0, -1), (0, 1), (1, 0), (1, 2)]⟩
def key2136 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (3, 1)]⟩
def key2137 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, -2), (1, 1), (2, 1)]⟩
def key2142 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -2)]⟩
def key2156 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, -1), (0, 2), (2, 1)]⟩
def key2157 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, -1), (0, 3), (2, 0)]⟩
def key2158 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, -1), (1, 0), (1, 3)]⟩
def key2159 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, -1), (0, -1), (1, 1), (1, 2)]⟩
def key2164 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 0), (0, 3), (2, -2)]⟩
def key2165 : Key := ⟨0, 1, [(-1, -1), (-1, 0), (0, 0), (0, 0), (1, -2), (1, 3)]⟩
def key2171 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (-1, 1), (0, -2), (0, 0), (3, 1)]⟩
def key2172 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, 0)]⟩
def key2173 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key2184 : Key := ⟨0, 1, [(-1, -1), (-1, 1), (0, -1), (0, -1), (1, 0), (1, 2)]⟩
def key2221 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -2), (1, 2), (2, -1)]⟩
def key2222 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (-1, 1), (0, -1), (1, 2), (2, -2)]⟩
def key2231 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 0), (0, 1), (2, 2)]⟩
def key2232 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 0), (0, 2), (2, 1)]⟩
def key2233 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -3), (0, 0), (1, 1), (1, 2)]⟩
def key2244 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 0), (0, 3), (2, -1)]⟩
def key2245 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -2), (0, 0), (1, -1), (1, 3)]⟩
def key2251 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 0), (0, 3), (2, -2)]⟩
def key2252 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, -1), (0, 0), (1, -2), (1, 3)]⟩
def key2256 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩
def key2257 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩
def key2258 : Key := ⟨0, 1, [(-1, 0), (-1, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩
def key2263 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -2), (0, -1), (3, 1)]⟩
def key2264 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -2), (1, 1), (2, -1)]⟩
def key2265 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (-1, 1), (0, -1), (1, 1), (2, -2)]⟩
def key2293 : Key := ⟨0, 1, [(-1, 0), (-1, 1), (0, 0), (0, 0), (1, -3), (1, 2)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramKeys_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def key770 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 0), (0, 1), (2, 2)]⟩
def key771 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 0), (0, 3), (2, 0)]⟩
def key772 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 0), (1, 0), (1, 3)]⟩
def key774 : Key := ⟨0, 0, [(-1, -1), (-1, -1), (0, -1), (0, 1), (0, 2), (2, 0)]⟩
def key797 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, -1), (0, 1), (2, 2)]⟩
def key798 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, -1), (0, 3), (2, 0)]⟩
def key799 : Key := ⟨0, 0, [(-1, -1), (-1, 0), (0, -1), (0, -1), (1, 0), (1, 3)]⟩
def key834 : Key := ⟨0, 0, [(-1, -1), (-1, 2), (0, -1), (0, -1), (0, 1), (2, 0)]⟩
def key849 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, -3), (1, 1), (2, 1)]⟩
def key853 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (-1, 1), (0, 1), (1, 1), (2, -3)]⟩
def key856 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 0), (0, 1), (2, 2)]⟩
def key857 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -3), (0, 0), (0, 2), (2, 1)]⟩
def key864 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, -2), (0, -1), (1, 1), (1, 2)]⟩
def key881 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 0), (0, 2), (2, -2)]⟩
def key883 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (2, -3)]⟩
def key884 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, 2)]⟩
def key885 : Key := ⟨0, 0, [(-1, 0), (-1, 0), (0, 0), (0, 2), (1, -3), (1, 1)]⟩
def key888 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (-1, 1), (0, -3), (1, 1), (2, 0)]⟩
def key889 : Key := ⟨0, 0, [(-1, 0), (-1, 1), (-1, 1), (0, 0), (1, 1), (2, -3)]⟩

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow104 : Integer.Sparse Key := [(key2787, -2), (key2797, 1), (key2797, 1), (key2810, 2), (key2899, -1), (key2899, -1), (key2833, -1), (key2833, -1), (key2906, 1), (key2906, 1), (key2633, 2), (key2643, -1), (key2643, -1), (key2707, -2), (key2978, 1), (key2978, 1), (key2730, 1), (key2730, 1), (key2985, -1), (key2985, -1), (key2617, -2), (key2655, 1), (key2655, 1), (key2672, 2), (key2749, -1), (key2749, -1), (key2945, -1), (key2945, -1), (key2962, 1), (key2962, 1), (key2620, 1), (key2620, 1), (key2643, -1), (key2643, -1), (key2675, -1), (key2675, -1), (key2730, 1), (key2730, 1), (key2797, 1), (key2797, 1), (key2833, -1), (key2833, -1)]

def rawRow107 : Integer.Sparse Key := [(key2810, -2), (key2833, 1), (key2833, 1), (key2787, 2), (key2906, -1), (key2906, -1), (key2797, -1), (key2797, -1), (key2899, 1), (key2899, 1), (key2707, 2), (key2730, -1), (key2730, -1), (key2633, -2), (key2985, 1), (key2985, 1), (key2643, 1), (key2643, 1), (key2978, -1), (key2978, -1), (key2672, -2), (key2749, 1), (key2749, 1), (key2617, 2), (key2962, -1), (key2962, -1), (key2655, -1), (key2655, -1), (key2749, 1), (key2749, 1), (key2675, 1), (key2675, 1), (key2797, -1), (key2797, -1), (key2620, -1), (key2620, -1), (key2833, 1), (key2833, 1), (key2643, 1), (key2643, 1), (key2730, -1), (key2730, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10694 : Integer.Sparse Key := [(key2378, 2), (key2390, 2), (key2392, 2), (key2406, 2), (key2480, 2), (key2543, 2), (key2437, 2), (key2440, 2), (key2503, 2), (key2554, 2), (key2522, 2), (key2563, 2), (key2378, -2), (key2381, -2), (key2392, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, -2), (key2506, -2), (key2554, -2)]

def rawRow10695 : Integer.Sparse Key := [(key2378, 2), (key2392, 2), (key2390, 2), (key2406, 2), (key2543, 2), (key2480, 2), (key2440, 2), (key2437, 2), (key2554, 2), (key2503, 2), (key2563, 2), (key2522, 2), (key2381, -2), (key2378, -2), (key2392, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2554, -2), (key2506, -2)]

def rawRow10696 : Integer.Sparse Key := [(key2390, 2), (key2378, 2), (key2392, 2), (key2480, 2), (key2406, 2), (key2543, 2), (key2503, 2), (key2522, 2), (key2437, 2), (key2563, 2), (key2440, 2), (key2554, 2), (key2378, -2), (key2392, -2), (key2381, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, -2), (key2440, -2), (key2554, -2)]

def rawRow10697 : Integer.Sparse Key := [(key2390, 2), (key2392, 2), (key2378, 2), (key2480, 2), (key2543, 2), (key2406, 2), (key2522, 2), (key2503, 2), (key2563, 2), (key2437, 2), (key2554, 2), (key2440, 2), (key2392, -2), (key2378, -2), (key2381, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, -2), (key2554, -2), (key2440, -2)]

def rawRow10698 : Integer.Sparse Key := [(key2392, 2), (key2378, 2), (key2390, 2), (key2543, 2), (key2406, 2), (key2480, 2), (key2554, 2), (key2563, 2), (key2440, 2), (key2522, 2), (key2437, 2), (key2503, 2), (key2381, -2), (key2392, -2), (key2378, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2440, -2), (key2506, -2)]

def rawRow10699 : Integer.Sparse Key := [(key2392, 2), (key2390, 2), (key2378, 2), (key2543, 2), (key2480, 2), (key2406, 2), (key2563, 2), (key2554, 2), (key2522, 2), (key2440, 2), (key2503, 2), (key2437, 2), (key2392, -2), (key2381, -2), (key2378, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, -2), (key2506, -2), (key2440, -2)]

def rawRow10700 : Integer.Sparse Key := [(key2406, 2), (key2437, 2), (key2440, 2), (key2378, 2), (key2503, 2), (key2554, 2), (key2390, 2), (key2392, 2), (key2480, 2), (key2543, 2), (key2522, 2), (key2563, 2), (key2406, -2), (key2409, -2), (key2440, -2), (key2378, -2), (key2381, -2), (key2472, -2), (key2538, -2), (key2506, -2), (key2554, -2), (key2392, -2), (key2482, -2), (key2543, -2)]

def rawRow10701 : Integer.Sparse Key := [(key2406, 2), (key2440, 2), (key2437, 2), (key2378, 2), (key2554, 2), (key2503, 2), (key2392, 2), (key2390, 2), (key2543, 2), (key2480, 2), (key2563, 2), (key2522, 2), (key2409, -2), (key2406, -2), (key2440, -2), (key2381, -2), (key2378, -2), (key2538, -2), (key2472, -2), (key2554, -2), (key2506, -2), (key2392, -2), (key2543, -2), (key2482, -2)]

def rawRow10702 : Integer.Sparse Key := [(key2437, 2), (key2406, 2), (key2440, 2), (key2503, 2), (key2378, 2), (key2554, 2), (key2480, 2), (key2522, 2), (key2390, 2), (key2563, 2), (key2392, 2), (key2543, 2), (key2406, -2), (key2440, -2), (key2409, -2), (key2472, -2), (key2506, -2), (key2378, -2), (key2554, -2), (key2381, -2), (key2538, -2), (key2482, -2), (key2392, -2), (key2543, -2)]

def rawRow10703 : Integer.Sparse Key := [(key2437, 2), (key2440, 2), (key2406, 2), (key2503, 2), (key2554, 2), (key2378, 2), (key2522, 2), (key2480, 2), (key2563, 2), (key2390, 2), (key2543, 2), (key2392, 2), (key2440, -2), (key2406, -2), (key2409, -2), (key2506, -2), (key2472, -2), (key2554, -2), (key2378, -2), (key2538, -2), (key2381, -2), (key2482, -2), (key2543, -2), (key2392, -2)]

def rawRow10704 : Integer.Sparse Key := [(key2440, 2), (key2406, 2), (key2437, 2), (key2554, 2), (key2378, 2), (key2503, 2), (key2543, 2), (key2563, 2), (key2392, 2), (key2522, 2), (key2390, 2), (key2480, 2), (key2409, -2), (key2440, -2), (key2406, -2), (key2538, -2), (key2554, -2), (key2381, -2), (key2506, -2), (key2378, -2), (key2472, -2), (key2543, -2), (key2392, -2), (key2482, -2)]

def rawRow10705 : Integer.Sparse Key := [(key2440, 2), (key2437, 2), (key2406, 2), (key2554, 2), (key2503, 2), (key2378, 2), (key2563, 2), (key2543, 2), (key2522, 2), (key2392, 2), (key2480, 2), (key2390, 2), (key2440, -2), (key2409, -2), (key2406, -2), (key2554, -2), (key2538, -2), (key2506, -2), (key2381, -2), (key2472, -2), (key2378, -2), (key2543, -2), (key2482, -2), (key2392, -2)]

def rawRow10706 : Integer.Sparse Key := [(key2480, 2), (key2503, 2), (key2522, 2), (key2390, 2), (key2437, 2), (key2563, 2), (key2378, 2), (key2392, 2), (key2406, 2), (key2543, 2), (key2440, 2), (key2554, 2), (key2472, -2), (key2482, -2), (key2506, -2), (key2378, -2), (key2392, -2), (key2406, -2), (key2543, -2), (key2440, -2), (key2554, -2), (key2381, -2), (key2409, -2), (key2538, -2)]

def rawRow10707 : Integer.Sparse Key := [(key2480, 2), (key2522, 2), (key2503, 2), (key2390, 2), (key2563, 2), (key2437, 2), (key2392, 2), (key2378, 2), (key2543, 2), (key2406, 2), (key2554, 2), (key2440, 2), (key2482, -2), (key2472, -2), (key2506, -2), (key2392, -2), (key2378, -2), (key2543, -2), (key2406, -2), (key2554, -2), (key2440, -2), (key2381, -2), (key2538, -2), (key2409, -2)]

def rawRow10708 : Integer.Sparse Key := [(key2503, 2), (key2480, 2), (key2522, 2), (key2437, 2), (key2390, 2), (key2563, 2), (key2406, 2), (key2440, 2), (key2378, 2), (key2554, 2), (key2392, 2), (key2543, 2), (key2472, -2), (key2506, -2), (key2482, -2), (key2406, -2), (key2440, -2), (key2378, -2), (key2554, -2), (key2392, -2), (key2543, -2), (key2409, -2), (key2381, -2), (key2538, -2)]

def rawRow10709 : Integer.Sparse Key := [(key2503, 2), (key2522, 2), (key2480, 2), (key2437, 2), (key2563, 2), (key2390, 2), (key2440, 2), (key2406, 2), (key2554, 2), (key2378, 2), (key2543, 2), (key2392, 2), (key2506, -2), (key2472, -2), (key2482, -2), (key2440, -2), (key2406, -2), (key2554, -2), (key2378, -2), (key2543, -2), (key2392, -2), (key2409, -2), (key2538, -2), (key2381, -2)]

def rawRow10710 : Integer.Sparse Key := [(key2522, 2), (key2480, 2), (key2503, 2), (key2563, 2), (key2390, 2), (key2437, 2), (key2543, 2), (key2554, 2), (key2392, 2), (key2440, 2), (key2378, 2), (key2406, 2), (key2482, -2), (key2506, -2), (key2472, -2), (key2543, -2), (key2554, -2), (key2392, -2), (key2440, -2), (key2378, -2), (key2406, -2), (key2538, -2), (key2381, -2), (key2409, -2)]

def rawRow10711 : Integer.Sparse Key := [(key2522, 2), (key2503, 2), (key2480, 2), (key2563, 2), (key2437, 2), (key2390, 2), (key2554, 2), (key2543, 2), (key2440, 2), (key2392, 2), (key2406, 2), (key2378, 2), (key2506, -2), (key2482, -2), (key2472, -2), (key2554, -2), (key2543, -2), (key2440, -2), (key2392, -2), (key2406, -2), (key2378, -2), (key2538, -2), (key2409, -2), (key2381, -2)]

def rawRow10712 : Integer.Sparse Key := [(key2543, 2), (key2554, 2), (key2563, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2378, 2), (key2390, 2), (key2406, 2), (key2480, 2), (key2437, 2), (key2503, 2), (key2538, -2), (key2543, -2), (key2554, -2), (key2381, -2), (key2392, -2), (key2409, -2), (key2482, -2), (key2440, -2), (key2506, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

def rawRow10713 : Integer.Sparse Key := [(key2543, 2), (key2563, 2), (key2554, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2390, 2), (key2378, 2), (key2480, 2), (key2406, 2), (key2503, 2), (key2437, 2), (key2543, -2), (key2538, -2), (key2554, -2), (key2392, -2), (key2381, -2), (key2482, -2), (key2409, -2), (key2506, -2), (key2440, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

def rawRow10714 : Integer.Sparse Key := [(key2554, 2), (key2543, 2), (key2563, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2406, 2), (key2437, 2), (key2378, 2), (key2503, 2), (key2390, 2), (key2480, 2), (key2538, -2), (key2554, -2), (key2543, -2), (key2409, -2), (key2440, -2), (key2381, -2), (key2506, -2), (key2392, -2), (key2482, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

def rawRow10715 : Integer.Sparse Key := [(key2554, 2), (key2563, 2), (key2543, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2437, 2), (key2406, 2), (key2503, 2), (key2378, 2), (key2480, 2), (key2390, 2), (key2554, -2), (key2538, -2), (key2543, -2), (key2440, -2), (key2409, -2), (key2506, -2), (key2381, -2), (key2482, -2), (key2392, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

def rawRow10716 : Integer.Sparse Key := [(key2563, 2), (key2543, 2), (key2554, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2480, 2), (key2503, 2), (key2390, 2), (key2437, 2), (key2378, 2), (key2406, 2), (key2543, -2), (key2554, -2), (key2538, -2), (key2482, -2), (key2506, -2), (key2392, -2), (key2440, -2), (key2381, -2), (key2409, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

def rawRow10717 : Integer.Sparse Key := [(key2563, 2), (key2554, 2), (key2543, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2503, 2), (key2480, 2), (key2437, 2), (key2390, 2), (key2406, 2), (key2378, 2), (key2554, -2), (key2543, -2), (key2538, -2), (key2506, -2), (key2482, -2), (key2440, -2), (key2392, -2), (key2409, -2), (key2381, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

def rawRow10718 : Integer.Sparse Key := [(key2381, 2), (key2392, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2482, 2), (key2440, 2), (key2440, 2), (key2506, 2), (key2506, 2), (key2522, 2), (key2522, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2503, -2)]

def rawRow10719 : Integer.Sparse Key := [(key2392, 2), (key2381, 2), (key2392, 2), (key2482, 2), (key2409, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2437, -2), (key2503, -2)]

def rawRow10720 : Integer.Sparse Key := [(key2392, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2482, 2), (key2409, 2), (key2522, 2), (key2506, 2), (key2522, 2), (key2440, 2), (key2506, 2), (key2440, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, -2), (key2503, -2), (key2437, -2)]

def rawRow10721 : Integer.Sparse Key := [(key2409, 2), (key2440, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2506, 2), (key2392, 2), (key2392, 2), (key2482, 2), (key2482, 2), (key2522, 2), (key2522, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2378, -2), (key2472, -2), (key2472, -2), (key2503, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2480, -2)]

def rawRow10722 : Integer.Sparse Key := [(key2440, 2), (key2409, 2), (key2440, 2), (key2506, 2), (key2381, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2480, -2), (key2390, -2), (key2480, -2)]

def rawRow10723 : Integer.Sparse Key := [(key2440, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2506, 2), (key2381, 2), (key2522, 2), (key2482, 2), (key2522, 2), (key2392, 2), (key2482, 2), (key2392, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -2), (key2472, -2), (key2503, -2), (key2378, -2), (key2472, -2), (key2378, -2), (key2480, -2), (key2480, -2), (key2390, -2)]

def rawRow10724 : Integer.Sparse Key := [(key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2522, 2), (key2381, 2), (key2392, 2), (key2409, 2), (key2482, 2), (key2440, 2), (key2506, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2378, -2), (key2390, -2), (key2406, -2), (key2480, -2), (key2437, -2), (key2503, -2), (key2378, -2), (key2406, -2), (key2472, -2)]

def rawRow10725 : Integer.Sparse Key := [(key2482, 2), (key2522, 2), (key2506, 2), (key2392, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2381, 2), (key2482, 2), (key2409, 2), (key2506, 2), (key2440, 2), (key2480, -2), (key2472, -2), (key2503, -2), (key2390, -2), (key2378, -2), (key2480, -2), (key2406, -2), (key2503, -2), (key2437, -2), (key2378, -2), (key2472, -2), (key2406, -2)]

def rawRow10726 : Integer.Sparse Key := [(key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2522, 2), (key2409, 2), (key2440, 2), (key2381, 2), (key2506, 2), (key2392, 2), (key2482, 2), (key2472, -2), (key2503, -2), (key2480, -2), (key2406, -2), (key2437, -2), (key2378, -2), (key2503, -2), (key2390, -2), (key2480, -2), (key2406, -2), (key2378, -2), (key2472, -2)]

def rawRow10727 : Integer.Sparse Key := [(key2506, 2), (key2522, 2), (key2482, 2), (key2440, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2409, 2), (key2506, 2), (key2381, 2), (key2482, 2), (key2392, 2), (key2503, -2), (key2472, -2), (key2480, -2), (key2437, -2), (key2406, -2), (key2503, -2), (key2378, -2), (key2480, -2), (key2390, -2), (key2406, -2), (key2472, -2), (key2378, -2)]

def rawRow10728 : Integer.Sparse Key := [(key2522, 2), (key2482, 2), (key2506, 2), (key2522, 2), (key2392, 2), (key2440, 2), (key2482, 2), (key2506, 2), (key2392, 2), (key2440, 2), (key2381, 2), (key2409, 2), (key2480, -2), (key2503, -2), (key2472, -2), (key2480, -2), (key2503, -2), (key2390, -2), (key2437, -2), (key2378, -2), (key2406, -2), (key2472, -2), (key2378, -2), (key2406, -2)]

def rawRow10729 : Integer.Sparse Key := [(key2522, 2), (key2506, 2), (key2482, 2), (key2522, 2), (key2440, 2), (key2392, 2), (key2506, 2), (key2482, 2), (key2440, 2), (key2392, 2), (key2409, 2), (key2381, 2), (key2503, -2), (key2480, -2), (key2472, -2), (key2503, -2), (key2480, -2), (key2437, -2), (key2390, -2), (key2406, -2), (key2378, -2), (key2472, -2), (key2406, -2), (key2378, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10874 : Integer.Sparse Key := [(key2625, -2), (key2629, -2), (key2637, -2), (key2699, -2), (key2703, -2), (key2852, -2), (key2973, -2), (key2857, -2), (key2975, -2), (key2723, -2), (key2867, -2), (key2982, -2), (key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1)]

def rawRow10875 : Integer.Sparse Key := [(key2629, -2), (key2625, -2), (key2637, -2), (key2703, -2), (key2699, -2), (key2973, -2), (key2852, -2), (key2975, -2), (key2857, -2), (key2723, -2), (key2982, -2), (key2867, -2), (key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1)]

def rawRow10876 : Integer.Sparse Key := [(key2625, -2), (key2637, -2), (key2629, -2), (key2852, -2), (key2857, -2), (key2699, -2), (key2975, -2), (key2703, -2), (key2973, -2), (key2867, -2), (key2723, -2), (key2982, -2), (key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1)]

def rawRow10877 : Integer.Sparse Key := [(key2637, -2), (key2625, -2), (key2629, -2), (key2857, -2), (key2852, -2), (key2975, -2), (key2699, -2), (key2973, -2), (key2703, -2), (key2867, -2), (key2982, -2), (key2723, -2), (key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1)]

def rawRow10878 : Integer.Sparse Key := [(key2629, -2), (key2637, -2), (key2625, -2), (key2973, -2), (key2975, -2), (key2703, -2), (key2857, -2), (key2699, -2), (key2852, -2), (key2982, -2), (key2723, -2), (key2867, -2), (key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1)]

def rawRow10879 : Integer.Sparse Key := [(key2637, -2), (key2629, -2), (key2625, -2), (key2975, -2), (key2973, -2), (key2857, -2), (key2703, -2), (key2852, -2), (key2699, -2), (key2982, -2), (key2867, -2), (key2723, -2), (key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block109
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow10880 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2625, -2), (key2629, -2), (key2852, -2), (key2973, -2), (key2867, -2), (key2982, -2), (key2637, -2), (key2857, -2), (key2975, -2), (key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1)]

def rawRow10881 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2629, -2), (key2625, -2), (key2973, -2), (key2852, -2), (key2982, -2), (key2867, -2), (key2637, -2), (key2975, -2), (key2857, -2), (key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1)]

def rawRow10882 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2852, -2), (key2867, -2), (key2625, -2), (key2982, -2), (key2629, -2), (key2973, -2), (key2857, -2), (key2637, -2), (key2975, -2), (key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1)]

def rawRow10883 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2867, -2), (key2852, -2), (key2982, -2), (key2625, -2), (key2973, -2), (key2629, -2), (key2857, -2), (key2975, -2), (key2637, -2), (key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1)]

def rawRow10884 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2973, -2), (key2982, -2), (key2629, -2), (key2867, -2), (key2625, -2), (key2852, -2), (key2975, -2), (key2637, -2), (key2857, -2), (key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1)]

def rawRow10885 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2982, -2), (key2973, -2), (key2867, -2), (key2629, -2), (key2852, -2), (key2625, -2), (key2975, -2), (key2857, -2), (key2637, -2), (key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1)]

def rawRow10886 : Integer.Sparse Key := [(key2852, -2), (key2857, -2), (key2867, -2), (key2625, -2), (key2637, -2), (key2699, -2), (key2975, -2), (key2723, -2), (key2982, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1)]

def rawRow10887 : Integer.Sparse Key := [(key2857, -2), (key2852, -2), (key2867, -2), (key2637, -2), (key2625, -2), (key2975, -2), (key2699, -2), (key2982, -2), (key2723, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1)]

def rawRow10888 : Integer.Sparse Key := [(key2852, -2), (key2867, -2), (key2857, -2), (key2699, -2), (key2723, -2), (key2625, -2), (key2982, -2), (key2637, -2), (key2975, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1)]

def rawRow10889 : Integer.Sparse Key := [(key2867, -2), (key2852, -2), (key2857, -2), (key2723, -2), (key2699, -2), (key2982, -2), (key2625, -2), (key2975, -2), (key2637, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1)]

def rawRow10890 : Integer.Sparse Key := [(key2857, -2), (key2867, -2), (key2852, -2), (key2975, -2), (key2982, -2), (key2637, -2), (key2723, -2), (key2625, -2), (key2699, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1)]

def rawRow10891 : Integer.Sparse Key := [(key2867, -2), (key2857, -2), (key2852, -2), (key2982, -2), (key2975, -2), (key2723, -2), (key2637, -2), (key2699, -2), (key2625, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1)]

def rawRow10892 : Integer.Sparse Key := [(key2973, -2), (key2975, -2), (key2982, -2), (key2629, -2), (key2637, -2), (key2703, -2), (key2857, -2), (key2723, -2), (key2867, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1)]

def rawRow10893 : Integer.Sparse Key := [(key2975, -2), (key2973, -2), (key2982, -2), (key2637, -2), (key2629, -2), (key2857, -2), (key2703, -2), (key2867, -2), (key2723, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1)]

def rawRow10894 : Integer.Sparse Key := [(key2973, -2), (key2982, -2), (key2975, -2), (key2703, -2), (key2723, -2), (key2629, -2), (key2867, -2), (key2637, -2), (key2857, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1)]

def rawRow10895 : Integer.Sparse Key := [(key2982, -2), (key2973, -2), (key2975, -2), (key2723, -2), (key2703, -2), (key2867, -2), (key2629, -2), (key2857, -2), (key2637, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1)]

def rawRow10896 : Integer.Sparse Key := [(key2975, -2), (key2982, -2), (key2973, -2), (key2857, -2), (key2867, -2), (key2637, -2), (key2723, -2), (key2629, -2), (key2703, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1)]

def rawRow10897 : Integer.Sparse Key := [(key2982, -2), (key2975, -2), (key2973, -2), (key2867, -2), (key2857, -2), (key2723, -2), (key2637, -2), (key2703, -2), (key2629, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1)]

def rawRow10898 : Integer.Sparse Key := [(key2647, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2736, -2), (key2894, -2), (key2894, -2), (key2896, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2903, -2), (key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1)]

def rawRow10899 : Integer.Sparse Key := [(key2647, -2), (key2652, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2746, -2), (key2903, -2), (key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1)]

def rawRow10900 : Integer.Sparse Key := [(key2652, -2), (key2647, -2), (key2647, -2), (key2896, -2), (key2894, -2), (key2896, -2), (key2736, -2), (key2894, -2), (key2736, -2), (key2903, -2), (key2903, -2), (key2746, -2), (key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1)]

def rawRow10901 : Integer.Sparse Key := [(key2736, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2647, -2), (key2894, -2), (key2894, -2), (key2903, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2896, -2), (key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1)]

def rawRow10902 : Integer.Sparse Key := [(key2736, -2), (key2746, -2), (key2736, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2896, -2), (key2652, -2), (key2896, -2), (key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1)]

def rawRow10903 : Integer.Sparse Key := [(key2746, -2), (key2736, -2), (key2736, -2), (key2903, -2), (key2894, -2), (key2903, -2), (key2647, -2), (key2894, -2), (key2647, -2), (key2896, -2), (key2896, -2), (key2652, -2), (key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1)]

def rawRow10904 : Integer.Sparse Key := [(key2894, -2), (key2896, -2), (key2903, -2), (key2647, -2), (key2652, -2), (key2736, -2), (key2896, -2), (key2746, -2), (key2903, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1)]

def rawRow10905 : Integer.Sparse Key := [(key2896, -2), (key2894, -2), (key2903, -2), (key2652, -2), (key2647, -2), (key2896, -2), (key2736, -2), (key2903, -2), (key2746, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1)]

def rawRow10906 : Integer.Sparse Key := [(key2894, -2), (key2903, -2), (key2896, -2), (key2736, -2), (key2746, -2), (key2647, -2), (key2903, -2), (key2652, -2), (key2896, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1)]

def rawRow10907 : Integer.Sparse Key := [(key2903, -2), (key2894, -2), (key2896, -2), (key2746, -2), (key2736, -2), (key2903, -2), (key2647, -2), (key2896, -2), (key2652, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1)]

def rawRow10908 : Integer.Sparse Key := [(key2896, -2), (key2903, -2), (key2894, -2), (key2896, -2), (key2903, -2), (key2652, -2), (key2746, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1)]

def rawRow10909 : Integer.Sparse Key := [(key2903, -2), (key2896, -2), (key2894, -2), (key2903, -2), (key2896, -2), (key2746, -2), (key2652, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1)]

def rawRow10946 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, -2), (key2802, -2), (key2806, -2), (key2852, -2), (key2894, -2), (key2857, -2), (key2896, -2), (key2826, -2), (key2867, -2), (key2903, -2), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, 2), (key2703, 2), (key2852, 2), (key2973, 2), (key2857, 2), (key2975, 2), (key2723, 2), (key2867, 2), (key2982, 2)]

def rawRow10947 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2791, -2), (key2806, -2), (key2802, -2), (key2894, -2), (key2852, -2), (key2896, -2), (key2857, -2), (key2826, -2), (key2903, -2), (key2867, -2), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, 2), (key2699, 2), (key2973, 2), (key2852, 2), (key2975, 2), (key2857, 2), (key2723, 2), (key2982, 2), (key2867, 2)]

def rawRow10948 : Integer.Sparse Key := [(key2779, -2), (key2791, -2), (key2783, -2), (key2852, -2), (key2857, -2), (key2802, -2), (key2896, -2), (key2806, -2), (key2894, -2), (key2867, -2), (key2826, -2), (key2903, -2), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, 2), (key2857, 2), (key2699, 2), (key2975, 2), (key2703, 2), (key2973, 2), (key2867, 2), (key2723, 2), (key2982, 2)]

def rawRow10949 : Integer.Sparse Key := [(key2791, -2), (key2779, -2), (key2783, -2), (key2857, -2), (key2852, -2), (key2896, -2), (key2802, -2), (key2894, -2), (key2806, -2), (key2867, -2), (key2903, -2), (key2826, -2), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, 2), (key2852, 2), (key2975, 2), (key2699, 2), (key2973, 2), (key2703, 2), (key2867, 2), (key2982, 2), (key2723, 2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11114 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2540, 6), (key2551, 6), (key2370, -6), (key2762, -6), (key2839, -6), (key2839, -6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13614 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13615 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13616 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13617 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13618 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13619 : Integer.Sparse Key := [(key2378, -2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, -2), (key2443, 4), (key2480, -2), (key2503, -2), (key2524, 4), (key2587, 4), (key2593, -2), (key2600, -2), (key2766, 4), (key2772, -2), (key2843, 4), (key2889, -2), (key2931, -2), (key2968, -2)]

def row13623 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13624 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13625 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13626 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13627 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

def row13628 : Integer.Sparse Key := [(key2378, 2), (key2383, -2), (key2390, -2), (key2394, 2), (key2406, 2), (key2411, -2), (key2437, -2), (key2443, 2), (key2472, 4), (key2480, -2), (key2484, -2), (key2503, -2), (key2509, -2), (key2524, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block132
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row13830 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13831 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13832 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13833 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13834 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13835 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 3), (key2657, -1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 4), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, 1), (key2868, -1), (key2919, -1), (key2922, -1)]

def row13839 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13840 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13841 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13842 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13843 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

def row13844 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, 1), (key2630, -2), (key2638, 1), (key2657, 1), (key2659, -1), (key2663, -1), (key2669, 1), (key2698, 1), (key2704, -2), (key2724, 1), (key2752, 1), (key2757, -1), (key2778, -1), (key2784, -1), (key2792, 2), (key2801, -1), (key2807, -1), (key2827, 2), (key2851, 2), (key2858, -1), (key2868, -1), (key2918, 2), (key2919, -1), (key2922, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block150
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16167 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16168 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16169 : Integer.Sparse Key := [(key2402, -4), (key2408, 6), (key2439, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2847, -4), (key2878, 4), (key2884, -4), (key2917, 6), (key2926, -4), (key3020, -2), (key3029, 4)]

def row16171 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16172 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16173 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16174 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16175 : Integer.Sparse Key := [(key2402, 4), (key2408, -2), (key2439, -2), (key2596, 2), (key2605, -2), (key2878, -4), (key2917, -2), (key2926, 4), (key3020, 2)]

def row16176 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16177 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16178 : Integer.Sparse Key := [(key2402, -4), (key2439, -2), (key2468, -4), (key2481, 6), (key2505, -2), (key2591, 4), (key2596, -2), (key2605, -2), (key2775, 6), (key2878, 4), (key2884, -4), (key2926, -4), (key3029, 4)]

def row16179 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16180 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16181 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16182 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16183 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16184 : Integer.Sparse Key := [(key2374, 2), (key2391, 2), (key2402, 2), (key2439, 2), (key2468, 4), (key2481, -2), (key2505, -2), (key2535, -2), (key2591, -2), (key2596, -2), (key2770, -2), (key2775, -2), (key2878, -2), (key2884, 4)]

def row16185 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16186 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16187 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16188 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16189 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16190 : Integer.Sparse Key := [(key2374, 2), (key2380, 2), (key2391, -2), (key2402, -2), (key2408, -2), (key2439, -2), (key2468, 2), (key2481, -2), (key2505, 2), (key2535, -2), (key2542, 4), (key2591, -2), (key2770, 6), (key2847, -2), (key2878, -2)]

def row16191 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16192 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16193 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16194 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16195 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16196 : Integer.Sparse Key := [(key2374, 2), (key2380, -2), (key2391, 2), (key2402, 2), (key2408, -2), (key2439, 2), (key2468, -2), (key2481, -2), (key2505, -2), (key2535, -2), (key2537, 4), (key2591, -2), (key2770, -2), (key2847, 6), (key2878, -2)]

def row16197 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16198 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16199 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16200 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16201 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

def row16202 : Integer.Sparse Key := [(key2374, -2), (key2380, 2), (key2391, 2), (key2402, -2), (key2408, 2), (key2439, 2), (key2468, -2), (key2481, 2), (key2505, 2), (key2535, 6), (key2537, -4), (key2542, -4), (key2553, -4), (key2591, -2), (key2770, -2), (key2847, -2), (key2878, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16311 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key3017, -2), (key3026, -2), (key3030, 4)]

def row16312 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

def row16313 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2632, -2), (key2640, 4), (key2644, -2), (key2658, 2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2870, -2), (key2885, -2), (key2923, 4), (key2927, -2), (key2948, -1), (key2960, -2), (key3026, -2), (key3030, 4)]

def row16314 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16315 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16316 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16317 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16318 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16319 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2632, 1), (key2640, -2), (key2644, 1), (key2658, -1), (key2660, 1), (key2706, 1), (key2726, -1), (key2732, 2), (key2753, -1), (key2758, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -2), (key2870, -1), (key2885, -1), (key2920, 1), (key2923, -1), (key2927, 2), (key2950, -1), (key2960, -1), (key3023, 1), (key3026, 2), (key3030, -1)]

def row16320 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -2), (key2835, 4), (key2885, -2), (key2927, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3017, -2), (key3030, 4)]

def row16321 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

def row16322 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2621, 2), (key2628, -2), (key2640, 4), (key2641, 2), (key2644, -2), (key2660, -2), (key2726, 4), (key2732, -2), (key2758, -2), (key2829, -1), (key2835, 4), (key2885, -2), (key2927, -2), (key2948, -1), (key2960, -2), (key2972, -2), (key2976, 4), (key2983, -2), (key3030, 4)]

def row16323 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16324 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16325 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16326 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16327 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16328 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2621, -1), (key2628, 1), (key2640, -1), (key2641, -1), (key2644, 1), (key2646, -1), (key2653, 1), (key2667, 2), (key2671, -1), (key2676, -1), (key2702, 1), (key2726, -1), (key2728, -1), (key2732, -1), (key2735, -1), (key2747, 1), (key2794, -1), (key2798, 1), (key2829, -1), (key2835, -1), (key2885, 2), (key2943, 2), (key2960, 2), (key2972, 2), (key2976, -1), (key2983, -1), (key2998, -1), (key3000, -1)]

def row16329 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16330 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16331 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16332 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16333 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16334 : Integer.Sparse Key := [(key2612, -1), (key2616, 2), (key2618, -1), (key2628, 2), (key2632, -1), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2706, -1), (key2726, -1), (key2782, 2), (key2795, -1), (key2805, -1), (key2809, 2), (key2829, 2), (key2831, -1), (key2860, -1), (key2870, -1), (key2893, -1), (key2897, 1), (key2904, 1), (key2938, 2), (key2943, -1), (key2950, -1), (key2960, -1), (key2976, -1), (key2983, 2), (key2997, -1), (key2998, 2), (key3000, -1)]

def row16335 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16336 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16337 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16338 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16339 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16340 : Integer.Sparse Key := [(key2612, 2), (key2616, -1), (key2618, -1), (key2628, -1), (key2632, 2), (key2640, -1), (key2641, -1), (key2646, -1), (key2648, 1), (key2653, 1), (key2667, 2), (key2671, -1), (key2673, -1), (key2702, -1), (key2726, -1), (key2728, -1), (key2735, -1), (key2737, 1), (key2747, 1), (key2786, 2), (key2794, -1), (key2829, -1), (key2870, 2), (key2938, -1), (key2943, 2), (key2950, -1), (key2960, 2), (key2976, -1), (key2983, -1), (key2997, 2), (key2998, -1), (key3000, -1)]

def row16341 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16342 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16343 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16344 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16345 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16346 : Integer.Sparse Key := [(key2612, -1), (key2616, -1), (key2618, 2), (key2628, -1), (key2632, -1), (key2640, 2), (key2641, 2), (key2646, 2), (key2648, -2), (key2653, -2), (key2667, -1), (key2671, -1), (key2673, 2), (key2702, -1), (key2706, -1), (key2728, 2), (key2735, 2), (key2737, -2), (key2747, -2), (key2782, -1), (key2786, -1), (key2794, 2), (key2795, 2), (key2805, -1), (key2809, -1), (key2831, 2), (key2860, 2), (key2893, 2), (key2897, -2), (key2904, -2)]

def row16383 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block152
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16384 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16385 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16386 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16387 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16388 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16389 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16390 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16391 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16392 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16393 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16394 : Integer.Sparse Key := [(key2591, 4), (key2594, -2), (key2601, -2), (key2770, -4), (key2773, 6), (key2847, -4), (key2878, 4), (key2881, -4), (key2890, 6), (key2911, -4), (key2932, -2), (key2969, -2), (key2990, 4)]

def row16395 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16396 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16397 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16398 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16399 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16400 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16401 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16402 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16403 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16404 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16405 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16406 : Integer.Sparse Key := [(key2594, 2), (key2601, -2), (key2770, 4), (key2773, -2), (key2878, -4), (key2890, -2), (key2911, 4), (key2932, -2), (key2969, 2)]

def row16407 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16408 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16409 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16410 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16411 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16412 : Integer.Sparse Key := [(key2594, -2), (key2601, 2), (key2773, -2), (key2847, 4), (key2878, -4), (key2881, 4), (key2890, -2), (key2932, 2), (key2969, -2)]

def row16413 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16414 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16415 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16416 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16417 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

def row16418 : Integer.Sparse Key := [(key2591, -4), (key2594, 2), (key2601, 2), (key2770, -4), (key2773, 2), (key2847, -4), (key2878, 12), (key2881, -4), (key2890, 2), (key2911, -4), (key2932, 2), (key2969, 2), (key2990, -4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block153
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16608 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 2), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2972, 2), (key2976, -4), (key2983, 2), (key3017, 2)]

def row16609 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

def row16610 : Integer.Sparse Key := [(key2612, 1), (key2616, 1), (key2621, -2), (key2628, 2), (key2641, -2), (key2667, -2), (key2676, 2), (key2735, -2), (key2747, -2), (key2782, -2), (key2795, 2), (key2798, 4), (key2829, 1), (key2835, -4), (key2893, -2), (key2897, 4), (key2904, -2), (key2948, 1), (key2960, 2), (key2972, 2), (key2976, -4), (key2983, 2)]

def row16611 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16612 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16613 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16614 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16615 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16616 : Integer.Sparse Key := [(key2628, -1), (key2641, 1), (key2644, -2), (key2646, 1), (key2653, 1), (key2702, -1), (key2728, 1), (key2732, 2), (key2735, 1), (key2747, 1), (key2782, 1), (key2795, -1), (key2798, -2), (key2805, 1), (key2831, -1), (key2835, 2), (key2893, 2), (key2897, -1), (key2904, -1), (key2936, -1), (key2943, -1), (key2948, -1), (key2960, -1), (key2972, -2), (key2976, 1), (key2983, 1)]

def row16617 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16618 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16619 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16620 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16621 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16622 : Integer.Sparse Key := [(key2612, 1), (key2616, -2), (key2618, 1), (key2646, 1), (key2648, 1), (key2653, -2), (key2667, -1), (key2671, 2), (key2673, -1), (key2702, -1), (key2728, -1), (key2737, -1), (key2747, -1), (key2786, 2), (key2794, 2), (key2805, 1), (key2809, -2), (key2829, -2), (key2831, 1), (key2893, 1), (key2897, -2), (key2904, 1), (key2936, -1), (key2938, -1), (key2943, 2), (key2950, 1), (key2960, 1), (key2972, -1), (key2976, 2), (key2983, -1)]

def row16623 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16624 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16625 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16626 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16627 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16628 : Integer.Sparse Key := [(key2628, 1), (key2632, -2), (key2641, 1), (key2646, 1), (key2648, -2), (key2653, 1), (key2702, 1), (key2706, 2), (key2728, 1), (key2735, 1), (key2737, -2), (key2747, 1), (key2782, -1), (key2786, -2), (key2795, -1), (key2805, -1), (key2809, 2), (key2831, -1), (key2860, 2), (key2870, -2), (key2897, -1), (key2904, -1), (key2936, -1), (key2938, 2), (key2943, -1), (key2948, -1), (key2950, 2), (key2960, -1), (key2976, 1), (key2983, 1)]

def row16629 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16630 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16631 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16632 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16633 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16634 : Integer.Sparse Key := [(key2640, -2), (key2646, -2), (key2648, 2), (key2653, 2), (key2726, 2), (key2735, -2), (key2737, 2), (key2747, 2), (key2794, -2), (key2829, 2), (key2860, -2), (key2870, 2), (key2893, -2), (key2897, 2), (key2904, 2), (key2936, 2), (key2938, -2), (key2943, -2), (key2948, 2), (key2950, -2), (key2960, -2), (key2972, 2), (key2976, -2), (key2983, -2)]

def row16635 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16636 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16637 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16638 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16639 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row16640 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16641 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16642 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16643 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16644 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16645 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16646 : Integer.Sparse Key := [(key2616, 2), (key2619, -2), (key2632, 2), (key2649, -2), (key2671, -2), (key2674, 2), (key2706, -2), (key2738, 2), (key2794, -2), (key2796, 4), (key2829, 2), (key2832, -4), (key2860, -2), (key2870, 2), (key2898, 4), (key2905, -4), (key2944, -2), (key2961, 2), (key2977, -2), (key2984, 2)]

def row16647 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16648 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16649 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16650 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16651 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16652 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16653 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16654 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16655 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16656 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16657 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16658 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2640, 1), (key2642, 1), (key2654, -2), (key2671, 1), (key2674, -1), (key2726, -1), (key2729, -1), (key2748, 2), (key2786, 1), (key2794, 2), (key2796, -1), (key2809, -1), (key2829, -2), (key2832, 1), (key2860, 1), (key2870, -1), (key2898, -2), (key2905, 2), (key2939, -1), (key2944, -1), (key2951, 1), (key2961, 1), (key2977, 1), (key2984, -1)]

def row16659 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16660 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16661 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16662 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16663 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16664 : Integer.Sparse Key := [(key2632, -1), (key2640, 1), (key2642, -2), (key2649, 1), (key2654, 1), (key2706, 1), (key2726, -1), (key2729, 2), (key2738, -1), (key2748, -1), (key2786, -1), (key2794, 1), (key2796, -2), (key2809, 1), (key2829, -1), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, -1), (key2905, 1), (key2939, 1), (key2944, 1), (key2951, -1), (key2961, -1), (key2977, -1), (key2984, 1)]

def row16665 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16666 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16667 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16668 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16669 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

def row16670 : Integer.Sparse Key := [(key2640, -4), (key2642, 2), (key2654, 2), (key2726, 4), (key2729, -2), (key2748, -2), (key2794, -4), (key2796, 2), (key2829, 4), (key2832, -2), (key2860, -4), (key2870, 4), (key2898, 2), (key2905, -2), (key2944, 2), (key2961, -2), (key2977, 2), (key2984, -2)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block169
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18579 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18580 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18581 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18582 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18583 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18584 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18585 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18586 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18587 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18588 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18589 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18590 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18591 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18592 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18593 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18594 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18595 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18596 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18597 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18598 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18599 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18600 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18601 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18602 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 8), (key2724, 8), (key2752, 8), (key2757, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18603 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18604 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18605 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18606 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18607 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18608 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18609 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18610 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18611 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18612 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18613 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18614 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 8), (key2752, 4), (key2757, 4), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18615 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18616 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18617 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18618 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 4), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18619 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18620 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 8), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 8), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 8), (key2801, 4), (key2807, 4), (key2827, 8), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3009, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18621 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18622 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18623 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18624 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18625 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18626 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 6), (key2657, 2), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 6), (key2752, 2), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 6), (key2801, 4), (key2807, 4), (key2827, 6), (key2851, 4), (key2858, 6), (key2868, 6), (key2918, 2), (key2919, 4), (key2922, 4), (key3007, 2), (key3009, 2), (key3011, 2), (key3016, 2), (key3021, 2), (key3022, 4), (key3025, 4)]

def row18627 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18628 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18629 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18630 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18631 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18632 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 8), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18633 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18634 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18635 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18636 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 6), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 2), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18637 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

def row18638 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2624, 4), (key2630, 4), (key2638, 4), (key2657, 4), (key2659, 2), (key2663, 2), (key2669, 4), (key2698, 4), (key2704, 4), (key2724, 4), (key2752, 4), (key2757, 2), (key2778, 4), (key2784, 4), (key2792, 4), (key2801, 4), (key2807, 4), (key2827, 4), (key2851, 4), (key2858, 4), (key2868, 4), (key2918, 4), (key2919, 4), (key2922, 4), (key3007, 4), (key3009, 2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, 4), (key3025, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block171
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row18819 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18820 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18821 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18822 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18823 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18824 : Integer.Sparse Key := [(key2378, 8), (key2383, 4), (key2390, 4), (key2394, 8), (key2406, 8), (key2411, 4), (key2437, 4), (key2443, 8), (key2472, 8), (key2480, 8), (key2484, 8), (key2503, 8), (key2509, 8), (key2524, 8), (key2569, 4), (key2571, 8), (key2576, 8), (key2580, 4)]

def row18825 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18826 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18827 : Integer.Sparse Key := [(key2378, 4), (key2383, 2), (key2390, 4), (key2394, 8), (key2406, 4), (key2411, 2), (key2437, 4), (key2443, 8), (key2480, 4), (key2484, 4), (key2503, 4), (key2509, 4), (key2524, 8), (key2571, 4), (key2576, 4), (key2580, 4), (key2587, 4), (key2593, 2), (key2766, 4), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 4), (key2889, 4), (key2910, 4), (key2966, 4), (key2968, 4), (key2989, 4)]

def row18828 : Integer.Sparse Key := [(key2383, 2), (key2390, 4), (key2394, 8), (key2411, 2), (key2437, 4), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2580, 4), (key2587, 8), (key2593, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2966, 8), (key2968, 4), (key2989, 8)]

def row18829 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

def row18830 : Integer.Sparse Key := [(key2383, 2), (key2390, 2), (key2394, 8), (key2411, 2), (key2437, 2), (key2443, 8), (key2484, 4), (key2509, 4), (key2524, 8), (key2587, 8), (key2593, 2), (key2598, 2), (key2766, 8), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 8), (key2889, 4), (key2910, 8), (key2929, 2), (key2966, 8), (key2968, 4), (key2989, 8), (key3002, 4)]

def row18831 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18832 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18833 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18834 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18835 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18836 : Integer.Sparse Key := [(key2378, 2), (key2383, 2), (key2390, 2), (key2394, 4), (key2406, 2), (key2411, 2), (key2437, 2), (key2443, 4), (key2480, 2), (key2484, 4), (key2503, 2), (key2509, 4), (key2524, 4), (key2587, 6), (key2593, 2), (key2598, 2), (key2600, 4), (key2766, 6), (key2772, 2), (key2843, 8), (key2880, 4), (key2887, 6), (key2889, 4), (key2910, 8), (key2929, 2), (key2931, 4), (key2966, 6), (key2968, 4), (key2989, 8), (key2995, 4), (key3002, 4)]

def row18837 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18838 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18839 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18840 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18841 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18842 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18843 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18844 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18845 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18846 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18847 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

def row18848 : Integer.Sparse Key := [(key2378, 4), (key2390, 2), (key2406, 4), (key2437, 2), (key2472, 4), (key2480, 4), (key2503, 4), (key2587, 4), (key2593, 4), (key2598, 2), (key2600, 8), (key2766, 4), (key2772, 4), (key2843, 4), (key2880, 4), (key2887, 4), (key2889, 8), (key2910, 8), (key2929, 2), (key2931, 8), (key2966, 4), (key2968, 8), (key2989, 8), (key2995, 8), (key3002, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block175
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19404 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19405 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19406 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19407 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19408 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19409 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19410 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19411 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19412 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19413 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19414 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19415 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19416 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19417 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19418 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19419 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19420 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19421 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19422 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19423 : Integer.Sparse Key := [(key222, 24), (key494, 72), (key548, 24)]

def row19444 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19445 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19446 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19447 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19448 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19449 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19450 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19451 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19452 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19453 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19454 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19455 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block176
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19456 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19457 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19458 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19459 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19460 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19461 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19462 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

def row19463 : Integer.Sparse Key := [(key1275, 24), (key1698, 72), (key1750, 24)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row19904 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19905 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19906 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19907 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19908 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19909 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19910 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19911 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19912 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19913 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19914 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19915 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19916 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19917 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19918 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19919 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19920 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19921 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19922 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19923 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19924 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19925 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19926 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19927 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19928 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19929 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19930 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19931 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19932 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19933 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19934 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19935 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19936 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19937 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19938 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19939 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19940 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19941 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19942 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19943 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19944 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19945 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19946 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19947 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19948 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19949 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19950 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19951 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19952 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19953 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19954 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19955 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19956 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19957 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19958 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19959 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19960 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19961 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19962 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

def row19963 : Integer.Sparse Key := [(key1256, 8), (key1261, 4), (key1265, 4), (key1268, 8), (key1531, 8), (key1536, 4), (key1609, 8), (key1642, 4), (key1648, 8), (key1651, 8), (key1674, 8), (key1765, 4), (key1768, 8), (key1806, 8), (key1809, 8), (key1832, 8), (key1837, 8), (key1848, 4)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20204 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20205 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20206 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20207 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20208 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20209 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20210 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20211 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20212 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20213 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20214 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20215 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20216 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20217 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20218 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20219 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20220 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20221 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20222 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20223 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block182
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def row20224 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20225 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20226 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20227 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20228 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20229 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20230 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20231 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20232 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20233 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20234 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20235 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20236 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20237 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20238 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20239 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20240 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20241 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20242 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20243 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20244 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20245 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20246 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20247 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20248 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20249 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20250 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20251 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20252 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20253 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20254 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20255 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20256 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20257 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20258 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20259 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20260 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20261 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20262 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

def row20263 : Integer.Sparse Key := [(key280, 6), (key283, 12), (key292, 6), (key349, 6), (key352, 12), (key369, 6), (key506, 12), (key509, 12), (key520, 12), (key541, 12), (key667, 12), (key671, 6), (key677, 6)]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1171 : Sparse Master := [(Sum.inr 1171, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Values19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def nodeValue1229 : Sparse Master := [(Sum.inr 1229, (1 / 1))]

def nodeValue1230 : Sparse Master := [(Sum.inr 1230, (1 / 1))]

def nodeValue1231 : Sparse Master := [(Sum.inr 1231, (1 / 1))]

end MUB6.Certificate.MixedSemantics

end OAI
end


