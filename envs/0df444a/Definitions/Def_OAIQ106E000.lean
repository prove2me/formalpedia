-- Prove2me | Definitions.Def_OAIQ106E000
-- name    : OAIQ106E000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T17:53:54.629466+00:00
-- url     : https://prove2.me/theorems/0a3177bb-cfb4-4561-8b9b-822122546c41
-- title:
--   Definitions bundle OAIQ106E000 of the split of OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 654 declarations of OpenAI's Lean: 641 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.MUB6.AllTransitionsFourierZero`, `OAI.MUB6.AuxiliarySample`, `OAI.MUB6.Balanced`, `OAI.MUB6.Certificate.ExponentCode`, `OAI.MUB6.Certificate.ExponentCode.moment`, `OAI.MUB6.Certificate.GramAssembly.Block0.entries`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRow0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRow1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRow2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRow3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRow4`, `OAI.MUB6.Certificate.GramAssembly.Block0.entryRows`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_0_0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_0_1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_0_2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_0_3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_0_4`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_1_0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_1_1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_1_2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_1_3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_1_4`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_2_0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_2_1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_2_2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_2_3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_2_4`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_3_0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_3_1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_3_2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_3_3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_3_4`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_4_0`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_4_1`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_4_2`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_4_3`, `OAI.MUB6.Certificate.GramAssembly.Block0.entry_4_4`, `OAI.MUB6.Certificate.GramAssembly.Block0.node0`, `OAI.MUB6.Certificate.GramAssembly.Block0.node1`, `OAI.MUB6.Certificate.GramAssembly.Block0.node10` and 602 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `MutuallyUnbiased_Bases_CompleteFamily`, `MutuallyUnbiased_Bases_Transitions`, `MutuallyUnbiased_Certificate_ExponentCode`, `MutuallyUnbiased_Certificate_Integer`, `MutuallyUnbiased_Certificate_IntegerMerge`, `MutuallyUnbiased_Fourier_Dichotomy`, `MutuallyUnbiased_GramAssembly_Block0`, `MutuallyUnbiased_GramAssembly_Block0Data`, `MutuallyUnbiased_GramAssembly_Block0Part0`, `MutuallyUnbiased_GramAssembly_Block1Data`, `MutuallyUnbiased_GramAssembly_Block1Part0`, `MutuallyUnbiased_GramAssembly_Block1Part3`, `MutuallyUnbiased_GramAssembly_Block1Part4`, `MutuallyUnbiased_GramAssembly_Block1Part5`, `MutuallyUnbiased_Matrix_Definitions`, `MutuallyUnbiased_Matrix_OffDiagonal`, `MutuallyUnbiased_MixedMoments_MixedAlpha`, `MutuallyUnbiased_Moments_AuxiliaryGram`, `MutuallyUnbiased_Moments_AverageAlgebra`, `MutuallyUnbiased_Moments_Averages`, `MutuallyUnbiased_Moments_EmbeddedCharge`, `MutuallyUnbiased_Moments_Moments`, `MutuallyUnbiased_Moments_PartitionExpansion`.
--
--   **Imports.** It imports the published bundle `Def_MUBSix`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ106E003`, `OAIQ106E006`, `OAIQ106E007`, `OAIQ106E010`, `OAIQ106E013`, `OAIQ106E015`, `OAIQ106E021`, `OAIQ106E025`, `OAIQ106E029`, `OAIQ106E032`, `OAIQ106E035`, `OAIQ106E039`, `OAIQ106E045`, `OAIQ106E046`, `OAIQ106E047`, `OAIQ106E048`, `OAIQ106E049`, `OAIQ106E050`, `OAIQ106E051`, `OAIQ106E052`, `OAIQ106E053`, `OAIQ106E054`, `OAIQ106E055`, `OAIQ106E056`, `OAIQ106E057`, `OAIQ106E058`, `OAIQ106E059`, `OAIQ106E060`, `OAIQ106E062`, `OAIQ106E063`, `OAIQ106E065`, `OAIQ106E066`, `OAIQ106E068`, `OAIQ106E070`, `OAIQ106E071`, `OAIQ106E140`, `OAIQ106E170`, `OAIQ106E172`, `OAIQ106E173`, `OAIQ106E174`, `OAIQ106E176`, `OAIQ106E178`, `OAIQ106E179`, `OAIQ106E181` and `OAIQ106E184`; the statements `OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_5_e` and `OAI.MUB6.complete_family_square_not_hadamard_e`.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def Balanced (a : Charge) : Prop := ∑ i, a i = 0

@[simp] theorem character_zero (x : Coord → ℂ) : character x 0 = 1 := by
  simp [character]

@[simp] theorem g_zero (H : CMatrix) : g H 0 = 1 := by
  norm_num [g]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def transition (b c : Basis) : CMatrix :=
  fun i k => (Real.sqrt 6 : ℂ) * inner ℂ (b i) (c k)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_OffDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def offDiagSum {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) : V :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, f i j

@[simp] theorem offDiagSum_zero {V : Type*} [AddCommMonoid V] :
    offDiagSum (fun _ _ => (0 : V)) = 0 := by simp [offDiagSum]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The six transitions from a fixed reference basis, with that basis omitted. -/
def relativeMatrix (B : Fin 7 → Basis) (r : Fin 7) (s : Coord) : CMatrix :=
  transition (B r) (B (r.succAbove s))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

def average {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

@[simp] theorem average_zero : average (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [average]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def exponentMonomial {p q : ℕ} (H : CMatrix) (A : Matrix (Fin p) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) : ℂ :=
  ∏ u, ∏ v, H (ρ u) (κ v) ^ A u v

def injectiveMoment {p q : ℕ} (H : CMatrix) (A : Matrix (Fin p) (Fin q) ℤ) : ℝ :=
  average (fun s : (Fin p ↪ Coord) × (Fin q ↪ Coord) =>
    ((exponentMonomial H A s.1 s.2).re +
      (exponentMonomial H.transpose A s.1 s.2).re) / 2)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_ExponentCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate

/-- A finite integer exponent matrix, with its dimensions retained. -/
structure ExponentCode where
  rows : ℕ
  columns : ℕ
  entries : Matrix (Fin rows) (Fin columns) ℤ
  deriving Inhabited

/-- The interpretation is the actual injective moment defined in Section 2. -/
noncomputable def ExponentCode.moment (H : CMatrix) (A : ExponentCode) : ℝ :=
  injectiveMoment H A.entries

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

abbrev Sparse (ι : Type*) := List (ι × ℤ)

namespace Sparse

variable {ι : Type*}

noncomputable def eval (v : Sparse ι) (x : ι → ℝ) : ℝ :=
  (v.map fun p => (p.2 : ℝ) * x p.1).sum

def coeff [DecidableEq ι] (v : Sparse ι) (i : ι) : ℤ :=
  (v.map fun p => if p.1 = i then p.2 else 0).sum

@[simp] theorem eval_nil (x : ι → ℝ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (p : ι × ℤ) (v : Sparse ι) (x : ι → ℝ) :
    eval (p :: v) x = (p.2 : ℝ) * x p.1 + eval v x := rfl
@[simp] theorem coeff_nil [DecidableEq ι] (i : ι) : coeff [] i = 0 := rfl
@[simp] theorem coeff_cons [DecidableEq ι] (p : ι × ℤ) (v : Sparse ι) (i : ι) :
    coeff (p :: v) i = (if p.1 = i then p.2 else 0) + coeff v i := rfl

end Sparse

end MUB6.Certificate.Integer

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

@[simp] theorem eval_append (a b : Sparse ι) (x : ι → ℝ) :
    eval (a ++ b) x = eval a x + eval b x := by simp [eval]

def scale (q : ℤ) (a : Sparse ι) : Sparse ι := a.map fun p => (p.1, q * p.2)

@[simp] theorem eval_scale (q : ℤ) (a : Sparse ι) (x : ι → ℝ) :
    eval (scale q a) x = (q : ℝ) * eval a x := by
  induction a with
  | nil => simp [scale]
  | cons p a ih =>
    change ((q * p.2 : ℤ) : ℝ) * x p.1 + eval (scale q a) x =
      (q : ℝ) * ((p.2 : ℝ) * x p.1 + eval a x)
    rw [ih]
    simp only [Int.cast_mul, mul_add, mul_assoc]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Dichotomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def FourierZero (H : CMatrix) : Prop :=
  ∀ π : Equiv.Perm Coord, g (fun i j => H (π i) j) alpha = 0

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

def rowFourier {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ k, ∏ i, H (ρ i) k ^ a i

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def embedCharge {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) : Charge :=
  Function.extend ρ a (fun _ => 0)

@[simp] theorem embedCharge_apply {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Fin p) :
    embedCharge ρ a (ρ i) = a i := ρ.injective.extend_apply _ _ _

@[simp] theorem rowFourier_zero {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ 0 = 1 := by norm_num [rowFourier]

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

/-- Reference index, row bijection, nonreference-label bijection, and a column
of the matrix assigned label zero. -/
abbrev AuxiliarySample := Fin 7 × (Coord ↪ Coord) × (Coord ↪ Coord) × Coord

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

open scoped BigOperators

def entry_0_0 : Integer.Sparse (Fin 2886) := [(204, 60), (207, -60), (215, -60), (224, 88), (230, 32), (234, -60), (261, -60), (264, 60), (274, 76), (284, -92), (290, -56), (295, 80), (337, 44), (349, -64), (357, -60), (369, 88), (408, 60), (414, -60), (497, -28), (501, 40), (506, 32), (511, -60), (522, -60), (528, 60)]

def entry_0_1 : Integer.Sparse (Fin 2886) := [(1154, 60), (1160, -60), (1173, -60), (1184, 60), (1194, 60), (1200, -60), (1240, -60), (1246, 60), (1267, 60), (1288, -60), (1298, -60), (1307, 60), (1382, 60), (1394, -60), (1408, -60), (1427, 60), (1483, 60), (1491, -60), (1591, -60), (1597, 60), (1606, 60), (1614, -60), (1630, -60), (1638, 60)]

def entry_0_2 : Integer.Sparse (Fin 2886) := [(1150, 60), (1156, -60), (1169, -60), (1182, 60), (1205, 60), (1208, -60), (1236, -60), (1242, 60), (1263, 60), (1286, -60), (1312, -60), (1320, 60), (1378, 60), (1392, -60), (1404, -60), (1425, 60), (1505, 60), (1510, -60), (1700, -60), (1703, 60), (1707, 60), (1712, -60), (1720, -60), (1725, 60)]

def entry_0_3 : Integer.Sparse (Fin 2886) := [(210, 60), (212, -60), (221, -60), (228, 60), (232, 60), (237, -60), (267, -60), (269, 60), (280, 60), (288, -60), (292, -60), (298, 60), (343, 60), (353, -60), (363, -60), (373, 60), (411, 60), (417, -60), (499, -60), (504, 60), (508, 60), (514, -60), (525, -60), (531, 60)]

def entry_0_4 : Integer.Sparse (Fin 2886) := [(1149, 60), (1153, -60), (1168, -60), (1180, 60), (1191, 60), (1198, -60), (1235, -60), (1239, 60), (1262, 60), (1284, -60), (1295, -60), (1305, 60), (1377, 60), (1390, -60), (1403, -60), (1423, 60), (1481, 60), (1489, -60), (1588, -60), (1595, 60), (1603, 60), (1612, -60), (1628, -60), (1636, 60)]

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4]

def entry_1_0 : Integer.Sparse (Fin 2886) := [(1154, 60), (1160, -60), (1173, -60), (1184, 60), (1194, 60), (1200, -60), (1240, -60), (1246, 60), (1267, 60), (1288, -60), (1298, -60), (1307, 60), (1382, 60), (1394, -60), (1408, -60), (1427, 60), (1483, 60), (1491, -60), (1591, -60), (1597, 60), (1606, 60), (1614, -60), (1630, -60), (1638, 60)]

def entry_1_1 : Integer.Sparse (Fin 2886) := [(2365, 60), (2368, -60), (2381, -60), (2391, 76), (2398, 44), (2403, -60), (2420, -60), (2423, 60), (2455, 80), (2478, -88), (2487, -60), (2497, 76), (2535, 40), (2545, -60), (2558, -60), (2580, 76), (2645, 60), (2652, -60), (2686, -32), (2691, 44), (2698, 44), (2707, -60), (2723, -60), (2730, 60)]

def entry_1_2 : Integer.Sparse (Fin 2886) := [(2364, 60), (2366, -24), (2369, -36), (2376, -16), (2380, -44), (2388, 6), (2389, 38), (2392, 44), (2394, -6), (2396, 16), (2401, -24), (2406, 22), (2408, -36), (2415, -18), (2419, -42), (2421, 28), (2424, 32), (2450, 28), (2454, 48), (2474, -2), (2476, -44), (2480, -48), (2483, 2), (2485, -28), (2495, 38), (2501, -32), (2506, 44), (2530, 12), (2534, 32), (2542, -2), (2543, -28), (2546, -32), (2553, -16), (2557, -44), (2576, 6), (2578, 38), (2582, 44), (2643, 28), (2650, -28), (2666, 32), (2669, -32), (2682, 2), (2684, -12), (2689, 16), (2694, -6), (2696, 16), (2705, -24), (2721, -28), (2728, 28), (2753, -16), (2755, 22), (2757, 22), (2762, -36), (2768, -32), (2771, 32)]

def entry_1_3 : Integer.Sparse (Fin 2886) := [(1159, 60), (1163, -60), (1178, -60), (1187, 60), (1197, 60), (1203, -60), (1245, -60), (1249, 60), (1272, 60), (1291, -60), (1301, -60), (1310, 60), (1387, 60), (1397, -60), (1413, -60), (1430, 60), (1486, 60), (1494, -60), (1594, -60), (1600, 60), (1609, 60), (1617, -60), (1633, -60), (1641, 60)]

def entry_1_4 : Integer.Sparse (Fin 2886) := [(2364, 60), (2367, -60), (2380, -60), (2390, 60), (2397, 60), (2402, -60), (2419, -60), (2422, 60), (2454, 60), (2477, -60), (2486, -60), (2496, 60), (2534, 60), (2544, -60), (2557, -60), (2579, 60), (2644, 60), (2651, -60), (2685, -60), (2690, 60), (2697, 60), (2706, -60), (2722, -60), (2729, 60)]

def entryRow1 : Array (Integer.Sparse (Fin 2886)) := #[entry_1_0, entry_1_1, entry_1_2, entry_1_3, entry_1_4]

def entry_2_0 : Integer.Sparse (Fin 2886) := [(1150, 60), (1156, -60), (1169, -60), (1182, 60), (1205, 60), (1208, -60), (1236, -60), (1242, 60), (1263, 60), (1286, -60), (1312, -60), (1320, 60), (1378, 60), (1392, -60), (1404, -60), (1425, 60), (1505, 60), (1510, -60), (1700, -60), (1703, 60), (1707, 60), (1712, -60), (1720, -60), (1725, 60)]

def entry_2_1 : Integer.Sparse (Fin 2886) := [(2364, 60), (2366, -24), (2369, -36), (2376, -16), (2380, -44), (2388, 6), (2389, 38), (2392, 44), (2394, -6), (2396, 16), (2401, -24), (2406, 22), (2408, -36), (2415, -18), (2419, -42), (2421, 28), (2424, 32), (2450, 28), (2454, 48), (2474, -2), (2476, -44), (2480, -48), (2483, 2), (2485, -28), (2495, 38), (2501, -32), (2506, 44), (2530, 12), (2534, 32), (2542, -2), (2543, -28), (2546, -32), (2553, -16), (2557, -44), (2576, 6), (2578, 38), (2582, 44), (2643, 28), (2650, -28), (2666, 32), (2669, -32), (2682, 2), (2684, -12), (2689, 16), (2694, -6), (2696, 16), (2705, -24), (2721, -28), (2728, 28), (2753, -16), (2755, 22), (2757, 22), (2762, -36), (2768, -32), (2771, 32)]

def entry_2_2 : Integer.Sparse (Fin 2886) := [(2356, 60), (2362, -60), (2372, -60), (2386, 88), (2405, 32), (2407, -60), (2411, -60), (2417, 60), (2446, 76), (2472, -92), (2500, -56), (2505, 80), (2526, 44), (2540, -64), (2549, -60), (2574, 88), (2665, 60), (2668, -60), (2752, -28), (2754, 40), (2756, 32), (2761, -60), (2767, -60), (2770, 60)]

def entry_2_3 : Integer.Sparse (Fin 2886) := [(1158, 60), (1164, -60), (1177, -60), (1188, 60), (1207, 60), (1210, -60), (1244, -60), (1250, 60), (1271, 60), (1292, -60), (1314, -60), (1322, 60), (1386, 60), (1398, -60), (1412, -60), (1431, 60), (1507, 60), (1512, -60), (1702, -60), (1705, 60), (1709, 60), (1714, -60), (1722, -60), (1727, 60)]

def entry_2_4 : Integer.Sparse (Fin 2886) := [(2357, 60), (2361, -60), (2373, -60), (2385, 60), (2395, 60), (2400, -60), (2412, -60), (2416, 60), (2447, 60), (2471, -60), (2484, -60), (2494, 60), (2527, 60), (2539, -60), (2550, -60), (2573, 60), (2642, 60), (2649, -60), (2683, -60), (2688, 60), (2695, 60), (2704, -60), (2720, -60), (2727, 60)]

def entryRow2 : Array (Integer.Sparse (Fin 2886)) := #[entry_2_0, entry_2_1, entry_2_2, entry_2_3, entry_2_4]

def entry_3_0 : Integer.Sparse (Fin 2886) := [(210, 60), (212, -60), (221, -60), (228, 60), (232, 60), (237, -60), (267, -60), (269, 60), (280, 60), (288, -60), (292, -60), (298, 60), (343, 60), (353, -60), (363, -60), (373, 60), (411, 60), (417, -60), (499, -60), (504, 60), (508, 60), (514, -60), (525, -60), (531, 60)]

def entry_3_1 : Integer.Sparse (Fin 2886) := [(1159, 60), (1163, -60), (1178, -60), (1187, 60), (1197, 60), (1203, -60), (1245, -60), (1249, 60), (1272, 60), (1291, -60), (1301, -60), (1310, 60), (1387, 60), (1397, -60), (1413, -60), (1430, 60), (1486, 60), (1494, -60), (1594, -60), (1600, 60), (1609, 60), (1617, -60), (1633, -60), (1641, 60)]

def entry_3_2 : Integer.Sparse (Fin 2886) := [(1158, 60), (1164, -60), (1177, -60), (1188, 60), (1207, 60), (1210, -60), (1244, -60), (1250, 60), (1271, 60), (1292, -60), (1314, -60), (1322, 60), (1386, 60), (1398, -60), (1412, -60), (1431, 60), (1507, 60), (1512, -60), (1702, -60), (1705, 60), (1709, 60), (1714, -60), (1722, -60), (1727, 60)]

def entry_3_3 : Integer.Sparse (Fin 2886) := [(211, 60), (213, -60), (222, -60), (229, 76), (233, 44), (238, -60), (268, -60), (270, 60), (281, 80), (289, -88), (293, -60), (299, 76), (344, 40), (354, -60), (364, -60), (374, 76), (412, 60), (418, -60), (500, -32), (505, 44), (509, 44), (515, -60), (526, -60), (532, 60)]

def entry_3_4 : Integer.Sparse (Fin 2886) := [(1158, 60), (1162, -60), (1177, -60), (1186, 60), (1196, 60), (1202, -60), (1244, -60), (1248, 60), (1271, 60), (1290, -60), (1300, -60), (1309, 60), (1386, 60), (1396, -60), (1412, -60), (1429, 60), (1485, 60), (1493, -60), (1593, -60), (1599, 60), (1608, 60), (1616, -60), (1632, -60), (1640, 60)]

def entryRow3 : Array (Integer.Sparse (Fin 2886)) := #[entry_3_0, entry_3_1, entry_3_2, entry_3_3, entry_3_4]

def entry_4_0 : Integer.Sparse (Fin 2886) := [(1149, 60), (1153, -60), (1168, -60), (1180, 60), (1191, 60), (1198, -60), (1235, -60), (1239, 60), (1262, 60), (1284, -60), (1295, -60), (1305, 60), (1377, 60), (1390, -60), (1403, -60), (1423, 60), (1481, 60), (1489, -60), (1588, -60), (1595, 60), (1603, 60), (1612, -60), (1628, -60), (1636, 60)]

def entry_4_1 : Integer.Sparse (Fin 2886) := [(2364, 60), (2367, -60), (2380, -60), (2390, 60), (2397, 60), (2402, -60), (2419, -60), (2422, 60), (2454, 60), (2477, -60), (2486, -60), (2496, 60), (2534, 60), (2544, -60), (2557, -60), (2579, 60), (2644, 60), (2651, -60), (2685, -60), (2690, 60), (2697, 60), (2706, -60), (2722, -60), (2729, 60)]

def entry_4_2 : Integer.Sparse (Fin 2886) := [(2357, 60), (2361, -60), (2373, -60), (2385, 60), (2395, 60), (2400, -60), (2412, -60), (2416, 60), (2447, 60), (2471, -60), (2484, -60), (2494, 60), (2527, 60), (2539, -60), (2550, -60), (2573, 60), (2642, 60), (2649, -60), (2683, -60), (2688, 60), (2695, 60), (2704, -60), (2720, -60), (2727, 60)]

def entry_4_3 : Integer.Sparse (Fin 2886) := [(1158, 60), (1162, -60), (1177, -60), (1186, 60), (1196, 60), (1202, -60), (1244, -60), (1248, 60), (1271, 60), (1290, -60), (1300, -60), (1309, 60), (1386, 60), (1396, -60), (1412, -60), (1429, 60), (1485, 60), (1493, -60), (1593, -60), (1599, 60), (1608, 60), (1616, -60), (1632, -60), (1640, 60)]

def entry_4_4 : Integer.Sparse (Fin 2886) := [(2356, 60), (2359, -60), (2372, -60), (2384, 88), (2393, 32), (2399, -60), (2411, -60), (2414, 60), (2446, 76), (2470, -92), (2482, -56), (2493, 80), (2526, 44), (2538, -64), (2549, -60), (2572, 88), (2641, 60), (2648, -60), (2681, -28), (2687, 40), (2693, 32), (2703, -60), (2719, -60), (2726, 60)]

def entryRow4 : Array (Integer.Sparse (Fin 2886)) := #[entry_4_0, entry_4_1, entry_4_2, entry_4_3, entry_4_4]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4]

def entries (i j : Fin 5) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

def weights : Matrix (Fin 5) (Fin 5) ℤ := ![
  ![7856995, -2793048, 8971673, 4076125, -23581960],
  ![-2793048, 5486181, -1693736, -2967341, 9048932],
  ![8971673, -1693736, 37455549, -242661, -37895129],
  ![4076125, -2967341, -242661, 7655001, -9254062],
  ![-23581960, 9048932, -37895129, -9254062, 86753990]
]

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

def node0 : Integer.Sparse (Fin 2886) := [(204, 471419700), (207, -471419700), (215, -471419700), (224, 691415560), (230, 251423840), (234, -471419700), (261, -471419700), (264, 471419700), (274, 597131620), (284, -722843540), (290, -439991720), (295, 628559600), (337, 345707780), (349, -502847680), (357, -471419700), (369, 691415560), (408, 471419700), (414, -471419700), (497, -219995860), (501, 314279800), (506, 251423840), (511, -471419700), (522, -471419700), (528, 471419700), (1154, -167582880), (1160, 167582880), (1173, 167582880), (1184, -167582880), (1194, -167582880), (1200, 167582880), (1240, 167582880), (1246, -167582880), (1267, -167582880), (1288, 167582880), (1298, 167582880), (1307, -167582880), (1382, -167582880), (1394, 167582880), (1408, 167582880), (1427, -167582880), (1483, -167582880), (1491, 167582880), (1591, 167582880), (1597, -167582880), (1606, -167582880), (1614, 167582880), (1630, 167582880), (1638, -167582880)]

def node1 : Integer.Sparse (Fin 2886) := [(210, 244567500), (212, -244567500), (221, -244567500), (228, 244567500), (232, 244567500), (237, -244567500), (267, -244567500), (269, 244567500), (280, 244567500), (288, -244567500), (292, -244567500), (298, 244567500), (343, 244567500), (353, -244567500), (363, -244567500), (373, 244567500), (411, 244567500), (417, -244567500), (499, -244567500), (504, 244567500), (508, 244567500), (514, -244567500), (525, -244567500), (531, 244567500), (1149, -1414917600), (1153, 1414917600), (1168, 1414917600), (1180, -1414917600), (1191, -1414917600), (1198, 1414917600), (1235, 1414917600), (1239, -1414917600), (1262, -1414917600), (1284, 1414917600), (1295, 1414917600), (1305, -1414917600), (1377, -1414917600), (1390, 1414917600), (1403, 1414917600), (1423, -1414917600), (1481, -1414917600), (1489, 1414917600), (1588, 1414917600), (1595, -1414917600), (1603, -1414917600), (1612, 1414917600), (1628, 1414917600), (1636, -1414917600)]

def node2 : Integer.Sparse (Fin 2886) := [(210, 244567500), (212, -244567500), (221, -244567500), (228, 244567500), (232, 244567500), (237, -244567500), (267, -244567500), (269, 244567500), (280, 244567500), (288, -244567500), (292, -244567500), (298, 244567500), (343, 244567500), (353, -244567500), (363, -244567500), (373, 244567500), (411, 244567500), (417, -244567500), (499, -244567500), (504, 244567500), (508, 244567500), (514, -244567500), (525, -244567500), (531, 244567500), (1149, -1414917600), (1150, 538300380), (1153, 1414917600), (1156, -538300380), (1168, 1414917600), (1169, -538300380), (1180, -1414917600), (1182, 538300380), (1191, -1414917600), (1198, 1414917600), (1205, 538300380), (1208, -538300380), (1235, 1414917600), (1236, -538300380), (1239, -1414917600), (1242, 538300380), (1262, -1414917600), (1263, 538300380), (1284, 1414917600), (1286, -538300380), (1295, 1414917600), (1305, -1414917600), (1312, -538300380), (1320, 538300380), (1377, -1414917600), (1378, 538300380), (1390, 1414917600), (1392, -538300380), (1403, 1414917600), (1404, -538300380), (1423, -1414917600), (1425, 538300380), (1481, -1414917600), (1489, 1414917600), (1505, 538300380), (1510, -538300380), (1588, 1414917600), (1595, -1414917600), (1603, -1414917600), (1612, 1414917600), (1628, 1414917600), (1636, -1414917600), (1700, -538300380), (1703, 538300380), (1707, 538300380), (1712, -538300380), (1720, -538300380), (1725, 538300380)]

def node3 : Integer.Sparse (Fin 2886) := [(204, 471419700), (207, -471419700), (210, 244567500), (212, -244567500), (215, -471419700), (221, -244567500), (224, 691415560), (228, 244567500), (230, 251423840), (232, 244567500), (234, -471419700), (237, -244567500), (261, -471419700), (264, 471419700), (267, -244567500), (269, 244567500), (274, 597131620), (280, 244567500), (284, -722843540), (288, -244567500), (290, -439991720), (292, -244567500), (295, 628559600), (298, 244567500), (337, 345707780), (343, 244567500), (349, -502847680), (353, -244567500), (357, -471419700), (363, -244567500), (369, 691415560), (373, 244567500), (408, 471419700), (411, 244567500), (414, -471419700), (417, -244567500), (497, -219995860), (499, -244567500), (501, 314279800), (504, 244567500), (506, 251423840), (508, 244567500), (511, -471419700), (514, -244567500), (522, -471419700), (525, -244567500), (528, 471419700), (531, 244567500), (1149, -1414917600), (1150, 538300380), (1153, 1414917600), (1154, -167582880), (1156, -538300380), (1160, 167582880), (1168, 1414917600), (1169, -538300380), (1173, 167582880), (1180, -1414917600), (1182, 538300380), (1184, -167582880), (1191, -1414917600), (1194, -167582880), (1198, 1414917600), (1200, 167582880), (1205, 538300380), (1208, -538300380), (1235, 1414917600), (1236, -538300380), (1239, -1414917600), (1240, 167582880), (1242, 538300380), (1246, -167582880), (1262, -1414917600), (1263, 538300380), (1267, -167582880), (1284, 1414917600), (1286, -538300380), (1288, 167582880), (1295, 1414917600), (1298, 167582880), (1305, -1414917600), (1307, -167582880), (1312, -538300380), (1320, 538300380), (1377, -1414917600), (1378, 538300380), (1382, -167582880), (1390, 1414917600), (1392, -538300380), (1394, 167582880), (1403, 1414917600), (1404, -538300380), (1408, 167582880), (1423, -1414917600), (1425, 538300380), (1427, -167582880), (1481, -1414917600), (1483, -167582880), (1489, 1414917600), (1491, 167582880), (1505, 538300380), (1510, -538300380), (1588, 1414917600), (1591, 167582880), (1595, -1414917600), (1597, -167582880), (1603, -1414917600), (1606, -167582880), (1612, 1414917600), (1614, 167582880), (1628, 1414917600), (1630, 167582880), (1636, -1414917600), (1638, -167582880), (1700, -538300380), (1703, 538300380), (1707, 538300380), (1712, -538300380), (1720, -538300380), (1725, 538300380)]

def node4 : Integer.Sparse (Fin 2886) := [(1154, -167582880), (1160, 167582880), (1173, 167582880), (1184, -167582880), (1194, -167582880), (1200, 167582880), (1240, 167582880), (1246, -167582880), (1267, -167582880), (1288, 167582880), (1298, 167582880), (1307, -167582880), (1382, -167582880), (1394, 167582880), (1408, 167582880), (1427, -167582880), (1483, -167582880), (1491, 167582880), (1591, 167582880), (1597, -167582880), (1606, -167582880), (1614, 167582880), (1630, 167582880), (1638, -167582880), (2365, 329170860), (2368, -329170860), (2381, -329170860), (2391, 416949756), (2398, 241391964), (2403, -329170860), (2420, -329170860), (2423, 329170860), (2455, 438894480), (2478, -482783928), (2487, -329170860), (2497, 416949756), (2535, 219447240), (2545, -329170860), (2558, -329170860), (2580, 416949756), (2645, 329170860), (2652, -329170860), (2686, -175557792), (2691, 241391964), (2698, 241391964), (2707, -329170860), (2723, -329170860), (2730, 329170860)]

def node5 : Integer.Sparse (Fin 2886) := [(1159, -178040460), (1163, 178040460), (1178, 178040460), (1187, -178040460), (1197, -178040460), (1203, 178040460), (1245, 178040460), (1249, -178040460), (1272, -178040460), (1291, 178040460), (1301, 178040460), (1310, -178040460), (1387, -178040460), (1397, 178040460), (1413, 178040460), (1430, -178040460), (1486, -178040460), (1494, 178040460), (1594, 178040460), (1600, -178040460), (1609, -178040460), (1617, 178040460), (1633, 178040460), (1641, -178040460), (2364, 542935920), (2367, -542935920), (2380, -542935920), (2390, 542935920), (2397, 542935920), (2402, -542935920), (2419, -542935920), (2422, 542935920), (2454, 542935920), (2477, -542935920), (2486, -542935920), (2496, 542935920), (2534, 542935920), (2544, -542935920), (2557, -542935920), (2579, 542935920), (2644, 542935920), (2651, -542935920), (2685, -542935920), (2690, 542935920), (2697, 542935920), (2706, -542935920), (2722, -542935920), (2729, 542935920)]

def node6 : Integer.Sparse (Fin 2886) := [(1159, -178040460), (1163, 178040460), (1178, 178040460), (1187, -178040460), (1197, -178040460), (1203, 178040460), (1245, 178040460), (1249, -178040460), (1272, -178040460), (1291, 178040460), (1301, 178040460), (1310, -178040460), (1387, -178040460), (1397, 178040460), (1413, 178040460), (1430, -178040460), (1486, -178040460), (1494, 178040460), (1594, 178040460), (1600, -178040460), (1609, -178040460), (1617, 178040460), (1633, 178040460), (1641, -178040460), (2364, 441311760), (2366, 40649664), (2367, -542935920), (2369, 60974496), (2376, 27099776), (2380, -468411536), (2388, -10162416), (2389, -64361968), (2390, 542935920), (2392, -74524384), (2394, 10162416), (2396, -27099776), (2397, 542935920), (2401, 40649664), (2402, -542935920), (2406, -37262192), (2408, 60974496), (2415, 30487248), (2419, -471799008), (2421, -47424608), (2422, 542935920), (2424, -54199552), (2450, -47424608), (2454, 461636592), (2474, 3387472), (2476, 74524384), (2477, -542935920), (2480, 81299328), (2483, -3387472), (2485, 47424608), (2486, -542935920), (2495, -64361968), (2496, 542935920), (2501, 54199552), (2506, -74524384), (2530, -20324832), (2534, 488736368), (2542, 3387472), (2543, 47424608), (2544, -542935920), (2546, 54199552), (2553, 27099776), (2557, -468411536), (2576, -10162416), (2578, -64361968), (2579, 542935920), (2582, -74524384), (2643, -47424608), (2644, 542935920), (2650, 47424608), (2651, -542935920), (2666, -54199552), (2669, 54199552), (2682, -3387472), (2684, 20324832), (2685, -542935920), (2689, -27099776), (2690, 542935920), (2694, 10162416), (2696, -27099776), (2697, 542935920), (2705, 40649664), (2706, -542935920), (2721, 47424608), (2722, -542935920), (2728, -47424608), (2729, 542935920), (2753, 27099776), (2755, -37262192), (2757, -37262192), (2762, 60974496), (2768, 54199552), (2771, -54199552)]

def node7 : Integer.Sparse (Fin 2886) := [(1154, -167582880), (1159, -178040460), (1160, 167582880), (1163, 178040460), (1173, 167582880), (1178, 178040460), (1184, -167582880), (1187, -178040460), (1194, -167582880), (1197, -178040460), (1200, 167582880), (1203, 178040460), (1240, 167582880), (1245, 178040460), (1246, -167582880), (1249, -178040460), (1267, -167582880), (1272, -178040460), (1288, 167582880), (1291, 178040460), (1298, 167582880), (1301, 178040460), (1307, -167582880), (1310, -178040460), (1382, -167582880), (1387, -178040460), (1394, 167582880), (1397, 178040460), (1408, 167582880), (1413, 178040460), (1427, -167582880), (1430, -178040460), (1483, -167582880), (1486, -178040460), (1491, 167582880), (1494, 178040460), (1591, 167582880), (1594, 178040460), (1597, -167582880), (1600, -178040460), (1606, -167582880), (1609, -178040460), (1614, 167582880), (1617, 178040460), (1630, 167582880), (1633, 178040460), (1638, -167582880), (1641, -178040460), (2364, 441311760), (2365, 329170860), (2366, 40649664), (2367, -542935920), (2368, -329170860), (2369, 60974496), (2376, 27099776), (2380, -468411536), (2381, -329170860), (2388, -10162416), (2389, -64361968), (2390, 542935920), (2391, 416949756), (2392, -74524384), (2394, 10162416), (2396, -27099776), (2397, 542935920), (2398, 241391964), (2401, 40649664), (2402, -542935920), (2403, -329170860), (2406, -37262192), (2408, 60974496), (2415, 30487248), (2419, -471799008), (2420, -329170860), (2421, -47424608), (2422, 542935920), (2423, 329170860), (2424, -54199552), (2450, -47424608), (2454, 461636592), (2455, 438894480), (2474, 3387472), (2476, 74524384), (2477, -542935920), (2478, -482783928), (2480, 81299328), (2483, -3387472), (2485, 47424608), (2486, -542935920), (2487, -329170860), (2495, -64361968), (2496, 542935920), (2497, 416949756), (2501, 54199552), (2506, -74524384), (2530, -20324832), (2534, 488736368), (2535, 219447240), (2542, 3387472), (2543, 47424608), (2544, -542935920), (2545, -329170860), (2546, 54199552), (2553, 27099776), (2557, -468411536), (2558, -329170860), (2576, -10162416), (2578, -64361968), (2579, 542935920), (2580, 416949756), (2582, -74524384), (2643, -47424608), (2644, 542935920), (2645, 329170860), (2650, 47424608), (2651, -542935920), (2652, -329170860), (2666, -54199552), (2669, 54199552), (2682, -3387472), (2684, 20324832), (2685, -542935920), (2686, -175557792), (2689, -27099776), (2690, 542935920), (2691, 241391964), (2694, 10162416), (2696, -27099776), (2697, 542935920), (2698, 241391964), (2705, 40649664), (2706, -542935920), (2707, -329170860), (2721, 47424608), (2722, -542935920), (2723, -329170860), (2728, -47424608), (2729, 542935920), (2730, 329170860), (2753, 27099776), (2755, -37262192), (2757, -37262192), (2762, 60974496), (2768, 54199552), (2771, -54199552)]

def node8 : Integer.Sparse (Fin 2886) := [(1150, 538300380), (1156, -538300380), (1169, -538300380), (1182, 538300380), (1205, 538300380), (1208, -538300380), (1236, -538300380), (1242, 538300380), (1263, 538300380), (1286, -538300380), (1312, -538300380), (1320, 538300380), (1378, 538300380), (1392, -538300380), (1404, -538300380), (1425, 538300380), (1505, 538300380), (1510, -538300380), (1700, -538300380), (1703, 538300380), (1707, 538300380), (1712, -538300380), (1720, -538300380), (1725, 538300380), (2364, -101624160), (2366, 40649664), (2369, 60974496), (2376, 27099776), (2380, 74524384), (2388, -10162416), (2389, -64361968), (2392, -74524384), (2394, 10162416), (2396, -27099776), (2401, 40649664), (2406, -37262192), (2408, 60974496), (2415, 30487248), (2419, 71136912), (2421, -47424608), (2424, -54199552), (2450, -47424608), (2454, -81299328), (2474, 3387472), (2476, 74524384), (2480, 81299328), (2483, -3387472), (2485, 47424608), (2495, -64361968), (2501, 54199552), (2506, -74524384), (2530, -20324832), (2534, -54199552), (2542, 3387472), (2543, 47424608), (2546, 54199552), (2553, 27099776), (2557, 74524384), (2576, -10162416), (2578, -64361968), (2582, -74524384), (2643, -47424608), (2650, 47424608), (2666, -54199552), (2669, 54199552), (2682, -3387472), (2684, 20324832), (2689, -27099776), (2694, 10162416), (2696, -27099776), (2705, 40649664), (2721, 47424608), (2728, -47424608), (2753, 27099776), (2755, -37262192), (2757, -37262192), (2762, 60974496), (2768, 54199552), (2771, -54199552)]

def node9 : Integer.Sparse (Fin 2886) := [(1158, -14559660), (1164, 14559660), (1177, 14559660), (1188, -14559660), (1207, -14559660), (1210, 14559660), (1244, 14559660), (1250, -14559660), (1271, -14559660), (1292, 14559660), (1314, 14559660), (1322, -14559660), (1386, -14559660), (1398, 14559660), (1412, 14559660), (1431, -14559660), (1507, -14559660), (1512, 14559660), (1702, 14559660), (1705, -14559660), (1709, -14559660), (1714, 14559660), (1722, 14559660), (1727, -14559660), (2357, -2273707740), (2361, 2273707740), (2373, 2273707740), (2385, -2273707740), (2395, -2273707740), (2400, 2273707740), (2412, 2273707740), (2416, -2273707740), (2447, -2273707740), (2471, 2273707740), (2484, 2273707740), (2494, -2273707740), (2527, -2273707740), (2539, 2273707740), (2550, 2273707740), (2573, -2273707740), (2642, -2273707740), (2649, 2273707740), (2683, 2273707740), (2688, -2273707740), (2695, -2273707740), (2704, 2273707740), (2720, 2273707740), (2727, -2273707740)]

def node10 : Integer.Sparse (Fin 2886) := [(1158, -14559660), (1164, 14559660), (1177, 14559660), (1188, -14559660), (1207, -14559660), (1210, 14559660), (1244, 14559660), (1250, -14559660), (1271, -14559660), (1292, 14559660), (1314, 14559660), (1322, -14559660), (1386, -14559660), (1398, 14559660), (1412, 14559660), (1431, -14559660), (1507, -14559660), (1512, 14559660), (1702, 14559660), (1705, -14559660), (1709, -14559660), (1714, 14559660), (1722, 14559660), (1727, -14559660), (2356, 2247332940), (2357, -2273707740), (2361, 2273707740), (2362, -2247332940), (2372, -2247332940), (2373, 2273707740), (2385, -2273707740), (2386, 3296088312), (2395, -2273707740), (2400, 2273707740), (2405, 1198577568), (2407, -2247332940), (2411, -2247332940), (2412, 2273707740), (2416, -2273707740), (2417, 2247332940), (2446, 2846621724), (2447, -2273707740), (2471, 2273707740), (2472, -3445910508), (2484, 2273707740), (2494, -2273707740), (2500, -2097510744), (2505, 2996443920), (2526, 1648044156), (2527, -2273707740), (2539, 2273707740), (2540, -2397155136), (2549, -2247332940), (2550, 2273707740), (2573, -2273707740), (2574, 3296088312), (2642, -2273707740), (2649, 2273707740), (2665, 2247332940), (2668, -2247332940), (2683, 2273707740), (2688, -2273707740), (2695, -2273707740), (2704, 2273707740), (2720, 2273707740), (2727, -2273707740), (2752, -1048755372), (2754, 1498221960), (2756, 1198577568), (2761, -2247332940), (2767, -2247332940), (2770, 2247332940)]

def node11 : Integer.Sparse (Fin 2886) := [(1150, 538300380), (1156, -538300380), (1158, -14559660), (1164, 14559660), (1169, -538300380), (1177, 14559660), (1182, 538300380), (1188, -14559660), (1205, 538300380), (1207, -14559660), (1208, -538300380), (1210, 14559660), (1236, -538300380), (1242, 538300380), (1244, 14559660), (1250, -14559660), (1263, 538300380), (1271, -14559660), (1286, -538300380), (1292, 14559660), (1312, -538300380), (1314, 14559660), (1320, 538300380), (1322, -14559660), (1378, 538300380), (1386, -14559660), (1392, -538300380), (1398, 14559660), (1404, -538300380), (1412, 14559660), (1425, 538300380), (1431, -14559660), (1505, 538300380), (1507, -14559660), (1510, -538300380), (1512, 14559660), (1700, -538300380), (1702, 14559660), (1703, 538300380), (1705, -14559660), (1707, 538300380), (1709, -14559660), (1712, -538300380), (1714, 14559660), (1720, -538300380), (1722, 14559660), (1725, 538300380), (1727, -14559660), (2356, 2247332940), (2357, -2273707740), (2361, 2273707740), (2362, -2247332940), (2364, -101624160), (2366, 40649664), (2369, 60974496), (2372, -2247332940), (2373, 2273707740), (2376, 27099776), (2380, 74524384), (2385, -2273707740), (2386, 3296088312), (2388, -10162416), (2389, -64361968), (2392, -74524384), (2394, 10162416), (2395, -2273707740), (2396, -27099776), (2400, 2273707740), (2401, 40649664), (2405, 1198577568), (2406, -37262192), (2407, -2247332940), (2408, 60974496), (2411, -2247332940), (2412, 2273707740), (2415, 30487248), (2416, -2273707740), (2417, 2247332940), (2419, 71136912), (2421, -47424608), (2424, -54199552), (2446, 2846621724), (2447, -2273707740), (2450, -47424608), (2454, -81299328), (2471, 2273707740), (2472, -3445910508), (2474, 3387472), (2476, 74524384), (2480, 81299328), (2483, -3387472), (2484, 2273707740), (2485, 47424608), (2494, -2273707740), (2495, -64361968), (2500, -2097510744), (2501, 54199552), (2505, 2996443920), (2506, -74524384), (2526, 1648044156), (2527, -2273707740), (2530, -20324832), (2534, -54199552), (2539, 2273707740), (2540, -2397155136), (2542, 3387472), (2543, 47424608), (2546, 54199552), (2549, -2247332940), (2550, 2273707740), (2553, 27099776), (2557, 74524384), (2573, -2273707740), (2574, 3296088312), (2576, -10162416), (2578, -64361968), (2582, -74524384), (2642, -2273707740), (2643, -47424608), (2649, 2273707740), (2650, 47424608), (2665, 2247332940), (2666, -54199552), (2668, -2247332940), (2669, 54199552), (2682, -3387472), (2683, 2273707740), (2684, 20324832), (2688, -2273707740), (2689, -27099776), (2694, 10162416), (2695, -2273707740), (2696, -27099776), (2704, 2273707740), (2705, 40649664), (2720, 2273707740), (2721, 47424608), (2727, -2273707740), (2728, -47424608), (2752, -1048755372), (2753, 27099776), (2754, 1498221960), (2755, -37262192), (2756, 1198577568), (2757, -37262192), (2761, -2247332940), (2762, 60974496), (2767, -2247332940), (2768, 54199552), (2770, 2247332940), (2771, -54199552)]

def node12 : Integer.Sparse (Fin 2886) := [(210, 244567500), (212, -244567500), (221, -244567500), (228, 244567500), (232, 244567500), (237, -244567500), (267, -244567500), (269, 244567500), (280, 244567500), (288, -244567500), (292, -244567500), (298, 244567500), (343, 244567500), (353, -244567500), (363, -244567500), (373, 244567500), (411, 244567500), (417, -244567500), (499, -244567500), (504, 244567500), (508, 244567500), (514, -244567500), (525, -244567500), (531, 244567500), (1159, -178040460), (1163, 178040460), (1178, 178040460), (1187, -178040460), (1197, -178040460), (1203, 178040460), (1245, 178040460), (1249, -178040460), (1272, -178040460), (1291, 178040460), (1301, 178040460), (1310, -178040460), (1387, -178040460), (1397, 178040460), (1413, 178040460), (1430, -178040460), (1486, -178040460), (1494, 178040460), (1594, 178040460), (1600, -178040460), (1609, -178040460), (1617, 178040460), (1633, 178040460), (1641, -178040460)]

def node13 : Integer.Sparse (Fin 2886) := [(211, 459300060), (213, -459300060), (222, -459300060), (229, 581780076), (233, 336820044), (238, -459300060), (268, -459300060), (270, 459300060), (281, 612400080), (289, -673640088), (293, -459300060), (299, 581780076), (344, 306200040), (354, -459300060), (364, -459300060), (374, 581780076), (412, 459300060), (418, -459300060), (500, -244960032), (505, 336820044), (509, 336820044), (515, -459300060), (526, -459300060), (532, 459300060), (1158, -555243720), (1162, 555243720), (1177, 555243720), (1186, -555243720), (1196, -555243720), (1202, 555243720), (1244, 555243720), (1248, -555243720), (1271, -555243720), (1290, 555243720), (1300, 555243720), (1309, -555243720), (1386, -555243720), (1396, 555243720), (1412, 555243720), (1429, -555243720), (1485, -555243720), (1493, 555243720), (1593, 555243720), (1599, -555243720), (1608, -555243720), (1616, 555243720), (1632, 555243720), (1640, -555243720)]

def node14 : Integer.Sparse (Fin 2886) := [(211, 459300060), (213, -459300060), (222, -459300060), (229, 581780076), (233, 336820044), (238, -459300060), (268, -459300060), (270, 459300060), (281, 612400080), (289, -673640088), (293, -459300060), (299, 581780076), (344, 306200040), (354, -459300060), (364, -459300060), (374, 581780076), (412, 459300060), (418, -459300060), (500, -244960032), (505, 336820044), (509, 336820044), (515, -459300060), (526, -459300060), (532, 459300060), (1158, -569803380), (1162, 555243720), (1164, 14559660), (1177, 569803380), (1186, -555243720), (1188, -14559660), (1196, -555243720), (1202, 555243720), (1207, -14559660), (1210, 14559660), (1244, 569803380), (1248, -555243720), (1250, -14559660), (1271, -569803380), (1290, 555243720), (1292, 14559660), (1300, 555243720), (1309, -555243720), (1314, 14559660), (1322, -14559660), (1386, -569803380), (1396, 555243720), (1398, 14559660), (1412, 569803380), (1429, -555243720), (1431, -14559660), (1485, -555243720), (1493, 555243720), (1507, -14559660), (1512, 14559660), (1593, 555243720), (1599, -555243720), (1608, -555243720), (1616, 555243720), (1632, 555243720), (1640, -555243720), (1702, 14559660), (1705, -14559660), (1709, -14559660), (1714, 14559660), (1722, 14559660), (1727, -14559660)]

def node15 : Integer.Sparse (Fin 2886) := [(210, 244567500), (211, 459300060), (212, -244567500), (213, -459300060), (221, -244567500), (222, -459300060), (228, 244567500), (229, 581780076), (232, 244567500), (233, 336820044), (237, -244567500), (238, -459300060), (267, -244567500), (268, -459300060), (269, 244567500), (270, 459300060), (280, 244567500), (281, 612400080), (288, -244567500), (289, -673640088), (292, -244567500), (293, -459300060), (298, 244567500), (299, 581780076), (343, 244567500), (344, 306200040), (353, -244567500), (354, -459300060), (363, -244567500), (364, -459300060), (373, 244567500), (374, 581780076), (411, 244567500), (412, 459300060), (417, -244567500), (418, -459300060), (499, -244567500), (500, -244960032), (504, 244567500), (505, 336820044), (508, 244567500), (509, 336820044), (514, -244567500), (515, -459300060), (525, -244567500), (526, -459300060), (531, 244567500), (532, 459300060), (1158, -569803380), (1159, -178040460), (1162, 555243720), (1163, 178040460), (1164, 14559660), (1177, 569803380), (1178, 178040460), (1186, -555243720), (1187, -178040460), (1188, -14559660), (1196, -555243720), (1197, -178040460), (1202, 555243720), (1203, 178040460), (1207, -14559660), (1210, 14559660), (1244, 569803380), (1245, 178040460), (1248, -555243720), (1249, -178040460), (1250, -14559660), (1271, -569803380), (1272, -178040460), (1290, 555243720), (1291, 178040460), (1292, 14559660), (1300, 555243720), (1301, 178040460), (1309, -555243720), (1310, -178040460), (1314, 14559660), (1322, -14559660), (1386, -569803380), (1387, -178040460), (1396, 555243720), (1397, 178040460), (1398, 14559660), (1412, 569803380), (1413, 178040460), (1429, -555243720), (1430, -178040460), (1431, -14559660), (1485, -555243720), (1486, -178040460), (1493, 555243720), (1494, 178040460), (1507, -14559660), (1512, 14559660), (1593, 555243720), (1594, 178040460), (1599, -555243720), (1600, -178040460), (1608, -555243720), (1609, -178040460), (1616, 555243720), (1617, 178040460), (1632, 555243720), (1633, 178040460), (1640, -555243720), (1641, -178040460), (1702, 14559660), (1705, -14559660), (1709, -14559660), (1714, 14559660), (1722, 14559660), (1727, -14559660)]

def node16 : Integer.Sparse (Fin 2886) := [(1149, -1414917600), (1153, 1414917600), (1168, 1414917600), (1180, -1414917600), (1191, -1414917600), (1198, 1414917600), (1235, 1414917600), (1239, -1414917600), (1262, -1414917600), (1284, 1414917600), (1295, 1414917600), (1305, -1414917600), (1377, -1414917600), (1390, 1414917600), (1403, 1414917600), (1423, -1414917600), (1481, -1414917600), (1489, 1414917600), (1588, 1414917600), (1595, -1414917600), (1603, -1414917600), (1612, 1414917600), (1628, 1414917600), (1636, -1414917600), (2364, 542935920), (2367, -542935920), (2380, -542935920), (2390, 542935920), (2397, 542935920), (2402, -542935920), (2419, -542935920), (2422, 542935920), (2454, 542935920), (2477, -542935920), (2486, -542935920), (2496, 542935920), (2534, 542935920), (2544, -542935920), (2557, -542935920), (2579, 542935920), (2644, 542935920), (2651, -542935920), (2685, -542935920), (2690, 542935920), (2697, 542935920), (2706, -542935920), (2722, -542935920), (2729, 542935920)]

def node17 : Integer.Sparse (Fin 2886) := [(1158, -555243720), (1162, 555243720), (1177, 555243720), (1186, -555243720), (1196, -555243720), (1202, 555243720), (1244, 555243720), (1248, -555243720), (1271, -555243720), (1290, 555243720), (1300, 555243720), (1309, -555243720), (1386, -555243720), (1396, 555243720), (1412, 555243720), (1429, -555243720), (1485, -555243720), (1493, 555243720), (1593, 555243720), (1599, -555243720), (1608, -555243720), (1616, 555243720), (1632, 555243720), (1640, -555243720), (2356, 5205239400), (2359, -5205239400), (2372, -5205239400), (2384, 7634351120), (2393, 2776127680), (2399, -5205239400), (2411, -5205239400), (2414, 5205239400), (2446, 6593303240), (2470, -7981367080), (2482, -4858223440), (2493, 6940319200), (2526, 3817175560), (2538, -5552255360), (2549, -5205239400), (2572, 7634351120), (2641, 5205239400), (2648, -5205239400), (2681, -2429111720), (2687, 3470159600), (2693, 2776127680), (2703, -5205239400), (2719, -5205239400), (2726, 5205239400)]

def node18 : Integer.Sparse (Fin 2886) := [(1158, -555243720), (1162, 555243720), (1177, 555243720), (1186, -555243720), (1196, -555243720), (1202, 555243720), (1244, 555243720), (1248, -555243720), (1271, -555243720), (1290, 555243720), (1300, 555243720), (1309, -555243720), (1386, -555243720), (1396, 555243720), (1412, 555243720), (1429, -555243720), (1485, -555243720), (1493, 555243720), (1593, 555243720), (1599, -555243720), (1608, -555243720), (1616, 555243720), (1632, 555243720), (1640, -555243720), (2356, 5205239400), (2357, -2273707740), (2359, -5205239400), (2361, 2273707740), (2372, -5205239400), (2373, 2273707740), (2384, 7634351120), (2385, -2273707740), (2393, 2776127680), (2395, -2273707740), (2399, -5205239400), (2400, 2273707740), (2411, -5205239400), (2412, 2273707740), (2414, 5205239400), (2416, -2273707740), (2446, 6593303240), (2447, -2273707740), (2470, -7981367080), (2471, 2273707740), (2482, -4858223440), (2484, 2273707740), (2493, 6940319200), (2494, -2273707740), (2526, 3817175560), (2527, -2273707740), (2538, -5552255360), (2539, 2273707740), (2549, -5205239400), (2550, 2273707740), (2572, 7634351120), (2573, -2273707740), (2641, 5205239400), (2642, -2273707740), (2648, -5205239400), (2649, 2273707740), (2681, -2429111720), (2683, 2273707740), (2687, 3470159600), (2688, -2273707740), (2693, 2776127680), (2695, -2273707740), (2703, -5205239400), (2704, 2273707740), (2719, -5205239400), (2720, 2273707740), (2726, 5205239400), (2727, -2273707740)]

def node19 : Integer.Sparse (Fin 2886) := [(1149, -1414917600), (1153, 1414917600), (1158, -555243720), (1162, 555243720), (1168, 1414917600), (1177, 555243720), (1180, -1414917600), (1186, -555243720), (1191, -1414917600), (1196, -555243720), (1198, 1414917600), (1202, 555243720), (1235, 1414917600), (1239, -1414917600), (1244, 555243720), (1248, -555243720), (1262, -1414917600), (1271, -555243720), (1284, 1414917600), (1290, 555243720), (1295, 1414917600), (1300, 555243720), (1305, -1414917600), (1309, -555243720), (1377, -1414917600), (1386, -555243720), (1390, 1414917600), (1396, 555243720), (1403, 1414917600), (1412, 555243720), (1423, -1414917600), (1429, -555243720), (1481, -1414917600), (1485, -555243720), (1489, 1414917600), (1493, 555243720), (1588, 1414917600), (1593, 555243720), (1595, -1414917600), (1599, -555243720), (1603, -1414917600), (1608, -555243720), (1612, 1414917600), (1616, 555243720), (1628, 1414917600), (1632, 555243720), (1636, -1414917600), (1640, -555243720), (2356, 5205239400), (2357, -2273707740), (2359, -5205239400), (2361, 2273707740), (2364, 542935920), (2367, -542935920), (2372, -5205239400), (2373, 2273707740), (2380, -542935920), (2384, 7634351120), (2385, -2273707740), (2390, 542935920), (2393, 2776127680), (2395, -2273707740), (2397, 542935920), (2399, -5205239400), (2400, 2273707740), (2402, -542935920), (2411, -5205239400), (2412, 2273707740), (2414, 5205239400), (2416, -2273707740), (2419, -542935920), (2422, 542935920), (2446, 6593303240), (2447, -2273707740), (2454, 542935920), (2470, -7981367080), (2471, 2273707740), (2477, -542935920), (2482, -4858223440), (2484, 2273707740), (2486, -542935920), (2493, 6940319200), (2494, -2273707740), (2496, 542935920), (2526, 3817175560), (2527, -2273707740), (2534, 542935920), (2538, -5552255360), (2539, 2273707740), (2544, -542935920), (2549, -5205239400), (2550, 2273707740), (2557, -542935920), (2572, 7634351120), (2573, -2273707740), (2579, 542935920), (2641, 5205239400), (2642, -2273707740), (2644, 542935920), (2648, -5205239400), (2649, 2273707740), (2651, -542935920), (2681, -2429111720), (2683, 2273707740), (2685, -542935920), (2687, 3470159600), (2688, -2273707740), (2690, 542935920), (2693, 2776127680), (2695, -2273707740), (2697, 542935920), (2703, -5205239400), (2704, 2273707740), (2706, -542935920), (2719, -5205239400), (2720, 2273707740), (2722, -542935920), (2726, 5205239400), (2727, -2273707740), (2729, 542935920)]

def node20 : Integer.Sparse (Fin 2886) := [(204, 471419700), (207, -471419700), (210, 244567500), (212, -244567500), (215, -471419700), (221, -244567500), (224, 691415560), (228, 244567500), (230, 251423840), (232, 244567500), (234, -471419700), (237, -244567500), (261, -471419700), (264, 471419700), (267, -244567500), (269, 244567500), (274, 597131620), (280, 244567500), (284, -722843540), (288, -244567500), (290, -439991720), (292, -244567500), (295, 628559600), (298, 244567500), (337, 345707780), (343, 244567500), (349, -502847680), (353, -244567500), (357, -471419700), (363, -244567500), (369, 691415560), (373, 244567500), (408, 471419700), (411, 244567500), (414, -471419700), (417, -244567500), (497, -219995860), (499, -244567500), (501, 314279800), (504, 244567500), (506, 251423840), (508, 244567500), (511, -471419700), (514, -244567500), (522, -471419700), (525, -244567500), (528, 471419700), (531, 244567500), (1149, -1414917600), (1150, 538300380), (1153, 1414917600), (1154, -335165760), (1156, -538300380), (1159, -178040460), (1160, 335165760), (1163, 178040460), (1168, 1414917600), (1169, -538300380), (1173, 335165760), (1178, 178040460), (1180, -1414917600), (1182, 538300380), (1184, -335165760), (1187, -178040460), (1191, -1414917600), (1194, -335165760), (1197, -178040460), (1198, 1414917600), (1200, 335165760), (1203, 178040460), (1205, 538300380), (1208, -538300380), (1235, 1414917600), (1236, -538300380), (1239, -1414917600), (1240, 335165760), (1242, 538300380), (1245, 178040460), (1246, -335165760), (1249, -178040460), (1262, -1414917600), (1263, 538300380), (1267, -335165760), (1272, -178040460), (1284, 1414917600), (1286, -538300380), (1288, 335165760), (1291, 178040460), (1295, 1414917600), (1298, 335165760), (1301, 178040460), (1305, -1414917600), (1307, -335165760), (1310, -178040460), (1312, -538300380), (1320, 538300380), (1377, -1414917600), (1378, 538300380), (1382, -335165760), (1387, -178040460), (1390, 1414917600), (1392, -538300380), (1394, 335165760), (1397, 178040460), (1403, 1414917600), (1404, -538300380), (1408, 335165760), (1413, 178040460), (1423, -1414917600), (1425, 538300380), (1427, -335165760), (1430, -178040460), (1481, -1414917600), (1483, -335165760), (1486, -178040460), (1489, 1414917600), (1491, 335165760), (1494, 178040460), (1505, 538300380), (1510, -538300380), (1588, 1414917600), (1591, 335165760), (1594, 178040460), (1595, -1414917600), (1597, -335165760), (1600, -178040460), (1603, -1414917600), (1606, -335165760), (1609, -178040460), (1612, 1414917600), (1614, 335165760), (1617, 178040460), (1628, 1414917600), (1630, 335165760), (1633, 178040460), (1636, -1414917600), (1638, -335165760), (1641, -178040460), (1700, -538300380), (1703, 538300380), (1707, 538300380), (1712, -538300380), (1720, -538300380), (1725, 538300380), (2364, 441311760), (2365, 329170860), (2366, 40649664), (2367, -542935920), (2368, -329170860), (2369, 60974496), (2376, 27099776), (2380, -468411536), (2381, -329170860), (2388, -10162416), (2389, -64361968), (2390, 542935920), (2391, 416949756), (2392, -74524384), (2394, 10162416), (2396, -27099776), (2397, 542935920), (2398, 241391964), (2401, 40649664), (2402, -542935920), (2403, -329170860), (2406, -37262192), (2408, 60974496), (2415, 30487248), (2419, -471799008), (2420, -329170860), (2421, -47424608), (2422, 542935920), (2423, 329170860), (2424, -54199552), (2450, -47424608), (2454, 461636592), (2455, 438894480), (2474, 3387472), (2476, 74524384), (2477, -542935920), (2478, -482783928), (2480, 81299328), (2483, -3387472), (2485, 47424608), (2486, -542935920), (2487, -329170860), (2495, -64361968), (2496, 542935920), (2497, 416949756), (2501, 54199552), (2506, -74524384), (2530, -20324832), (2534, 488736368), (2535, 219447240), (2542, 3387472), (2543, 47424608), (2544, -542935920), (2545, -329170860), (2546, 54199552), (2553, 27099776), (2557, -468411536), (2558, -329170860), (2576, -10162416), (2578, -64361968), (2579, 542935920), (2580, 416949756), (2582, -74524384), (2643, -47424608), (2644, 542935920), (2645, 329170860), (2650, 47424608), (2651, -542935920), (2652, -329170860), (2666, -54199552), (2669, 54199552), (2682, -3387472), (2684, 20324832), (2685, -542935920), (2686, -175557792), (2689, -27099776), (2690, 542935920), (2691, 241391964), (2694, 10162416), (2696, -27099776), (2697, 542935920), (2698, 241391964), (2705, 40649664), (2706, -542935920), (2707, -329170860), (2721, 47424608), (2722, -542935920), (2723, -329170860), (2728, -47424608), (2729, 542935920), (2730, 329170860), (2753, 27099776), (2755, -37262192), (2757, -37262192), (2762, 60974496), (2768, 54199552), (2771, -54199552)]

def node21 : Integer.Sparse (Fin 2886) := [(210, 244567500), (211, 459300060), (212, -244567500), (213, -459300060), (221, -244567500), (222, -459300060), (228, 244567500), (229, 581780076), (232, 244567500), (233, 336820044), (237, -244567500), (238, -459300060), (267, -244567500), (268, -459300060), (269, 244567500), (270, 459300060), (280, 244567500), (281, 612400080), (288, -244567500), (289, -673640088), (292, -244567500), (293, -459300060), (298, 244567500), (299, 581780076), (343, 244567500), (344, 306200040), (353, -244567500), (354, -459300060), (363, -244567500), (364, -459300060), (373, 244567500), (374, 581780076), (411, 244567500), (412, 459300060), (417, -244567500), (418, -459300060), (499, -244567500), (500, -244960032), (504, 244567500), (505, 336820044), (508, 244567500), (509, 336820044), (514, -244567500), (515, -459300060), (525, -244567500), (526, -459300060), (531, 244567500), (532, 459300060), (1149, -1414917600), (1153, 1414917600), (1158, -1125047100), (1159, -178040460), (1162, 1110487440), (1163, 178040460), (1164, 14559660), (1168, 1414917600), (1177, 1125047100), (1178, 178040460), (1180, -1414917600), (1186, -1110487440), (1187, -178040460), (1188, -14559660), (1191, -1414917600), (1196, -1110487440), (1197, -178040460), (1198, 1414917600), (1202, 1110487440), (1203, 178040460), (1207, -14559660), (1210, 14559660), (1235, 1414917600), (1239, -1414917600), (1244, 1125047100), (1245, 178040460), (1248, -1110487440), (1249, -178040460), (1250, -14559660), (1262, -1414917600), (1271, -1125047100), (1272, -178040460), (1284, 1414917600), (1290, 1110487440), (1291, 178040460), (1292, 14559660), (1295, 1414917600), (1300, 1110487440), (1301, 178040460), (1305, -1414917600), (1309, -1110487440), (1310, -178040460), (1314, 14559660), (1322, -14559660), (1377, -1414917600), (1386, -1125047100), (1387, -178040460), (1390, 1414917600), (1396, 1110487440), (1397, 178040460), (1398, 14559660), (1403, 1414917600), (1412, 1125047100), (1413, 178040460), (1423, -1414917600), (1429, -1110487440), (1430, -178040460), (1431, -14559660), (1481, -1414917600), (1485, -1110487440), (1486, -178040460), (1489, 1414917600), (1493, 1110487440), (1494, 178040460), (1507, -14559660), (1512, 14559660), (1588, 1414917600), (1593, 1110487440), (1594, 178040460), (1595, -1414917600), (1599, -1110487440), (1600, -178040460), (1603, -1414917600), (1608, -1110487440), (1609, -178040460), (1612, 1414917600), (1616, 1110487440), (1617, 178040460), (1628, 1414917600), (1632, 1110487440), (1633, 178040460), (1636, -1414917600), (1640, -1110487440), (1641, -178040460), (1702, 14559660), (1705, -14559660), (1709, -14559660), (1714, 14559660), (1722, 14559660), (1727, -14559660), (2356, 5205239400), (2357, -2273707740), (2359, -5205239400), (2361, 2273707740), (2364, 542935920), (2367, -542935920), (2372, -5205239400), (2373, 2273707740), (2380, -542935920), (2384, 7634351120), (2385, -2273707740), (2390, 542935920), (2393, 2776127680), (2395, -2273707740), (2397, 542935920), (2399, -5205239400), (2400, 2273707740), (2402, -542935920), (2411, -5205239400), (2412, 2273707740), (2414, 5205239400), (2416, -2273707740), (2419, -542935920), (2422, 542935920), (2446, 6593303240), (2447, -2273707740), (2454, 542935920), (2470, -7981367080), (2471, 2273707740), (2477, -542935920), (2482, -4858223440), (2484, 2273707740), (2486, -542935920), (2493, 6940319200), (2494, -2273707740), (2496, 542935920), (2526, 3817175560), (2527, -2273707740), (2534, 542935920), (2538, -5552255360), (2539, 2273707740), (2544, -542935920), (2549, -5205239400), (2550, 2273707740), (2557, -542935920), (2572, 7634351120), (2573, -2273707740), (2579, 542935920), (2641, 5205239400), (2642, -2273707740), (2644, 542935920), (2648, -5205239400), (2649, 2273707740), (2651, -542935920), (2681, -2429111720), (2683, 2273707740), (2685, -542935920), (2687, 3470159600), (2688, -2273707740), (2690, 542935920), (2693, 2776127680), (2695, -2273707740), (2697, 542935920), (2703, -5205239400), (2704, 2273707740), (2706, -542935920), (2719, -5205239400), (2720, 2273707740), (2722, -542935920), (2726, 5205239400), (2727, -2273707740), (2729, 542935920)]

def node22 : Integer.Sparse (Fin 2886) := [(210, 244567500), (211, 459300060), (212, -244567500), (213, -459300060), (221, -244567500), (222, -459300060), (228, 244567500), (229, 581780076), (232, 244567500), (233, 336820044), (237, -244567500), (238, -459300060), (267, -244567500), (268, -459300060), (269, 244567500), (270, 459300060), (280, 244567500), (281, 612400080), (288, -244567500), (289, -673640088), (292, -244567500), (293, -459300060), (298, 244567500), (299, 581780076), (343, 244567500), (344, 306200040), (353, -244567500), (354, -459300060), (363, -244567500), (364, -459300060), (373, 244567500), (374, 581780076), (411, 244567500), (412, 459300060), (417, -244567500), (418, -459300060), (499, -244567500), (500, -244960032), (504, 244567500), (505, 336820044), (508, 244567500), (509, 336820044), (514, -244567500), (515, -459300060), (525, -244567500), (526, -459300060), (531, 244567500), (532, 459300060), (1149, -1414917600), (1150, 538300380), (1153, 1414917600), (1156, -538300380), (1158, -1139606760), (1159, -178040460), (1162, 1110487440), (1163, 178040460), (1164, 29119320), (1168, 1414917600), (1169, -538300380), (1177, 1139606760), (1178, 178040460), (1180, -1414917600), (1182, 538300380), (1186, -1110487440), (1187, -178040460), (1188, -29119320), (1191, -1414917600), (1196, -1110487440), (1197, -178040460), (1198, 1414917600), (1202, 1110487440), (1203, 178040460), (1205, 538300380), (1207, -29119320), (1208, -538300380), (1210, 29119320), (1235, 1414917600), (1236, -538300380), (1239, -1414917600), (1242, 538300380), (1244, 1139606760), (1245, 178040460), (1248, -1110487440), (1249, -178040460), (1250, -29119320), (1262, -1414917600), (1263, 538300380), (1271, -1139606760), (1272, -178040460), (1284, 1414917600), (1286, -538300380), (1290, 1110487440), (1291, 178040460), (1292, 29119320), (1295, 1414917600), (1300, 1110487440), (1301, 178040460), (1305, -1414917600), (1309, -1110487440), (1310, -178040460), (1312, -538300380), (1314, 29119320), (1320, 538300380), (1322, -29119320), (1377, -1414917600), (1378, 538300380), (1386, -1139606760), (1387, -178040460), (1390, 1414917600), (1392, -538300380), (1396, 1110487440), (1397, 178040460), (1398, 29119320), (1403, 1414917600), (1404, -538300380), (1412, 1139606760), (1413, 178040460), (1423, -1414917600), (1425, 538300380), (1429, -1110487440), (1430, -178040460), (1431, -29119320), (1481, -1414917600), (1485, -1110487440), (1486, -178040460), (1489, 1414917600), (1493, 1110487440), (1494, 178040460), (1505, 538300380), (1507, -29119320), (1510, -538300380), (1512, 29119320), (1588, 1414917600), (1593, 1110487440), (1594, 178040460), (1595, -1414917600), (1599, -1110487440), (1600, -178040460), (1603, -1414917600), (1608, -1110487440), (1609, -178040460), (1612, 1414917600), (1616, 1110487440), (1617, 178040460), (1628, 1414917600), (1632, 1110487440), (1633, 178040460), (1636, -1414917600), (1640, -1110487440), (1641, -178040460), (1700, -538300380), (1702, 29119320), (1703, 538300380), (1705, -29119320), (1707, 538300380), (1709, -29119320), (1712, -538300380), (1714, 29119320), (1720, -538300380), (1722, 29119320), (1725, 538300380), (1727, -29119320), (2356, 7452572340), (2357, -4547415480), (2359, -5205239400), (2361, 4547415480), (2362, -2247332940), (2364, 441311760), (2366, 40649664), (2367, -542935920), (2369, 60974496), (2372, -7452572340), (2373, 4547415480), (2376, 27099776), (2380, -468411536), (2384, 7634351120), (2385, -4547415480), (2386, 3296088312), (2388, -10162416), (2389, -64361968), (2390, 542935920), (2392, -74524384), (2393, 2776127680), (2394, 10162416), (2395, -4547415480), (2396, -27099776), (2397, 542935920), (2399, -5205239400), (2400, 4547415480), (2401, 40649664), (2402, -542935920), (2405, 1198577568), (2406, -37262192), (2407, -2247332940), (2408, 60974496), (2411, -7452572340), (2412, 4547415480), (2414, 5205239400), (2415, 30487248), (2416, -4547415480), (2417, 2247332940), (2419, -471799008), (2421, -47424608), (2422, 542935920), (2424, -54199552), (2446, 9439924964), (2447, -4547415480), (2450, -47424608), (2454, 461636592), (2470, -7981367080), (2471, 4547415480), (2472, -3445910508), (2474, 3387472), (2476, 74524384), (2477, -542935920), (2480, 81299328), (2482, -4858223440), (2483, -3387472), (2484, 4547415480), (2485, 47424608), (2486, -542935920), (2493, 6940319200), (2494, -4547415480), (2495, -64361968), (2496, 542935920), (2500, -2097510744), (2501, 54199552), (2505, 2996443920), (2506, -74524384), (2526, 5465219716), (2527, -4547415480), (2530, -20324832), (2534, 488736368), (2538, -5552255360), (2539, 4547415480), (2540, -2397155136), (2542, 3387472), (2543, 47424608), (2544, -542935920), (2546, 54199552), (2549, -7452572340), (2550, 4547415480), (2553, 27099776), (2557, -468411536), (2572, 7634351120), (2573, -4547415480), (2574, 3296088312), (2576, -10162416), (2578, -64361968), (2579, 542935920), (2582, -74524384), (2641, 5205239400), (2642, -4547415480), (2643, -47424608), (2644, 542935920), (2648, -5205239400), (2649, 4547415480), (2650, 47424608), (2651, -542935920), (2665, 2247332940), (2666, -54199552), (2668, -2247332940), (2669, 54199552), (2681, -2429111720), (2682, -3387472), (2683, 4547415480), (2684, 20324832), (2685, -542935920), (2687, 3470159600), (2688, -4547415480), (2689, -27099776), (2690, 542935920), (2693, 2776127680), (2694, 10162416), (2695, -4547415480), (2696, -27099776), (2697, 542935920), (2703, -5205239400), (2704, 4547415480), (2705, 40649664), (2706, -542935920), (2719, -5205239400), (2720, 4547415480), (2721, 47424608), (2722, -542935920), (2726, 5205239400), (2727, -4547415480), (2728, -47424608), (2729, 542935920), (2752, -1048755372), (2753, 27099776), (2754, 1498221960), (2755, -37262192), (2756, 1198577568), (2757, -37262192), (2761, -2247332940), (2762, 60974496), (2767, -2247332940), (2768, 54199552), (2770, 2247332940), (2771, -54199552)]

set_option maxHeartbeats 1000000 in
def node23 : Integer.Sparse (Fin 2886) := [(204, 471419700), (207, -471419700), (210, 489135000), (211, 459300060), (212, -489135000), (213, -459300060), (215, -471419700), (221, -489135000), (222, -459300060), (224, 691415560), (228, 489135000), (229, 581780076), (230, 251423840), (232, 489135000), (233, 336820044), (234, -471419700), (237, -489135000), (238, -459300060), (261, -471419700), (264, 471419700), (267, -489135000), (268, -459300060), (269, 489135000), (270, 459300060), (274, 597131620), (280, 489135000), (281, 612400080), (284, -722843540), (288, -489135000), (289, -673640088), (290, -439991720), (292, -489135000), (293, -459300060), (295, 628559600), (298, 489135000), (299, 581780076), (337, 345707780), (343, 489135000), (344, 306200040), (349, -502847680), (353, -489135000), (354, -459300060), (357, -471419700), (363, -489135000), (364, -459300060), (369, 691415560), (373, 489135000), (374, 581780076), (408, 471419700), (411, 489135000), (412, 459300060), (414, -471419700), (417, -489135000), (418, -459300060), (497, -219995860), (499, -489135000), (500, -244960032), (501, 314279800), (504, 489135000), (505, 336820044), (506, 251423840), (508, 489135000), (509, 336820044), (511, -471419700), (514, -489135000), (515, -459300060), (522, -471419700), (525, -489135000), (526, -459300060), (528, 471419700), (531, 489135000), (532, 459300060), (1149, -2829835200), (1150, 1076600760), (1153, 2829835200), (1154, -335165760), (1156, -1076600760), (1158, -1139606760), (1159, -356080920), (1160, 335165760), (1162, 1110487440), (1163, 356080920), (1164, 29119320), (1168, 2829835200), (1169, -1076600760), (1173, 335165760), (1177, 1139606760), (1178, 356080920), (1180, -2829835200), (1182, 1076600760), (1184, -335165760), (1186, -1110487440), (1187, -356080920), (1188, -29119320), (1191, -2829835200), (1194, -335165760), (1196, -1110487440), (1197, -356080920), (1198, 2829835200), (1200, 335165760), (1202, 1110487440), (1203, 356080920), (1205, 1076600760), (1207, -29119320), (1208, -1076600760), (1210, 29119320), (1235, 2829835200), (1236, -1076600760), (1239, -2829835200), (1240, 335165760), (1242, 1076600760), (1244, 1139606760), (1245, 356080920), (1246, -335165760), (1248, -1110487440), (1249, -356080920), (1250, -29119320), (1262, -2829835200), (1263, 1076600760), (1267, -335165760), (1271, -1139606760), (1272, -356080920), (1284, 2829835200), (1286, -1076600760), (1288, 335165760), (1290, 1110487440), (1291, 356080920), (1292, 29119320), (1295, 2829835200), (1298, 335165760), (1300, 1110487440), (1301, 356080920), (1305, -2829835200), (1307, -335165760), (1309, -1110487440), (1310, -356080920), (1312, -1076600760), (1314, 29119320), (1320, 1076600760), (1322, -29119320), (1377, -2829835200), (1378, 1076600760), (1382, -335165760), (1386, -1139606760), (1387, -356080920), (1390, 2829835200), (1392, -1076600760), (1394, 335165760), (1396, 1110487440), (1397, 356080920), (1398, 29119320), (1403, 2829835200), (1404, -1076600760), (1408, 335165760), (1412, 1139606760), (1413, 356080920), (1423, -2829835200), (1425, 1076600760), (1427, -335165760), (1429, -1110487440), (1430, -356080920), (1431, -29119320), (1481, -2829835200), (1483, -335165760), (1485, -1110487440), (1486, -356080920), (1489, 2829835200), (1491, 335165760), (1493, 1110487440), (1494, 356080920), (1505, 1076600760), (1507, -29119320), (1510, -1076600760), (1512, 29119320), (1588, 2829835200), (1591, 335165760), (1593, 1110487440), (1594, 356080920), (1595, -2829835200), (1597, -335165760), (1599, -1110487440), (1600, -356080920), (1603, -2829835200), (1606, -335165760), (1608, -1110487440), (1609, -356080920), (1612, 2829835200), (1614, 335165760), (1616, 1110487440), (1617, 356080920), (1628, 2829835200), (1630, 335165760), (1632, 1110487440), (1633, 356080920), (1636, -2829835200), (1638, -335165760), (1640, -1110487440), (1641, -356080920), (1700, -1076600760), (1702, 29119320), (1703, 1076600760), (1705, -29119320), (1707, 1076600760), (1709, -29119320), (1712, -1076600760), (1714, 29119320), (1720, -1076600760), (1722, 29119320), (1725, 1076600760), (1727, -29119320), (2356, 7452572340), (2357, -4547415480), (2359, -5205239400), (2361, 4547415480), (2362, -2247332940), (2364, 882623520), (2365, 329170860), (2366, 81299328), (2367, -1085871840), (2368, -329170860), (2369, 121948992), (2372, -7452572340), (2373, 4547415480), (2376, 54199552), (2380, -936823072), (2381, -329170860), (2384, 7634351120), (2385, -4547415480), (2386, 3296088312), (2388, -20324832), (2389, -128723936), (2390, 1085871840), (2391, 416949756), (2392, -149048768), (2393, 2776127680), (2394, 20324832), (2395, -4547415480), (2396, -54199552), (2397, 1085871840), (2398, 241391964), (2399, -5205239400), (2400, 4547415480), (2401, 81299328), (2402, -1085871840), (2403, -329170860), (2405, 1198577568), (2406, -74524384), (2407, -2247332940), (2408, 121948992), (2411, -7452572340), (2412, 4547415480), (2414, 5205239400), (2415, 60974496), (2416, -4547415480), (2417, 2247332940), (2419, -943598016), (2420, -329170860), (2421, -94849216), (2422, 1085871840), (2423, 329170860), (2424, -108399104), (2446, 9439924964), (2447, -4547415480), (2450, -94849216), (2454, 923273184), (2455, 438894480), (2470, -7981367080), (2471, 4547415480), (2472, -3445910508), (2474, 6774944), (2476, 149048768), (2477, -1085871840), (2478, -482783928), (2480, 162598656), (2482, -4858223440), (2483, -6774944), (2484, 4547415480), (2485, 94849216), (2486, -1085871840), (2487, -329170860), (2493, 6940319200), (2494, -4547415480), (2495, -128723936), (2496, 1085871840), (2497, 416949756), (2500, -2097510744), (2501, 108399104), (2505, 2996443920), (2506, -149048768), (2526, 5465219716), (2527, -4547415480), (2530, -40649664), (2534, 977472736), (2535, 219447240), (2538, -5552255360), (2539, 4547415480), (2540, -2397155136), (2542, 6774944), (2543, 94849216), (2544, -1085871840), (2545, -329170860), (2546, 108399104), (2549, -7452572340), (2550, 4547415480), (2553, 54199552), (2557, -936823072), (2558, -329170860), (2572, 7634351120), (2573, -4547415480), (2574, 3296088312), (2576, -20324832), (2578, -128723936), (2579, 1085871840), (2580, 416949756), (2582, -149048768), (2641, 5205239400), (2642, -4547415480), (2643, -94849216), (2644, 1085871840), (2645, 329170860), (2648, -5205239400), (2649, 4547415480), (2650, 94849216), (2651, -1085871840), (2652, -329170860), (2665, 2247332940), (2666, -108399104), (2668, -2247332940), (2669, 108399104), (2681, -2429111720), (2682, -6774944), (2683, 4547415480), (2684, 40649664), (2685, -1085871840), (2686, -175557792), (2687, 3470159600), (2688, -4547415480), (2689, -54199552), (2690, 1085871840), (2691, 241391964), (2693, 2776127680), (2694, 20324832), (2695, -4547415480), (2696, -54199552), (2697, 1085871840), (2698, 241391964), (2703, -5205239400), (2704, 4547415480), (2705, 81299328), (2706, -1085871840), (2707, -329170860), (2719, -5205239400), (2720, 4547415480), (2721, 94849216), (2722, -1085871840), (2723, -329170860), (2726, 5205239400), (2727, -4547415480), (2728, -94849216), (2729, 1085871840), (2730, 329170860), (2752, -1048755372), (2753, 54199552), (2754, 1498221960), (2755, -74524384), (2756, 1198577568), (2757, -74524384), (2761, -2247332940), (2762, 121948992), (2767, -2247332940), (2768, 108399104), (2770, 2247332940), (2771, -108399104)]

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block0

open scoped BigOperators

def rows (i : Fin 5) : Integer.Sparse (Fin 2886) :=
  (#[node3, node7, node11, node15, node19]).getD i.val []

def polynomial : Integer.Sparse (Fin 2886) := node23

end MUB6.Certificate.GramAssembly.Block0

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

def entry_0_0 : Integer.Sparse (Fin 2886) := [(2365, 48), (2368, -48), (2381, -48), (2391, 60), (2398, 36), (2403, -48), (2420, 12), (2423, -12), (2455, -24), (2478, 24), (2487, 12), (2497, -32), (2545, 12), (2558, 12), (2580, -32), (2645, -12), (2652, 24), (2691, 8), (2698, 8), (2707, 72), (2709, -60), (2730, -72), (2739, 84), (2746, 36), (2749, -60)]

def entry_0_1 : Integer.Sparse (Fin 2886) := [(1265, 120), (1294, -120), (1406, -120), (1477, 120), (1602, 120), (1625, -120)]

def entry_0_2 : Integer.Sparse (Fin 2886) := [(2364, 12), (2366, -12), (2380, -12), (2388, 6), (2389, 12), (2392, 6), (2394, -6), (2396, 6), (2401, -12), (2415, -12), (2421, 12), (2450, 72), (2454, 12), (2474, -6), (2476, 48), (2480, -6), (2483, -60), (2485, -12), (2495, -48), (2543, -12), (2553, -72), (2576, 16), (2578, -48), (2607, 18), (2617, -18), (2639, 42), (2643, 12), (2650, 30), (2682, 6), (2684, -6), (2689, 12), (2694, 44), (2696, 12), (2705, 40), (2717, -42), (2721, -12), (2728, -30), (2762, 8), (2768, 18), (2771, -18)]

def entry_0_3 : Integer.Sparse (Fin 2886) := [(902, 120), (910, -120), (977, -120), (993, 120), (1058, 120), (1064, -120)]

def entry_0_4 : Integer.Sparse (Fin 2886) := [(2533, 120), (2541, -120), (2556, -120), (2575, 120), (2606, 120), (2616, -120)]

def entry_0_5 : Integer.Sparse (Fin 2886) := [(1154, 48), (1161, -48), (1173, -48), (1185, 48), (1195, 48), (1201, -48), (1240, 12), (1247, -12), (1267, -12), (1289, 12), (1299, 12), (1308, -12), (1382, -12), (1395, 12), (1408, 12), (1428, -12), (1484, -12), (1492, 12), (1592, 12), (1598, -12), (1604, 60), (1607, -72), (1615, 12), (1626, -60), (1631, 72), (1639, -12), (1649, 60), (1651, -60)]

def entry_0_6 : Integer.Sparse (Fin 2886) := [(2434, 12), (2441, 128), (2443, -72), (2467, -96), (2481, 96), (2504, 48), (2507, -84), (2569, 12), (2583, -12), (2763, 8), (2792, -12), (2796, -8), (2797, -48), (2810, -24), (2814, 72), (2817, 24), (2818, -36), (2847, -12), (2855, 12), (2856, -8)]

def entry_0_7 : Integer.Sparse (Fin 2886) := [(1154, 12), (1161, -12), (1173, -12), (1185, 12), (1195, 12), (1201, -12), (1240, -12), (1247, 12), (1267, 72), (1289, 48), (1296, -60), (1299, -12), (1308, -48), (1382, 12), (1395, -12), (1408, -72), (1428, -48), (1479, 60), (1484, 12), (1492, 48), (1592, -12), (1598, 12), (1604, 60), (1607, 12), (1615, 48), (1626, -60), (1631, -12), (1639, -48)]

def entry_0_8 : Integer.Sparse (Fin 2886) := [(902, 120), (909, -120), (977, -120), (992, 120), (1057, 120), (1063, -120)]

def entry_0_9 : Integer.Sparse (Fin 2886) := [(2365, 12), (2368, -12), (2381, -12), (2391, 18), (2398, 6), (2403, -12), (2420, 48), (2423, -48), (2455, -12), (2478, 18), (2487, 18), (2497, 46), (2499, -42), (2535, -24), (2545, 18), (2558, -12), (2580, 18), (2645, 12), (2652, -42), (2661, 42), (2686, 18), (2691, -22), (2692, -18), (2698, 6), (2707, -12), (2723, -42), (2730, 12), (2739, 42), (2744, 18), (2746, 18), (2749, -60)]

def entry_0_10 : Integer.Sparse (Fin 2886) := [(2130, -12), (2141, 12), (2152, 60), (2158, -72), (2218, -36), (2231, 72), (2255, 12), (2285, -12), (2287, 36), (2292, -48), (2303, -12), (2344, 12), (2353, -12), (2518, 60), (2523, -48), (2594, -84), (2624, 12), (2630, 84), (2663, 48), (2672, -72), (2765, -12), (2774, 12)]

def entry_0_11 : Integer.Sparse (Fin 2886) := [(2518, 120), (2521, -120), (2594, -120), (2627, 120), (2636, 120), (2657, -120)]

def entry_0_12 : Integer.Sparse (Fin 2886) := [(2364, 12), (2367, -12), (2380, -12), (2390, 12), (2397, 12), (2402, -12), (2419, -12), (2422, 12), (2454, 12), (2477, -12), (2486, -12), (2496, 12), (2534, 72), (2542, -60), (2544, -12), (2557, -72), (2576, 60), (2579, 12), (2607, 60), (2617, -60), (2644, 12), (2651, -12), (2685, 48), (2690, -48), (2697, -48), (2706, 48), (2722, 48), (2729, -48)]

def entry_0_13 : Integer.Sparse (Fin 2886) := [(1948, 120), (1952, -120), (2030, -120), (2036, 120), (2078, 120), (2080, -120)]

def entry_0_14 : Integer.Sparse (Fin 2886) := [(2129, 6), (2132, -6), (2143, 14), (2157, 54), (2160, -30), (2191, 56), (2195, -42), (2223, -36), (2233, 30), (2257, -24), (2276, 42), (2289, 24), (2294, -32), (2305, -8), (2307, 18), (2315, -30), (2340, -6), (2343, 6), (2350, -14), (2519, 6), (2522, -30), (2595, -24), (2628, 36), (2637, 30), (2658, -28), (2679, 4), (2680, -18), (2715, -36), (2736, 8), (2738, 42), (2741, 18), (2748, -30)]

def entry_0_15 : Integer.Sparse (Fin 2886) := [(2364, 48), (2366, -18), (2369, -30), (2376, -12), (2380, -36), (2388, 6), (2389, 30), (2392, 36), (2394, -6), (2396, 12), (2401, -18), (2406, 18), (2408, -30), (2419, 12), (2421, -6), (2424, -6), (2454, -12), (2476, 12), (2480, 18), (2483, -12), (2485, 6), (2495, -12), (2501, 6), (2506, -18), (2534, -12), (2542, 12), (2543, 6), (2546, 6), (2553, -12), (2557, 24), (2576, 52), (2578, -12), (2582, -54), (2607, -6), (2617, -36), (2631, 42), (2639, 6), (2643, -6), (2650, 6), (2666, -6), (2669, 30), (2673, -36), (2684, -6), (2689, 6), (2694, 8), (2696, -18), (2705, 4), (2717, -24), (2721, 42), (2742, 18), (2743, -24), (2745, -6), (2762, 8), (2768, 6), (2771, -12), (2775, 6)]

def entry_0_16 : Integer.Sparse (Fin 2886) := [(2364, -24), (2367, 24), (2380, 24), (2390, -24), (2397, -24), (2402, 24), (2419, 24), (2422, -24), (2454, -24), (2477, 24), (2486, 24), (2496, -24), (2534, 96), (2544, -96), (2557, -96), (2579, 96), (2644, 96), (2651, -96), (2685, 24), (2690, -24), (2697, -24), (2706, 24), (2722, 24), (2729, -24)]

def entry_0_17 : Integer.Sparse (Fin 2886) := [(1154, 48), (1160, -48), (1173, -48), (1184, 48), (1194, 48), (1200, -48), (1240, 12), (1246, -12), (1267, -12), (1288, 12), (1298, 12), (1307, -12), (1382, -12), (1394, 12), (1408, 12), (1427, -12), (1483, -12), (1491, 12), (1591, 12), (1597, -12), (1604, 60), (1606, -72), (1614, 12), (1626, -60), (1630, 72), (1638, -12), (1648, 60), (1650, -60)]

def entry_0_18 : Integer.Sparse (Fin 2886) := [(2364, 48), (2367, -48), (2380, -48), (2390, 48), (2397, 48), (2402, -48), (2419, 12), (2422, -12), (2454, -12), (2477, 12), (2486, 12), (2496, -12), (2534, -12), (2544, 12), (2557, 12), (2576, 60), (2579, -72), (2617, -60), (2629, 60), (2644, -12), (2651, 72), (2659, -60), (2685, 12), (2690, -12), (2697, -12), (2706, 12), (2722, 12), (2729, -12)]

def entry_0_19 : Integer.Sparse (Fin 2886) := [(1332, 120), (1336, -120), (1537, -120), (1547, 120), (1671, 120), (1676, -120)]

def entry_0_20 : Integer.Sparse (Fin 2886) := [(2365, 24), (2368, -24), (2381, -24), (2391, 36), (2398, 12), (2403, -24), (2420, -24), (2423, 24), (2455, 36), (2478, 84), (2487, -24), (2497, -96), (2535, 12), (2545, -24), (2558, -24), (2580, -96), (2645, 24), (2652, 60), (2686, -12), (2691, 24), (2698, 24), (2707, 96), (2723, 12), (2730, -96)]

def entryRow0 : Array (Integer.Sparse (Fin 2886)) := #[entry_0_0, entry_0_1, entry_0_2, entry_0_3, entry_0_4, entry_0_5, entry_0_6, entry_0_7, entry_0_8, entry_0_9, entry_0_10, entry_0_11, entry_0_12, entry_0_13, entry_0_14, entry_0_15, entry_0_16, entry_0_17, entry_0_18, entry_0_19, entry_0_20]

def entry_1_0 : Integer.Sparse (Fin 2886) := [(1265, 120), (1294, -120), (1406, -120), (1477, 120), (1602, 120), (1625, -120)]

def entry_1_1 : Integer.Sparse (Fin 2886) := [(203, 120), (214, -120), (260, -120), (273, 144), (335, 96), (355, -120)]

def entry_1_2 : Integer.Sparse (Fin 2886) := [(1148, 120), (1167, -120), (1234, -120), (1261, 120), (1375, 120), (1401, -120)]

def entry_1_3 : Integer.Sparse (Fin 2886) := [(17, 120), (27, -120), (39, -120), (64, 120), (99, 120), (118, -120)]

def entry_1_4 : Integer.Sparse (Fin 2886) := [(1146, 120), (1165, -120), (1232, -120), (1259, 120), (1373, 120), (1399, -120)]

def entry_1_5 : Integer.Sparse (Fin 2886) := [(339, 120), (348, -120), (359, -120), (368, 120), (388, 120), (393, -120)]

def entry_1_6 : Integer.Sparse (Fin 2886) := [(1275, 120), (1315, -120), (1416, -120), (1508, 120), (1710, 120), (1723, -120)]

def entry_1_7 : Integer.Sparse (Fin 2886) := [(206, 120), (217, -120), (263, -120), (276, 120), (339, 120), (359, -120)]

def entry_1_8 : Integer.Sparse (Fin 2886) := [(15, 120), (24, -120), (36, -120), (63, 120), (96, 120), (117, -120)]

def entry_1_9 : Integer.Sparse (Fin 2886) := [(1171, 120), (1190, -120), (1380, -120), (1477, 120), (1587, 120), (1625, -120)]

def entry_1_10 : Integer.Sparse (Fin 2886) := [(1114, 120), (1130, -120), (1361, -120), (1499, 120), (1697, 120), (1715, -120)]

def entry_1_11 : Integer.Sparse (Fin 2886) := [(1113, 120), (1124, -120), (1360, -120), (1469, 120), (1580, 120), (1618, -120)]

def entry_1_12 : Integer.Sparse (Fin 2886) := [(1147, 120), (1166, -120), (1233, -120), (1260, 120), (1374, 120), (1400, -120)]

def entry_1_13 : Integer.Sparse (Fin 2886) := [(660, 120), (661, -120), (739, -120), (740, 120), (822, 120), (823, -120)]

def entry_1_14 : Integer.Sparse (Fin 2886) := [(1118, 120), (1125, -120), (1365, -120), (1470, 120), (1581, 120), (1619, -120)]

def entry_1_15 : Integer.Sparse (Fin 2886) := [(1261, 120), (1311, -120), (1401, -120), (1502, 120), (1706, 120), (1717, -120)]

def entry_1_16 : Integer.Sparse (Fin 2886) := [(1147, 120), (1189, -120), (1233, -120), (1293, 120), (1586, 120), (1601, -120)]

def entry_1_17 : Integer.Sparse (Fin 2886) := [(336, 120), (345, -120), (356, -120), (367, 120), (385, 120), (392, -120)]

def entry_1_18 : Integer.Sparse (Fin 2886) := [(1260, 120), (1293, -120), (1400, -120), (1476, 120), (1601, 120), (1624, -120)]

def entry_1_19 : Integer.Sparse (Fin 2886) := [(242, 120), (251, -120), (304, -120), (320, 120), (450, 120), (470, -120)]

def entry_1_20 : Integer.Sparse (Fin 2886) := [(1152, 120), (1171, -120), (1238, -120), (1265, 120), (1380, 120), (1406, -120)]

def entryRow1 : Array (Integer.Sparse (Fin 2886)) := #[entry_1_0, entry_1_1, entry_1_2, entry_1_3, entry_1_4, entry_1_5, entry_1_6, entry_1_7, entry_1_8, entry_1_9, entry_1_10, entry_1_11, entry_1_12, entry_1_13, entry_1_14, entry_1_15, entry_1_16, entry_1_17, entry_1_18, entry_1_19, entry_1_20]

def entry_2_0 : Integer.Sparse (Fin 2886) := [(2364, 12), (2366, -12), (2380, -12), (2388, 6), (2389, 12), (2392, 6), (2394, -6), (2396, 6), (2401, -12), (2415, -12), (2421, 12), (2450, 72), (2454, 12), (2474, -6), (2476, 48), (2480, -6), (2483, -60), (2485, -12), (2495, -48), (2543, -12), (2553, -72), (2576, 16), (2578, -48), (2607, 18), (2617, -18), (2639, 42), (2643, 12), (2650, 30), (2682, 6), (2684, -6), (2689, 12), (2694, 44), (2696, 12), (2705, 40), (2717, -42), (2721, -12), (2728, -30), (2762, 8), (2768, 18), (2771, -18)]

def entry_2_1 : Integer.Sparse (Fin 2886) := [(1148, 120), (1167, -120), (1234, -120), (1261, 120), (1375, 120), (1401, -120)]

def entry_2_2 : Integer.Sparse (Fin 2886) := [(2356, 48), (2362, 72), (2372, -48), (2378, -60), (2386, -32), (2405, 8), (2407, 12), (2411, -48), (2417, -72), (2446, 60), (2452, 84), (2472, 24), (2505, -24), (2526, 36), (2532, 36), (2540, 24), (2549, -48), (2555, -60), (2574, -32), (2665, -12), (2668, 12), (2756, 8), (2761, 12), (2767, 12), (2770, -12)]

def entry_2_3 : Integer.Sparse (Fin 2886) := [(870, 120), (884, -120), (905, -120), (937, 120), (989, 120), (1016, -120)]

def entry_2_4 : Integer.Sparse (Fin 2886) := [(2358, 120), (2374, -120), (2413, -120), (2448, 120), (2528, 120), (2551, -120)]

def entry_2_5 : Integer.Sparse (Fin 2886) := [(1149, 12), (1157, -12), (1168, -12), (1183, 12), (1206, 12), (1209, -12), (1235, -12), (1243, 12), (1262, 12), (1287, -12), (1313, -12), (1321, 12), (1377, 12), (1385, 60), (1393, -72), (1403, -12), (1411, -60), (1426, 72), (1453, 60), (1461, -60), (1506, 12), (1511, -12), (1701, 48), (1704, -48), (1708, -48), (1713, 48), (1721, 48), (1726, -48)]

def entry_2_6 : Integer.Sparse (Fin 2886) := [(2427, -12), (2439, -8), (2458, 12), (2465, 132), (2502, -12), (2503, -132), (2561, -12), (2568, -132), (2667, 96), (2758, 12), (2759, 116), (2769, -96), (2789, 12), (2798, 8), (2801, -12), (2808, 12), (2815, -12), (2816, 12), (2836, 12), (2845, -12), (2853, 12), (2854, 4), (2879, 24), (2880, -24)]

def entry_2_7 : Integer.Sparse (Fin 2886) := [(1149, 48), (1157, 72), (1168, -48), (1176, -60), (1183, -12), (1206, -12), (1209, 12), (1235, -48), (1243, -72), (1262, 48), (1270, 60), (1287, 12), (1313, 12), (1321, -12), (1377, 48), (1385, 60), (1393, 12), (1403, -48), (1411, -60), (1426, -12), (1506, -12), (1511, 12), (1701, 12), (1704, -12), (1708, -12), (1713, 12), (1721, 12), (1726, -12)]

def entry_2_8 : Integer.Sparse (Fin 2886) := [(869, 120), (883, -120), (904, -120), (936, 120), (988, 120), (1015, -120)]

def entry_2_9 : Integer.Sparse (Fin 2886) := [(2364, -12), (2366, 12), (2376, 72), (2388, -16), (2389, 48), (2394, -44), (2396, -12), (2401, -40), (2408, -8), (2415, -6), (2419, 18), (2421, -6), (2424, -6), (2454, -30), (2474, 36), (2476, 12), (2480, 6), (2483, -6), (2485, 6), (2495, -12), (2501, -18), (2506, 30), (2530, -42), (2534, -12), (2542, 6), (2543, -30), (2546, 6), (2557, 12), (2576, -6), (2578, -12), (2582, -6), (2607, 18), (2617, -18), (2639, 42), (2643, 30), (2650, 12), (2666, 18), (2669, -18), (2682, 24), (2684, 6), (2689, 18), (2694, 6), (2696, -6), (2705, 12), (2717, -42), (2721, -30), (2728, -12)]

def entry_2_10 : Integer.Sparse (Fin 2886) := [(2120, -12), (2126, 36), (2138, -60), (2148, 12), (2154, -36), (2185, 60), (2228, 48), (2251, -48), (2332, 12), (2338, 84), (2352, -60), (2510, -12), (2516, -84), (2662, 72), (2750, 60), (2764, -72)]

def entry_2_11 : Integer.Sparse (Fin 2886) := [(2337, 120), (2347, -120), (2515, -120), (2634, 120), (2676, 120), (2712, -120)]

def entry_2_12 : Integer.Sparse (Fin 2886) := [(2357, 48), (2361, 72), (2373, -48), (2377, -60), (2385, -12), (2395, -12), (2400, 12), (2412, -48), (2416, -72), (2447, 48), (2451, 60), (2471, 12), (2484, 12), (2494, -12), (2527, 48), (2531, 60), (2539, 12), (2550, -48), (2554, -60), (2573, -12), (2642, -12), (2649, 12), (2683, 12), (2688, -12), (2695, -12), (2704, 12), (2720, 12), (2727, -12)]

def entry_2_13 : Integer.Sparse (Fin 2886) := [(1870, 120), (1876, -120), (1949, -120), (1959, 120), (2034, 120), (2042, -120)]

def entry_2_14 : Integer.Sparse (Fin 2886) := [(2128, 12), (2133, 24), (2140, -36), (2144, -36), (2156, -12), (2161, -24), (2187, 36), (2193, 36), (2230, 24), (2234, 24), (2253, -24), (2259, -24), (2336, 48), (2341, 36), (2346, -24), (2348, -24), (2514, -48), (2520, -36), (2633, 36), (2635, 36), (2675, 24), (2677, 24), (2711, -36), (2713, -36)]

def entry_2_15 : Integer.Sparse (Fin 2886) := [(2356, 12), (2362, -12), (2372, -12), (2386, 24), (2407, -12), (2411, -12), (2417, 12), (2446, 18), (2452, 66), (2472, 36), (2500, -72), (2505, -48), (2526, 6), (2532, -6), (2540, -12), (2549, -12), (2555, -60), (2574, -44), (2605, 18), (2615, -18), (2664, 42), (2665, 12), (2668, 30), (2754, 12), (2756, 68), (2761, 48), (2766, -42), (2767, 6), (2770, -48)]

def entry_2_16 : Integer.Sparse (Fin 2886) := [(2357, 24), (2361, 96), (2373, -24), (2385, 24), (2395, -96), (2400, -24), (2412, -24), (2416, -96), (2447, 24), (2471, -24), (2484, 96), (2494, 24), (2527, 24), (2539, -24), (2550, -24), (2573, 24), (2642, 24), (2649, -24), (2683, 96), (2688, 24), (2695, -96), (2704, -24), (2720, -24), (2727, 24)]

def entry_2_17 : Integer.Sparse (Fin 2886) := [(1150, 12), (1156, -12), (1169, -12), (1182, 12), (1205, 12), (1208, -12), (1236, -12), (1242, 12), (1263, 12), (1286, -12), (1312, -12), (1320, 12), (1378, 12), (1384, 60), (1392, -72), (1404, -12), (1410, -60), (1425, 72), (1452, 60), (1460, -60), (1505, 12), (1510, -12), (1700, 48), (1703, -48), (1707, -48), (1712, 48), (1720, 48), (1725, -48)]

def entry_2_18 : Integer.Sparse (Fin 2886) := [(2357, 12), (2361, -12), (2373, -12), (2385, 12), (2395, 12), (2400, -12), (2412, -12), (2416, 12), (2447, 12), (2451, 60), (2471, 48), (2484, -72), (2494, -48), (2527, 12), (2539, -12), (2550, -12), (2554, -60), (2573, -48), (2640, 60), (2642, 12), (2649, 48), (2683, -12), (2688, 12), (2695, 72), (2704, 48), (2718, -60), (2720, -12), (2727, -48)]

def entry_2_19 : Integer.Sparse (Fin 2886) := [(1220, 120), (1228, -120), (1333, -120), (1353, 120), (1544, 120), (1562, -120)]

def entry_2_20 : Integer.Sparse (Fin 2886) := [(2360, 48), (2364, 48), (2366, 16), (2369, 8), (2376, -60), (2380, -36), (2388, -8), (2389, -24), (2392, -24), (2394, 8), (2401, 16), (2408, 8), (2415, -48), (2419, -48), (2421, -12), (2424, -12), (2450, 72), (2454, 60), (2476, 24), (2480, 24), (2483, -12), (2485, 12), (2495, -24), (2501, 12), (2506, -24), (2530, 36), (2534, 24), (2542, 12), (2543, 12), (2546, 12), (2553, -60), (2557, -36), (2576, -8), (2578, -24), (2582, -24), (2643, -12), (2650, 12), (2666, -12), (2669, 12), (2694, 8), (2705, 16), (2721, 12), (2728, -12), (2762, 8), (2768, 12), (2771, -12)]

def entryRow2 : Array (Integer.Sparse (Fin 2886)) := #[entry_2_0, entry_2_1, entry_2_2, entry_2_3, entry_2_4, entry_2_5, entry_2_6, entry_2_7, entry_2_8, entry_2_9, entry_2_10, entry_2_11, entry_2_12, entry_2_13, entry_2_14, entry_2_15, entry_2_16, entry_2_17, entry_2_18, entry_2_19, entry_2_20]

def entry_3_0 : Integer.Sparse (Fin 2886) := [(902, 120), (910, -120), (977, -120), (993, 120), (1058, 120), (1064, -120)]

def entry_3_1 : Integer.Sparse (Fin 2886) := [(17, 120), (27, -120), (39, -120), (64, 120), (99, 120), (118, -120)]

def entry_3_2 : Integer.Sparse (Fin 2886) := [(870, 120), (884, -120), (905, -120), (937, 120), (989, 120), (1016, -120)]

def entry_3_3 : Integer.Sparse (Fin 2886) := [(1, 120), (7, -120), (76, -120), (133, 192), (167, 48), (176, -120)]

def entry_3_4 : Integer.Sparse (Fin 2886) := [(865, 120), (880, -120), (899, -120), (933, 120), (985, 120), (1012, -120)]

def entry_3_5 : Integer.Sparse (Fin 2886) := [(16, 12), (19, -12), (30, 12), (37, 108), (42, -72), (91, -76), (102, 84), (121, 12), (169, 36), (170, -60), (174, -12), (180, -12), (185, 12), (191, -12), (327, 12), (333, -48), (376, -44), (400, 84), (423, 36), (427, -60), (574, -12), (578, 12)]

def entry_3_6 : Integer.Sparse (Fin 2886) := [(916, 120), (922, -120), (1000, -120), (1008, 120), (1103, 120), (1105, -120)]

def entry_3_7 : Integer.Sparse (Fin 2886) := [(16, -12), (19, 36), (30, -60), (37, 12), (42, -36), (66, 60), (102, 48), (121, -48), (180, 12), (185, 84), (191, -60), (327, -12), (333, -84), (423, 72), (569, 60), (574, -72)]

def entry_3_8 : Integer.Sparse (Fin 2886) := [(2, 120), (6, -120), (77, -120), (132, 120), (147, 120), (162, -120)]

def entry_3_9 : Integer.Sparse (Fin 2886) := [(867, 120), (875, -120), (977, -120), (1021, 120), (1058, 120), (1077, -120)]

def entry_3_10 : Integer.Sparse (Fin 2886) := [(843, 120), (851, -120), (951, -120), (1030, 120), (1093, 120), (1110, -120)]

def entry_3_11 : Integer.Sparse (Fin 2886) := [(844, 120), (849, -120), (952, -120), (1028, 120), (1047, 120), (1083, -120)]

def entry_3_12 : Integer.Sparse (Fin 2886) := [(868, 120), (882, -120), (903, -120), (935, 120), (987, 120), (1014, -120)]

def entry_3_13 : Integer.Sparse (Fin 2886) := [(624, 120), (626, -120), (775, -120), (798, 120), (836, 120), (839, -120)]

def entry_3_14 : Integer.Sparse (Fin 2886) := [(848, 120), (855, -120), (956, -120), (1035, 120), (1049, 120), (1085, -120)]

def entry_3_15 : Integer.Sparse (Fin 2886) := [(897, 120), (905, -120), (972, -120), (989, 120), (1097, 120), (1100, -120)]

def entry_3_16 : Integer.Sparse (Fin 2886) := [(864, 120), (882, -120), (898, -120), (935, 120), (1062, 120), (1075, -120)]

def entry_3_17 : Integer.Sparse (Fin 2886) := [(38, 120), (41, -120), (92, -120), (101, 120), (152, 120), (155, -120)]

def entry_3_18 : Integer.Sparse (Fin 2886) := [(898, 120), (903, -120), (973, -120), (987, 120), (1056, 120), (1062, -120)]

def entry_3_19 : Integer.Sparse (Fin 2886) := [(25, 60), (29, -72), (97, -48), (131, 96), (154, 24), (161, -60), (196, 60), (200, -48), (432, -72), (484, 96), (580, 24), (597, -60)]

def entry_3_20 : Integer.Sparse (Fin 2886) := [(875, 120), (888, -120), (910, -120), (942, 120), (993, 120), (1021, -120)]

def entryRow3 : Array (Integer.Sparse (Fin 2886)) := #[entry_3_0, entry_3_1, entry_3_2, entry_3_3, entry_3_4, entry_3_5, entry_3_6, entry_3_7, entry_3_8, entry_3_9, entry_3_10, entry_3_11, entry_3_12, entry_3_13, entry_3_14, entry_3_15, entry_3_16, entry_3_17, entry_3_18, entry_3_19, entry_3_20]

def entry_4_0 : Integer.Sparse (Fin 2886) := [(2533, 120), (2541, -120), (2556, -120), (2575, 120), (2606, 120), (2616, -120)]

def entry_4_1 : Integer.Sparse (Fin 2886) := [(1146, 120), (1165, -120), (1232, -120), (1259, 120), (1373, 120), (1399, -120)]

def entry_4_2 : Integer.Sparse (Fin 2886) := [(2358, 120), (2374, -120), (2413, -120), (2448, 120), (2528, 120), (2551, -120)]

def entry_4_3 : Integer.Sparse (Fin 2886) := [(865, 120), (880, -120), (899, -120), (933, 120), (985, 120), (1012, -120)]

def entry_4_4 : Integer.Sparse (Fin 2886) := [(2354, 120), (2370, -120), (2409, -120), (2444, 144), (2524, 96), (2547, -120)]

def entry_4_5 : Integer.Sparse (Fin 2886) := [(1379, 120), (1389, -120), (1405, -120), (1422, 120), (1449, 120), (1457, -120)]

def entry_4_6 : Integer.Sparse (Fin 2886) := [(2803, 120), (2805, -120), (2838, -120), (2842, 120), (2863, 120), (2865, -120)]

def entry_4_7 : Integer.Sparse (Fin 2886) := [(1151, 120), (1170, -120), (1237, -120), (1264, 120), (1379, 120), (1405, -120)]

def entry_4_8 : Integer.Sparse (Fin 2886) := [(862, 120), (879, -120), (896, -120), (932, 120), (984, 120), (1011, -120)]

def entry_4_9 : Integer.Sparse (Fin 2886) := [(2379, 120), (2387, -120), (2453, -120), (2473, 120), (2606, 120), (2616, -120)]

def entry_4_10 : Integer.Sparse (Fin 2886) := [(2122, 120), (2135, -120), (2150, -120), (2182, 120), (2225, 120), (2248, -120)]

def entry_4_11 : Integer.Sparse (Fin 2886) := [(2119, 120), (2134, -120), (2147, -120), (2181, 120), (2224, 120), (2247, -120)]

def entry_4_12 : Integer.Sparse (Fin 2886) := [(2355, 120), (2371, -120), (2410, -120), (2445, 120), (2525, 120), (2548, -120)]

def entry_4_13 : Integer.Sparse (Fin 2886) := [(1889, 120), (1890, -120), (1974, -120), (1977, 120), (2070, 120), (2073, -120)]

def entry_4_14 : Integer.Sparse (Fin 2886) := [(2127, 120), (2139, -120), (2155, -120), (2186, 120), (2229, 120), (2252, -120)]

def entry_4_15 : Integer.Sparse (Fin 2886) := [(2528, 120), (2537, -120), (2551, -120), (2571, 120), (2602, 120), (2612, -120)]

def entry_4_16 : Integer.Sparse (Fin 2886) := [(2355, 120), (2382, -120), (2410, -120), (2468, 120), (2536, 120), (2570, -120)]

def entry_4_17 : Integer.Sparse (Fin 2886) := [(1376, 120), (1388, -120), (1402, -120), (1421, 120), (1448, 120), (1456, -120)]

def entry_4_18 : Integer.Sparse (Fin 2886) := [(2525, 120), (2536, -120), (2548, -120), (2570, 120), (2601, 120), (2611, -120)]

def entry_4_19 : Integer.Sparse (Fin 2886) := [(1215, 120), (1225, -120), (1327, -120), (1350, 120), (1541, 120), (1559, -120)]

def entry_4_20 : Integer.Sparse (Fin 2886) := [(2363, 120), (2379, -120), (2418, -120), (2453, 120), (2533, 120), (2556, -120)]

def entryRow4 : Array (Integer.Sparse (Fin 2886)) := #[entry_4_0, entry_4_1, entry_4_2, entry_4_3, entry_4_4, entry_4_5, entry_4_6, entry_4_7, entry_4_8, entry_4_9, entry_4_10, entry_4_11, entry_4_12, entry_4_13, entry_4_14, entry_4_15, entry_4_16, entry_4_17, entry_4_18, entry_4_19, entry_4_20]

def entry_5_0 : Integer.Sparse (Fin 2886) := [(1154, 48), (1161, -48), (1173, -48), (1185, 48), (1195, 48), (1201, -48), (1240, 12), (1247, -12), (1267, -12), (1289, 12), (1299, 12), (1308, -12), (1382, -12), (1395, 12), (1408, 12), (1428, -12), (1484, -12), (1492, 12), (1592, 12), (1598, -12), (1604, 60), (1607, -72), (1615, 12), (1626, -60), (1631, 72), (1639, -12), (1649, 60), (1651, -60)]

def entry_5_1 : Integer.Sparse (Fin 2886) := [(339, 120), (348, -120), (359, -120), (368, 120), (388, 120), (393, -120)]

def entry_5_2 : Integer.Sparse (Fin 2886) := [(1149, 12), (1157, -12), (1168, -12), (1183, 12), (1206, 12), (1209, -12), (1235, -12), (1243, 12), (1262, 12), (1287, -12), (1313, -12), (1321, 12), (1377, 12), (1385, 60), (1393, -72), (1403, -12), (1411, -60), (1426, 72), (1453, 60), (1461, -60), (1506, 12), (1511, -12), (1701, 48), (1704, -48), (1708, -48), (1713, 48), (1721, 48), (1726, -48)]

def entry_5_3 : Integer.Sparse (Fin 2886) := [(16, 12), (19, -12), (30, 12), (37, 108), (42, -72), (91, -76), (102, 84), (121, 12), (169, 36), (170, -60), (174, -12), (180, -12), (185, 12), (191, -12), (327, 12), (333, -48), (376, -44), (400, 84), (423, 36), (427, -60), (574, -12), (578, 12)]

def entry_5_4 : Integer.Sparse (Fin 2886) := [(1379, 120), (1389, -120), (1405, -120), (1422, 120), (1449, 120), (1457, -120)]

def entry_5_5 : Integer.Sparse (Fin 2886) := [(204, 48), (209, -48), (215, -48), (227, 72), (239, 24), (240, -48), (261, 12), (266, -12), (274, -32), (279, 12), (287, 24), (301, -24), (337, 8), (342, -12), (352, 24), (357, 72), (362, -60), (372, -32), (382, -60), (391, 72), (395, 12), (424, 48), (425, -72), (572, 8), (573, 12), (575, -12), (576, 24), (577, -12)]

def entry_5_6 : Integer.Sparse (Fin 2886) := [(1252, 120), (1257, -120), (1276, -120), (1282, 120), (1317, 120), (1319, -120)]

def entry_5_7 : Integer.Sparse (Fin 2886) := [(204, 12), (209, -12), (215, -12), (227, 24), (240, -12), (261, -12), (266, 12), (274, 18), (279, 66), (287, 36), (300, -72), (301, -48), (337, 6), (342, -6), (352, -12), (357, -12), (362, -60), (372, -44), (391, 18), (395, -18), (424, 42), (425, 12), (426, 30), (571, 12), (572, 68), (573, 48), (575, -42), (576, 6), (577, -48)]

def entry_5_8 : Integer.Sparse (Fin 2886) := [(328, 120), (332, -120), (377, -120), (399, 120), (404, 120), (421, -120)]

def entry_5_9 : Integer.Sparse (Fin 2886) := [(1154, 12), (1161, -12), (1173, -12), (1185, 12), (1195, 12), (1201, -12), (1240, 48), (1247, -48), (1267, -48), (1289, 48), (1299, 48), (1308, -48), (1382, 12), (1395, -12), (1408, -12), (1428, 12), (1484, 12), (1492, -12), (1589, 60), (1592, -72), (1598, 12), (1607, 12), (1615, -12), (1626, -60), (1631, -12), (1639, 72), (1649, 60), (1653, -60)]

def entry_5_10 : Integer.Sparse (Fin 2886) := [(1362, 120), (1370, -120), (1435, -120), (1466, 120), (1501, 120), (1514, -120)]

def entry_5_11 : Integer.Sparse (Fin 2886) := [(1363, 120), (1368, -120), (1436, -120), (1464, 120), (1473, 120), (1496, -120)]

def entry_5_12 : Integer.Sparse (Fin 2886) := [(1150, 12), (1155, -12), (1169, -12), (1181, 12), (1193, 12), (1199, -12), (1236, -12), (1241, 12), (1263, 12), (1285, -12), (1297, -12), (1306, 12), (1378, 12), (1383, 60), (1391, -72), (1404, -12), (1409, -60), (1424, 72), (1451, 60), (1459, -60), (1482, 12), (1490, -12), (1590, 48), (1596, -48), (1605, -48), (1613, 48), (1629, 48), (1637, -48)]

def entry_5_13 : Integer.Sparse (Fin 2886) := [(715, 120), (716, -120), (782, -120), (786, 120), (837, 120), (838, -120)]

def entry_5_14 : Integer.Sparse (Fin 2886) := [(1367, 60), (1372, -60), (1439, -60), (1468, 60), (1475, 60), (1498, -60), (1582, 60), (1585, -60), (1620, -60), (1644, 60), (1647, 60), (1655, -60)]

def entry_5_15 : Integer.Sparse (Fin 2886) := [(1149, 48), (1157, -48), (1168, -48), (1183, 48), (1206, 48), (1209, -48), (1235, 12), (1243, -12), (1262, -12), (1287, 12), (1313, 12), (1321, -12), (1377, -12), (1393, 12), (1403, 72), (1411, -60), (1426, -12), (1445, -60), (1453, 60), (1504, 60), (1506, -72), (1511, 12), (1701, 12), (1704, -12), (1708, -12), (1713, 12), (1721, 12), (1726, -12)]

def entry_5_16 : Integer.Sparse (Fin 2886) := [(1150, -24), (1155, 24), (1169, 24), (1181, -24), (1193, -24), (1199, 24), (1236, 24), (1241, -24), (1263, -24), (1285, 24), (1297, 24), (1306, -24), (1378, 96), (1391, -96), (1404, -96), (1424, 96), (1482, 96), (1490, -96), (1590, 24), (1596, -24), (1605, -24), (1613, 24), (1629, 24), (1637, -24)]

def entry_5_17 : Integer.Sparse (Fin 2886) := [(205, 48), (208, -48), (216, -48), (226, 48), (231, 48), (236, -48), (262, 12), (265, -12), (275, -12), (286, 12), (291, 12), (297, -12), (338, -12), (351, 12), (358, 72), (361, -60), (371, -12), (383, -60), (390, 60), (407, 60), (410, -72), (416, 12), (498, 12), (503, -12), (507, -12), (513, 12), (524, 12), (530, -12)]

def entry_5_18 : Integer.Sparse (Fin 2886) := [(1150, 48), (1155, -48), (1169, -48), (1181, 48), (1193, 48), (1199, -48), (1236, 12), (1241, -12), (1263, -12), (1285, 12), (1297, 12), (1306, -12), (1378, -12), (1391, 12), (1404, 72), (1409, -60), (1424, -12), (1446, -60), (1451, 60), (1480, 60), (1482, -72), (1490, 12), (1590, 12), (1596, -12), (1605, -12), (1613, 12), (1629, 12), (1637, -12)]

def entry_5_19 : Integer.Sparse (Fin 2886) := [(223, -12), (225, 12), (235, -12), (243, 12), (246, -12), (256, 12), (305, 120), (308, -72), (350, -48), (386, -36), (398, 84), (409, 36), (420, -60), (443, -84), (457, 84), (474, 12), (523, -12), (534, 12), (583, 36), (587, -60), (593, -12)]

def entry_5_20 : Integer.Sparse (Fin 2886) := [(1154, 24), (1161, -24), (1173, -24), (1185, 24), (1195, 24), (1201, -24), (1240, -24), (1247, 24), (1267, 24), (1289, -24), (1299, -24), (1308, 24), (1382, 24), (1395, -24), (1408, -24), (1428, 24), (1484, 24), (1492, -24), (1592, 96), (1598, -96), (1607, -96), (1615, 96), (1631, 96), (1639, -96)]

def entryRow5 : Array (Integer.Sparse (Fin 2886)) := #[entry_5_0, entry_5_1, entry_5_2, entry_5_3, entry_5_4, entry_5_5, entry_5_6, entry_5_7, entry_5_8, entry_5_9, entry_5_10, entry_5_11, entry_5_12, entry_5_13, entry_5_14, entry_5_15, entry_5_16, entry_5_17, entry_5_18, entry_5_19, entry_5_20]

def entry_6_0 : Integer.Sparse (Fin 2886) := [(2434, 12), (2441, 128), (2443, -72), (2467, -96), (2481, 96), (2504, 48), (2507, -84), (2569, 12), (2583, -12), (2763, 8), (2792, -12), (2796, -8), (2797, -48), (2810, -24), (2814, 72), (2817, 24), (2818, -36), (2847, -12), (2855, 12), (2856, -8)]

def entry_6_1 : Integer.Sparse (Fin 2886) := [(1275, 120), (1315, -120), (1416, -120), (1508, 120), (1710, 120), (1723, -120)]

def entry_6_2 : Integer.Sparse (Fin 2886) := [(2427, -12), (2439, -8), (2458, 12), (2465, 132), (2502, -12), (2503, -132), (2561, -12), (2568, -132), (2667, 96), (2758, 12), (2759, 116), (2769, -96), (2789, 12), (2798, 8), (2801, -12), (2808, 12), (2815, -12), (2816, 12), (2836, 12), (2845, -12), (2853, 12), (2854, 4), (2879, 24), (2880, -24)]

def entry_6_3 : Integer.Sparse (Fin 2886) := [(916, 120), (922, -120), (1000, -120), (1008, 120), (1103, 120), (1105, -120)]

def entry_6_4 : Integer.Sparse (Fin 2886) := [(2803, 120), (2805, -120), (2838, -120), (2842, 120), (2863, 120), (2865, -120)]

def entry_6_5 : Integer.Sparse (Fin 2886) := [(1252, 120), (1257, -120), (1276, -120), (1282, 120), (1317, 120), (1319, -120)]

def entry_6_6 : Integer.Sparse (Fin 2886) := [(2821, 120), (2823, -120), (2826, -120), (2829, 144), (2832, 96), (2833, -120)]

def entry_6_7 : Integer.Sparse (Fin 2886) := [(1282, 120), (1319, -120), (1420, -120), (1509, 120), (1711, 120), (1724, -120)]

def entry_6_8 : Integer.Sparse (Fin 2886) := [(917, 120), (921, -120), (1001, -120), (1007, 120), (1102, 120), (1104, -120)]

def entry_6_9 : Integer.Sparse (Fin 2886) := [(2441, 144), (2443, -84), (2467, 12), (2481, -12), (2504, -12), (2507, 24), (2569, -96), (2583, 96), (2760, 48), (2763, -84), (2796, -24), (2797, -36), (2810, -12), (2814, 12), (2817, 12), (2818, -24), (2847, -24), (2852, 72), (2855, 24), (2856, -36)]

def entry_6_10 : Integer.Sparse (Fin 2886) := [(2164, 120), (2169, -96), (2176, 24), (2237, -84), (2244, 96), (2322, 48), (2323, -84), (2781, -24), (2785, -24), (2859, -36), (2869, 72), (2878, 24), (2881, -36)]

def entry_6_11 : Integer.Sparse (Fin 2886) := [(2778, 120), (2780, -120), (2860, -120), (2868, 120), (2872, 120), (2876, -120)]

def entry_6_12 : Integer.Sparse (Fin 2886) := [(2811, 120), (2813, -120), (2848, -120), (2851, 120), (2873, 120), (2874, -120)]

def entry_6_13 : Integer.Sparse (Fin 2886) := [(1955, 120), (1956, -120), (2039, -120), (2040, 120), (2095, 120), (2096, -120)]

def entry_6_14 : Integer.Sparse (Fin 2886) := [(2178, 156), (2180, -96), (2194, 12), (2246, -96), (2260, 96), (2324, 48), (2327, -84), (2783, -36), (2784, -24), (2786, -12), (2871, -24), (2877, 72), (2882, 24), (2885, -36)]

def entry_6_15 : Integer.Sparse (Fin 2886) := [(2427, 72), (2432, -60), (2439, 4), (2458, -84), (2465, 96), (2502, 48), (2503, -84), (2561, 8), (2568, -12), (2759, 8), (2789, 48), (2794, -60), (2798, -4), (2801, -36), (2808, 72), (2815, 24), (2816, -36), (2836, -8), (2853, 12), (2854, -8)]

def entry_6_16 : Integer.Sparse (Fin 2886) := [(2802, 120), (2807, -120), (2837, -120), (2844, 120), (2873, 120), (2874, -120)]

def entry_6_17 : Integer.Sparse (Fin 2886) := [(1253, 120), (1256, -120), (1277, -120), (1281, 120), (1316, 120), (1318, -120)]

def entry_6_18 : Integer.Sparse (Fin 2886) := [(2790, 120), (2793, -120), (2802, -120), (2807, 120), (2811, 120), (2813, -120)]

def entry_6_19 : Integer.Sparse (Fin 2886) := [(1341, 120), (1343, -120), (1553, -120), (1556, 120), (1742, 120), (1743, -120)]

def entry_6_20 : Integer.Sparse (Fin 2886) := [(2441, -16), (2467, 24), (2481, 120), (2504, -24), (2507, -120), (2569, -24), (2583, -120), (2670, 96), (2760, 24), (2763, 104), (2772, -96), (2796, 16), (2810, -24), (2814, 24), (2847, 24), (2852, -24), (2856, 16), (2883, 24), (2884, -24)]

def entryRow6 : Array (Integer.Sparse (Fin 2886)) := #[entry_6_0, entry_6_1, entry_6_2, entry_6_3, entry_6_4, entry_6_5, entry_6_6, entry_6_7, entry_6_8, entry_6_9, entry_6_10, entry_6_11, entry_6_12, entry_6_13, entry_6_14, entry_6_15, entry_6_16, entry_6_17, entry_6_18, entry_6_19, entry_6_20]

def entry_7_0 : Integer.Sparse (Fin 2886) := [(1154, 12), (1161, -12), (1173, -12), (1185, 12), (1195, 12), (1201, -12), (1240, -12), (1247, 12), (1267, 72), (1289, 48), (1296, -60), (1299, -12), (1308, -48), (1382, 12), (1395, -12), (1408, -72), (1428, -48), (1479, 60), (1484, 12), (1492, 48), (1592, -12), (1598, 12), (1604, 60), (1607, 12), (1615, 48), (1626, -60), (1631, -12), (1639, -48)]

def entry_7_1 : Integer.Sparse (Fin 2886) := [(206, 120), (217, -120), (263, -120), (276, 120), (339, 120), (359, -120)]

def entry_7_2 : Integer.Sparse (Fin 2886) := [(1149, 48), (1157, 72), (1168, -48), (1176, -60), (1183, -12), (1206, -12), (1209, 12), (1235, -48), (1243, -72), (1262, 48), (1270, 60), (1287, 12), (1313, 12), (1321, -12), (1377, 48), (1385, 60), (1393, 12), (1403, -48), (1411, -60), (1426, -12), (1506, -12), (1511, 12), (1701, 12), (1704, -12), (1708, -12), (1713, 12), (1721, 12), (1726, -12)]

def entry_7_3 : Integer.Sparse (Fin 2886) := [(16, -12), (19, 36), (30, -60), (37, 12), (42, -36), (66, 60), (102, 48), (121, -48), (180, 12), (185, 84), (191, -60), (327, -12), (333, -84), (423, 72), (569, 60), (574, -72)]

def entry_7_4 : Integer.Sparse (Fin 2886) := [(1151, 120), (1170, -120), (1237, -120), (1264, 120), (1379, 120), (1405, -120)]

def entry_7_5 : Integer.Sparse (Fin 2886) := [(204, 12), (209, -12), (215, -12), (227, 24), (240, -12), (261, -12), (266, 12), (274, 18), (279, 66), (287, 36), (300, -72), (301, -48), (337, 6), (342, -6), (352, -12), (357, -12), (362, -60), (372, -44), (391, 18), (395, -18), (424, 42), (425, 12), (426, 30), (571, 12), (572, 68), (573, 48), (575, -42), (576, 6), (577, -48)]

def entry_7_6 : Integer.Sparse (Fin 2886) := [(1282, 120), (1319, -120), (1420, -120), (1509, 120), (1711, 120), (1724, -120)]

def entry_7_7 : Integer.Sparse (Fin 2886) := [(204, 48), (209, 72), (215, -48), (220, -60), (227, -32), (239, 8), (240, 12), (261, -48), (266, -72), (274, 60), (279, 84), (287, 24), (301, -24), (337, 36), (342, 36), (352, 24), (357, -48), (362, -60), (372, -32), (425, -12), (426, 12), (572, 8), (573, 12), (576, 12), (577, -12)]

def entry_7_8 : Integer.Sparse (Fin 2886) := [(184, 120), (189, -120), (332, -120), (404, 120), (495, 120), (518, -120)]

def entry_7_9 : Integer.Sparse (Fin 2886) := [(1154, -12), (1161, 12), (1173, 72), (1185, 48), (1192, -60), (1195, -12), (1201, -48), (1240, 12), (1247, -12), (1267, -12), (1289, 12), (1299, 12), (1308, -12), (1382, -72), (1395, -48), (1408, 12), (1428, -12), (1479, 60), (1484, 48), (1492, 12), (1589, 60), (1592, 12), (1598, 48), (1607, -12), (1615, 12), (1626, -60), (1631, -48), (1639, -12)]

def entry_7_10 : Integer.Sparse (Fin 2886) := [(1121, 120), (1131, -120), (1370, -120), (1501, 120), (1698, 120), (1716, -120)]

def entry_7_11 : Integer.Sparse (Fin 2886) := [(1120, 120), (1127, -120), (1368, -120), (1473, 120), (1583, 120), (1621, -120)]

def entry_7_12 : Integer.Sparse (Fin 2886) := [(1150, 48), (1155, 72), (1169, -48), (1174, -60), (1181, -12), (1193, -12), (1199, 12), (1236, -48), (1241, -72), (1263, 48), (1268, 60), (1285, 12), (1297, 12), (1306, -12), (1378, 48), (1383, 60), (1391, 12), (1404, -48), (1409, -60), (1424, -12), (1482, -12), (1490, 12), (1590, 12), (1596, -12), (1605, -12), (1613, 12), (1629, 12), (1637, -12)]

def entry_7_13 : Integer.Sparse (Fin 2886) := [(647, 120), (652, -120), (716, -120), (723, 120), (786, 120), (792, -120)]

def entry_7_14 : Integer.Sparse (Fin 2886) := [(1119, 60), (1123, 60), (1126, -60), (1129, -60), (1367, -60), (1372, -60), (1472, 60), (1475, 60), (1582, 60), (1585, 60), (1620, -60), (1623, -60)]

def entry_7_15 : Integer.Sparse (Fin 2886) := [(1149, 12), (1157, -12), (1168, -12), (1183, 12), (1206, 12), (1209, -12), (1235, -12), (1243, 12), (1262, 12), (1270, 60), (1287, 48), (1313, -72), (1321, -48), (1377, 12), (1393, -12), (1403, -12), (1411, -60), (1426, -48), (1504, 60), (1506, 12), (1511, 48), (1701, -12), (1704, 12), (1708, 72), (1713, 48), (1719, -60), (1721, -12), (1726, -48)]

def entry_7_16 : Integer.Sparse (Fin 2886) := [(1150, 24), (1155, 96), (1169, -24), (1181, 24), (1193, -96), (1199, -24), (1236, -24), (1241, -96), (1263, 24), (1285, -24), (1297, 96), (1306, 24), (1378, 24), (1391, -24), (1404, -24), (1424, 24), (1482, 24), (1490, -24), (1590, 96), (1596, 24), (1605, -96), (1613, -24), (1629, -24), (1637, 24)]

def entry_7_17 : Integer.Sparse (Fin 2886) := [(205, 12), (208, -12), (216, -12), (226, 12), (231, 12), (236, -12), (262, -12), (265, 12), (275, 12), (278, 60), (286, 48), (291, -72), (297, -48), (338, 12), (351, -12), (358, -12), (361, -60), (371, -48), (407, 60), (410, 12), (416, 48), (498, -12), (503, 12), (507, 72), (513, 48), (521, -60), (524, -12), (530, -48)]

def entry_7_18 : Integer.Sparse (Fin 2886) := [(1150, 12), (1155, -12), (1169, -12), (1181, 12), (1193, 12), (1199, -12), (1236, -12), (1241, 12), (1263, 12), (1268, 60), (1285, 48), (1297, -72), (1306, -48), (1378, 12), (1391, -12), (1404, -12), (1409, -60), (1424, -48), (1480, 60), (1482, 12), (1490, 48), (1590, -12), (1596, 12), (1605, 72), (1613, 48), (1627, -60), (1629, -12), (1637, -48)]

def entry_7_19 : Integer.Sparse (Fin 2886) := [(223, 12), (225, 128), (235, -108), (243, -12), (246, -8), (256, -12), (305, 12), (308, -36), (324, 60), (346, -12), (350, -84), (409, 72), (457, 48), (474, -48), (502, 60), (523, -72)]

def entry_7_20 : Integer.Sparse (Fin 2886) := [(1154, 96), (1161, 24), (1173, -96), (1185, -24), (1195, -24), (1201, 24), (1240, -96), (1247, -24), (1267, 96), (1289, 24), (1299, 24), (1308, -24), (1382, 96), (1395, 24), (1408, -96), (1428, -24), (1484, -24), (1492, 24), (1592, 24), (1598, -24), (1607, -24), (1615, 24), (1631, 24), (1639, -24)]

def entryRow7 : Array (Integer.Sparse (Fin 2886)) := #[entry_7_0, entry_7_1, entry_7_2, entry_7_3, entry_7_4, entry_7_5, entry_7_6, entry_7_7, entry_7_8, entry_7_9, entry_7_10, entry_7_11, entry_7_12, entry_7_13, entry_7_14, entry_7_15, entry_7_16, entry_7_17, entry_7_18, entry_7_19, entry_7_20]

def entry_8_0 : Integer.Sparse (Fin 2886) := [(902, 120), (909, -120), (977, -120), (992, 120), (1057, 120), (1063, -120)]

def entry_8_1 : Integer.Sparse (Fin 2886) := [(15, 120), (24, -120), (36, -120), (63, 120), (96, 120), (117, -120)]

def entry_8_2 : Integer.Sparse (Fin 2886) := [(869, 120), (883, -120), (904, -120), (936, 120), (988, 120), (1015, -120)]

def entry_8_3 : Integer.Sparse (Fin 2886) := [(2, 120), (6, -120), (77, -120), (132, 120), (147, 120), (162, -120)]

def entry_8_4 : Integer.Sparse (Fin 2886) := [(862, 120), (879, -120), (896, -120), (932, 120), (984, 120), (1011, -120)]

def entry_8_5 : Integer.Sparse (Fin 2886) := [(328, 120), (332, -120), (377, -120), (399, 120), (404, 120), (421, -120)]

def entry_8_6 : Integer.Sparse (Fin 2886) := [(917, 120), (921, -120), (1001, -120), (1007, 120), (1102, 120), (1104, -120)]

def entry_8_7 : Integer.Sparse (Fin 2886) := [(184, 120), (189, -120), (332, -120), (404, 120), (495, 120), (518, -120)]

def entry_8_8 : Integer.Sparse (Fin 2886) := [(1, 120), (4, -120), (76, -120), (130, 192), (145, 48), (160, -120)]

def entry_8_9 : Integer.Sparse (Fin 2886) := [(867, 120), (874, -120), (977, -120), (1020, 120), (1057, 120), (1076, -120)]

def entry_8_10 : Integer.Sparse (Fin 2886) := [(844, 120), (850, -120), (952, -120), (1029, 120), (1092, 120), (1109, -120)]

def entry_8_11 : Integer.Sparse (Fin 2886) := [(843, 120), (847, -120), (951, -120), (1027, 120), (1045, 120), (1082, -120)]

def entry_8_12 : Integer.Sparse (Fin 2886) := [(866, 120), (881, -120), (901, -120), (934, 120), (986, 120), (1013, -120)]

def entry_8_13 : Integer.Sparse (Fin 2886) := [(632, 120), (633, -120), (803, -120), (818, 120), (836, 120), (839, -120)]

def entry_8_14 : Integer.Sparse (Fin 2886) := [(848, 120), (854, -120), (956, -120), (1034, 120), (1048, 120), (1084, -120)]

def entry_8_15 : Integer.Sparse (Fin 2886) := [(898, 120), (904, -120), (973, -120), (988, 120), (1096, 120), (1099, -120)]

def entry_8_16 : Integer.Sparse (Fin 2886) := [(863, 120), (881, -120), (897, -120), (934, 120), (1061, 120), (1074, -120)]

def entry_8_17 : Integer.Sparse (Fin 2886) := [(16, 12), (18, -12), (28, 12), (37, 108), (40, -72), (91, -76), (100, 84), (119, 12), (151, 36), (153, -60), (157, -12), (180, -12), (182, 12), (187, -12), (327, 12), (330, -48), (376, -44), (397, 84), (402, 36), (419, -60), (516, -12), (533, 12)]

def entry_8_18 : Integer.Sparse (Fin 2886) := [(897, 120), (901, -120), (972, -120), (986, 120), (1054, 120), (1061, -120)]

def entry_8_19 : Integer.Sparse (Fin 2886) := [(196, 120), (198, -120), (432, -120), (482, 120), (541, 120), (562, -120)]

def entry_8_20 : Integer.Sparse (Fin 2886) := [(874, 120), (887, -120), (909, -120), (941, 120), (992, 120), (1020, -120)]

def entryRow8 : Array (Integer.Sparse (Fin 2886)) := #[entry_8_0, entry_8_1, entry_8_2, entry_8_3, entry_8_4, entry_8_5, entry_8_6, entry_8_7, entry_8_8, entry_8_9, entry_8_10, entry_8_11, entry_8_12, entry_8_13, entry_8_14, entry_8_15, entry_8_16, entry_8_17, entry_8_18, entry_8_19, entry_8_20]

def entry_9_0 : Integer.Sparse (Fin 2886) := [(2365, 12), (2368, -12), (2381, -12), (2391, 18), (2398, 6), (2403, -12), (2420, 48), (2423, -48), (2455, -12), (2478, 18), (2487, 18), (2497, 46), (2499, -42), (2535, -24), (2545, 18), (2558, -12), (2580, 18), (2645, 12), (2652, -42), (2661, 42), (2686, 18), (2691, -22), (2692, -18), (2698, 6), (2707, -12), (2723, -42), (2730, 12), (2739, 42), (2744, 18), (2746, 18), (2749, -60)]

def entry_9_1 : Integer.Sparse (Fin 2886) := [(1171, 120), (1190, -120), (1380, -120), (1477, 120), (1587, 120), (1625, -120)]

def entry_9_2 : Integer.Sparse (Fin 2886) := [(2364, -12), (2366, 12), (2376, 72), (2388, -16), (2389, 48), (2394, -44), (2396, -12), (2401, -40), (2408, -8), (2415, -6), (2419, 18), (2421, -6), (2424, -6), (2454, -30), (2474, 36), (2476, 12), (2480, 6), (2483, -6), (2485, 6), (2495, -12), (2501, -18), (2506, 30), (2530, -42), (2534, -12), (2542, 6), (2543, -30), (2546, 6), (2557, 12), (2576, -6), (2578, -12), (2582, -6), (2607, 18), (2617, -18), (2639, 42), (2643, 30), (2650, 12), (2666, 18), (2669, -18), (2682, 24), (2684, 6), (2689, 18), (2694, 6), (2696, -6), (2705, 12), (2717, -42), (2721, -30), (2728, -12)]

def entry_9_3 : Integer.Sparse (Fin 2886) := [(867, 120), (875, -120), (977, -120), (1021, 120), (1058, 120), (1077, -120)]

def entry_9_4 : Integer.Sparse (Fin 2886) := [(2379, 120), (2387, -120), (2453, -120), (2473, 120), (2606, 120), (2616, -120)]

def entry_9_5 : Integer.Sparse (Fin 2886) := [(1154, 12), (1161, -12), (1173, -12), (1185, 12), (1195, 12), (1201, -12), (1240, 48), (1247, -48), (1267, -48), (1289, 48), (1299, 48), (1308, -48), (1382, 12), (1395, -12), (1408, -12), (1428, 12), (1484, 12), (1492, -12), (1589, 60), (1592, -72), (1598, 12), (1607, 12), (1615, -12), (1626, -60), (1631, -12), (1639, 72), (1649, 60), (1653, -60)]

def entry_9_6 : Integer.Sparse (Fin 2886) := [(2441, 144), (2443, -84), (2467, 12), (2481, -12), (2504, -12), (2507, 24), (2569, -96), (2583, 96), (2760, 48), (2763, -84), (2796, -24), (2797, -36), (2810, -12), (2814, 12), (2817, 12), (2818, -24), (2847, -24), (2852, 72), (2855, 24), (2856, -36)]

def entry_9_7 : Integer.Sparse (Fin 2886) := [(1154, -12), (1161, 12), (1173, 72), (1185, 48), (1192, -60), (1195, -12), (1201, -48), (1240, 12), (1247, -12), (1267, -12), (1289, 12), (1299, 12), (1308, -12), (1382, -72), (1395, -48), (1408, 12), (1428, -12), (1479, 60), (1484, 48), (1492, 12), (1589, 60), (1592, 12), (1598, 48), (1607, -12), (1615, 12), (1626, -60), (1631, -48), (1639, -12)]

def entry_9_8 : Integer.Sparse (Fin 2886) := [(867, 120), (874, -120), (977, -120), (1020, 120), (1057, 120), (1076, -120)]

def entry_9_9 : Integer.Sparse (Fin 2886) := [(2365, 48), (2368, -48), (2381, 12), (2391, -32), (2398, 8), (2403, 72), (2404, -60), (2420, 12), (2423, -12), (2478, 12), (2497, 16), (2535, -24), (2545, 24), (2558, -48), (2580, 60), (2645, -72), (2661, 84), (2686, 12), (2691, -40), (2698, 36), (2707, -48), (2723, 24), (2730, -12), (2744, 36), (2749, -60)]

def entry_9_10 : Integer.Sparse (Fin 2886) := [(2124, 60), (2130, -72), (2158, -12), (2189, 12), (2218, -36), (2231, 12), (2255, 72), (2285, -12), (2287, 36), (2292, -12), (2303, -48), (2339, 60), (2344, -48), (2523, 12), (2594, -84), (2624, 12), (2630, 84), (2663, -12), (2672, 12), (2751, -12), (2765, 48), (2774, -72)]

def entry_9_11 : Integer.Sparse (Fin 2886) := [(2339, 120), (2342, -120), (2594, -120), (2627, 120), (2714, 120), (2735, -120)]

def entry_9_12 : Integer.Sparse (Fin 2886) := [(2364, -12), (2367, 12), (2380, 72), (2388, -60), (2390, -12), (2397, 48), (2402, -48), (2419, 12), (2422, -12), (2454, -72), (2474, 60), (2477, 12), (2486, -48), (2496, 48), (2534, -12), (2544, 12), (2557, 12), (2579, -12), (2607, 60), (2617, -60), (2644, 48), (2651, -48), (2685, 12), (2690, -12), (2697, -12), (2706, 12), (2722, 12), (2729, -12)]

def entry_9_13 : Integer.Sparse (Fin 2886) := [(1869, 120), (1873, -120), (2030, -120), (2044, 120), (2078, 120), (2083, -120)]

def entry_9_14 : Integer.Sparse (Fin 2886) := [(2129, 54), (2132, -30), (2143, 56), (2145, -42), (2157, 6), (2160, -6), (2191, 14), (2223, -36), (2233, -24), (2257, 30), (2276, 42), (2289, 24), (2294, -8), (2295, 18), (2305, -32), (2315, -30), (2340, 6), (2343, -30), (2350, 4), (2351, -18), (2519, -6), (2522, 6), (2595, -24), (2628, 36), (2637, -36), (2658, 8), (2660, 42), (2679, -14), (2715, 30), (2736, -28), (2741, 18), (2748, -30)]

def entry_9_15 : Integer.Sparse (Fin 2886) := [(2364, 12), (2366, -6), (2369, -6), (2380, -12), (2388, 12), (2389, 12), (2392, 6), (2394, -12), (2396, 6), (2401, -12), (2415, -6), (2419, 54), (2421, -12), (2424, -36), (2450, -12), (2454, 18), (2474, 60), (2476, 30), (2480, -60), (2483, -6), (2485, 12), (2495, -18), (2501, -6), (2506, 18), (2530, -6), (2534, -36), (2542, 6), (2543, -6), (2546, 36), (2557, -12), (2578, 6), (2582, 18), (2607, -6), (2617, -36), (2631, 42), (2639, 6), (2643, 6), (2650, -6), (2666, 6), (2669, -12), (2673, 6), (2684, -12), (2689, -6), (2696, -6), (2705, 6), (2717, -24), (2728, 42), (2742, 18), (2743, -6), (2745, -24), (2753, 18), (2755, -30), (2757, 6), (2762, -18), (2768, -6), (2771, 30), (2775, -36)]

def entry_9_16 : Integer.Sparse (Fin 2886) := [(2364, 24), (2367, -24), (2380, 96), (2390, -96), (2397, 24), (2402, -24), (2419, -24), (2422, 24), (2454, -96), (2477, 96), (2486, -24), (2496, 24), (2534, 24), (2544, -24), (2557, -24), (2579, 24), (2644, 24), (2651, -24), (2685, -24), (2690, 24), (2697, 24), (2706, -24), (2722, 96), (2729, -96)]

def entry_9_17 : Integer.Sparse (Fin 2886) := [(1154, 12), (1160, -12), (1173, -12), (1184, 12), (1194, 12), (1200, -12), (1240, 48), (1246, -48), (1267, -48), (1288, 48), (1298, 48), (1307, -48), (1382, 12), (1394, -12), (1408, -12), (1427, 12), (1483, 12), (1491, -12), (1589, 60), (1591, -72), (1597, 12), (1606, 12), (1614, -12), (1626, -60), (1630, -12), (1638, 72), (1648, 60), (1652, -60)]

def entry_9_18 : Integer.Sparse (Fin 2886) := [(2364, 12), (2367, -12), (2380, -12), (2390, 12), (2397, 12), (2402, -12), (2419, 48), (2422, -48), (2454, 12), (2474, 60), (2477, -72), (2486, -12), (2496, 12), (2534, -48), (2544, 48), (2557, -12), (2579, 12), (2617, -60), (2629, 60), (2644, 12), (2651, -12), (2685, 48), (2690, -48), (2697, 12), (2706, -12), (2722, -12), (2729, 72), (2737, -60)]

def entry_9_19 : Integer.Sparse (Fin 2886) := [(1219, 120), (1222, -120), (1537, -120), (1565, 120), (1671, 120), (1685, -120)]

def entry_9_20 : Integer.Sparse (Fin 2886) := [(2365, -24), (2368, 24), (2381, 24), (2391, 96), (2398, -24), (2403, -96), (2420, 24), (2423, -24), (2455, -24), (2478, 36), (2487, -24), (2497, 36), (2535, -24), (2545, -48), (2558, 24), (2580, -36), (2645, 96), (2652, -12), (2686, 12), (2691, 36), (2698, -12), (2707, 24), (2723, -60), (2730, -24)]

def entryRow9 : Array (Integer.Sparse (Fin 2886)) := #[entry_9_0, entry_9_1, entry_9_2, entry_9_3, entry_9_4, entry_9_5, entry_9_6, entry_9_7, entry_9_8, entry_9_9, entry_9_10, entry_9_11, entry_9_12, entry_9_13, entry_9_14, entry_9_15, entry_9_16, entry_9_17, entry_9_18, entry_9_19, entry_9_20]

def entry_10_0 : Integer.Sparse (Fin 2886) := [(2130, -12), (2141, 12), (2152, 60), (2158, -72), (2218, -36), (2231, 72), (2255, 12), (2285, -12), (2287, 36), (2292, -48), (2303, -12), (2344, 12), (2353, -12), (2518, 60), (2523, -48), (2594, -84), (2624, 12), (2630, 84), (2663, 48), (2672, -72), (2765, -12), (2774, 12)]

def entry_10_1 : Integer.Sparse (Fin 2886) := [(1114, 120), (1130, -120), (1361, -120), (1499, 120), (1697, 120), (1715, -120)]

def entry_10_2 : Integer.Sparse (Fin 2886) := [(2120, -12), (2126, 36), (2138, -60), (2148, 12), (2154, -36), (2185, 60), (2228, 48), (2251, -48), (2332, 12), (2338, 84), (2352, -60), (2510, -12), (2516, -84), (2662, 72), (2750, 60), (2764, -72)]

def entry_10_3 : Integer.Sparse (Fin 2886) := [(843, 120), (851, -120), (951, -120), (1030, 120), (1093, 120), (1110, -120)]

def entry_10_4 : Integer.Sparse (Fin 2886) := [(2122, 120), (2135, -120), (2150, -120), (2182, 120), (2225, 120), (2248, -120)]

def entry_10_5 : Integer.Sparse (Fin 2886) := [(1362, 120), (1370, -120), (1435, -120), (1466, 120), (1501, 120), (1514, -120)]

def entry_10_6 : Integer.Sparse (Fin 2886) := [(2164, 120), (2169, -96), (2176, 24), (2237, -84), (2244, 96), (2322, 48), (2323, -84), (2781, -24), (2785, -24), (2859, -36), (2869, 72), (2878, 24), (2881, -36)]

def entry_10_7 : Integer.Sparse (Fin 2886) := [(1121, 120), (1131, -120), (1370, -120), (1501, 120), (1698, 120), (1716, -120)]

def entry_10_8 : Integer.Sparse (Fin 2886) := [(844, 120), (850, -120), (952, -120), (1029, 120), (1092, 120), (1109, -120)]

def entry_10_9 : Integer.Sparse (Fin 2886) := [(2124, 60), (2130, -72), (2158, -12), (2189, 12), (2218, -36), (2231, 12), (2255, 72), (2285, -12), (2287, 36), (2292, -12), (2303, -48), (2339, 60), (2344, -48), (2523, 12), (2594, -84), (2624, 12), (2630, 84), (2663, -12), (2672, 12), (2751, -12), (2765, 48), (2774, -72)]

def entry_10_10 : Integer.Sparse (Fin 2886) := [(2103, 120), (2109, -120), (2198, -120), (2265, 192), (2316, 48), (2328, -120)]

def entry_10_11 : Integer.Sparse (Fin 2886) := [(2104, 120), (2108, -120), (2199, -120), (2264, 120), (2279, 120), (2309, -120)]

def entry_10_12 : Integer.Sparse (Fin 2886) := [(2125, 120), (2137, -120), (2153, -120), (2184, 120), (2227, 120), (2250, -120)]

def entry_10_13 : Integer.Sparse (Fin 2886) := [(1791, 120), (1793, -120), (2022, -120), (2047, 120), (2090, 120), (2099, -120)]

def entry_10_14 : Integer.Sparse (Fin 2886) := [(2111, 120), (2113, -44), (2116, -76), (2202, -36), (2206, -84), (2267, 12), (2269, 84), (2273, 96), (2278, -12), (2280, 24), (2310, -48), (2317, 36), (2329, -72)]

def entry_10_15 : Integer.Sparse (Fin 2886) := [(2120, 12), (2126, -12), (2138, 12), (2148, 108), (2154, -72), (2214, -76), (2228, 84), (2251, 12), (2318, 36), (2320, -60), (2325, -12), (2332, -12), (2338, 12), (2352, -12), (2510, 12), (2516, -48), (2586, -44), (2623, 84), (2662, 36), (2671, -60), (2764, -12), (2773, 12)]

def entry_10_16 : Integer.Sparse (Fin 2886) := [(2121, 120), (2137, -120), (2149, -120), (2184, 120), (2291, 120), (2302, -120)]

def entry_10_17 : Integer.Sparse (Fin 2886) := [(1363, 120), (1369, -120), (1436, -120), (1465, 120), (1500, 120), (1513, -120)]

def entry_10_18 : Integer.Sparse (Fin 2886) := [(2149, 120), (2153, -120), (2215, -120), (2227, 120), (2286, 120), (2291, -120)]

def entry_10_19 : Integer.Sparse (Fin 2886) := [(1136, 120), (1141, -120), (1519, -120), (1571, 120), (1731, 120), (1750, -120)]

def entry_10_20 : Integer.Sparse (Fin 2886) := [(2124, -24), (2130, 48), (2141, -60), (2152, 24), (2158, -48), (2189, 60), (2231, 48), (2255, -48), (2339, 24), (2344, 72), (2353, -60), (2518, -24), (2523, -72), (2663, 72), (2751, 60), (2765, -72)]

def entryRow10 : Array (Integer.Sparse (Fin 2886)) := #[entry_10_0, entry_10_1, entry_10_2, entry_10_3, entry_10_4, entry_10_5, entry_10_6, entry_10_7, entry_10_8, entry_10_9, entry_10_10, entry_10_11, entry_10_12, entry_10_13, entry_10_14, entry_10_15, entry_10_16, entry_10_17, entry_10_18, entry_10_19, entry_10_20]

def entry_11_0 : Integer.Sparse (Fin 2886) := [(2518, 120), (2521, -120), (2594, -120), (2627, 120), (2636, 120), (2657, -120)]

def entry_11_1 : Integer.Sparse (Fin 2886) := [(1113, 120), (1124, -120), (1360, -120), (1469, 120), (1580, 120), (1618, -120)]

def entry_11_2 : Integer.Sparse (Fin 2886) := [(2337, 120), (2347, -120), (2515, -120), (2634, 120), (2676, 120), (2712, -120)]

def entry_11_3 : Integer.Sparse (Fin 2886) := [(844, 120), (849, -120), (952, -120), (1028, 120), (1047, 120), (1083, -120)]

def entry_11_4 : Integer.Sparse (Fin 2886) := [(2119, 120), (2134, -120), (2147, -120), (2181, 120), (2224, 120), (2247, -120)]

def entry_11_5 : Integer.Sparse (Fin 2886) := [(1363, 120), (1368, -120), (1436, -120), (1464, 120), (1473, 120), (1496, -120)]

def entry_11_6 : Integer.Sparse (Fin 2886) := [(2778, 120), (2780, -120), (2860, -120), (2868, 120), (2872, 120), (2876, -120)]

def entry_11_7 : Integer.Sparse (Fin 2886) := [(1120, 120), (1127, -120), (1368, -120), (1473, 120), (1583, 120), (1621, -120)]

def entry_11_8 : Integer.Sparse (Fin 2886) := [(843, 120), (847, -120), (951, -120), (1027, 120), (1045, 120), (1082, -120)]

def entry_11_9 : Integer.Sparse (Fin 2886) := [(2339, 120), (2342, -120), (2594, -120), (2627, 120), (2714, 120), (2735, -120)]

def entry_11_10 : Integer.Sparse (Fin 2886) := [(2104, 120), (2108, -120), (2199, -120), (2264, 120), (2279, 120), (2309, -120)]

def entry_11_11 : Integer.Sparse (Fin 2886) := [(2103, 120), (2106, -120), (2198, -120), (2263, 192), (2277, 48), (2308, -120)]

def entry_11_12 : Integer.Sparse (Fin 2886) := [(2120, -12), (2123, 36), (2136, -60), (2148, 12), (2151, -36), (2183, 60), (2226, 48), (2249, -48), (2332, 12), (2335, 84), (2345, -60), (2510, -12), (2513, -84), (2632, 72), (2674, 60), (2710, -72)]

def entry_11_13 : Integer.Sparse (Fin 2886) := [(1799, 120), (1800, -120), (2053, -120), (2067, 120), (2090, 120), (2099, -120)]

def entry_11_14 : Integer.Sparse (Fin 2886) := [(2111, 120), (2114, -120), (2206, -120), (2270, 120), (2281, 120), (2311, -120)]

def entry_11_15 : Integer.Sparse (Fin 2886) := [(2511, 120), (2515, -120), (2587, -120), (2622, 120), (2634, 120), (2655, -120)]

def entry_11_16 : Integer.Sparse (Fin 2886) := [(2120, 84), (2123, -24), (2136, -72), (2148, -84), (2151, 24), (2183, 72), (2226, -24), (2249, 24), (2290, 48), (2301, -48), (2332, 36), (2335, 24), (2345, -48), (2510, -36), (2513, -24), (2632, 24), (2654, 72), (2674, 48), (2710, -24), (2732, -72)]

def entry_11_17 : Integer.Sparse (Fin 2886) := [(1362, 120), (1366, -120), (1435, -120), (1463, 120), (1471, 120), (1495, -120)]

def entry_11_18 : Integer.Sparse (Fin 2886) := [(2120, 12), (2123, -12), (2136, 12), (2148, 108), (2151, -72), (2214, -76), (2226, 84), (2249, 12), (2284, 36), (2290, -60), (2301, -12), (2332, -12), (2335, 12), (2345, -12), (2510, 12), (2513, -48), (2586, -44), (2621, 84), (2632, 36), (2654, -60), (2710, -12), (2732, 12)]

def entry_11_19 : Integer.Sparse (Fin 2886) := [(1136, 120), (1139, -120), (1519, -120), (1570, 120), (1659, 120), (1690, -120)]

def entry_11_20 : Integer.Sparse (Fin 2886) := [(2342, 120), (2349, -120), (2521, -120), (2636, 120), (2678, 120), (2714, -120)]

def entryRow11 : Array (Integer.Sparse (Fin 2886)) := #[entry_11_0, entry_11_1, entry_11_2, entry_11_3, entry_11_4, entry_11_5, entry_11_6, entry_11_7, entry_11_8, entry_11_9, entry_11_10, entry_11_11, entry_11_12, entry_11_13, entry_11_14, entry_11_15, entry_11_16, entry_11_17, entry_11_18, entry_11_19, entry_11_20]

def entry_12_0 : Integer.Sparse (Fin 2886) := [(2364, 12), (2367, -12), (2380, -12), (2390, 12), (2397, 12), (2402, -12), (2419, -12), (2422, 12), (2454, 12), (2477, -12), (2486, -12), (2496, 12), (2534, 72), (2542, -60), (2544, -12), (2557, -72), (2576, 60), (2579, 12), (2607, 60), (2617, -60), (2644, 12), (2651, -12), (2685, 48), (2690, -48), (2697, -48), (2706, 48), (2722, 48), (2729, -48)]

def entry_12_1 : Integer.Sparse (Fin 2886) := [(1147, 120), (1166, -120), (1233, -120), (1260, 120), (1374, 120), (1400, -120)]

def entry_12_2 : Integer.Sparse (Fin 2886) := [(2357, 48), (2361, 72), (2373, -48), (2377, -60), (2385, -12), (2395, -12), (2400, 12), (2412, -48), (2416, -72), (2447, 48), (2451, 60), (2471, 12), (2484, 12), (2494, -12), (2527, 48), (2531, 60), (2539, 12), (2550, -48), (2554, -60), (2573, -12), (2642, -12), (2649, 12), (2683, 12), (2688, -12), (2695, -12), (2704, 12), (2720, 12), (2727, -12)]

def entry_12_3 : Integer.Sparse (Fin 2886) := [(868, 120), (882, -120), (903, -120), (935, 120), (987, 120), (1014, -120)]

def entry_12_4 : Integer.Sparse (Fin 2886) := [(2355, 120), (2371, -120), (2410, -120), (2445, 120), (2525, 120), (2548, -120)]

def entry_12_5 : Integer.Sparse (Fin 2886) := [(1150, 12), (1155, -12), (1169, -12), (1181, 12), (1193, 12), (1199, -12), (1236, -12), (1241, 12), (1263, 12), (1285, -12), (1297, -12), (1306, 12), (1378, 12), (1383, 60), (1391, -72), (1404, -12), (1409, -60), (1424, 72), (1451, 60), (1459, -60), (1482, 12), (1490, -12), (1590, 48), (1596, -48), (1605, -48), (1613, 48), (1629, 48), (1637, -48)]

def entry_12_6 : Integer.Sparse (Fin 2886) := [(2811, 120), (2813, -120), (2848, -120), (2851, 120), (2873, 120), (2874, -120)]

def entry_12_7 : Integer.Sparse (Fin 2886) := [(1150, 48), (1155, 72), (1169, -48), (1174, -60), (1181, -12), (1193, -12), (1199, 12), (1236, -48), (1241, -72), (1263, 48), (1268, 60), (1285, 12), (1297, 12), (1306, -12), (1378, 48), (1383, 60), (1391, 12), (1404, -48), (1409, -60), (1424, -12), (1482, -12), (1490, 12), (1590, 12), (1596, -12), (1605, -12), (1613, 12), (1629, 12), (1637, -12)]

def entry_12_8 : Integer.Sparse (Fin 2886) := [(866, 120), (881, -120), (901, -120), (934, 120), (986, 120), (1013, -120)]

def entry_12_9 : Integer.Sparse (Fin 2886) := [(2364, -12), (2367, 12), (2380, 72), (2388, -60), (2390, -12), (2397, 48), (2402, -48), (2419, 12), (2422, -12), (2454, -72), (2474, 60), (2477, 12), (2486, -48), (2496, 48), (2534, -12), (2544, 12), (2557, 12), (2579, -12), (2607, 60), (2617, -60), (2644, 48), (2651, -48), (2685, 12), (2690, -12), (2697, -12), (2706, 12), (2722, 12), (2729, -12)]

def entry_12_10 : Integer.Sparse (Fin 2886) := [(2125, 120), (2137, -120), (2153, -120), (2184, 120), (2227, 120), (2250, -120)]

def entry_12_11 : Integer.Sparse (Fin 2886) := [(2120, -12), (2123, 36), (2136, -60), (2148, 12), (2151, -36), (2183, 60), (2226, 48), (2249, -48), (2332, 12), (2335, 84), (2345, -60), (2510, -12), (2513, -84), (2632, 72), (2674, 60), (2710, -72)]

def entry_12_12 : Integer.Sparse (Fin 2886) := [(2356, 48), (2359, 72), (2372, -48), (2375, -60), (2384, -32), (2393, 8), (2399, 12), (2411, -48), (2414, -72), (2446, 60), (2449, 84), (2470, 24), (2493, -24), (2526, 36), (2529, 36), (2538, 24), (2549, -48), (2552, -60), (2572, -32), (2641, -12), (2648, 12), (2693, 8), (2703, 12), (2719, 12), (2726, -12)]

def entry_12_13 : Integer.Sparse (Fin 2886) := [(1883, 120), (1886, -120), (1966, -120), (1971, 120), (2059, 120), (2064, -120)]

def entry_12_14 : Integer.Sparse (Fin 2886) := [(2128, 60), (2131, 60), (2140, -60), (2142, -60), (2156, -60), (2159, -60), (2187, 60), (2190, 60), (2230, 60), (2232, 60), (2253, -60), (2256, -60)]

def entry_12_15 : Integer.Sparse (Fin 2886) := [(2357, 12), (2361, -12), (2373, -12), (2385, 12), (2395, 12), (2400, -12), (2412, -12), (2416, 12), (2447, 12), (2471, -12), (2484, -12), (2494, 12), (2527, 12), (2531, 60), (2539, -72), (2550, -12), (2554, -60), (2573, 72), (2604, 60), (2614, -60), (2642, 12), (2649, -12), (2683, 48), (2688, -48), (2695, -48), (2704, 48), (2720, 48), (2727, -48)]

def entry_12_16 : Integer.Sparse (Fin 2886) := [(2356, 24), (2359, 96), (2372, -24), (2384, -12), (2393, -60), (2399, -24), (2411, -24), (2414, -96), (2446, 36), (2470, 36), (2482, 60), (2493, 36), (2526, 12), (2538, 12), (2549, -24), (2572, -12), (2641, 24), (2648, -24), (2681, 36), (2687, 12), (2693, -60), (2703, -24), (2719, -24), (2726, 24)]

def entry_12_17 : Integer.Sparse (Fin 2886) := [(1149, 12), (1153, -12), (1168, -12), (1180, 12), (1191, 12), (1198, -12), (1235, -12), (1239, 12), (1262, 12), (1284, -12), (1295, -12), (1305, 12), (1377, 12), (1381, 60), (1390, -72), (1403, -12), (1407, -60), (1423, 72), (1450, 60), (1458, -60), (1481, 12), (1489, -12), (1588, 48), (1595, -48), (1603, -48), (1612, 48), (1628, 48), (1636, -48)]

def entry_12_18 : Integer.Sparse (Fin 2886) := [(2356, 12), (2359, -12), (2372, -12), (2384, 24), (2399, -12), (2411, -12), (2414, 12), (2446, 18), (2449, 66), (2470, 36), (2482, -72), (2493, -48), (2526, 6), (2529, -6), (2538, -12), (2549, -12), (2552, -60), (2572, -44), (2603, 18), (2613, -18), (2638, 42), (2641, 12), (2648, 30), (2687, 12), (2693, 68), (2703, 48), (2716, -42), (2719, 6), (2726, -48)]

def entry_12_19 : Integer.Sparse (Fin 2886) := [(1218, 120), (1227, -120), (1331, -120), (1352, 120), (1543, 120), (1561, -120)]

def entry_12_20 : Integer.Sparse (Fin 2886) := [(2364, 96), (2367, 24), (2380, -96), (2390, -24), (2397, -24), (2402, 24), (2419, -96), (2422, -24), (2454, 96), (2477, 24), (2486, 24), (2496, -24), (2534, 96), (2544, 24), (2557, -96), (2579, -24), (2644, -24), (2651, 24), (2685, 24), (2690, -24), (2697, -24), (2706, 24), (2722, 24), (2729, -24)]

def entryRow12 : Array (Integer.Sparse (Fin 2886)) := #[entry_12_0, entry_12_1, entry_12_2, entry_12_3, entry_12_4, entry_12_5, entry_12_6, entry_12_7, entry_12_8, entry_12_9, entry_12_10, entry_12_11, entry_12_12, entry_12_13, entry_12_14, entry_12_15, entry_12_16, entry_12_17, entry_12_18, entry_12_19, entry_12_20]

def entry_13_0 : Integer.Sparse (Fin 2886) := [(1948, 120), (1952, -120), (2030, -120), (2036, 120), (2078, 120), (2080, -120)]

def entry_13_1 : Integer.Sparse (Fin 2886) := [(660, 120), (661, -120), (739, -120), (740, 120), (822, 120), (823, -120)]

def entry_13_2 : Integer.Sparse (Fin 2886) := [(1870, 120), (1876, -120), (1949, -120), (1959, 120), (2034, 120), (2042, -120)]

def entry_13_3 : Integer.Sparse (Fin 2886) := [(624, 120), (626, -120), (775, -120), (798, 120), (836, 120), (839, -120)]

def entry_13_4 : Integer.Sparse (Fin 2886) := [(1889, 120), (1890, -120), (1974, -120), (1977, 120), (2070, 120), (2073, -120)]

def entry_13_5 : Integer.Sparse (Fin 2886) := [(715, 120), (716, -120), (782, -120), (786, 120), (837, 120), (838, -120)]

def entry_13_6 : Integer.Sparse (Fin 2886) := [(1955, 120), (1956, -120), (2039, -120), (2040, 120), (2095, 120), (2096, -120)]

def entry_13_7 : Integer.Sparse (Fin 2886) := [(647, 120), (652, -120), (716, -120), (723, 120), (786, 120), (792, -120)]

def entry_13_8 : Integer.Sparse (Fin 2886) := [(632, 120), (633, -120), (803, -120), (818, 120), (836, 120), (839, -120)]

def entry_13_9 : Integer.Sparse (Fin 2886) := [(1869, 120), (1873, -120), (2030, -120), (2044, 120), (2078, 120), (2083, -120)]

def entry_13_10 : Integer.Sparse (Fin 2886) := [(1791, 120), (1793, -120), (2022, -120), (2047, 120), (2090, 120), (2099, -120)]

def entry_13_11 : Integer.Sparse (Fin 2886) := [(1799, 120), (1800, -120), (2053, -120), (2067, 120), (2090, 120), (2099, -120)]

def entry_13_12 : Integer.Sparse (Fin 2886) := [(1883, 120), (1886, -120), (1966, -120), (1971, 120), (2059, 120), (2064, -120)]

def entry_13_13 : Integer.Sparse (Fin 2886) := [(678, 120), (680, -120), (699, -120), (709, 192), (733, 48), (736, -120)]

def entry_13_14 : Integer.Sparse (Fin 2886) := [(1792, 120), (1796, -120), (2023, -120), (2048, 120), (2075, 120), (2086, -120)]

def entry_13_15 : Integer.Sparse (Fin 2886) := [(1947, 120), (1949, -120), (2029, -120), (2034, 120), (2091, 120), (2093, -120)]

def entry_13_16 : Integer.Sparse (Fin 2886) := [(1882, 120), (1886, -120), (1965, -120), (1971, 120), (2093, 120), (2097, -120)]

def entry_13_17 : Integer.Sparse (Fin 2886) := [(728, 120), (729, -120), (806, -120), (808, 120), (837, 120), (838, -120)]

def entry_13_18 : Integer.Sparse (Fin 2886) := [(1965, 120), (1966, -120), (2056, -120), (2059, 120), (2091, 120), (2093, -120)]

def entry_13_19 : Integer.Sparse (Fin 2886) := [(650, 120), (651, -120), (784, -120), (797, 120), (828, 120), (831, -120)]

def entry_13_20 : Integer.Sparse (Fin 2886) := [(1873, 120), (1878, -120), (1952, -120), (1961, 120), (2036, 120), (2044, -120)]

def entryRow13 : Array (Integer.Sparse (Fin 2886)) := #[entry_13_0, entry_13_1, entry_13_2, entry_13_3, entry_13_4, entry_13_5, entry_13_6, entry_13_7, entry_13_8, entry_13_9, entry_13_10, entry_13_11, entry_13_12, entry_13_13, entry_13_14, entry_13_15, entry_13_16, entry_13_17, entry_13_18, entry_13_19, entry_13_20]

def entry_14_0 : Integer.Sparse (Fin 2886) := [(2129, 6), (2132, -6), (2143, 14), (2157, 54), (2160, -30), (2191, 56), (2195, -42), (2223, -36), (2233, 30), (2257, -24), (2276, 42), (2289, 24), (2294, -32), (2305, -8), (2307, 18), (2315, -30), (2340, -6), (2343, 6), (2350, -14), (2519, 6), (2522, -30), (2595, -24), (2628, 36), (2637, 30), (2658, -28), (2679, 4), (2680, -18), (2715, -36), (2736, 8), (2738, 42), (2741, 18), (2748, -30)]

def entry_14_1 : Integer.Sparse (Fin 2886) := [(1118, 120), (1125, -120), (1365, -120), (1470, 120), (1581, 120), (1619, -120)]

def entry_14_2 : Integer.Sparse (Fin 2886) := [(2128, 12), (2133, 24), (2140, -36), (2144, -36), (2156, -12), (2161, -24), (2187, 36), (2193, 36), (2230, 24), (2234, 24), (2253, -24), (2259, -24), (2336, 48), (2341, 36), (2346, -24), (2348, -24), (2514, -48), (2520, -36), (2633, 36), (2635, 36), (2675, 24), (2677, 24), (2711, -36), (2713, -36)]

def entry_14_3 : Integer.Sparse (Fin 2886) := [(848, 120), (855, -120), (956, -120), (1035, 120), (1049, 120), (1085, -120)]

def entry_14_4 : Integer.Sparse (Fin 2886) := [(2127, 120), (2139, -120), (2155, -120), (2186, 120), (2229, 120), (2252, -120)]

def entry_14_5 : Integer.Sparse (Fin 2886) := [(1367, 60), (1372, -60), (1439, -60), (1468, 60), (1475, 60), (1498, -60), (1582, 60), (1585, -60), (1620, -60), (1644, 60), (1647, 60), (1655, -60)]

def entry_14_6 : Integer.Sparse (Fin 2886) := [(2178, 156), (2180, -96), (2194, 12), (2246, -96), (2260, 96), (2324, 48), (2327, -84), (2783, -36), (2784, -24), (2786, -12), (2871, -24), (2877, 72), (2882, 24), (2885, -36)]

def entry_14_7 : Integer.Sparse (Fin 2886) := [(1119, 60), (1123, 60), (1126, -60), (1129, -60), (1367, -60), (1372, -60), (1472, 60), (1475, 60), (1582, 60), (1585, 60), (1620, -60), (1623, -60)]

def entry_14_8 : Integer.Sparse (Fin 2886) := [(848, 120), (854, -120), (956, -120), (1034, 120), (1048, 120), (1084, -120)]

def entry_14_9 : Integer.Sparse (Fin 2886) := [(2129, 54), (2132, -30), (2143, 56), (2145, -42), (2157, 6), (2160, -6), (2191, 14), (2223, -36), (2233, -24), (2257, 30), (2276, 42), (2289, 24), (2294, -8), (2295, 18), (2305, -32), (2315, -30), (2340, 6), (2343, -30), (2350, 4), (2351, -18), (2519, -6), (2522, 6), (2595, -24), (2628, 36), (2637, -36), (2658, 8), (2660, 42), (2679, -14), (2715, 30), (2736, -28), (2741, 18), (2748, -30)]

def entry_14_10 : Integer.Sparse (Fin 2886) := [(2111, 120), (2113, -44), (2116, -76), (2202, -36), (2206, -84), (2267, 12), (2269, 84), (2273, 96), (2278, -12), (2280, 24), (2310, -48), (2317, 36), (2329, -72)]

def entry_14_11 : Integer.Sparse (Fin 2886) := [(2111, 120), (2114, -120), (2206, -120), (2270, 120), (2281, 120), (2311, -120)]

def entry_14_12 : Integer.Sparse (Fin 2886) := [(2128, 60), (2131, 60), (2140, -60), (2142, -60), (2156, -60), (2159, -60), (2187, 60), (2190, 60), (2230, 60), (2232, 60), (2253, -60), (2256, -60)]

def entry_14_13 : Integer.Sparse (Fin 2886) := [(1792, 120), (1796, -120), (2023, -120), (2048, 120), (2075, 120), (2086, -120)]

def entry_14_14 : Integer.Sparse (Fin 2886) := [(2112, 60), (2117, -60), (2207, -60), (2210, -60), (2271, 88), (2275, 84), (2282, 32), (2283, 36), (2312, -60), (2314, -60)]

def entry_14_15 : Integer.Sparse (Fin 2886) := [(2133, -6), (2140, 12), (2144, 6), (2156, 72), (2161, -42), (2187, 60), (2193, -42), (2222, -48), (2234, 42), (2253, -36), (2259, 6), (2274, 48), (2319, 24), (2321, -36), (2326, 12), (2330, -36), (2341, 6), (2346, -12), (2348, -6), (2514, -12), (2520, -18), (2590, -12), (2626, 36), (2635, 18), (2656, -24), (2677, -18), (2711, -24), (2713, -6), (2734, 48), (2740, 12), (2747, -24)]

def entry_14_16 : Integer.Sparse (Fin 2886) := [(2128, 120), (2142, -120), (2156, -120), (2190, 120), (2293, 120), (2304, -120)]

def entry_14_17 : Integer.Sparse (Fin 2886) := [(1367, 60), (1371, -60), (1439, -60), (1467, 60), (1474, 60), (1497, -60), (1582, 60), (1584, -60), (1620, -60), (1643, 60), (1646, 60), (1654, -60)]

def entry_14_18 : Integer.Sparse (Fin 2886) := [(2156, 60), (2159, -60), (2187, 60), (2190, -60), (2222, -60), (2232, 60), (2253, -60), (2272, 60), (2288, 60), (2293, -60), (2304, 60), (2313, -60)]

def entry_14_19 : Integer.Sparse (Fin 2886) := [(1140, 120), (1143, -120), (1523, -120), (1575, 120), (1662, 120), (1692, -120)]

def entry_14_20 : Integer.Sparse (Fin 2886) := [(2129, -12), (2132, 48), (2143, -72), (2157, 12), (2160, -48), (2191, 72), (2233, 48), (2257, -48), (2340, 12), (2343, 72), (2350, -48), (2519, -12), (2522, -72), (2637, 72), (2679, 48), (2715, -72)]

def entryRow14 : Array (Integer.Sparse (Fin 2886)) := #[entry_14_0, entry_14_1, entry_14_2, entry_14_3, entry_14_4, entry_14_5, entry_14_6, entry_14_7, entry_14_8, entry_14_9, entry_14_10, entry_14_11, entry_14_12, entry_14_13, entry_14_14, entry_14_15, entry_14_16, entry_14_17, entry_14_18, entry_14_19, entry_14_20]

def entry_15_0 : Integer.Sparse (Fin 2886) := [(2364, 48), (2366, -18), (2369, -30), (2376, -12), (2380, -36), (2388, 6), (2389, 30), (2392, 36), (2394, -6), (2396, 12), (2401, -18), (2406, 18), (2408, -30), (2419, 12), (2421, -6), (2424, -6), (2454, -12), (2476, 12), (2480, 18), (2483, -12), (2485, 6), (2495, -12), (2501, 6), (2506, -18), (2534, -12), (2542, 12), (2543, 6), (2546, 6), (2553, -12), (2557, 24), (2576, 52), (2578, -12), (2582, -54), (2607, -6), (2617, -36), (2631, 42), (2639, 6), (2643, -6), (2650, 6), (2666, -6), (2669, 30), (2673, -36), (2684, -6), (2689, 6), (2694, 8), (2696, -18), (2705, 4), (2717, -24), (2721, 42), (2742, 18), (2743, -24), (2745, -6), (2762, 8), (2768, 6), (2771, -12), (2775, 6)]

def entry_15_1 : Integer.Sparse (Fin 2886) := [(1261, 120), (1311, -120), (1401, -120), (1502, 120), (1706, 120), (1717, -120)]

def entry_15_2 : Integer.Sparse (Fin 2886) := [(2356, 12), (2362, -12), (2372, -12), (2386, 24), (2407, -12), (2411, -12), (2417, 12), (2446, 18), (2452, 66), (2472, 36), (2500, -72), (2505, -48), (2526, 6), (2532, -6), (2540, -12), (2549, -12), (2555, -60), (2574, -44), (2605, 18), (2615, -18), (2664, 42), (2665, 12), (2668, 30), (2754, 12), (2756, 68), (2761, 48), (2766, -42), (2767, 6), (2770, -48)]

def entry_15_3 : Integer.Sparse (Fin 2886) := [(897, 120), (905, -120), (972, -120), (989, 120), (1097, 120), (1100, -120)]

def entry_15_4 : Integer.Sparse (Fin 2886) := [(2528, 120), (2537, -120), (2551, -120), (2571, 120), (2602, 120), (2612, -120)]

def entry_15_5 : Integer.Sparse (Fin 2886) := [(1149, 48), (1157, -48), (1168, -48), (1183, 48), (1206, 48), (1209, -48), (1235, 12), (1243, -12), (1262, -12), (1287, 12), (1313, 12), (1321, -12), (1377, -12), (1393, 12), (1403, 72), (1411, -60), (1426, -12), (1445, -60), (1453, 60), (1504, 60), (1506, -72), (1511, 12), (1701, 12), (1704, -12), (1708, -12), (1713, 12), (1721, 12), (1726, -12)]

def entry_15_6 : Integer.Sparse (Fin 2886) := [(2427, 72), (2432, -60), (2439, 4), (2458, -84), (2465, 96), (2502, 48), (2503, -84), (2561, 8), (2568, -12), (2759, 8), (2789, 48), (2794, -60), (2798, -4), (2801, -36), (2808, 72), (2815, 24), (2816, -36), (2836, -8), (2853, 12), (2854, -8)]

def entry_15_7 : Integer.Sparse (Fin 2886) := [(1149, 12), (1157, -12), (1168, -12), (1183, 12), (1206, 12), (1209, -12), (1235, -12), (1243, 12), (1262, 12), (1270, 60), (1287, 48), (1313, -72), (1321, -48), (1377, 12), (1393, -12), (1403, -12), (1411, -60), (1426, -48), (1504, 60), (1506, 12), (1511, 48), (1701, -12), (1704, 12), (1708, 72), (1713, 48), (1719, -60), (1721, -12), (1726, -48)]

def entry_15_8 : Integer.Sparse (Fin 2886) := [(898, 120), (904, -120), (973, -120), (988, 120), (1096, 120), (1099, -120)]

def entry_15_9 : Integer.Sparse (Fin 2886) := [(2364, 12), (2366, -6), (2369, -6), (2380, -12), (2388, 12), (2389, 12), (2392, 6), (2394, -12), (2396, 6), (2401, -12), (2415, -6), (2419, 54), (2421, -12), (2424, -36), (2450, -12), (2454, 18), (2474, 60), (2476, 30), (2480, -60), (2483, -6), (2485, 12), (2495, -18), (2501, -6), (2506, 18), (2530, -6), (2534, -36), (2542, 6), (2543, -6), (2546, 36), (2557, -12), (2578, 6), (2582, 18), (2607, -6), (2617, -36), (2631, 42), (2639, 6), (2643, 6), (2650, -6), (2666, 6), (2669, -12), (2673, 6), (2684, -12), (2689, -6), (2696, -6), (2705, 6), (2717, -24), (2728, 42), (2742, 18), (2743, -6), (2745, -24), (2753, 18), (2755, -30), (2757, 6), (2762, -18), (2768, -6), (2771, 30), (2775, -36)]

def entry_15_10 : Integer.Sparse (Fin 2886) := [(2120, 12), (2126, -12), (2138, 12), (2148, 108), (2154, -72), (2214, -76), (2228, 84), (2251, 12), (2318, 36), (2320, -60), (2325, -12), (2332, -12), (2338, 12), (2352, -12), (2510, 12), (2516, -48), (2586, -44), (2623, 84), (2662, 36), (2671, -60), (2764, -12), (2773, 12)]

def entry_15_11 : Integer.Sparse (Fin 2886) := [(2511, 120), (2515, -120), (2587, -120), (2622, 120), (2634, 120), (2655, -120)]

def entry_15_12 : Integer.Sparse (Fin 2886) := [(2357, 12), (2361, -12), (2373, -12), (2385, 12), (2395, 12), (2400, -12), (2412, -12), (2416, 12), (2447, 12), (2471, -12), (2484, -12), (2494, 12), (2527, 12), (2531, 60), (2539, -72), (2550, -12), (2554, -60), (2573, 72), (2604, 60), (2614, -60), (2642, 12), (2649, -12), (2683, 48), (2688, -48), (2695, -48), (2704, 48), (2720, 48), (2727, -48)]

def entry_15_13 : Integer.Sparse (Fin 2886) := [(1947, 120), (1949, -120), (2029, -120), (2034, 120), (2091, 120), (2093, -120)]

def entry_15_14 : Integer.Sparse (Fin 2886) := [(2133, -6), (2140, 12), (2144, 6), (2156, 72), (2161, -42), (2187, 60), (2193, -42), (2222, -48), (2234, 42), (2253, -36), (2259, 6), (2274, 48), (2319, 24), (2321, -36), (2326, 12), (2330, -36), (2341, 6), (2346, -12), (2348, -6), (2514, -12), (2520, -18), (2590, -12), (2626, 36), (2635, 18), (2656, -24), (2677, -18), (2711, -24), (2713, -6), (2734, 48), (2740, 12), (2747, -24)]

def entry_15_15 : Integer.Sparse (Fin 2886) := [(2356, 48), (2362, -48), (2372, -48), (2386, 72), (2405, 24), (2407, -48), (2411, 12), (2417, -12), (2446, -32), (2452, 12), (2472, 24), (2505, -24), (2526, 8), (2532, -12), (2540, 24), (2549, 72), (2555, -60), (2574, -32), (2598, -60), (2605, 72), (2615, 12), (2664, 48), (2665, -72), (2756, 8), (2761, 12), (2766, -12), (2767, 24), (2770, -12)]

def entry_15_16 : Integer.Sparse (Fin 2886) := [(2357, -24), (2361, 24), (2373, 24), (2385, -24), (2395, -24), (2400, 24), (2412, 24), (2416, -24), (2447, -24), (2471, 24), (2484, 24), (2494, -24), (2527, 96), (2539, -96), (2550, -96), (2573, 96), (2642, 96), (2649, -96), (2683, 24), (2688, -24), (2695, -24), (2704, 24), (2720, 24), (2727, -24)]

def entry_15_17 : Integer.Sparse (Fin 2886) := [(1150, 48), (1156, -48), (1169, -48), (1182, 48), (1205, 48), (1208, -48), (1236, 12), (1242, -12), (1263, -12), (1286, 12), (1312, 12), (1320, -12), (1378, -12), (1392, 12), (1404, 72), (1410, -60), (1425, -12), (1446, -60), (1452, 60), (1503, 60), (1505, -72), (1510, 12), (1700, 12), (1703, -12), (1707, -12), (1712, 12), (1720, 12), (1725, -12)]

def entry_15_18 : Integer.Sparse (Fin 2886) := [(2357, 48), (2361, -48), (2373, -48), (2385, 48), (2395, 48), (2400, -48), (2412, 12), (2416, -12), (2447, -12), (2471, 12), (2484, 12), (2494, -12), (2527, -12), (2539, 12), (2550, 72), (2554, -60), (2573, -12), (2599, -60), (2604, 60), (2640, 60), (2642, -72), (2649, 12), (2683, 12), (2688, -12), (2695, -12), (2704, 12), (2720, 12), (2727, -12)]

def entry_15_19 : Integer.Sparse (Fin 2886) := [(1328, 120), (1333, -120), (1533, -120), (1544, 120), (1735, 120), (1738, -120)]

def entry_15_20 : Integer.Sparse (Fin 2886) := [(2360, 12), (2364, 12), (2369, -24), (2376, -12), (2380, -12), (2389, 12), (2392, 24), (2406, 12), (2408, -24), (2419, -24), (2424, 24), (2450, 12), (2454, 24), (2476, -12), (2480, 96), (2501, -24), (2506, -96), (2534, 12), (2546, -24), (2557, -24), (2576, -8), (2582, -96), (2666, 24), (2669, 60), (2694, 8), (2705, 16), (2721, 36), (2728, -36), (2753, -12), (2755, 24), (2757, 24), (2762, 80), (2768, -24), (2771, -60)]

def entryRow15 : Array (Integer.Sparse (Fin 2886)) := #[entry_15_0, entry_15_1, entry_15_2, entry_15_3, entry_15_4, entry_15_5, entry_15_6, entry_15_7, entry_15_8, entry_15_9, entry_15_10, entry_15_11, entry_15_12, entry_15_13, entry_15_14, entry_15_15, entry_15_16, entry_15_17, entry_15_18, entry_15_19, entry_15_20]

def entry_16_0 : Integer.Sparse (Fin 2886) := [(2364, -24), (2367, 24), (2380, 24), (2390, -24), (2397, -24), (2402, 24), (2419, 24), (2422, -24), (2454, -24), (2477, 24), (2486, 24), (2496, -24), (2534, 96), (2544, -96), (2557, -96), (2579, 96), (2644, 96), (2651, -96), (2685, 24), (2690, -24), (2697, -24), (2706, 24), (2722, 24), (2729, -24)]

def entry_16_1 : Integer.Sparse (Fin 2886) := [(1147, 120), (1189, -120), (1233, -120), (1293, 120), (1586, 120), (1601, -120)]

def entry_16_2 : Integer.Sparse (Fin 2886) := [(2357, 24), (2361, 96), (2373, -24), (2385, 24), (2395, -96), (2400, -24), (2412, -24), (2416, -96), (2447, 24), (2471, -24), (2484, 96), (2494, 24), (2527, 24), (2539, -24), (2550, -24), (2573, 24), (2642, 24), (2649, -24), (2683, 96), (2688, 24), (2695, -96), (2704, -24), (2720, -24), (2727, 24)]

def entry_16_3 : Integer.Sparse (Fin 2886) := [(864, 120), (882, -120), (898, -120), (935, 120), (1062, 120), (1075, -120)]

def entry_16_4 : Integer.Sparse (Fin 2886) := [(2355, 120), (2382, -120), (2410, -120), (2468, 120), (2536, 120), (2570, -120)]

def entry_16_5 : Integer.Sparse (Fin 2886) := [(1150, -24), (1155, 24), (1169, 24), (1181, -24), (1193, -24), (1199, 24), (1236, 24), (1241, -24), (1263, -24), (1285, 24), (1297, 24), (1306, -24), (1378, 96), (1391, -96), (1404, -96), (1424, 96), (1482, 96), (1490, -96), (1590, 24), (1596, -24), (1605, -24), (1613, 24), (1629, 24), (1637, -24)]

def entry_16_6 : Integer.Sparse (Fin 2886) := [(2802, 120), (2807, -120), (2837, -120), (2844, 120), (2873, 120), (2874, -120)]

def entry_16_7 : Integer.Sparse (Fin 2886) := [(1150, 24), (1155, 96), (1169, -24), (1181, 24), (1193, -96), (1199, -24), (1236, -24), (1241, -96), (1263, 24), (1285, -24), (1297, 96), (1306, 24), (1378, 24), (1391, -24), (1404, -24), (1424, 24), (1482, 24), (1490, -24), (1590, 96), (1596, 24), (1605, -96), (1613, -24), (1629, -24), (1637, 24)]

def entry_16_8 : Integer.Sparse (Fin 2886) := [(863, 120), (881, -120), (897, -120), (934, 120), (1061, 120), (1074, -120)]

def entry_16_9 : Integer.Sparse (Fin 2886) := [(2364, 24), (2367, -24), (2380, 96), (2390, -96), (2397, 24), (2402, -24), (2419, -24), (2422, 24), (2454, -96), (2477, 96), (2486, -24), (2496, 24), (2534, 24), (2544, -24), (2557, -24), (2579, 24), (2644, 24), (2651, -24), (2685, -24), (2690, 24), (2697, 24), (2706, -24), (2722, 96), (2729, -96)]

def entry_16_10 : Integer.Sparse (Fin 2886) := [(2121, 120), (2137, -120), (2149, -120), (2184, 120), (2291, 120), (2302, -120)]

def entry_16_11 : Integer.Sparse (Fin 2886) := [(2120, 84), (2123, -24), (2136, -72), (2148, -84), (2151, 24), (2183, 72), (2226, -24), (2249, 24), (2290, 48), (2301, -48), (2332, 36), (2335, 24), (2345, -48), (2510, -36), (2513, -24), (2632, 24), (2654, 72), (2674, 48), (2710, -24), (2732, -72)]

def entry_16_12 : Integer.Sparse (Fin 2886) := [(2356, 24), (2359, 96), (2372, -24), (2384, -12), (2393, -60), (2399, -24), (2411, -24), (2414, -96), (2446, 36), (2470, 36), (2482, 60), (2493, 36), (2526, 12), (2538, 12), (2549, -24), (2572, -12), (2641, 24), (2648, -24), (2681, 36), (2687, 12), (2693, -60), (2703, -24), (2719, -24), (2726, 24)]

def entry_16_13 : Integer.Sparse (Fin 2886) := [(1882, 120), (1886, -120), (1965, -120), (1971, 120), (2093, 120), (2097, -120)]

def entry_16_14 : Integer.Sparse (Fin 2886) := [(2128, 120), (2142, -120), (2156, -120), (2190, 120), (2293, 120), (2304, -120)]

def entry_16_15 : Integer.Sparse (Fin 2886) := [(2357, -24), (2361, 24), (2373, 24), (2385, -24), (2395, -24), (2400, 24), (2412, 24), (2416, -24), (2447, -24), (2471, 24), (2484, 24), (2494, -24), (2527, 96), (2539, -96), (2550, -96), (2573, 96), (2642, 96), (2649, -96), (2683, 24), (2688, -24), (2695, -24), (2704, 24), (2720, 24), (2727, -24)]

def entry_16_16 : Integer.Sparse (Fin 2886) := [(2356, 72), (2359, 48), (2372, 48), (2393, -96), (2399, -72), (2411, -72), (2414, -48), (2446, -96), (2470, 48), (2482, 96), (2493, 96), (2549, 48), (2641, -48), (2648, 48), (2681, 48), (2687, 48), (2693, -96), (2703, -72), (2719, 48), (2726, -48)]

def entry_16_17 : Integer.Sparse (Fin 2886) := [(1149, -24), (1153, 24), (1168, 24), (1180, -24), (1191, -24), (1198, 24), (1235, 24), (1239, -24), (1262, -24), (1284, 24), (1295, 24), (1305, -24), (1377, 96), (1390, -96), (1403, -96), (1423, 96), (1481, 96), (1489, -96), (1588, 24), (1595, -24), (1603, -24), (1612, 24), (1628, 24), (1636, -24)]

def entry_16_18 : Integer.Sparse (Fin 2886) := [(2356, -24), (2359, 24), (2372, 24), (2384, -24), (2393, -24), (2399, 24), (2411, 24), (2414, -24), (2446, 96), (2449, 12), (2470, 36), (2482, -60), (2493, -36), (2526, -24), (2529, -12), (2538, -12), (2549, -96), (2572, 12), (2603, -12), (2613, 12), (2638, 12), (2641, 96), (2648, -12), (2681, 12), (2687, -12), (2693, 60), (2703, 24), (2716, -12), (2719, -60), (2726, -24)]

def entry_16_19 : Integer.Sparse (Fin 2886) := [(1216, 120), (1227, -120), (1328, -120), (1352, 120), (1674, 120), (1684, -120)]

def entry_16_20 : Integer.Sparse (Fin 2886) := [(2364, 48), (2367, 72), (2380, -48), (2390, 48), (2397, -72), (2402, -48), (2419, -48), (2422, -72), (2454, 48), (2477, -48), (2486, 72), (2496, 48), (2534, 48), (2544, -48), (2557, -48), (2579, 48), (2644, 48), (2651, -48), (2685, 72), (2690, 48), (2697, -72), (2706, -48), (2722, -48), (2729, 48)]

def entryRow16 : Array (Integer.Sparse (Fin 2886)) := #[entry_16_0, entry_16_1, entry_16_2, entry_16_3, entry_16_4, entry_16_5, entry_16_6, entry_16_7, entry_16_8, entry_16_9, entry_16_10, entry_16_11, entry_16_12, entry_16_13, entry_16_14, entry_16_15, entry_16_16, entry_16_17, entry_16_18, entry_16_19, entry_16_20]

def entry_17_0 : Integer.Sparse (Fin 2886) := [(1154, 48), (1160, -48), (1173, -48), (1184, 48), (1194, 48), (1200, -48), (1240, 12), (1246, -12), (1267, -12), (1288, 12), (1298, 12), (1307, -12), (1382, -12), (1394, 12), (1408, 12), (1427, -12), (1483, -12), (1491, 12), (1591, 12), (1597, -12), (1604, 60), (1606, -72), (1614, 12), (1626, -60), (1630, 72), (1638, -12), (1648, 60), (1650, -60)]

def entry_17_1 : Integer.Sparse (Fin 2886) := [(336, 120), (345, -120), (356, -120), (367, 120), (385, 120), (392, -120)]

def entry_17_2 : Integer.Sparse (Fin 2886) := [(1150, 12), (1156, -12), (1169, -12), (1182, 12), (1205, 12), (1208, -12), (1236, -12), (1242, 12), (1263, 12), (1286, -12), (1312, -12), (1320, 12), (1378, 12), (1384, 60), (1392, -72), (1404, -12), (1410, -60), (1425, 72), (1452, 60), (1460, -60), (1505, 12), (1510, -12), (1700, 48), (1703, -48), (1707, -48), (1712, 48), (1720, 48), (1725, -48)]

def entry_17_3 : Integer.Sparse (Fin 2886) := [(38, 120), (41, -120), (92, -120), (101, 120), (152, 120), (155, -120)]

def entry_17_4 : Integer.Sparse (Fin 2886) := [(1376, 120), (1388, -120), (1402, -120), (1421, 120), (1448, 120), (1456, -120)]

def entry_17_5 : Integer.Sparse (Fin 2886) := [(205, 48), (208, -48), (216, -48), (226, 48), (231, 48), (236, -48), (262, 12), (265, -12), (275, -12), (286, 12), (291, 12), (297, -12), (338, -12), (351, 12), (358, 72), (361, -60), (371, -12), (383, -60), (390, 60), (407, 60), (410, -72), (416, 12), (498, 12), (503, -12), (507, -12), (513, 12), (524, 12), (530, -12)]

def entry_17_6 : Integer.Sparse (Fin 2886) := [(1253, 120), (1256, -120), (1277, -120), (1281, 120), (1316, 120), (1318, -120)]

def entry_17_7 : Integer.Sparse (Fin 2886) := [(205, 12), (208, -12), (216, -12), (226, 12), (231, 12), (236, -12), (262, -12), (265, 12), (275, 12), (278, 60), (286, 48), (291, -72), (297, -48), (338, 12), (351, -12), (358, -12), (361, -60), (371, -48), (407, 60), (410, 12), (416, 48), (498, -12), (503, 12), (507, 72), (513, 48), (521, -60), (524, -12), (530, -48)]

def entry_17_8 : Integer.Sparse (Fin 2886) := [(16, 12), (18, -12), (28, 12), (37, 108), (40, -72), (91, -76), (100, 84), (119, 12), (151, 36), (153, -60), (157, -12), (180, -12), (182, 12), (187, -12), (327, 12), (330, -48), (376, -44), (397, 84), (402, 36), (419, -60), (516, -12), (533, 12)]

def entry_17_9 : Integer.Sparse (Fin 2886) := [(1154, 12), (1160, -12), (1173, -12), (1184, 12), (1194, 12), (1200, -12), (1240, 48), (1246, -48), (1267, -48), (1288, 48), (1298, 48), (1307, -48), (1382, 12), (1394, -12), (1408, -12), (1427, 12), (1483, 12), (1491, -12), (1589, 60), (1591, -72), (1597, 12), (1606, 12), (1614, -12), (1626, -60), (1630, -12), (1638, 72), (1648, 60), (1652, -60)]

def entry_17_10 : Integer.Sparse (Fin 2886) := [(1363, 120), (1369, -120), (1436, -120), (1465, 120), (1500, 120), (1513, -120)]

def entry_17_11 : Integer.Sparse (Fin 2886) := [(1362, 120), (1366, -120), (1435, -120), (1463, 120), (1471, 120), (1495, -120)]

def entry_17_12 : Integer.Sparse (Fin 2886) := [(1149, 12), (1153, -12), (1168, -12), (1180, 12), (1191, 12), (1198, -12), (1235, -12), (1239, 12), (1262, 12), (1284, -12), (1295, -12), (1305, 12), (1377, 12), (1381, 60), (1390, -72), (1403, -12), (1407, -60), (1423, 72), (1450, 60), (1458, -60), (1481, 12), (1489, -12), (1588, 48), (1595, -48), (1603, -48), (1612, 48), (1628, 48), (1636, -48)]

def entry_17_13 : Integer.Sparse (Fin 2886) := [(728, 120), (729, -120), (806, -120), (808, 120), (837, 120), (838, -120)]

def entry_17_14 : Integer.Sparse (Fin 2886) := [(1367, 60), (1371, -60), (1439, -60), (1467, 60), (1474, 60), (1497, -60), (1582, 60), (1584, -60), (1620, -60), (1643, 60), (1646, 60), (1654, -60)]

def entry_17_15 : Integer.Sparse (Fin 2886) := [(1150, 48), (1156, -48), (1169, -48), (1182, 48), (1205, 48), (1208, -48), (1236, 12), (1242, -12), (1263, -12), (1286, 12), (1312, 12), (1320, -12), (1378, -12), (1392, 12), (1404, 72), (1410, -60), (1425, -12), (1446, -60), (1452, 60), (1503, 60), (1505, -72), (1510, 12), (1700, 12), (1703, -12), (1707, -12), (1712, 12), (1720, 12), (1725, -12)]

def entry_17_16 : Integer.Sparse (Fin 2886) := [(1149, -24), (1153, 24), (1168, 24), (1180, -24), (1191, -24), (1198, 24), (1235, 24), (1239, -24), (1262, -24), (1284, 24), (1295, 24), (1305, -24), (1377, 96), (1390, -96), (1403, -96), (1423, 96), (1481, 96), (1489, -96), (1588, 24), (1595, -24), (1603, -24), (1612, 24), (1628, 24), (1636, -24)]

def entry_17_17 : Integer.Sparse (Fin 2886) := [(204, 48), (207, -48), (215, -48), (224, 72), (230, 24), (234, -48), (261, 12), (264, -12), (274, -32), (277, 12), (284, 24), (295, -24), (337, 8), (340, -12), (349, 24), (357, 72), (360, -60), (369, -32), (382, -60), (389, 72), (394, 12), (406, 48), (408, -72), (506, 8), (511, 12), (520, -12), (522, 24), (528, -12)]

def entry_17_18 : Integer.Sparse (Fin 2886) := [(1149, 48), (1153, -48), (1168, -48), (1180, 48), (1191, 48), (1198, -48), (1235, 12), (1239, -12), (1262, -12), (1284, 12), (1295, 12), (1305, -12), (1377, -12), (1390, 12), (1403, 72), (1407, -60), (1423, -12), (1445, -60), (1450, 60), (1478, 60), (1481, -72), (1489, 12), (1588, 12), (1595, -12), (1603, -12), (1612, 12), (1628, 12), (1636, -12)]

def entry_17_19 : Integer.Sparse (Fin 2886) := [(305, 120), (307, -120), (443, -120), (455, 120), (549, 120), (551, -120)]

def entry_17_20 : Integer.Sparse (Fin 2886) := [(1154, 24), (1160, -24), (1173, -24), (1184, 24), (1194, 24), (1200, -24), (1240, -24), (1246, 24), (1267, 24), (1288, -24), (1298, -24), (1307, 24), (1382, 24), (1394, -24), (1408, -24), (1427, 24), (1483, 24), (1491, -24), (1591, 96), (1597, -96), (1606, -96), (1614, 96), (1630, 96), (1638, -96)]

def entryRow17 : Array (Integer.Sparse (Fin 2886)) := #[entry_17_0, entry_17_1, entry_17_2, entry_17_3, entry_17_4, entry_17_5, entry_17_6, entry_17_7, entry_17_8, entry_17_9, entry_17_10, entry_17_11, entry_17_12, entry_17_13, entry_17_14, entry_17_15, entry_17_16, entry_17_17, entry_17_18, entry_17_19, entry_17_20]

def entry_18_0 : Integer.Sparse (Fin 2886) := [(2364, 48), (2367, -48), (2380, -48), (2390, 48), (2397, 48), (2402, -48), (2419, 12), (2422, -12), (2454, -12), (2477, 12), (2486, 12), (2496, -12), (2534, -12), (2544, 12), (2557, 12), (2576, 60), (2579, -72), (2617, -60), (2629, 60), (2644, -12), (2651, 72), (2659, -60), (2685, 12), (2690, -12), (2697, -12), (2706, 12), (2722, 12), (2729, -12)]

def entry_18_1 : Integer.Sparse (Fin 2886) := [(1260, 120), (1293, -120), (1400, -120), (1476, 120), (1601, 120), (1624, -120)]

def entry_18_2 : Integer.Sparse (Fin 2886) := [(2357, 12), (2361, -12), (2373, -12), (2385, 12), (2395, 12), (2400, -12), (2412, -12), (2416, 12), (2447, 12), (2451, 60), (2471, 48), (2484, -72), (2494, -48), (2527, 12), (2539, -12), (2550, -12), (2554, -60), (2573, -48), (2640, 60), (2642, 12), (2649, 48), (2683, -12), (2688, 12), (2695, 72), (2704, 48), (2718, -60), (2720, -12), (2727, -48)]

def entry_18_3 : Integer.Sparse (Fin 2886) := [(898, 120), (903, -120), (973, -120), (987, 120), (1056, 120), (1062, -120)]

def entry_18_4 : Integer.Sparse (Fin 2886) := [(2525, 120), (2536, -120), (2548, -120), (2570, 120), (2601, 120), (2611, -120)]

def entry_18_5 : Integer.Sparse (Fin 2886) := [(1150, 48), (1155, -48), (1169, -48), (1181, 48), (1193, 48), (1199, -48), (1236, 12), (1241, -12), (1263, -12), (1285, 12), (1297, 12), (1306, -12), (1378, -12), (1391, 12), (1404, 72), (1409, -60), (1424, -12), (1446, -60), (1451, 60), (1480, 60), (1482, -72), (1490, 12), (1590, 12), (1596, -12), (1605, -12), (1613, 12), (1629, 12), (1637, -12)]

def entry_18_6 : Integer.Sparse (Fin 2886) := [(2790, 120), (2793, -120), (2802, -120), (2807, 120), (2811, 120), (2813, -120)]

def entry_18_7 : Integer.Sparse (Fin 2886) := [(1150, 12), (1155, -12), (1169, -12), (1181, 12), (1193, 12), (1199, -12), (1236, -12), (1241, 12), (1263, 12), (1268, 60), (1285, 48), (1297, -72), (1306, -48), (1378, 12), (1391, -12), (1404, -12), (1409, -60), (1424, -48), (1480, 60), (1482, 12), (1490, 48), (1590, -12), (1596, 12), (1605, 72), (1613, 48), (1627, -60), (1629, -12), (1637, -48)]

def entry_18_8 : Integer.Sparse (Fin 2886) := [(897, 120), (901, -120), (972, -120), (986, 120), (1054, 120), (1061, -120)]

def entry_18_9 : Integer.Sparse (Fin 2886) := [(2364, 12), (2367, -12), (2380, -12), (2390, 12), (2397, 12), (2402, -12), (2419, 48), (2422, -48), (2454, 12), (2474, 60), (2477, -72), (2486, -12), (2496, 12), (2534, -48), (2544, 48), (2557, -12), (2579, 12), (2617, -60), (2629, 60), (2644, 12), (2651, -12), (2685, 48), (2690, -48), (2697, 12), (2706, -12), (2722, -12), (2729, 72), (2737, -60)]

def entry_18_10 : Integer.Sparse (Fin 2886) := [(2149, 120), (2153, -120), (2215, -120), (2227, 120), (2286, 120), (2291, -120)]

def entry_18_11 : Integer.Sparse (Fin 2886) := [(2120, 12), (2123, -12), (2136, 12), (2148, 108), (2151, -72), (2214, -76), (2226, 84), (2249, 12), (2284, 36), (2290, -60), (2301, -12), (2332, -12), (2335, 12), (2345, -12), (2510, 12), (2513, -48), (2586, -44), (2621, 84), (2632, 36), (2654, -60), (2710, -12), (2732, 12)]

def entry_18_12 : Integer.Sparse (Fin 2886) := [(2356, 12), (2359, -12), (2372, -12), (2384, 24), (2399, -12), (2411, -12), (2414, 12), (2446, 18), (2449, 66), (2470, 36), (2482, -72), (2493, -48), (2526, 6), (2529, -6), (2538, -12), (2549, -12), (2552, -60), (2572, -44), (2603, 18), (2613, -18), (2638, 42), (2641, 12), (2648, 30), (2687, 12), (2693, 68), (2703, 48), (2716, -42), (2719, 6), (2726, -48)]

def entry_18_13 : Integer.Sparse (Fin 2886) := [(1965, 120), (1966, -120), (2056, -120), (2059, 120), (2091, 120), (2093, -120)]

def entry_18_14 : Integer.Sparse (Fin 2886) := [(2156, 60), (2159, -60), (2187, 60), (2190, -60), (2222, -60), (2232, 60), (2253, -60), (2272, 60), (2288, 60), (2293, -60), (2304, 60), (2313, -60)]

def entry_18_15 : Integer.Sparse (Fin 2886) := [(2357, 48), (2361, -48), (2373, -48), (2385, 48), (2395, 48), (2400, -48), (2412, 12), (2416, -12), (2447, -12), (2471, 12), (2484, 12), (2494, -12), (2527, -12), (2539, 12), (2550, 72), (2554, -60), (2573, -12), (2599, -60), (2604, 60), (2640, 60), (2642, -72), (2649, 12), (2683, 12), (2688, -12), (2695, -12), (2704, 12), (2720, 12), (2727, -12)]

def entry_18_16 : Integer.Sparse (Fin 2886) := [(2356, -24), (2359, 24), (2372, 24), (2384, -24), (2393, -24), (2399, 24), (2411, 24), (2414, -24), (2446, 96), (2449, 12), (2470, 36), (2482, -60), (2493, -36), (2526, -24), (2529, -12), (2538, -12), (2549, -96), (2572, 12), (2603, -12), (2613, 12), (2638, 12), (2641, 96), (2648, -12), (2681, 12), (2687, -12), (2693, 60), (2703, 24), (2716, -12), (2719, -60), (2726, -24)]

def entry_18_17 : Integer.Sparse (Fin 2886) := [(1149, 48), (1153, -48), (1168, -48), (1180, 48), (1191, 48), (1198, -48), (1235, 12), (1239, -12), (1262, -12), (1284, 12), (1295, 12), (1305, -12), (1377, -12), (1390, 12), (1403, 72), (1407, -60), (1423, -12), (1445, -60), (1450, 60), (1478, 60), (1481, -72), (1489, 12), (1588, 12), (1595, -12), (1603, -12), (1612, 12), (1628, 12), (1636, -12)]

def entry_18_18 : Integer.Sparse (Fin 2886) := [(2356, 48), (2359, -48), (2372, -48), (2384, 72), (2393, 24), (2399, -48), (2411, 12), (2414, -12), (2446, -32), (2449, 12), (2470, 24), (2493, -24), (2526, 8), (2529, -12), (2538, 24), (2549, 72), (2552, -60), (2572, -32), (2598, -60), (2603, 72), (2613, 12), (2638, 48), (2641, -72), (2693, 8), (2703, 12), (2716, -12), (2719, 24), (2726, -12)]

def entry_18_19 : Integer.Sparse (Fin 2886) := [(1328, 120), (1331, -120), (1533, -120), (1543, 120), (1668, 120), (1674, -120)]

def entry_18_20 : Integer.Sparse (Fin 2886) := [(2364, 24), (2367, -24), (2380, -24), (2390, 24), (2397, 24), (2402, -24), (2419, -24), (2422, 24), (2454, 24), (2477, 96), (2486, -24), (2496, -96), (2534, 24), (2544, -24), (2557, -24), (2579, -96), (2644, 24), (2651, 96), (2685, -24), (2690, 24), (2697, 24), (2706, 96), (2722, -24), (2729, -96)]

def entryRow18 : Array (Integer.Sparse (Fin 2886)) := #[entry_18_0, entry_18_1, entry_18_2, entry_18_3, entry_18_4, entry_18_5, entry_18_6, entry_18_7, entry_18_8, entry_18_9, entry_18_10, entry_18_11, entry_18_12, entry_18_13, entry_18_14, entry_18_15, entry_18_16, entry_18_17, entry_18_18, entry_18_19, entry_18_20]

def entry_19_0 : Integer.Sparse (Fin 2886) := [(1332, 120), (1336, -120), (1537, -120), (1547, 120), (1671, 120), (1676, -120)]

def entry_19_1 : Integer.Sparse (Fin 2886) := [(242, 120), (251, -120), (304, -120), (320, 120), (450, 120), (470, -120)]

def entry_19_2 : Integer.Sparse (Fin 2886) := [(1220, 120), (1228, -120), (1333, -120), (1353, 120), (1544, 120), (1562, -120)]

def entry_19_3 : Integer.Sparse (Fin 2886) := [(25, 60), (29, -72), (97, -48), (131, 96), (154, 24), (161, -60), (196, 60), (200, -48), (432, -72), (484, 96), (580, 24), (597, -60)]

def entry_19_4 : Integer.Sparse (Fin 2886) := [(1215, 120), (1225, -120), (1327, -120), (1350, 120), (1541, 120), (1559, -120)]

def entry_19_5 : Integer.Sparse (Fin 2886) := [(223, -12), (225, 12), (235, -12), (243, 12), (246, -12), (256, 12), (305, 120), (308, -72), (350, -48), (386, -36), (398, 84), (409, 36), (420, -60), (443, -84), (457, 84), (474, 12), (523, -12), (534, 12), (583, 36), (587, -60), (593, -12)]

def entry_19_6 : Integer.Sparse (Fin 2886) := [(1341, 120), (1343, -120), (1553, -120), (1556, 120), (1742, 120), (1743, -120)]

def entry_19_7 : Integer.Sparse (Fin 2886) := [(223, 12), (225, 128), (235, -108), (243, -12), (246, -8), (256, -12), (305, 12), (308, -36), (324, 60), (346, -12), (350, -84), (409, 72), (457, 48), (474, -48), (502, 60), (523, -72)]

def entry_19_8 : Integer.Sparse (Fin 2886) := [(196, 120), (198, -120), (432, -120), (482, 120), (541, 120), (562, -120)]

def entry_19_9 : Integer.Sparse (Fin 2886) := [(1219, 120), (1222, -120), (1537, -120), (1565, 120), (1671, 120), (1685, -120)]

def entry_19_10 : Integer.Sparse (Fin 2886) := [(1136, 120), (1141, -120), (1519, -120), (1571, 120), (1731, 120), (1750, -120)]

def entry_19_11 : Integer.Sparse (Fin 2886) := [(1136, 120), (1139, -120), (1519, -120), (1570, 120), (1659, 120), (1690, -120)]

def entry_19_12 : Integer.Sparse (Fin 2886) := [(1218, 120), (1227, -120), (1331, -120), (1352, 120), (1543, 120), (1561, -120)]

def entry_19_13 : Integer.Sparse (Fin 2886) := [(650, 120), (651, -120), (784, -120), (797, 120), (828, 120), (831, -120)]

def entry_19_14 : Integer.Sparse (Fin 2886) := [(1140, 120), (1143, -120), (1523, -120), (1575, 120), (1662, 120), (1692, -120)]

def entry_19_15 : Integer.Sparse (Fin 2886) := [(1328, 120), (1333, -120), (1533, -120), (1544, 120), (1735, 120), (1738, -120)]

def entry_19_16 : Integer.Sparse (Fin 2886) := [(1216, 120), (1227, -120), (1328, -120), (1352, 120), (1674, 120), (1684, -120)]

def entry_19_17 : Integer.Sparse (Fin 2886) := [(305, 120), (307, -120), (443, -120), (455, 120), (549, 120), (551, -120)]

def entry_19_18 : Integer.Sparse (Fin 2886) := [(1328, 120), (1331, -120), (1533, -120), (1543, 120), (1668, 120), (1674, -120)]

def entry_19_19 : Integer.Sparse (Fin 2886) := [(252, 120), (255, -120), (452, -120), (483, 192), (552, 48), (563, -120)]

def entry_19_20 : Integer.Sparse (Fin 2886) := [(1222, 120), (1230, -120), (1336, -120), (1356, 120), (1547, 120), (1565, -120)]

def entryRow19 : Array (Integer.Sparse (Fin 2886)) := #[entry_19_0, entry_19_1, entry_19_2, entry_19_3, entry_19_4, entry_19_5, entry_19_6, entry_19_7, entry_19_8, entry_19_9, entry_19_10, entry_19_11, entry_19_12, entry_19_13, entry_19_14, entry_19_15, entry_19_16, entry_19_17, entry_19_18, entry_19_19, entry_19_20]

def entry_20_0 : Integer.Sparse (Fin 2886) := [(2365, 24), (2368, -24), (2381, -24), (2391, 36), (2398, 12), (2403, -24), (2420, -24), (2423, 24), (2455, 36), (2478, 84), (2487, -24), (2497, -96), (2535, 12), (2545, -24), (2558, -24), (2580, -96), (2645, 24), (2652, 60), (2686, -12), (2691, 24), (2698, 24), (2707, 96), (2723, 12), (2730, -96)]

def entry_20_1 : Integer.Sparse (Fin 2886) := [(1152, 120), (1171, -120), (1238, -120), (1265, 120), (1380, 120), (1406, -120)]

def entry_20_2 : Integer.Sparse (Fin 2886) := [(2360, 48), (2364, 48), (2366, 16), (2369, 8), (2376, -60), (2380, -36), (2388, -8), (2389, -24), (2392, -24), (2394, 8), (2401, 16), (2408, 8), (2415, -48), (2419, -48), (2421, -12), (2424, -12), (2450, 72), (2454, 60), (2476, 24), (2480, 24), (2483, -12), (2485, 12), (2495, -24), (2501, 12), (2506, -24), (2530, 36), (2534, 24), (2542, 12), (2543, 12), (2546, 12), (2553, -60), (2557, -36), (2576, -8), (2578, -24), (2582, -24), (2643, -12), (2650, 12), (2666, -12), (2669, 12), (2694, 8), (2705, 16), (2721, 12), (2728, -12), (2762, 8), (2768, 12), (2771, -12)]

def entry_20_3 : Integer.Sparse (Fin 2886) := [(875, 120), (888, -120), (910, -120), (942, 120), (993, 120), (1021, -120)]

def entry_20_4 : Integer.Sparse (Fin 2886) := [(2363, 120), (2379, -120), (2418, -120), (2453, 120), (2533, 120), (2556, -120)]

def entry_20_5 : Integer.Sparse (Fin 2886) := [(1154, 24), (1161, -24), (1173, -24), (1185, 24), (1195, 24), (1201, -24), (1240, -24), (1247, 24), (1267, 24), (1289, -24), (1299, -24), (1308, 24), (1382, 24), (1395, -24), (1408, -24), (1428, 24), (1484, 24), (1492, -24), (1592, 96), (1598, -96), (1607, -96), (1615, 96), (1631, 96), (1639, -96)]

def entry_20_6 : Integer.Sparse (Fin 2886) := [(2441, -16), (2467, 24), (2481, 120), (2504, -24), (2507, -120), (2569, -24), (2583, -120), (2670, 96), (2760, 24), (2763, 104), (2772, -96), (2796, 16), (2810, -24), (2814, 24), (2847, 24), (2852, -24), (2856, 16), (2883, 24), (2884, -24)]

def entry_20_7 : Integer.Sparse (Fin 2886) := [(1154, 96), (1161, 24), (1173, -96), (1185, -24), (1195, -24), (1201, 24), (1240, -96), (1247, -24), (1267, 96), (1289, 24), (1299, 24), (1308, -24), (1382, 96), (1395, 24), (1408, -96), (1428, -24), (1484, -24), (1492, 24), (1592, 24), (1598, -24), (1607, -24), (1615, 24), (1631, 24), (1639, -24)]

def entry_20_8 : Integer.Sparse (Fin 2886) := [(874, 120), (887, -120), (909, -120), (941, 120), (992, 120), (1020, -120)]

def entry_20_9 : Integer.Sparse (Fin 2886) := [(2365, -24), (2368, 24), (2381, 24), (2391, 96), (2398, -24), (2403, -96), (2420, 24), (2423, -24), (2455, -24), (2478, 36), (2487, -24), (2497, 36), (2535, -24), (2545, -48), (2558, 24), (2580, -36), (2645, 96), (2652, -12), (2686, 12), (2691, 36), (2698, -12), (2707, 24), (2723, -60), (2730, -24)]

def entry_20_10 : Integer.Sparse (Fin 2886) := [(2124, -24), (2130, 48), (2141, -60), (2152, 24), (2158, -48), (2189, 60), (2231, 48), (2255, -48), (2339, 24), (2344, 72), (2353, -60), (2518, -24), (2523, -72), (2663, 72), (2751, 60), (2765, -72)]

def entry_20_11 : Integer.Sparse (Fin 2886) := [(2342, 120), (2349, -120), (2521, -120), (2636, 120), (2678, 120), (2714, -120)]

def entry_20_12 : Integer.Sparse (Fin 2886) := [(2364, 96), (2367, 24), (2380, -96), (2390, -24), (2397, -24), (2402, 24), (2419, -96), (2422, -24), (2454, 96), (2477, 24), (2486, 24), (2496, -24), (2534, 96), (2544, 24), (2557, -96), (2579, -24), (2644, -24), (2651, 24), (2685, 24), (2690, -24), (2697, -24), (2706, 24), (2722, 24), (2729, -24)]

def entry_20_13 : Integer.Sparse (Fin 2886) := [(1873, 120), (1878, -120), (1952, -120), (1961, 120), (2036, 120), (2044, -120)]

def entry_20_14 : Integer.Sparse (Fin 2886) := [(2129, -12), (2132, 48), (2143, -72), (2157, 12), (2160, -48), (2191, 72), (2233, 48), (2257, -48), (2340, 12), (2343, 72), (2350, -48), (2519, -12), (2522, -72), (2637, 72), (2679, 48), (2715, -72)]

def entry_20_15 : Integer.Sparse (Fin 2886) := [(2360, 12), (2364, 12), (2369, -24), (2376, -12), (2380, -12), (2389, 12), (2392, 24), (2406, 12), (2408, -24), (2419, -24), (2424, 24), (2450, 12), (2454, 24), (2476, -12), (2480, 96), (2501, -24), (2506, -96), (2534, 12), (2546, -24), (2557, -24), (2576, -8), (2582, -96), (2666, 24), (2669, 60), (2694, 8), (2705, 16), (2721, 36), (2728, -36), (2753, -12), (2755, 24), (2757, 24), (2762, 80), (2768, -24), (2771, -60)]

def entry_20_16 : Integer.Sparse (Fin 2886) := [(2364, 48), (2367, 72), (2380, -48), (2390, 48), (2397, -72), (2402, -48), (2419, -48), (2422, -72), (2454, 48), (2477, -48), (2486, 72), (2496, 48), (2534, 48), (2544, -48), (2557, -48), (2579, 48), (2644, 48), (2651, -48), (2685, 72), (2690, 48), (2697, -72), (2706, -48), (2722, -48), (2729, 48)]

def entry_20_17 : Integer.Sparse (Fin 2886) := [(1154, 24), (1160, -24), (1173, -24), (1184, 24), (1194, 24), (1200, -24), (1240, -24), (1246, 24), (1267, 24), (1288, -24), (1298, -24), (1307, 24), (1382, 24), (1394, -24), (1408, -24), (1427, 24), (1483, 24), (1491, -24), (1591, 96), (1597, -96), (1606, -96), (1614, 96), (1630, 96), (1638, -96)]

def entry_20_18 : Integer.Sparse (Fin 2886) := [(2364, 24), (2367, -24), (2380, -24), (2390, 24), (2397, 24), (2402, -24), (2419, -24), (2422, 24), (2454, 24), (2477, 96), (2486, -24), (2496, -96), (2534, 24), (2544, -24), (2557, -24), (2579, -96), (2644, 24), (2651, 96), (2685, -24), (2690, 24), (2697, 24), (2706, 96), (2722, -24), (2729, -96)]

def entry_20_19 : Integer.Sparse (Fin 2886) := [(1222, 120), (1230, -120), (1336, -120), (1356, 120), (1547, 120), (1565, -120)]

def entry_20_20 : Integer.Sparse (Fin 2886) := [(2365, 72), (2368, 48), (2381, -72), (2391, -96), (2403, 48), (2420, -72), (2423, -48), (2455, 96), (2478, 96), (2487, 48), (2497, -96), (2535, 48), (2545, 48), (2558, -72), (2580, -96), (2645, -48), (2652, 48), (2707, 48), (2723, 48), (2730, -48)]

def entryRow20 : Array (Integer.Sparse (Fin 2886)) := #[entry_20_0, entry_20_1, entry_20_2, entry_20_3, entry_20_4, entry_20_5, entry_20_6, entry_20_7, entry_20_8, entry_20_9, entry_20_10, entry_20_11, entry_20_12, entry_20_13, entry_20_14, entry_20_15, entry_20_16, entry_20_17, entry_20_18, entry_20_19, entry_20_20]

def entryRows : Array (Array (Integer.Sparse (Fin 2886))) := #[entryRow0, entryRow1, entryRow2, entryRow3, entryRow4, entryRow5, entryRow6, entryRow7, entryRow8, entryRow9, entryRow10, entryRow11, entryRow12, entryRow13, entryRow14, entryRow15, entryRow16, entryRow17, entryRow18, entryRow19, entryRow20]

def entries (i j : Fin 21) : Integer.Sparse (Fin 2886) :=
  (entryRows.getD i.val #[]).getD j.val []

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node0 : Integer.Sparse (Fin 2886) := [(1265, 38094840), (1294, -38094840), (1406, -38094840), (1477, 38094840), (1602, 38094840), (1625, -38094840), (2365, 397534752), (2368, -397534752), (2381, -397534752), (2391, 496918440), (2398, 298151064), (2403, -397534752), (2420, 99383688), (2423, -99383688), (2455, -198767376), (2478, 198767376), (2487, 99383688), (2497, -265023168), (2545, 99383688), (2558, 99383688), (2580, -265023168), (2645, -99383688), (2652, 198767376), (2691, 66255792), (2698, 66255792), (2707, 596302128), (2709, -496918440), (2730, -596302128), (2739, 695685816), (2746, 298151064), (2749, -496918440)]

def node1 : Integer.Sparse (Fin 2886) := [(902, 70989360), (910, -70989360), (977, -70989360), (993, 70989360), (1058, 70989360), (1064, -70989360), (2533, -427788720), (2541, 427788720), (2556, 427788720), (2575, -427788720), (2606, -427788720), (2616, 427788720)]

def node10 : Integer.Sparse (Fin 2886) := [(1948, 151802760), (1952, -151802760), (2030, -151802760), (2036, 151802760), (2078, 151802760), (2080, -151802760), (2129, -23880774), (2132, 23880774), (2143, -55721806), (2157, -214926966), (2160, 119403870), (2191, -222887224), (2195, 167165418), (2223, 143284644), (2233, -119403870), (2257, 95523096), (2276, -167165418), (2289, -95523096), (2294, 127364128), (2305, 31841032), (2307, -71642322), (2315, 119403870), (2340, 23880774), (2343, -23880774), (2350, 55721806), (2519, -23880774), (2522, 119403870), (2595, 95523096), (2628, -143284644), (2637, -119403870), (2658, 111443612), (2679, -15920516), (2680, 71642322), (2715, 143284644), (2736, -31841032), (2738, -167165418), (2741, -71642322), (2748, 119403870)]

def node11 : Integer.Sparse (Fin 2886) := [(1948, 151802760), (1952, -151802760), (2030, -151802760), (2036, 151802760), (2078, 151802760), (2080, -151802760), (2129, -23880774), (2132, 23880774), (2143, -55721806), (2157, -214926966), (2160, 119403870), (2191, -222887224), (2195, 167165418), (2223, 143284644), (2233, -119403870), (2257, 95523096), (2276, -167165418), (2289, -95523096), (2294, 127364128), (2305, 31841032), (2307, -71642322), (2315, 119403870), (2340, 23880774), (2343, -23880774), (2350, 55721806), (2364, 2501916), (2367, -2501916), (2380, -2501916), (2390, 2501916), (2397, 2501916), (2402, -2501916), (2419, -2501916), (2422, 2501916), (2454, 2501916), (2477, -2501916), (2486, -2501916), (2496, 2501916), (2519, -23880774), (2522, 119403870), (2534, 15011496), (2542, -12509580), (2544, -2501916), (2557, -15011496), (2576, 12509580), (2579, 2501916), (2595, 95523096), (2607, 12509580), (2617, -12509580), (2628, -143284644), (2637, -119403870), (2644, 2501916), (2651, -2501916), (2658, 111443612), (2679, -15920516), (2680, 71642322), (2685, 10007664), (2690, -10007664), (2697, -10007664), (2706, 10007664), (2715, 143284644), (2722, 10007664), (2729, -10007664), (2736, -31841032), (2738, -167165418), (2741, -71642322), (2748, 119403870)]

def node12 : Integer.Sparse (Fin 2886) := [(1948, 151802760), (1952, -151802760), (2030, -151802760), (2036, 151802760), (2078, 151802760), (2080, -151802760), (2129, -23880774), (2130, 19585788), (2132, 23880774), (2141, -19585788), (2143, -55721806), (2152, -97928940), (2157, -214926966), (2158, 117514728), (2160, 119403870), (2191, -222887224), (2195, 167165418), (2218, 58757364), (2223, 143284644), (2231, -117514728), (2233, -119403870), (2255, -19585788), (2257, 95523096), (2276, -167165418), (2285, 19585788), (2287, -58757364), (2289, -95523096), (2292, 78343152), (2294, 127364128), (2303, 19585788), (2305, 31841032), (2307, -71642322), (2315, 119403870), (2340, 23880774), (2343, -23880774), (2344, -19585788), (2350, 55721806), (2353, 19585788), (2364, 2501916), (2367, -2501916), (2380, -2501916), (2390, 2501916), (2397, 2501916), (2402, -2501916), (2419, -2501916), (2422, 2501916), (2454, 2501916), (2477, -2501916), (2486, -2501916), (2496, 2501916), (2518, -242334540), (2519, -23880774), (2521, 144405600), (2522, 119403870), (2523, 78343152), (2534, 15011496), (2542, -12509580), (2544, -2501916), (2557, -15011496), (2576, 12509580), (2579, 2501916), (2594, 281506116), (2595, 95523096), (2607, 12509580), (2617, -12509580), (2624, -19585788), (2627, -144405600), (2628, -143284644), (2630, -137100516), (2636, -144405600), (2637, -119403870), (2644, 2501916), (2651, -2501916), (2657, 144405600), (2658, 111443612), (2663, -78343152), (2672, 117514728), (2679, -15920516), (2680, 71642322), (2685, 10007664), (2690, -10007664), (2697, -10007664), (2706, 10007664), (2715, 143284644), (2722, 10007664), (2729, -10007664), (2736, -31841032), (2738, -167165418), (2741, -71642322), (2748, 119403870), (2765, 19585788), (2774, -19585788)]

def node13 : Integer.Sparse (Fin 2886) := [(1154, -132658656), (1160, 132658656), (1173, 132658656), (1184, -132658656), (1194, -132658656), (1200, 132658656), (1240, -33164664), (1246, 33164664), (1267, 33164664), (1288, -33164664), (1298, -33164664), (1307, 33164664), (1382, 33164664), (1394, -33164664), (1408, -33164664), (1427, 33164664), (1483, 33164664), (1491, -33164664), (1591, -33164664), (1597, 33164664), (1604, -165823320), (1606, 198987984), (1614, -33164664), (1626, 165823320), (1630, -198987984), (1638, 33164664), (1648, -165823320), (1650, 165823320), (2364, 127652160), (2367, -127652160), (2380, -127652160), (2390, 127652160), (2397, 127652160), (2402, -127652160), (2419, -127652160), (2422, 127652160), (2454, 127652160), (2477, -127652160), (2486, -127652160), (2496, 127652160), (2534, -510608640), (2544, 510608640), (2557, 510608640), (2579, -510608640), (2644, -510608640), (2651, 510608640), (2685, -127652160), (2690, 127652160), (2697, 127652160), (2706, -127652160), (2722, -127652160), (2729, 127652160)]

def node14 : Integer.Sparse (Fin 2886) := [(1154, -132658656), (1160, 132658656), (1173, 132658656), (1184, -132658656), (1194, -132658656), (1200, 132658656), (1240, -33164664), (1246, 33164664), (1267, 33164664), (1288, -33164664), (1298, -33164664), (1307, 33164664), (1382, 33164664), (1394, -33164664), (1408, -33164664), (1427, 33164664), (1483, 33164664), (1491, -33164664), (1591, -33164664), (1597, 33164664), (1604, -165823320), (1606, 198987984), (1614, -33164664), (1626, 165823320), (1630, -198987984), (1638, 33164664), (1648, -165823320), (1650, 165823320), (2364, 366147120), (2366, -89435610), (2367, -127652160), (2369, -149059350), (2376, -59623740), (2380, -306523380), (2388, 29811870), (2389, 149059350), (2390, 127652160), (2392, 178871220), (2394, -29811870), (2396, 59623740), (2397, 127652160), (2401, -89435610), (2402, -127652160), (2406, 89435610), (2408, -149059350), (2419, -68028420), (2421, -29811870), (2422, 127652160), (2424, -29811870), (2454, 68028420), (2476, 59623740), (2477, -127652160), (2480, 89435610), (2483, -59623740), (2485, 29811870), (2486, -127652160), (2495, -59623740), (2496, 127652160), (2501, 29811870), (2506, -89435610), (2534, -570232380), (2542, 59623740), (2543, 29811870), (2544, 510608640), (2546, 29811870), (2553, -59623740), (2557, 629856120), (2576, 258369540), (2578, -59623740), (2579, -510608640), (2582, -268306830), (2607, -29811870), (2617, -178871220), (2631, 208683090), (2639, 29811870), (2643, -29811870), (2644, -510608640), (2650, 29811870), (2651, 510608640), (2666, -29811870), (2669, 149059350), (2673, -178871220), (2684, -29811870), (2685, -127652160), (2689, 29811870), (2690, 127652160), (2694, 39749160), (2696, -89435610), (2697, 127652160), (2705, 19874580), (2706, -127652160), (2717, -119247480), (2721, 208683090), (2722, -127652160), (2729, 127652160), (2742, 89435610), (2743, -119247480), (2745, -29811870), (2762, 39749160), (2768, 29811870), (2771, -59623740), (2775, 29811870)]

def node15 : Integer.Sparse (Fin 2886) := [(1332, 132134640), (1336, -132134640), (1537, -132134640), (1547, 132134640), (1671, 132134640), (1676, -132134640), (2365, -198234408), (2368, 198234408), (2381, 198234408), (2391, -297351612), (2398, -99117204), (2403, 198234408), (2420, 198234408), (2423, -198234408), (2455, -297351612), (2478, -693820428), (2487, 198234408), (2497, 792937632), (2535, -99117204), (2545, 198234408), (2558, 198234408), (2580, 792937632), (2645, -198234408), (2652, -495586020), (2686, 99117204), (2691, -198234408), (2698, -198234408), (2707, -792937632), (2723, -99117204), (2730, 792937632)]

def node16 : Integer.Sparse (Fin 2886) := [(1332, 132134640), (1336, -132134640), (1537, -132134640), (1547, 132134640), (1671, 132134640), (1676, -132134640), (2364, 111038496), (2365, -198234408), (2367, -111038496), (2368, 198234408), (2380, -111038496), (2381, 198234408), (2390, 111038496), (2391, -297351612), (2397, 111038496), (2398, -99117204), (2402, -111038496), (2403, 198234408), (2419, 27759624), (2420, 198234408), (2422, -27759624), (2423, -198234408), (2454, -27759624), (2455, -297351612), (2477, 27759624), (2478, -693820428), (2486, 27759624), (2487, 198234408), (2496, -27759624), (2497, 792937632), (2534, -27759624), (2535, -99117204), (2544, 27759624), (2545, 198234408), (2557, 27759624), (2558, 198234408), (2576, 138798120), (2579, -166557744), (2580, 792937632), (2617, -138798120), (2629, 138798120), (2644, -27759624), (2645, -198234408), (2651, 166557744), (2652, -495586020), (2659, -138798120), (2685, 27759624), (2686, 99117204), (2690, -27759624), (2691, -198234408), (2697, -27759624), (2698, -198234408), (2706, 27759624), (2707, -792937632), (2722, 27759624), (2723, -99117204), (2729, -27759624), (2730, 792937632)]

def node17 : Integer.Sparse (Fin 2886) := [(1154, -132658656), (1160, 132658656), (1173, 132658656), (1184, -132658656), (1194, -132658656), (1200, 132658656), (1240, -33164664), (1246, 33164664), (1267, 33164664), (1288, -33164664), (1298, -33164664), (1307, 33164664), (1332, 132134640), (1336, -132134640), (1382, 33164664), (1394, -33164664), (1408, -33164664), (1427, 33164664), (1483, 33164664), (1491, -33164664), (1537, -132134640), (1547, 132134640), (1591, -33164664), (1597, 33164664), (1604, -165823320), (1606, 198987984), (1614, -33164664), (1626, 165823320), (1630, -198987984), (1638, 33164664), (1648, -165823320), (1650, 165823320), (1671, 132134640), (1676, -132134640), (2364, 477185616), (2365, -198234408), (2366, -89435610), (2367, -238690656), (2368, 198234408), (2369, -149059350), (2376, -59623740), (2380, -417561876), (2381, 198234408), (2388, 29811870), (2389, 149059350), (2390, 238690656), (2391, -297351612), (2392, 178871220), (2394, -29811870), (2396, 59623740), (2397, 238690656), (2398, -99117204), (2401, -89435610), (2402, -238690656), (2403, 198234408), (2406, 89435610), (2408, -149059350), (2419, -40268796), (2420, 198234408), (2421, -29811870), (2422, 99892536), (2423, -198234408), (2424, -29811870), (2454, 40268796), (2455, -297351612), (2476, 59623740), (2477, -99892536), (2478, -693820428), (2480, 89435610), (2483, -59623740), (2485, 29811870), (2486, -99892536), (2487, 198234408), (2495, -59623740), (2496, 99892536), (2497, 792937632), (2501, 29811870), (2506, -89435610), (2534, -597992004), (2535, -99117204), (2542, 59623740), (2543, 29811870), (2544, 538368264), (2545, 198234408), (2546, 29811870), (2553, -59623740), (2557, 657615744), (2558, 198234408), (2576, 397167660), (2578, -59623740), (2579, -677166384), (2580, 792937632), (2582, -268306830), (2607, -29811870), (2617, -317669340), (2629, 138798120), (2631, 208683090), (2639, 29811870), (2643, -29811870), (2644, -538368264), (2645, -198234408), (2650, 29811870), (2651, 677166384), (2652, -495586020), (2659, -138798120), (2666, -29811870), (2669, 149059350), (2673, -178871220), (2684, -29811870), (2685, -99892536), (2686, 99117204), (2689, 29811870), (2690, 99892536), (2691, -198234408), (2694, 39749160), (2696, -89435610), (2697, 99892536), (2698, -198234408), (2705, 19874580), (2706, -99892536), (2707, -792937632), (2717, -119247480), (2721, 208683090), (2722, -99892536), (2723, -99117204), (2729, 99892536), (2730, 792937632), (2742, 89435610), (2743, -119247480), (2745, -29811870), (2762, 39749160), (2768, 29811870), (2771, -59623740), (2775, 29811870)]

def node18 : Integer.Sparse (Fin 2886) := [(1154, -132658656), (1160, 132658656), (1173, 132658656), (1184, -132658656), (1194, -132658656), (1200, 132658656), (1240, -33164664), (1246, 33164664), (1267, 33164664), (1288, -33164664), (1298, -33164664), (1307, 33164664), (1332, 132134640), (1336, -132134640), (1382, 33164664), (1394, -33164664), (1408, -33164664), (1427, 33164664), (1483, 33164664), (1491, -33164664), (1537, -132134640), (1547, 132134640), (1591, -33164664), (1597, 33164664), (1604, -165823320), (1606, 198987984), (1614, -33164664), (1626, 165823320), (1630, -198987984), (1638, 33164664), (1648, -165823320), (1650, 165823320), (1671, 132134640), (1676, -132134640), (1948, 151802760), (1952, -151802760), (2030, -151802760), (2036, 151802760), (2078, 151802760), (2080, -151802760), (2129, -23880774), (2130, 19585788), (2132, 23880774), (2141, -19585788), (2143, -55721806), (2152, -97928940), (2157, -214926966), (2158, 117514728), (2160, 119403870), (2191, -222887224), (2195, 167165418), (2218, 58757364), (2223, 143284644), (2231, -117514728), (2233, -119403870), (2255, -19585788), (2257, 95523096), (2276, -167165418), (2285, 19585788), (2287, -58757364), (2289, -95523096), (2292, 78343152), (2294, 127364128), (2303, 19585788), (2305, 31841032), (2307, -71642322), (2315, 119403870), (2340, 23880774), (2343, -23880774), (2344, -19585788), (2350, 55721806), (2353, 19585788), (2364, 479687532), (2365, -198234408), (2366, -89435610), (2367, -241192572), (2368, 198234408), (2369, -149059350), (2376, -59623740), (2380, -420063792), (2381, 198234408), (2388, 29811870), (2389, 149059350), (2390, 241192572), (2391, -297351612), (2392, 178871220), (2394, -29811870), (2396, 59623740), (2397, 241192572), (2398, -99117204), (2401, -89435610), (2402, -241192572), (2403, 198234408), (2406, 89435610), (2408, -149059350), (2419, -42770712), (2420, 198234408), (2421, -29811870), (2422, 102394452), (2423, -198234408), (2424, -29811870), (2454, 42770712), (2455, -297351612), (2476, 59623740), (2477, -102394452), (2478, -693820428), (2480, 89435610), (2483, -59623740), (2485, 29811870), (2486, -102394452), (2487, 198234408), (2495, -59623740), (2496, 102394452), (2497, 792937632), (2501, 29811870), (2506, -89435610), (2518, -242334540), (2519, -23880774), (2521, 144405600), (2522, 119403870), (2523, 78343152), (2534, -582980508), (2535, -99117204), (2542, 47114160), (2543, 29811870), (2544, 535866348), (2545, 198234408), (2546, 29811870), (2553, -59623740), (2557, 642604248), (2558, 198234408), (2576, 409677240), (2578, -59623740), (2579, -674664468), (2580, 792937632), (2582, -268306830), (2594, 281506116), (2595, 95523096), (2607, -17302290), (2617, -330178920), (2624, -19585788), (2627, -144405600), (2628, -143284644), (2629, 138798120), (2630, -137100516), (2631, 208683090), (2636, -144405600), (2637, -119403870), (2639, 29811870), (2643, -29811870), (2644, -535866348), (2645, -198234408), (2650, 29811870), (2651, 674664468), (2652, -495586020), (2657, 144405600), (2658, 111443612), (2659, -138798120), (2663, -78343152), (2666, -29811870), (2669, 149059350), (2672, 117514728), (2673, -178871220), (2679, -15920516), (2680, 71642322), (2684, -29811870), (2685, -89884872), (2686, 99117204), (2689, 29811870), (2690, 89884872), (2691, -198234408), (2694, 39749160), (2696, -89435610), (2697, 89884872), (2698, -198234408), (2705, 19874580), (2706, -89884872), (2707, -792937632), (2715, 143284644), (2717, -119247480), (2721, 208683090), (2722, -89884872), (2723, -99117204), (2729, 89884872), (2730, 792937632), (2736, -31841032), (2738, -167165418), (2741, -71642322), (2742, 89435610), (2743, -119247480), (2745, -29811870), (2748, 119403870), (2762, 39749160), (2765, 19585788), (2768, 29811870), (2771, -59623740), (2774, -19585788), (2775, 29811870)]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node100 : Integer.Sparse (Fin 2886) := [(339, -12544200), (348, 12544200), (359, 12544200), (368, -12544200), (388, -12544200), (393, 12544200), (1154, -78613392), (1161, 78613392), (1173, 78613392), (1185, -78613392), (1195, -78613392), (1201, 78613392), (1240, -19653348), (1247, 19653348), (1267, 19653348), (1289, -19653348), (1299, -19653348), (1308, 19653348), (1382, 19653348), (1395, -19653348), (1408, -19653348), (1428, 19653348), (1484, 19653348), (1492, -19653348), (1592, -19653348), (1598, 19653348), (1604, -98266740), (1607, 117920088), (1615, -19653348), (1626, 98266740), (1631, -117920088), (1639, 19653348), (1649, -98266740), (1651, 98266740)]

def node101 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (327, 1139532), (333, -4558128), (376, -4178284), (400, 7976724), (423, 3418596), (427, -5697660), (574, -1139532), (578, 1139532), (1379, 95074440), (1389, -95074440), (1405, -95074440), (1422, 95074440), (1449, 95074440), (1457, -95074440)]

def node102 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (327, 1139532), (333, -4558128), (376, -4178284), (400, 7976724), (423, 3418596), (427, -5697660), (574, -1139532), (578, 1139532), (1149, 21578028), (1157, -21578028), (1168, -21578028), (1183, 21578028), (1206, 21578028), (1209, -21578028), (1235, -21578028), (1243, 21578028), (1262, 21578028), (1287, -21578028), (1313, -21578028), (1321, 21578028), (1377, 21578028), (1379, 95074440), (1385, 107890140), (1389, -95074440), (1393, -129468168), (1403, -21578028), (1405, -95074440), (1411, -107890140), (1422, 95074440), (1426, 129468168), (1449, 95074440), (1453, 107890140), (1457, -95074440), (1461, -107890140), (1506, 21578028), (1511, -21578028), (1701, 86312112), (1704, -86312112), (1708, -86312112), (1713, 86312112), (1721, 86312112), (1726, -86312112)]

def node103 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (327, 1139532), (333, -4558128), (339, -12544200), (348, 12544200), (359, 12544200), (368, -12544200), (376, -4178284), (388, -12544200), (393, 12544200), (400, 7976724), (423, 3418596), (427, -5697660), (574, -1139532), (578, 1139532), (1149, 21578028), (1154, -78613392), (1157, -21578028), (1161, 78613392), (1168, -21578028), (1173, 78613392), (1183, 21578028), (1185, -78613392), (1195, -78613392), (1201, 78613392), (1206, 21578028), (1209, -21578028), (1235, -21578028), (1240, -19653348), (1243, 21578028), (1247, 19653348), (1262, 21578028), (1267, 19653348), (1287, -21578028), (1289, -19653348), (1299, -19653348), (1308, 19653348), (1313, -21578028), (1321, 21578028), (1377, 21578028), (1379, 95074440), (1382, 19653348), (1385, 107890140), (1389, -95074440), (1393, -129468168), (1395, -19653348), (1403, -21578028), (1405, -95074440), (1408, -19653348), (1411, -107890140), (1422, 95074440), (1426, 129468168), (1428, 19653348), (1449, 95074440), (1453, 107890140), (1457, -95074440), (1461, -107890140), (1484, 19653348), (1492, -19653348), (1506, 21578028), (1511, -21578028), (1592, -19653348), (1598, 19653348), (1604, -98266740), (1607, 117920088), (1615, -19653348), (1626, 98266740), (1631, -117920088), (1639, 19653348), (1649, -98266740), (1651, 98266740), (1701, 86312112), (1704, -86312112), (1708, -86312112), (1713, 86312112), (1721, 86312112), (1726, -86312112)]

def node104 : Integer.Sparse (Fin 2886) := [(204, 233856912), (209, -233856912), (215, -233856912), (227, 350785368), (239, 116928456), (240, -233856912), (261, 58464228), (266, -58464228), (274, -155904608), (279, 58464228), (287, 116928456), (301, -116928456), (337, 38976152), (342, -58464228), (352, 116928456), (357, 350785368), (362, -292321140), (372, -155904608), (382, -292321140), (391, 350785368), (395, 58464228), (424, 233856912), (425, -350785368), (572, 38976152), (573, 58464228), (575, -58464228), (576, 116928456), (577, -58464228), (1252, -247390920), (1257, 247390920), (1276, 247390920), (1282, -247390920), (1317, -247390920), (1319, 247390920)]

def node105 : Integer.Sparse (Fin 2886) := [(328, -15109920), (332, 15109920), (377, 15109920), (399, -15109920), (404, -15109920), (421, 15109920), (1154, -36212232), (1161, 36212232), (1173, 36212232), (1185, -36212232), (1195, -36212232), (1201, 36212232), (1240, -144848928), (1247, 144848928), (1267, 144848928), (1289, -144848928), (1299, -144848928), (1308, 144848928), (1382, -36212232), (1395, 36212232), (1408, 36212232), (1428, -36212232), (1484, -36212232), (1492, 36212232), (1589, -181061160), (1592, 217273392), (1598, -36212232), (1607, -36212232), (1615, 36212232), (1626, 181061160), (1631, 36212232), (1639, -217273392), (1649, -181061160), (1653, 181061160)]

def node106 : Integer.Sparse (Fin 2886) := [(204, 2084280), (209, -2084280), (215, -2084280), (227, 4168560), (240, -2084280), (261, -2084280), (266, 2084280), (274, 3126420), (279, 11463540), (287, 6252840), (300, -12505680), (301, -8337120), (328, -15109920), (332, 15109920), (337, 1042140), (342, -1042140), (352, -2084280), (357, -2084280), (362, -10421400), (372, -7642360), (377, 15109920), (391, 3126420), (395, -3126420), (399, -15109920), (404, -15109920), (421, 15109920), (424, 7294980), (425, 2084280), (426, 5210700), (571, 2084280), (572, 11810920), (573, 8337120), (575, -7294980), (576, 1042140), (577, -8337120), (1154, -36212232), (1161, 36212232), (1173, 36212232), (1185, -36212232), (1195, -36212232), (1201, 36212232), (1240, -144848928), (1247, 144848928), (1267, 144848928), (1289, -144848928), (1299, -144848928), (1308, 144848928), (1382, -36212232), (1395, 36212232), (1408, 36212232), (1428, -36212232), (1484, -36212232), (1492, 36212232), (1589, -181061160), (1592, 217273392), (1598, -36212232), (1607, -36212232), (1615, 36212232), (1626, 181061160), (1631, 36212232), (1639, -217273392), (1649, -181061160), (1653, 181061160)]

def node107 : Integer.Sparse (Fin 2886) := [(204, 235941192), (209, -235941192), (215, -235941192), (227, 354953928), (239, 116928456), (240, -235941192), (261, 56379948), (266, -56379948), (274, -152778188), (279, 69927768), (287, 123181296), (300, -12505680), (301, -125265576), (328, -15109920), (332, 15109920), (337, 40018292), (342, -59506368), (352, 114844176), (357, 348701088), (362, -302742540), (372, -163546968), (377, 15109920), (382, -292321140), (391, 353911788), (395, 55337808), (399, -15109920), (404, -15109920), (421, 15109920), (424, 241151892), (425, -348701088), (426, 5210700), (571, 2084280), (572, 50787072), (573, 66801348), (575, -65759208), (576, 117970596), (577, -66801348), (1154, -36212232), (1161, 36212232), (1173, 36212232), (1185, -36212232), (1195, -36212232), (1201, 36212232), (1240, -144848928), (1247, 144848928), (1252, -247390920), (1257, 247390920), (1267, 144848928), (1276, 247390920), (1282, -247390920), (1289, -144848928), (1299, -144848928), (1308, 144848928), (1317, -247390920), (1319, 247390920), (1382, -36212232), (1395, 36212232), (1408, 36212232), (1428, -36212232), (1484, -36212232), (1492, 36212232), (1589, -181061160), (1592, 217273392), (1598, -36212232), (1607, -36212232), (1615, 36212232), (1626, 181061160), (1631, 36212232), (1639, -217273392), (1649, -181061160), (1653, 181061160)]

def node108 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (204, 235941192), (209, -235941192), (215, -235941192), (227, 354953928), (239, 116928456), (240, -235941192), (261, 56379948), (266, -56379948), (274, -152778188), (279, 69927768), (287, 123181296), (300, -12505680), (301, -125265576), (327, 1139532), (328, -15109920), (332, 15109920), (333, -4558128), (337, 40018292), (339, -12544200), (342, -59506368), (348, 12544200), (352, 114844176), (357, 348701088), (359, 12544200), (362, -302742540), (368, -12544200), (372, -163546968), (376, -4178284), (377, 15109920), (382, -292321140), (388, -12544200), (391, 353911788), (393, 12544200), (395, 55337808), (399, -15109920), (400, 7976724), (404, -15109920), (421, 15109920), (423, 3418596), (424, 241151892), (425, -348701088), (426, 5210700), (427, -5697660), (571, 2084280), (572, 50787072), (573, 66801348), (574, -1139532), (575, -65759208), (576, 117970596), (577, -66801348), (578, 1139532), (1149, 21578028), (1154, -114825624), (1157, -21578028), (1161, 114825624), (1168, -21578028), (1173, 114825624), (1183, 21578028), (1185, -114825624), (1195, -114825624), (1201, 114825624), (1206, 21578028), (1209, -21578028), (1235, -21578028), (1240, -164502276), (1243, 21578028), (1247, 164502276), (1252, -247390920), (1257, 247390920), (1262, 21578028), (1267, 164502276), (1276, 247390920), (1282, -247390920), (1287, -21578028), (1289, -164502276), (1299, -164502276), (1308, 164502276), (1313, -21578028), (1317, -247390920), (1319, 247390920), (1321, 21578028), (1377, 21578028), (1379, 95074440), (1382, -16558884), (1385, 107890140), (1389, -95074440), (1393, -129468168), (1395, 16558884), (1403, -21578028), (1405, -95074440), (1408, 16558884), (1411, -107890140), (1422, 95074440), (1426, 129468168), (1428, -16558884), (1449, 95074440), (1453, 107890140), (1457, -95074440), (1461, -107890140), (1484, -16558884), (1492, 16558884), (1506, 21578028), (1511, -21578028), (1589, -181061160), (1592, 197620044), (1598, -16558884), (1604, -98266740), (1607, 81707856), (1615, 16558884), (1626, 279327900), (1631, -81707856), (1639, -197620044), (1649, -279327900), (1651, 98266740), (1653, 181061160), (1701, 86312112), (1704, -86312112), (1708, -86312112), (1713, 86312112), (1721, 86312112), (1726, -86312112)]

def node109 : Integer.Sparse (Fin 2886) := [(1362, 118984320), (1363, 203483040), (1368, -203483040), (1370, -118984320), (1435, -118984320), (1436, -203483040), (1464, 203483040), (1466, 118984320), (1473, 203483040), (1496, -203483040), (1501, 118984320), (1514, -118984320)]

def node110 : Integer.Sparse (Fin 2886) := [(715, -246386400), (716, 246386400), (782, 246386400), (786, -246386400), (837, -246386400), (838, 246386400), (1367, 128597280), (1372, -128597280), (1439, -128597280), (1468, 128597280), (1475, 128597280), (1498, -128597280), (1582, 128597280), (1585, -128597280), (1620, -128597280), (1644, 128597280), (1647, 128597280), (1655, -128597280)]

def node111 : Integer.Sparse (Fin 2886) := [(715, -246386400), (716, 246386400), (782, 246386400), (786, -246386400), (837, -246386400), (838, 246386400), (1150, 14549292), (1155, -14549292), (1169, -14549292), (1181, 14549292), (1193, 14549292), (1199, -14549292), (1236, -14549292), (1241, 14549292), (1263, 14549292), (1285, -14549292), (1297, -14549292), (1306, 14549292), (1367, 128597280), (1372, -128597280), (1378, 14549292), (1383, 72746460), (1391, -87295752), (1404, -14549292), (1409, -72746460), (1424, 87295752), (1439, -128597280), (1451, 72746460), (1459, -72746460), (1468, 128597280), (1475, 128597280), (1482, 14549292), (1490, -14549292), (1498, -128597280), (1582, 128597280), (1585, -128597280), (1590, 58197168), (1596, -58197168), (1605, -58197168), (1613, 58197168), (1620, -128597280), (1629, 58197168), (1637, -58197168), (1644, 128597280), (1647, 128597280), (1655, -128597280)]

def node112 : Integer.Sparse (Fin 2886) := [(715, -246386400), (716, 246386400), (782, 246386400), (786, -246386400), (837, -246386400), (838, 246386400), (1150, 14549292), (1155, -14549292), (1169, -14549292), (1181, 14549292), (1193, 14549292), (1199, -14549292), (1236, -14549292), (1241, 14549292), (1263, 14549292), (1285, -14549292), (1297, -14549292), (1306, 14549292), (1362, 118984320), (1363, 203483040), (1367, 128597280), (1368, -203483040), (1370, -118984320), (1372, -128597280), (1378, 14549292), (1383, 72746460), (1391, -87295752), (1404, -14549292), (1409, -72746460), (1424, 87295752), (1435, -118984320), (1436, -203483040), (1439, -128597280), (1451, 72746460), (1459, -72746460), (1464, 203483040), (1466, 118984320), (1468, 128597280), (1473, 203483040), (1475, 128597280), (1482, 14549292), (1490, -14549292), (1496, -203483040), (1498, -128597280), (1501, 118984320), (1514, -118984320), (1582, 128597280), (1585, -128597280), (1590, 58197168), (1596, -58197168), (1605, -58197168), (1613, 58197168), (1620, -128597280), (1629, 58197168), (1637, -58197168), (1644, 128597280), (1647, 128597280), (1655, -128597280)]

def node113 : Integer.Sparse (Fin 2886) := [(205, 251318640), (208, -251318640), (216, -251318640), (226, 251318640), (231, 251318640), (236, -251318640), (262, 62829660), (265, -62829660), (275, -62829660), (286, 62829660), (291, 62829660), (297, -62829660), (338, -62829660), (351, 62829660), (358, 376977960), (361, -314148300), (371, -62829660), (383, -314148300), (390, 314148300), (407, 314148300), (410, -376977960), (416, 62829660), (498, 62829660), (503, -62829660), (507, -62829660), (513, 62829660), (524, 62829660), (530, -62829660), (1150, 3310224), (1155, -3310224), (1169, -3310224), (1181, 3310224), (1193, 3310224), (1199, -3310224), (1236, -3310224), (1241, 3310224), (1263, 3310224), (1285, -3310224), (1297, -3310224), (1306, 3310224), (1378, -13240896), (1391, 13240896), (1404, 13240896), (1424, -13240896), (1482, -13240896), (1490, 13240896), (1590, -3310224), (1596, 3310224), (1605, 3310224), (1613, -3310224), (1629, -3310224), (1637, 3310224)]

def node114 : Integer.Sparse (Fin 2886) := [(205, 251318640), (208, -251318640), (216, -251318640), (226, 251318640), (231, 251318640), (236, -251318640), (262, 62829660), (265, -62829660), (275, -62829660), (286, 62829660), (291, 62829660), (297, -62829660), (338, -62829660), (351, 62829660), (358, 376977960), (361, -314148300), (371, -62829660), (383, -314148300), (390, 314148300), (407, 314148300), (410, -376977960), (416, 62829660), (498, 62829660), (503, -62829660), (507, -62829660), (513, 62829660), (524, 62829660), (530, -62829660), (1149, -178298592), (1150, 3310224), (1155, -3310224), (1157, 178298592), (1168, 178298592), (1169, -3310224), (1181, 3310224), (1183, -178298592), (1193, 3310224), (1199, -3310224), (1206, -178298592), (1209, 178298592), (1235, -44574648), (1236, -3310224), (1241, 3310224), (1243, 44574648), (1262, 44574648), (1263, 3310224), (1285, -3310224), (1287, -44574648), (1297, -3310224), (1306, 3310224), (1313, -44574648), (1321, 44574648), (1377, 44574648), (1378, -13240896), (1391, 13240896), (1393, -44574648), (1403, -267447888), (1404, 13240896), (1411, 222873240), (1424, -13240896), (1426, 44574648), (1445, 222873240), (1453, -222873240), (1482, -13240896), (1490, 13240896), (1504, -222873240), (1506, 267447888), (1511, -44574648), (1590, -3310224), (1596, 3310224), (1605, 3310224), (1613, -3310224), (1629, -3310224), (1637, 3310224), (1701, -44574648), (1704, 44574648), (1708, 44574648), (1713, -44574648), (1721, -44574648), (1726, 44574648)]

def node115 : Integer.Sparse (Fin 2886) := [(223, 22659036), (225, -22659036), (235, 22659036), (243, -22659036), (246, 22659036), (256, -22659036), (305, -226590360), (308, 135954216), (350, 90636144), (386, 67977108), (398, -158613252), (409, -67977108), (420, 113295180), (443, 158613252), (457, -158613252), (474, -22659036), (523, 22659036), (534, -22659036), (583, -67977108), (587, 113295180), (593, 22659036), (1154, 81819264), (1161, -81819264), (1173, -81819264), (1185, 81819264), (1195, 81819264), (1201, -81819264), (1240, -81819264), (1247, 81819264), (1267, 81819264), (1289, -81819264), (1299, -81819264), (1308, 81819264), (1382, 81819264), (1395, -81819264), (1408, -81819264), (1428, 81819264), (1484, 81819264), (1492, -81819264), (1592, 327277056), (1598, -327277056), (1607, -327277056), (1615, 327277056), (1631, 327277056), (1639, -327277056)]

def node116 : Integer.Sparse (Fin 2886) := [(223, 22659036), (225, -22659036), (235, 22659036), (243, -22659036), (246, 22659036), (256, -22659036), (305, -226590360), (308, 135954216), (350, 90636144), (386, 67977108), (398, -158613252), (409, -67977108), (420, 113295180), (443, 158613252), (457, -158613252), (474, -22659036), (523, 22659036), (534, -22659036), (583, -67977108), (587, 113295180), (593, 22659036), (1150, 12017184), (1154, 81819264), (1155, -12017184), (1161, -81819264), (1169, -12017184), (1173, -81819264), (1181, 12017184), (1185, 81819264), (1193, 12017184), (1195, 81819264), (1199, -12017184), (1201, -81819264), (1236, 3004296), (1240, -81819264), (1241, -3004296), (1247, 81819264), (1263, -3004296), (1267, 81819264), (1285, 3004296), (1289, -81819264), (1297, 3004296), (1299, -81819264), (1306, -3004296), (1308, 81819264), (1378, -3004296), (1382, 81819264), (1391, 3004296), (1395, -81819264), (1404, 18025776), (1408, -81819264), (1409, -15021480), (1424, -3004296), (1428, 81819264), (1446, -15021480), (1451, 15021480), (1480, 15021480), (1482, -18025776), (1484, 81819264), (1490, 3004296), (1492, -81819264), (1590, 3004296), (1592, 327277056), (1596, -3004296), (1598, -327277056), (1605, -3004296), (1607, -327277056), (1613, 3004296), (1615, 327277056), (1629, 3004296), (1631, 327277056), (1637, -3004296), (1639, -327277056)]

set_option maxHeartbeats 1000000 in
def node117 : Integer.Sparse (Fin 2886) := [(205, 251318640), (208, -251318640), (216, -251318640), (223, 22659036), (225, -22659036), (226, 251318640), (231, 251318640), (235, 22659036), (236, -251318640), (243, -22659036), (246, 22659036), (256, -22659036), (262, 62829660), (265, -62829660), (275, -62829660), (286, 62829660), (291, 62829660), (297, -62829660), (305, -226590360), (308, 135954216), (338, -62829660), (350, 90636144), (351, 62829660), (358, 376977960), (361, -314148300), (371, -62829660), (383, -314148300), (386, 67977108), (390, 314148300), (398, -158613252), (407, 314148300), (409, -67977108), (410, -376977960), (416, 62829660), (420, 113295180), (443, 158613252), (457, -158613252), (474, -22659036), (498, 62829660), (503, -62829660), (507, -62829660), (513, 62829660), (523, 22659036), (524, 62829660), (530, -62829660), (534, -22659036), (583, -67977108), (587, 113295180), (593, 22659036), (1149, -178298592), (1150, 15327408), (1154, 81819264), (1155, -15327408), (1157, 178298592), (1161, -81819264), (1168, 178298592), (1169, -15327408), (1173, -81819264), (1181, 15327408), (1183, -178298592), (1185, 81819264), (1193, 15327408), (1195, 81819264), (1199, -15327408), (1201, -81819264), (1206, -178298592), (1209, 178298592), (1235, -44574648), (1236, -305928), (1240, -81819264), (1241, 305928), (1243, 44574648), (1247, 81819264), (1262, 44574648), (1263, 305928), (1267, 81819264), (1285, -305928), (1287, -44574648), (1289, -81819264), (1297, -305928), (1299, -81819264), (1306, 305928), (1308, 81819264), (1313, -44574648), (1321, 44574648), (1377, 44574648), (1378, -16245192), (1382, 81819264), (1391, 16245192), (1393, -44574648), (1395, -81819264), (1403, -267447888), (1404, 31266672), (1408, -81819264), (1409, -15021480), (1411, 222873240), (1424, -16245192), (1426, 44574648), (1428, 81819264), (1445, 222873240), (1446, -15021480), (1451, 15021480), (1453, -222873240), (1480, 15021480), (1482, -31266672), (1484, 81819264), (1490, 16245192), (1492, -81819264), (1504, -222873240), (1506, 267447888), (1511, -44574648), (1590, -305928), (1592, 327277056), (1596, 305928), (1598, -327277056), (1605, 305928), (1607, -327277056), (1613, -305928), (1615, 327277056), (1629, -305928), (1631, 327277056), (1637, 305928), (1639, -327277056), (1701, -44574648), (1704, 44574648), (1708, 44574648), (1713, -44574648), (1721, -44574648), (1726, 44574648)]

def node118 : Integer.Sparse (Fin 2886) := [(205, 251318640), (208, -251318640), (216, -251318640), (223, 22659036), (225, -22659036), (226, 251318640), (231, 251318640), (235, 22659036), (236, -251318640), (243, -22659036), (246, 22659036), (256, -22659036), (262, 62829660), (265, -62829660), (275, -62829660), (286, 62829660), (291, 62829660), (297, -62829660), (305, -226590360), (308, 135954216), (338, -62829660), (350, 90636144), (351, 62829660), (358, 376977960), (361, -314148300), (371, -62829660), (383, -314148300), (386, 67977108), (390, 314148300), (398, -158613252), (407, 314148300), (409, -67977108), (410, -376977960), (416, 62829660), (420, 113295180), (443, 158613252), (457, -158613252), (474, -22659036), (498, 62829660), (503, -62829660), (507, -62829660), (513, 62829660), (523, 22659036), (524, 62829660), (530, -62829660), (534, -22659036), (583, -67977108), (587, 113295180), (593, 22659036), (715, -246386400), (716, 246386400), (782, 246386400), (786, -246386400), (837, -246386400), (838, 246386400), (1149, -178298592), (1150, 29876700), (1154, 81819264), (1155, -29876700), (1157, 178298592), (1161, -81819264), (1168, 178298592), (1169, -29876700), (1173, -81819264), (1181, 29876700), (1183, -178298592), (1185, 81819264), (1193, 29876700), (1195, 81819264), (1199, -29876700), (1201, -81819264), (1206, -178298592), (1209, 178298592), (1235, -44574648), (1236, -14855220), (1240, -81819264), (1241, 14855220), (1243, 44574648), (1247, 81819264), (1262, 44574648), (1263, 14855220), (1267, 81819264), (1285, -14855220), (1287, -44574648), (1289, -81819264), (1297, -14855220), (1299, -81819264), (1306, 14855220), (1308, 81819264), (1313, -44574648), (1321, 44574648), (1362, 118984320), (1363, 203483040), (1367, 128597280), (1368, -203483040), (1370, -118984320), (1372, -128597280), (1377, 44574648), (1378, -1695900), (1382, 81819264), (1383, 72746460), (1391, -71050560), (1393, -44574648), (1395, -81819264), (1403, -267447888), (1404, 16717380), (1408, -81819264), (1409, -87767940), (1411, 222873240), (1424, 71050560), (1426, 44574648), (1428, 81819264), (1435, -118984320), (1436, -203483040), (1439, -128597280), (1445, 222873240), (1446, -15021480), (1451, 87767940), (1453, -222873240), (1459, -72746460), (1464, 203483040), (1466, 118984320), (1468, 128597280), (1473, 203483040), (1475, 128597280), (1480, 15021480), (1482, -16717380), (1484, 81819264), (1490, 1695900), (1492, -81819264), (1496, -203483040), (1498, -128597280), (1501, 118984320), (1504, -222873240), (1506, 267447888), (1511, -44574648), (1514, -118984320), (1582, 128597280), (1585, -128597280), (1590, 57891240), (1592, 327277056), (1596, -57891240), (1598, -327277056), (1605, -57891240), (1607, -327277056), (1613, 57891240), (1615, 327277056), (1620, -128597280), (1629, 57891240), (1631, 327277056), (1637, -57891240), (1639, -327277056), (1644, 128597280), (1647, 128597280), (1655, -128597280), (1701, -44574648), (1704, 44574648), (1708, 44574648), (1713, -44574648), (1721, -44574648), (1726, 44574648)]

def node119 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (204, 235941192), (205, 251318640), (208, -251318640), (209, -235941192), (215, -235941192), (216, -251318640), (223, 22659036), (225, -22659036), (226, 251318640), (227, 354953928), (231, 251318640), (235, 22659036), (236, -251318640), (239, 116928456), (240, -235941192), (243, -22659036), (246, 22659036), (256, -22659036), (261, 56379948), (262, 62829660), (265, -62829660), (266, -56379948), (274, -152778188), (275, -62829660), (279, 69927768), (286, 62829660), (287, 123181296), (291, 62829660), (297, -62829660), (300, -12505680), (301, -125265576), (305, -226590360), (308, 135954216), (327, 1139532), (328, -15109920), (332, 15109920), (333, -4558128), (337, 40018292), (338, -62829660), (339, -12544200), (342, -59506368), (348, 12544200), (350, 90636144), (351, 62829660), (352, 114844176), (357, 348701088), (358, 376977960), (359, 12544200), (361, -314148300), (362, -302742540), (368, -12544200), (371, -62829660), (372, -163546968), (376, -4178284), (377, 15109920), (382, -292321140), (383, -314148300), (386, 67977108), (388, -12544200), (390, 314148300), (391, 353911788), (393, 12544200), (395, 55337808), (398, -158613252), (399, -15109920), (400, 7976724), (404, -15109920), (407, 314148300), (409, -67977108), (410, -376977960), (416, 62829660), (420, 113295180), (421, 15109920), (423, 3418596), (424, 241151892), (425, -348701088), (426, 5210700), (427, -5697660), (443, 158613252), (457, -158613252), (474, -22659036), (498, 62829660), (503, -62829660), (507, -62829660), (513, 62829660), (523, 22659036), (524, 62829660), (530, -62829660), (534, -22659036), (571, 2084280), (572, 50787072), (573, 66801348), (574, -1139532), (575, -65759208), (576, 117970596), (577, -66801348), (578, 1139532), (583, -67977108), (587, 113295180), (593, 22659036), (715, -246386400), (716, 246386400), (782, 246386400), (786, -246386400), (837, -246386400), (838, 246386400), (1149, -156720564), (1150, 29876700), (1154, -33006360), (1155, -29876700), (1157, 156720564), (1161, 33006360), (1168, 156720564), (1169, -29876700), (1173, 33006360), (1181, 29876700), (1183, -156720564), (1185, -33006360), (1193, 29876700), (1195, -33006360), (1199, -29876700), (1201, 33006360), (1206, -156720564), (1209, 156720564), (1235, -66152676), (1236, -14855220), (1240, -246321540), (1241, 14855220), (1243, 66152676), (1247, 246321540), (1252, -247390920), (1257, 247390920), (1262, 66152676), (1263, 14855220), (1267, 246321540), (1276, 247390920), (1282, -247390920), (1285, -14855220), (1287, -66152676), (1289, -246321540), (1297, -14855220), (1299, -246321540), (1306, 14855220), (1308, 246321540), (1313, -66152676), (1317, -247390920), (1319, 247390920), (1321, 66152676), (1362, 118984320), (1363, 203483040), (1367, 128597280), (1368, -203483040), (1370, -118984320), (1372, -128597280), (1377, 66152676), (1378, -1695900), (1379, 95074440), (1382, 65260380), (1383, 72746460), (1385, 107890140), (1389, -95074440), (1391, -71050560), (1393, -174042816), (1395, -65260380), (1403, -289025916), (1404, 16717380), (1405, -95074440), (1408, -65260380), (1409, -87767940), (1411, 114983100), (1422, 95074440), (1424, 71050560), (1426, 174042816), (1428, 65260380), (1435, -118984320), (1436, -203483040), (1439, -128597280), (1445, 222873240), (1446, -15021480), (1449, 95074440), (1451, 87767940), (1453, -114983100), (1457, -95074440), (1459, -72746460), (1461, -107890140), (1464, 203483040), (1466, 118984320), (1468, 128597280), (1473, 203483040), (1475, 128597280), (1480, 15021480), (1482, -16717380), (1484, 65260380), (1490, 1695900), (1492, -65260380), (1496, -203483040), (1498, -128597280), (1501, 118984320), (1504, -222873240), (1506, 289025916), (1511, -66152676), (1514, -118984320), (1582, 128597280), (1585, -128597280), (1589, -181061160), (1590, 57891240), (1592, 524897100), (1596, -57891240), (1598, -343835940), (1604, -98266740), (1605, -57891240), (1607, -245569200), (1613, 57891240), (1615, 343835940), (1620, -128597280), (1626, 279327900), (1629, 57891240), (1631, 245569200), (1637, -57891240), (1639, -524897100), (1644, 128597280), (1647, 128597280), (1649, -279327900), (1651, 98266740), (1653, 181061160), (1655, -128597280), (1701, 41737464), (1704, -41737464), (1708, -41737464), (1713, 41737464), (1721, 41737464), (1726, -41737464)]

def node120 : Integer.Sparse (Fin 2886) := [(1275, -117830160), (1315, 117830160), (1416, 117830160), (1508, -117830160), (1710, -117830160), (1723, 117830160), (2434, 32314788), (2441, 344691072), (2443, -193888728), (2467, -258518304), (2481, 258518304), (2504, 129259152), (2507, -226203516), (2569, 32314788), (2583, -32314788), (2763, 21543192), (2792, -32314788), (2796, -21543192), (2797, -129259152), (2810, -64629576), (2814, 193888728), (2817, 64629576), (2818, -96944364), (2847, -32314788), (2855, 32314788), (2856, -21543192)]

def node121 : Integer.Sparse (Fin 2886) := [(916, 36039360), (922, -36039360), (1000, -36039360), (1008, 36039360), (1103, 36039360), (1105, -36039360), (2803, -282378360), (2805, 282378360), (2838, 282378360), (2842, -282378360), (2863, -282378360), (2865, 282378360)]

def node122 : Integer.Sparse (Fin 2886) := [(916, 36039360), (922, -36039360), (1000, -36039360), (1008, 36039360), (1103, 36039360), (1105, -36039360), (2427, 17688504), (2439, 11792336), (2458, -17688504), (2465, -194573544), (2502, 17688504), (2503, 194573544), (2561, 17688504), (2568, 194573544), (2667, -141508032), (2758, -17688504), (2759, -170988872), (2769, 141508032), (2789, -17688504), (2798, -11792336), (2801, 17688504), (2803, -282378360), (2805, 282378360), (2808, -17688504), (2815, 17688504), (2816, -17688504), (2836, -17688504), (2838, 282378360), (2842, -282378360), (2845, 17688504), (2853, -17688504), (2854, -5896168), (2863, -282378360), (2865, 282378360), (2879, -35377008), (2880, 35377008)]

def node123 : Integer.Sparse (Fin 2886) := [(916, 36039360), (922, -36039360), (1000, -36039360), (1008, 36039360), (1103, 36039360), (1105, -36039360), (1275, -117830160), (1315, 117830160), (1416, 117830160), (1508, -117830160), (1710, -117830160), (1723, 117830160), (2427, 17688504), (2434, 32314788), (2439, 11792336), (2441, 344691072), (2443, -193888728), (2458, -17688504), (2465, -194573544), (2467, -258518304), (2481, 258518304), (2502, 17688504), (2503, 194573544), (2504, 129259152), (2507, -226203516), (2561, 17688504), (2568, 194573544), (2569, 32314788), (2583, -32314788), (2667, -141508032), (2758, -17688504), (2759, -170988872), (2763, 21543192), (2769, 141508032), (2789, -17688504), (2792, -32314788), (2796, -21543192), (2797, -129259152), (2798, -11792336), (2801, 17688504), (2803, -282378360), (2805, 282378360), (2808, -17688504), (2810, -64629576), (2814, 193888728), (2815, 17688504), (2816, -17688504), (2817, 64629576), (2818, -96944364), (2836, -17688504), (2838, 282378360), (2842, -282378360), (2845, 17688504), (2847, -32314788), (2853, -17688504), (2854, -5896168), (2855, 32314788), (2856, -21543192), (2863, -282378360), (2865, 282378360), (2879, -35377008), (2880, 35377008)]

def node124 : Integer.Sparse (Fin 2886) := [(1252, -247390920), (1257, 247390920), (1276, 247390920), (1282, -247390920), (1317, -247390920), (1319, 247390920), (2821, 473240400), (2823, -473240400), (2826, -473240400), (2829, 567888480), (2832, 378592320), (2833, -473240400)]

def node125 : Integer.Sparse (Fin 2886) := [(917, 133529400), (921, -133529400), (1001, -133529400), (1007, 133529400), (1102, 133529400), (1104, -133529400), (2441, 258197328), (2443, -150615108), (2467, 21516444), (2481, -21516444), (2504, -21516444), (2507, 43032888), (2569, -172131552), (2583, 172131552), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

def node126 : Integer.Sparse (Fin 2886) := [(917, 133529400), (921, -133529400), (1001, -133529400), (1007, 133529400), (1102, 133529400), (1104, -133529400), (1282, -15916680), (1319, 15916680), (1420, 15916680), (1509, -15916680), (1711, -15916680), (1724, 15916680), (2441, 258197328), (2443, -150615108), (2467, 21516444), (2481, -21516444), (2504, -21516444), (2507, 43032888), (2569, -172131552), (2583, 172131552), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

def node127 : Integer.Sparse (Fin 2886) := [(917, 133529400), (921, -133529400), (1001, -133529400), (1007, 133529400), (1102, 133529400), (1104, -133529400), (1252, -247390920), (1257, 247390920), (1276, 247390920), (1282, -263307600), (1317, -247390920), (1319, 263307600), (1420, 15916680), (1509, -15916680), (1711, -15916680), (1724, 15916680), (2441, 258197328), (2443, -150615108), (2467, 21516444), (2481, -21516444), (2504, -21516444), (2507, 43032888), (2569, -172131552), (2583, 172131552), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2821, 473240400), (2823, -473240400), (2826, -473240400), (2829, 567888480), (2832, 378592320), (2833, -473240400), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node128 : Integer.Sparse (Fin 2886) := [(916, 36039360), (917, 133529400), (921, -133529400), (922, -36039360), (1000, -36039360), (1001, -133529400), (1007, 133529400), (1008, 36039360), (1102, 133529400), (1103, 36039360), (1104, -133529400), (1105, -36039360), (1252, -247390920), (1257, 247390920), (1275, -117830160), (1276, 247390920), (1282, -263307600), (1315, 117830160), (1317, -247390920), (1319, 263307600), (1416, 117830160), (1420, 15916680), (1508, -117830160), (1509, -15916680), (1710, -117830160), (1711, -15916680), (1723, 117830160), (1724, 15916680), (2427, 17688504), (2434, 32314788), (2439, 11792336), (2441, 602888400), (2443, -344503836), (2458, -17688504), (2465, -194573544), (2467, -237001860), (2481, 237001860), (2502, 17688504), (2503, 194573544), (2504, 107742708), (2507, -183170628), (2561, 17688504), (2568, 194573544), (2569, -139816764), (2583, 139816764), (2667, -141508032), (2758, -17688504), (2759, -170988872), (2760, 86065776), (2763, -129071916), (2769, 141508032), (2789, -17688504), (2792, -32314788), (2796, -64576080), (2797, -193808484), (2798, -11792336), (2801, 17688504), (2803, -282378360), (2805, 282378360), (2808, -17688504), (2810, -86146020), (2814, 215405172), (2815, 17688504), (2816, -17688504), (2817, 86146020), (2818, -139977252), (2821, 473240400), (2823, -473240400), (2826, -473240400), (2829, 567888480), (2832, 378592320), (2833, -473240400), (2836, -17688504), (2838, 282378360), (2842, -282378360), (2845, 17688504), (2847, -75347676), (2852, 129098664), (2853, -17688504), (2854, -5896168), (2855, 75347676), (2856, -86092524), (2863, -282378360), (2865, 282378360), (2879, -35377008), (2880, 35377008)]

def node129 : Integer.Sparse (Fin 2886) := [(2164, -140368800), (2169, 112295040), (2176, -28073760), (2237, 98258160), (2244, -112295040), (2322, -56147520), (2323, 98258160), (2778, -189148320), (2780, 189148320), (2781, 28073760), (2785, 28073760), (2859, 42110640), (2860, 189148320), (2868, -189148320), (2869, -84221280), (2872, -189148320), (2876, 189148320), (2878, -28073760), (2881, 42110640)]

def node130 : Integer.Sparse (Fin 2886) := [(1955, 145419960), (1956, -145419960), (2039, -145419960), (2040, 145419960), (2095, 145419960), (2096, -145419960), (2178, -337123176), (2180, 207460416), (2194, -25932552), (2246, 207460416), (2260, -207460416), (2324, -103730208), (2327, 181527864), (2783, 77797656), (2784, 51865104), (2786, 25932552), (2871, 51865104), (2877, -155595312), (2882, -51865104), (2885, 77797656)]

def node131 : Integer.Sparse (Fin 2886) := [(1955, 145419960), (1956, -145419960), (2039, -145419960), (2040, 145419960), (2095, 145419960), (2096, -145419960), (2178, -337123176), (2180, 207460416), (2194, -25932552), (2246, 207460416), (2260, -207460416), (2324, -103730208), (2327, 181527864), (2783, 77797656), (2784, 51865104), (2786, 25932552), (2811, -993497880), (2813, 993497880), (2848, 993497880), (2851, -993497880), (2871, 51865104), (2873, -993497880), (2874, 993497880), (2877, -155595312), (2882, -51865104), (2885, 77797656)]

def node132 : Integer.Sparse (Fin 2886) := [(1955, 145419960), (1956, -145419960), (2039, -145419960), (2040, 145419960), (2095, 145419960), (2096, -145419960), (2164, -140368800), (2169, 112295040), (2176, -28073760), (2178, -337123176), (2180, 207460416), (2194, -25932552), (2237, 98258160), (2244, -112295040), (2246, 207460416), (2260, -207460416), (2322, -56147520), (2323, 98258160), (2324, -103730208), (2327, 181527864), (2778, -189148320), (2780, 189148320), (2781, 28073760), (2783, 77797656), (2784, 51865104), (2785, 28073760), (2786, 25932552), (2811, -993497880), (2813, 993497880), (2848, 993497880), (2851, -993497880), (2859, 42110640), (2860, 189148320), (2868, -189148320), (2869, -84221280), (2871, 51865104), (2872, -189148320), (2873, -993497880), (2874, 993497880), (2876, 189148320), (2877, -155595312), (2878, -28073760), (2881, 42110640), (2882, -51865104), (2885, 77797656)]

set_option maxHeartbeats 1000000 in
def node133 : Integer.Sparse (Fin 2886) := [(1253, -290176440), (1256, 290176440), (1277, 290176440), (1281, -290176440), (1316, -290176440), (1318, 290176440), (2802, 205020480), (2807, -205020480), (2837, -205020480), (2844, 205020480), (2873, 205020480), (2874, -205020480)]

def node134 : Integer.Sparse (Fin 2886) := [(1253, -290176440), (1256, 290176440), (1277, 290176440), (1281, -290176440), (1316, -290176440), (1318, 290176440), (2427, 448065000), (2432, -373387500), (2439, 24892500), (2458, -522742500), (2465, 597420000), (2502, 298710000), (2503, -522742500), (2561, 49785000), (2568, -74677500), (2759, 49785000), (2789, 298710000), (2794, -373387500), (2798, -24892500), (2801, -224032500), (2802, 205020480), (2807, -205020480), (2808, 448065000), (2815, 149355000), (2816, -224032500), (2836, -49785000), (2837, -205020480), (2844, 205020480), (2853, 74677500), (2854, -49785000), (2873, 205020480), (2874, -205020480)]

def node135 : Integer.Sparse (Fin 2886) := [(1341, 205539480), (1343, -205539480), (1553, -205539480), (1556, 205539480), (1742, 205539480), (1743, -205539480), (2441, 4799504), (2467, -7199256), (2481, -35996280), (2504, 7199256), (2507, 35996280), (2569, 7199256), (2583, 35996280), (2670, -28797024), (2760, -7199256), (2763, -31196776), (2772, 28797024), (2796, -4799504), (2810, 7199256), (2814, -7199256), (2847, -7199256), (2852, 7199256), (2856, -4799504), (2883, -7199256), (2884, 7199256)]

def node136 : Integer.Sparse (Fin 2886) := [(1341, 205539480), (1343, -205539480), (1553, -205539480), (1556, 205539480), (1742, 205539480), (1743, -205539480), (2441, 4799504), (2467, -7199256), (2481, -35996280), (2504, 7199256), (2507, 35996280), (2569, 7199256), (2583, 35996280), (2670, -28797024), (2760, -7199256), (2763, -31196776), (2772, 28797024), (2790, 611468400), (2793, -611468400), (2796, -4799504), (2802, -611468400), (2807, 611468400), (2810, 7199256), (2811, 611468400), (2813, -611468400), (2814, -7199256), (2847, -7199256), (2852, 7199256), (2856, -4799504), (2883, -7199256), (2884, 7199256)]

def node137 : Integer.Sparse (Fin 2886) := [(1253, -290176440), (1256, 290176440), (1277, 290176440), (1281, -290176440), (1316, -290176440), (1318, 290176440), (1341, 205539480), (1343, -205539480), (1553, -205539480), (1556, 205539480), (1742, 205539480), (1743, -205539480), (2427, 448065000), (2432, -373387500), (2439, 24892500), (2441, 4799504), (2458, -522742500), (2465, 597420000), (2467, -7199256), (2481, -35996280), (2502, 298710000), (2503, -522742500), (2504, 7199256), (2507, 35996280), (2561, 49785000), (2568, -74677500), (2569, 7199256), (2583, 35996280), (2670, -28797024), (2759, 49785000), (2760, -7199256), (2763, -31196776), (2772, 28797024), (2789, 298710000), (2790, 611468400), (2793, -611468400), (2794, -373387500), (2796, -4799504), (2798, -24892500), (2801, -224032500), (2802, -406447920), (2807, 406447920), (2808, 448065000), (2810, 7199256), (2811, 611468400), (2813, -611468400), (2814, -7199256), (2815, 149355000), (2816, -224032500), (2836, -49785000), (2837, -205020480), (2844, 205020480), (2847, -7199256), (2852, 7199256), (2853, 74677500), (2854, -49785000), (2856, -4799504), (2873, 205020480), (2874, -205020480), (2883, -7199256), (2884, 7199256)]

def node138 : Integer.Sparse (Fin 2886) := [(1253, -290176440), (1256, 290176440), (1277, 290176440), (1281, -290176440), (1316, -290176440), (1318, 290176440), (1341, 205539480), (1343, -205539480), (1553, -205539480), (1556, 205539480), (1742, 205539480), (1743, -205539480), (1955, 145419960), (1956, -145419960), (2039, -145419960), (2040, 145419960), (2095, 145419960), (2096, -145419960), (2164, -140368800), (2169, 112295040), (2176, -28073760), (2178, -337123176), (2180, 207460416), (2194, -25932552), (2237, 98258160), (2244, -112295040), (2246, 207460416), (2260, -207460416), (2322, -56147520), (2323, 98258160), (2324, -103730208), (2327, 181527864), (2427, 448065000), (2432, -373387500), (2439, 24892500), (2441, 4799504), (2458, -522742500), (2465, 597420000), (2467, -7199256), (2481, -35996280), (2502, 298710000), (2503, -522742500), (2504, 7199256), (2507, 35996280), (2561, 49785000), (2568, -74677500), (2569, 7199256), (2583, 35996280), (2670, -28797024), (2759, 49785000), (2760, -7199256), (2763, -31196776), (2772, 28797024), (2778, -189148320), (2780, 189148320), (2781, 28073760), (2783, 77797656), (2784, 51865104), (2785, 28073760), (2786, 25932552), (2789, 298710000), (2790, 611468400), (2793, -611468400), (2794, -373387500), (2796, -4799504), (2798, -24892500), (2801, -224032500), (2802, -406447920), (2807, 406447920), (2808, 448065000), (2810, 7199256), (2811, -382029480), (2813, 382029480), (2814, -7199256), (2815, 149355000), (2816, -224032500), (2836, -49785000), (2837, -205020480), (2844, 205020480), (2847, -7199256), (2848, 993497880), (2851, -993497880), (2852, 7199256), (2853, 74677500), (2854, -49785000), (2856, -4799504), (2859, 42110640), (2860, 189148320), (2868, -189148320), (2869, -84221280), (2871, 51865104), (2872, -189148320), (2873, -788477400), (2874, 788477400), (2876, 189148320), (2877, -155595312), (2878, -28073760), (2881, 42110640), (2882, -51865104), (2883, -7199256), (2884, 7199256), (2885, 77797656)]

def node139 : Integer.Sparse (Fin 2886) := [(916, 36039360), (917, 133529400), (921, -133529400), (922, -36039360), (1000, -36039360), (1001, -133529400), (1007, 133529400), (1008, 36039360), (1102, 133529400), (1103, 36039360), (1104, -133529400), (1105, -36039360), (1252, -247390920), (1253, -290176440), (1256, 290176440), (1257, 247390920), (1275, -117830160), (1276, 247390920), (1277, 290176440), (1281, -290176440), (1282, -263307600), (1315, 117830160), (1316, -290176440), (1317, -247390920), (1318, 290176440), (1319, 263307600), (1341, 205539480), (1343, -205539480), (1416, 117830160), (1420, 15916680), (1508, -117830160), (1509, -15916680), (1553, -205539480), (1556, 205539480), (1710, -117830160), (1711, -15916680), (1723, 117830160), (1724, 15916680), (1742, 205539480), (1743, -205539480), (1955, 145419960), (1956, -145419960), (2039, -145419960), (2040, 145419960), (2095, 145419960), (2096, -145419960), (2164, -140368800), (2169, 112295040), (2176, -28073760), (2178, -337123176), (2180, 207460416), (2194, -25932552), (2237, 98258160), (2244, -112295040), (2246, 207460416), (2260, -207460416), (2322, -56147520), (2323, 98258160), (2324, -103730208), (2327, 181527864), (2427, 465753504), (2432, -373387500), (2434, 32314788), (2439, 36684836), (2441, 607687904), (2443, -344503836), (2458, -540431004), (2465, 402846456), (2467, -244201116), (2481, 201005580), (2502, 316398504), (2503, -328168956), (2504, 114941964), (2507, -147174348), (2561, 67473504), (2568, 119896044), (2569, -132617508), (2583, 175813044), (2667, -141508032), (2670, -28797024), (2758, -17688504), (2759, -121203872), (2760, 78866520), (2763, -160268692), (2769, 141508032), (2772, 28797024), (2778, -189148320), (2780, 189148320), (2781, 28073760), (2783, 77797656), (2784, 51865104), (2785, 28073760), (2786, 25932552), (2789, 281021496), (2790, 611468400), (2792, -32314788), (2793, -611468400), (2794, -373387500), (2796, -69375584), (2797, -193808484), (2798, -36684836), (2801, -206343996), (2802, -406447920), (2803, -282378360), (2805, 282378360), (2807, 406447920), (2808, 430376496), (2810, -78946764), (2811, -382029480), (2813, 382029480), (2814, 208205916), (2815, 167043504), (2816, -241721004), (2817, 86146020), (2818, -139977252), (2821, 473240400), (2823, -473240400), (2826, -473240400), (2829, 567888480), (2832, 378592320), (2833, -473240400), (2836, -67473504), (2837, -205020480), (2838, 282378360), (2842, -282378360), (2844, 205020480), (2845, 17688504), (2847, -82546932), (2848, 993497880), (2851, -993497880), (2852, 136297920), (2853, 56988996), (2854, -55681168), (2855, 75347676), (2856, -90892028), (2859, 42110640), (2860, 189148320), (2863, -282378360), (2865, 282378360), (2868, -189148320), (2869, -84221280), (2871, 51865104), (2872, -189148320), (2873, -788477400), (2874, 788477400), (2876, 189148320), (2877, -155595312), (2878, -28073760), (2879, -35377008), (2880, 35377008), (2881, 42110640), (2882, -51865104), (2883, -7199256), (2884, 7199256), (2885, 77797656)]

def node140 : Integer.Sparse (Fin 2886) := [(206, -19441320), (217, 19441320), (263, 19441320), (276, -19441320), (339, -19441320), (359, 19441320), (1154, -1968708), (1161, 1968708), (1173, 1968708), (1185, -1968708), (1195, -1968708), (1201, 1968708), (1240, 1968708), (1247, -1968708), (1267, -11812248), (1289, -7874832), (1296, 9843540), (1299, 1968708), (1308, 7874832), (1382, -1968708), (1395, 1968708), (1408, 11812248), (1428, 7874832), (1479, -9843540), (1484, -1968708), (1492, -7874832), (1592, 1968708), (1598, -1968708), (1604, -9843540), (1607, -1968708), (1615, -7874832), (1626, 9843540), (1631, 1968708), (1639, 7874832)]

def node141 : Integer.Sparse (Fin 2886) := [(16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (102, -9389184), (121, 9389184), (180, -2347296), (185, -16431072), (191, 11736480), (327, 2347296), (333, 16431072), (423, -14083776), (569, -11736480), (574, 14083776), (1151, -59629680), (1170, 59629680), (1237, 59629680), (1264, -59629680), (1379, -59629680), (1405, 59629680)]

def node142 : Integer.Sparse (Fin 2886) := [(16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (102, -9389184), (121, 9389184), (180, -2347296), (185, -16431072), (191, 11736480), (327, 2347296), (333, 16431072), (423, -14083776), (569, -11736480), (574, 14083776), (1149, -82032432), (1151, -59629680), (1157, -123048648), (1168, 82032432), (1170, 59629680), (1176, 102540540), (1183, 20508108), (1206, 20508108), (1209, -20508108), (1235, 82032432), (1237, 59629680), (1243, 123048648), (1262, -82032432), (1264, -59629680), (1270, -102540540), (1287, -20508108), (1313, -20508108), (1321, 20508108), (1377, -82032432), (1379, -59629680), (1385, -102540540), (1393, -20508108), (1403, 82032432), (1405, 59629680), (1411, 102540540), (1426, 20508108), (1506, 20508108), (1511, -20508108), (1701, -20508108), (1704, 20508108), (1708, 20508108), (1713, -20508108), (1721, -20508108), (1726, 20508108)]

def node143 : Integer.Sparse (Fin 2886) := [(16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (102, -9389184), (121, 9389184), (180, -2347296), (185, -16431072), (191, 11736480), (206, -19441320), (217, 19441320), (263, 19441320), (276, -19441320), (327, 2347296), (333, 16431072), (339, -19441320), (359, 19441320), (423, -14083776), (569, -11736480), (574, 14083776), (1149, -82032432), (1151, -59629680), (1154, -1968708), (1157, -123048648), (1161, 1968708), (1168, 82032432), (1170, 59629680), (1173, 1968708), (1176, 102540540), (1183, 20508108), (1185, -1968708), (1195, -1968708), (1201, 1968708), (1206, 20508108), (1209, -20508108), (1235, 82032432), (1237, 59629680), (1240, 1968708), (1243, 123048648), (1247, -1968708), (1262, -82032432), (1264, -59629680), (1267, -11812248), (1270, -102540540), (1287, -20508108), (1289, -7874832), (1296, 9843540), (1299, 1968708), (1308, 7874832), (1313, -20508108), (1321, 20508108), (1377, -82032432), (1379, -59629680), (1382, -1968708), (1385, -102540540), (1393, -20508108), (1395, 1968708), (1403, 82032432), (1405, 59629680), (1408, 11812248), (1411, 102540540), (1426, 20508108), (1428, 7874832), (1479, -9843540), (1484, -1968708), (1492, -7874832), (1506, 20508108), (1511, -20508108), (1592, 1968708), (1598, -1968708), (1604, -9843540), (1607, -1968708), (1615, -7874832), (1626, 9843540), (1631, 1968708), (1639, 7874832), (1701, -20508108), (1704, 20508108), (1708, 20508108), (1713, -20508108), (1721, -20508108), (1726, 20508108)]

def node144 : Integer.Sparse (Fin 2886) := [(204, 2084280), (209, -2084280), (215, -2084280), (227, 4168560), (240, -2084280), (261, -2084280), (266, 2084280), (274, 3126420), (279, 11463540), (287, 6252840), (300, -12505680), (301, -8337120), (337, 1042140), (342, -1042140), (352, -2084280), (357, -2084280), (362, -10421400), (372, -7642360), (391, 3126420), (395, -3126420), (424, 7294980), (425, 2084280), (426, 5210700), (571, 2084280), (572, 11810920), (573, 8337120), (575, -7294980), (576, 1042140), (577, -8337120), (1282, -15916680), (1319, 15916680), (1420, 15916680), (1509, -15916680), (1711, -15916680), (1724, 15916680)]

def node145 : Integer.Sparse (Fin 2886) := [(184, -23917920), (189, 23917920), (332, 23917920), (404, -23917920), (495, -23917920), (518, 23917920), (1154, -12646824), (1161, 12646824), (1173, 75880944), (1185, 50587296), (1192, -63234120), (1195, -12646824), (1201, -50587296), (1240, 12646824), (1247, -12646824), (1267, -12646824), (1289, 12646824), (1299, 12646824), (1308, -12646824), (1382, -75880944), (1395, -50587296), (1408, 12646824), (1428, -12646824), (1479, 63234120), (1484, 50587296), (1492, 12646824), (1589, 63234120), (1592, 12646824), (1598, 50587296), (1607, -12646824), (1615, 12646824), (1626, -63234120), (1631, -50587296), (1639, -12646824)]

def node146 : Integer.Sparse (Fin 2886) := [(184, -23917920), (189, 23917920), (204, 74758320), (209, 112137480), (215, -74758320), (220, -93447900), (227, -49838880), (239, 12459720), (240, 18689580), (261, -74758320), (266, -112137480), (274, 93447900), (279, 130827060), (287, 37379160), (301, -37379160), (332, 23917920), (337, 56068740), (342, 56068740), (352, 37379160), (357, -74758320), (362, -93447900), (372, -49838880), (404, -23917920), (425, -18689580), (426, 18689580), (495, -23917920), (518, 23917920), (572, 12459720), (573, 18689580), (576, 18689580), (577, -18689580), (1154, -12646824), (1161, 12646824), (1173, 75880944), (1185, 50587296), (1192, -63234120), (1195, -12646824), (1201, -50587296), (1240, 12646824), (1247, -12646824), (1267, -12646824), (1289, 12646824), (1299, 12646824), (1308, -12646824), (1382, -75880944), (1395, -50587296), (1408, 12646824), (1428, -12646824), (1479, 63234120), (1484, 50587296), (1492, 12646824), (1589, 63234120), (1592, 12646824), (1598, 50587296), (1607, -12646824), (1615, 12646824), (1626, -63234120), (1631, -50587296), (1639, -12646824)]

def node147 : Integer.Sparse (Fin 2886) := [(184, -23917920), (189, 23917920), (204, 76842600), (209, 110053200), (215, -76842600), (220, -93447900), (227, -45670320), (239, 12459720), (240, 16605300), (261, -76842600), (266, -110053200), (274, 96574320), (279, 142290600), (287, 43632000), (300, -12505680), (301, -45716280), (332, 23917920), (337, 57110880), (342, 55026600), (352, 35294880), (357, -76842600), (362, -103869300), (372, -57481240), (391, 3126420), (395, -3126420), (404, -23917920), (424, 7294980), (425, -16605300), (426, 23900280), (495, -23917920), (518, 23917920), (571, 2084280), (572, 24270640), (573, 27026700), (575, -7294980), (576, 19731720), (577, -27026700), (1154, -12646824), (1161, 12646824), (1173, 75880944), (1185, 50587296), (1192, -63234120), (1195, -12646824), (1201, -50587296), (1240, 12646824), (1247, -12646824), (1267, -12646824), (1282, -15916680), (1289, 12646824), (1299, 12646824), (1308, -12646824), (1319, 15916680), (1382, -75880944), (1395, -50587296), (1408, 12646824), (1420, 15916680), (1428, -12646824), (1479, 63234120), (1484, 50587296), (1492, 12646824), (1509, -15916680), (1589, 63234120), (1592, 12646824), (1598, 50587296), (1607, -12646824), (1615, 12646824), (1626, -63234120), (1631, -50587296), (1639, -12646824), (1711, -15916680), (1724, 15916680)]

def node148 : Integer.Sparse (Fin 2886) := [(16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (102, -9389184), (121, 9389184), (180, -2347296), (184, -23917920), (185, -16431072), (189, 23917920), (191, 11736480), (204, 76842600), (206, -19441320), (209, 110053200), (215, -76842600), (217, 19441320), (220, -93447900), (227, -45670320), (239, 12459720), (240, 16605300), (261, -76842600), (263, 19441320), (266, -110053200), (274, 96574320), (276, -19441320), (279, 142290600), (287, 43632000), (300, -12505680), (301, -45716280), (327, 2347296), (332, 23917920), (333, 16431072), (337, 57110880), (339, -19441320), (342, 55026600), (352, 35294880), (357, -76842600), (359, 19441320), (362, -103869300), (372, -57481240), (391, 3126420), (395, -3126420), (404, -23917920), (423, -14083776), (424, 7294980), (425, -16605300), (426, 23900280), (495, -23917920), (518, 23917920), (569, -11736480), (571, 2084280), (572, 24270640), (573, 27026700), (574, 14083776), (575, -7294980), (576, 19731720), (577, -27026700), (1149, -82032432), (1151, -59629680), (1154, -14615532), (1157, -123048648), (1161, 14615532), (1168, 82032432), (1170, 59629680), (1173, 77849652), (1176, 102540540), (1183, 20508108), (1185, 48618588), (1192, -63234120), (1195, -14615532), (1201, -48618588), (1206, 20508108), (1209, -20508108), (1235, 82032432), (1237, 59629680), (1240, 14615532), (1243, 123048648), (1247, -14615532), (1262, -82032432), (1264, -59629680), (1267, -24459072), (1270, -102540540), (1282, -15916680), (1287, -20508108), (1289, 4771992), (1296, 9843540), (1299, 14615532), (1308, -4771992), (1313, -20508108), (1319, 15916680), (1321, 20508108), (1377, -82032432), (1379, -59629680), (1382, -77849652), (1385, -102540540), (1393, -20508108), (1395, -48618588), (1403, 82032432), (1405, 59629680), (1408, 24459072), (1411, 102540540), (1420, 15916680), (1426, 20508108), (1428, -4771992), (1479, 53390580), (1484, 48618588), (1492, 4771992), (1506, 20508108), (1509, -15916680), (1511, -20508108), (1589, 63234120), (1592, 14615532), (1598, 48618588), (1604, -9843540), (1607, -14615532), (1615, 4771992), (1626, -53390580), (1631, -48618588), (1639, -4771992), (1701, -20508108), (1704, 20508108), (1708, 20508108), (1711, -15916680), (1713, -20508108), (1721, -20508108), (1724, 15916680), (1726, 20508108)]

def node149 : Integer.Sparse (Fin 2886) := [(1120, -21388080), (1121, -10263960), (1127, 21388080), (1131, 10263960), (1368, 21388080), (1370, 10263960), (1473, -21388080), (1501, -10263960), (1583, -21388080), (1621, 21388080), (1698, -10263960), (1716, 10263960)]

def node150 : Integer.Sparse (Fin 2886) := [(647, -15968880), (652, 15968880), (716, 15968880), (723, -15968880), (786, -15968880), (792, 15968880), (1119, 20396280), (1123, 20396280), (1126, -20396280), (1129, -20396280), (1367, -20396280), (1372, -20396280), (1472, 20396280), (1475, 20396280), (1582, 20396280), (1585, 20396280), (1620, -20396280), (1623, -20396280)]

def node151 : Integer.Sparse (Fin 2886) := [(647, -15968880), (652, 15968880), (716, 15968880), (723, -15968880), (786, -15968880), (792, 15968880), (1119, 20396280), (1123, 20396280), (1126, -20396280), (1129, -20396280), (1150, 53505840), (1155, 80258760), (1169, -53505840), (1174, -66882300), (1181, -13376460), (1193, -13376460), (1199, 13376460), (1236, -53505840), (1241, -80258760), (1263, 53505840), (1268, 66882300), (1285, 13376460), (1297, 13376460), (1306, -13376460), (1367, -20396280), (1372, -20396280), (1378, 53505840), (1383, 66882300), (1391, 13376460), (1404, -53505840), (1409, -66882300), (1424, -13376460), (1472, 20396280), (1475, 20396280), (1482, -13376460), (1490, 13376460), (1582, 20396280), (1585, 20396280), (1590, 13376460), (1596, -13376460), (1605, -13376460), (1613, 13376460), (1620, -20396280), (1623, -20396280), (1629, 13376460), (1637, -13376460)]

def node152 : Integer.Sparse (Fin 2886) := [(647, -15968880), (652, 15968880), (716, 15968880), (723, -15968880), (786, -15968880), (792, 15968880), (1119, 20396280), (1120, -21388080), (1121, -10263960), (1123, 20396280), (1126, -20396280), (1127, 21388080), (1129, -20396280), (1131, 10263960), (1150, 53505840), (1155, 80258760), (1169, -53505840), (1174, -66882300), (1181, -13376460), (1193, -13376460), (1199, 13376460), (1236, -53505840), (1241, -80258760), (1263, 53505840), (1268, 66882300), (1285, 13376460), (1297, 13376460), (1306, -13376460), (1367, -20396280), (1368, 21388080), (1370, 10263960), (1372, -20396280), (1378, 53505840), (1383, 66882300), (1391, 13376460), (1404, -53505840), (1409, -66882300), (1424, -13376460), (1472, 20396280), (1473, -21388080), (1475, 20396280), (1482, -13376460), (1490, 13376460), (1501, -10263960), (1582, 20396280), (1583, -21388080), (1585, 20396280), (1590, 13376460), (1596, -13376460), (1605, -13376460), (1613, 13376460), (1620, -20396280), (1621, 21388080), (1623, -20396280), (1629, 13376460), (1637, -13376460), (1698, -10263960), (1716, 10263960)]

def node153 : Integer.Sparse (Fin 2886) := [(205, 9701616), (208, -9701616), (216, -9701616), (226, 9701616), (231, 9701616), (236, -9701616), (262, -9701616), (265, 9701616), (275, 9701616), (278, 48508080), (286, 38806464), (291, -58209696), (297, -38806464), (338, 9701616), (351, -9701616), (358, -9701616), (361, -48508080), (371, -38806464), (407, 48508080), (410, 9701616), (416, 38806464), (498, -9701616), (503, 9701616), (507, 58209696), (513, 38806464), (521, -48508080), (524, -9701616), (530, -38806464), (1150, 23512944), (1155, 94051776), (1169, -23512944), (1181, 23512944), (1193, -94051776), (1199, -23512944), (1236, -23512944), (1241, -94051776), (1263, 23512944), (1285, -23512944), (1297, 94051776), (1306, 23512944), (1378, 23512944), (1391, -23512944), (1404, -23512944), (1424, 23512944), (1482, 23512944), (1490, -23512944), (1590, 94051776), (1596, 23512944), (1605, -94051776), (1613, -23512944), (1629, -23512944), (1637, 23512944)]

def node154 : Integer.Sparse (Fin 2886) := [(205, 9701616), (208, -9701616), (216, -9701616), (226, 9701616), (231, 9701616), (236, -9701616), (262, -9701616), (265, 9701616), (275, 9701616), (278, 48508080), (286, 38806464), (291, -58209696), (297, -38806464), (338, 9701616), (351, -9701616), (358, -9701616), (361, -48508080), (371, -38806464), (407, 48508080), (410, 9701616), (416, 38806464), (498, -9701616), (503, 9701616), (507, 58209696), (513, 38806464), (521, -48508080), (524, -9701616), (530, -38806464), (1149, -4460160), (1150, 23512944), (1155, 94051776), (1157, 4460160), (1168, 4460160), (1169, -23512944), (1181, 23512944), (1183, -4460160), (1193, -94051776), (1199, -23512944), (1206, -4460160), (1209, 4460160), (1235, 4460160), (1236, -23512944), (1241, -94051776), (1243, -4460160), (1262, -4460160), (1263, 23512944), (1270, -22300800), (1285, -23512944), (1287, -17840640), (1297, 94051776), (1306, 23512944), (1313, 26760960), (1321, 17840640), (1377, -4460160), (1378, 23512944), (1391, -23512944), (1393, 4460160), (1403, 4460160), (1404, -23512944), (1411, 22300800), (1424, 23512944), (1426, 17840640), (1482, 23512944), (1490, -23512944), (1504, -22300800), (1506, -4460160), (1511, -17840640), (1590, 94051776), (1596, 23512944), (1605, -94051776), (1613, -23512944), (1629, -23512944), (1637, 23512944), (1701, 4460160), (1704, -4460160), (1708, -26760960), (1713, -17840640), (1719, 22300800), (1721, 4460160), (1726, 17840640)]

set_option maxHeartbeats 1000000 in
def node155 : Integer.Sparse (Fin 2886) := [(223, -4842156), (225, -51649664), (235, 43579404), (243, 4842156), (246, 3228104), (256, 4842156), (305, -4842156), (308, 14526468), (324, -24210780), (346, 4842156), (350, 33895092), (409, -29052936), (457, -19368624), (474, 19368624), (502, -24210780), (523, 29052936), (1154, 161082624), (1161, 40270656), (1173, -161082624), (1185, -40270656), (1195, -40270656), (1201, 40270656), (1240, -161082624), (1247, -40270656), (1267, 161082624), (1289, 40270656), (1299, 40270656), (1308, -40270656), (1382, 161082624), (1395, 40270656), (1408, -161082624), (1428, -40270656), (1484, -40270656), (1492, 40270656), (1592, 40270656), (1598, -40270656), (1607, -40270656), (1615, 40270656), (1631, 40270656), (1639, -40270656)]

def node156 : Integer.Sparse (Fin 2886) := [(223, -4842156), (225, -51649664), (235, 43579404), (243, 4842156), (246, 3228104), (256, 4842156), (305, -4842156), (308, 14526468), (324, -24210780), (346, 4842156), (350, 33895092), (409, -29052936), (457, -19368624), (474, 19368624), (502, -24210780), (523, 29052936), (1150, 2421900), (1154, 161082624), (1155, -2421900), (1161, 40270656), (1169, -2421900), (1173, -161082624), (1181, 2421900), (1185, -40270656), (1193, 2421900), (1195, -40270656), (1199, -2421900), (1201, 40270656), (1236, -2421900), (1240, -161082624), (1241, 2421900), (1247, -40270656), (1263, 2421900), (1267, 161082624), (1268, 12109500), (1285, 9687600), (1289, 40270656), (1297, -14531400), (1299, 40270656), (1306, -9687600), (1308, -40270656), (1378, 2421900), (1382, 161082624), (1391, -2421900), (1395, 40270656), (1404, -2421900), (1408, -161082624), (1409, -12109500), (1424, -9687600), (1428, -40270656), (1480, 12109500), (1482, 2421900), (1484, -40270656), (1490, 9687600), (1492, 40270656), (1590, -2421900), (1592, 40270656), (1596, 2421900), (1598, -40270656), (1605, 14531400), (1607, -40270656), (1613, 9687600), (1615, 40270656), (1627, -12109500), (1629, -2421900), (1631, 40270656), (1637, -9687600), (1639, -40270656)]

def node157 : Integer.Sparse (Fin 2886) := [(205, 9701616), (208, -9701616), (216, -9701616), (223, -4842156), (225, -51649664), (226, 9701616), (231, 9701616), (235, 43579404), (236, -9701616), (243, 4842156), (246, 3228104), (256, 4842156), (262, -9701616), (265, 9701616), (275, 9701616), (278, 48508080), (286, 38806464), (291, -58209696), (297, -38806464), (305, -4842156), (308, 14526468), (324, -24210780), (338, 9701616), (346, 4842156), (350, 33895092), (351, -9701616), (358, -9701616), (361, -48508080), (371, -38806464), (407, 48508080), (409, -29052936), (410, 9701616), (416, 38806464), (457, -19368624), (474, 19368624), (498, -9701616), (502, -24210780), (503, 9701616), (507, 58209696), (513, 38806464), (521, -48508080), (523, 29052936), (524, -9701616), (530, -38806464), (1149, -4460160), (1150, 25934844), (1154, 161082624), (1155, 91629876), (1157, 4460160), (1161, 40270656), (1168, 4460160), (1169, -25934844), (1173, -161082624), (1181, 25934844), (1183, -4460160), (1185, -40270656), (1193, -91629876), (1195, -40270656), (1199, -25934844), (1201, 40270656), (1206, -4460160), (1209, 4460160), (1235, 4460160), (1236, -25934844), (1240, -161082624), (1241, -91629876), (1243, -4460160), (1247, -40270656), (1262, -4460160), (1263, 25934844), (1267, 161082624), (1268, 12109500), (1270, -22300800), (1285, -13825344), (1287, -17840640), (1289, 40270656), (1297, 79520376), (1299, 40270656), (1306, 13825344), (1308, -40270656), (1313, 26760960), (1321, 17840640), (1377, -4460160), (1378, 25934844), (1382, 161082624), (1391, -25934844), (1393, 4460160), (1395, 40270656), (1403, 4460160), (1404, -25934844), (1408, -161082624), (1409, -12109500), (1411, 22300800), (1424, 13825344), (1426, 17840640), (1428, -40270656), (1480, 12109500), (1482, 25934844), (1484, -40270656), (1490, -13825344), (1492, 40270656), (1504, -22300800), (1506, -4460160), (1511, -17840640), (1590, 91629876), (1592, 40270656), (1596, 25934844), (1598, -40270656), (1605, -79520376), (1607, -40270656), (1613, -13825344), (1615, 40270656), (1627, -12109500), (1629, -25934844), (1631, 40270656), (1637, 13825344), (1639, -40270656), (1701, 4460160), (1704, -4460160), (1708, -26760960), (1713, -17840640), (1719, 22300800), (1721, 4460160), (1726, 17840640)]

def node158 : Integer.Sparse (Fin 2886) := [(205, 9701616), (208, -9701616), (216, -9701616), (223, -4842156), (225, -51649664), (226, 9701616), (231, 9701616), (235, 43579404), (236, -9701616), (243, 4842156), (246, 3228104), (256, 4842156), (262, -9701616), (265, 9701616), (275, 9701616), (278, 48508080), (286, 38806464), (291, -58209696), (297, -38806464), (305, -4842156), (308, 14526468), (324, -24210780), (338, 9701616), (346, 4842156), (350, 33895092), (351, -9701616), (358, -9701616), (361, -48508080), (371, -38806464), (407, 48508080), (409, -29052936), (410, 9701616), (416, 38806464), (457, -19368624), (474, 19368624), (498, -9701616), (502, -24210780), (503, 9701616), (507, 58209696), (513, 38806464), (521, -48508080), (523, 29052936), (524, -9701616), (530, -38806464), (647, -15968880), (652, 15968880), (716, 15968880), (723, -15968880), (786, -15968880), (792, 15968880), (1119, 20396280), (1120, -21388080), (1121, -10263960), (1123, 20396280), (1126, -20396280), (1127, 21388080), (1129, -20396280), (1131, 10263960), (1149, -4460160), (1150, 79440684), (1154, 161082624), (1155, 171888636), (1157, 4460160), (1161, 40270656), (1168, 4460160), (1169, -79440684), (1173, -161082624), (1174, -66882300), (1181, 12558384), (1183, -4460160), (1185, -40270656), (1193, -105006336), (1195, -40270656), (1199, -12558384), (1201, 40270656), (1206, -4460160), (1209, 4460160), (1235, 4460160), (1236, -79440684), (1240, -161082624), (1241, -171888636), (1243, -4460160), (1247, -40270656), (1262, -4460160), (1263, 79440684), (1267, 161082624), (1268, 78991800), (1270, -22300800), (1285, -448884), (1287, -17840640), (1289, 40270656), (1297, 92896836), (1299, 40270656), (1306, 448884), (1308, -40270656), (1313, 26760960), (1321, 17840640), (1367, -20396280), (1368, 21388080), (1370, 10263960), (1372, -20396280), (1377, -4460160), (1378, 79440684), (1382, 161082624), (1383, 66882300), (1391, -12558384), (1393, 4460160), (1395, 40270656), (1403, 4460160), (1404, -79440684), (1408, -161082624), (1409, -78991800), (1411, 22300800), (1424, 448884), (1426, 17840640), (1428, -40270656), (1472, 20396280), (1473, -21388080), (1475, 20396280), (1480, 12109500), (1482, 12558384), (1484, -40270656), (1490, -448884), (1492, 40270656), (1501, -10263960), (1504, -22300800), (1506, -4460160), (1511, -17840640), (1582, 20396280), (1583, -21388080), (1585, 20396280), (1590, 105006336), (1592, 40270656), (1596, 12558384), (1598, -40270656), (1605, -92896836), (1607, -40270656), (1613, -448884), (1615, 40270656), (1620, -20396280), (1621, 21388080), (1623, -20396280), (1627, -12109500), (1629, -12558384), (1631, 40270656), (1637, 448884), (1639, -40270656), (1698, -10263960), (1701, 4460160), (1704, -4460160), (1708, -26760960), (1713, -17840640), (1716, 10263960), (1719, 22300800), (1721, 4460160), (1726, 17840640)]

def node159 : Integer.Sparse (Fin 2886) := [(16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (102, -9389184), (121, 9389184), (180, -2347296), (184, -23917920), (185, -16431072), (189, 23917920), (191, 11736480), (204, 76842600), (205, 9701616), (206, -19441320), (208, -9701616), (209, 110053200), (215, -76842600), (216, -9701616), (217, 19441320), (220, -93447900), (223, -4842156), (225, -51649664), (226, 9701616), (227, -45670320), (231, 9701616), (235, 43579404), (236, -9701616), (239, 12459720), (240, 16605300), (243, 4842156), (246, 3228104), (256, 4842156), (261, -76842600), (262, -9701616), (263, 19441320), (265, 9701616), (266, -110053200), (274, 96574320), (275, 9701616), (276, -19441320), (278, 48508080), (279, 142290600), (286, 38806464), (287, 43632000), (291, -58209696), (297, -38806464), (300, -12505680), (301, -45716280), (305, -4842156), (308, 14526468), (324, -24210780), (327, 2347296), (332, 23917920), (333, 16431072), (337, 57110880), (338, 9701616), (339, -19441320), (342, 55026600), (346, 4842156), (350, 33895092), (351, -9701616), (352, 35294880), (357, -76842600), (358, -9701616), (359, 19441320), (361, -48508080), (362, -103869300), (371, -38806464), (372, -57481240), (391, 3126420), (395, -3126420), (404, -23917920), (407, 48508080), (409, -29052936), (410, 9701616), (416, 38806464), (423, -14083776), (424, 7294980), (425, -16605300), (426, 23900280), (457, -19368624), (474, 19368624), (495, -23917920), (498, -9701616), (502, -24210780), (503, 9701616), (507, 58209696), (513, 38806464), (518, 23917920), (521, -48508080), (523, 29052936), (524, -9701616), (530, -38806464), (569, -11736480), (571, 2084280), (572, 24270640), (573, 27026700), (574, 14083776), (575, -7294980), (576, 19731720), (577, -27026700), (647, -15968880), (652, 15968880), (716, 15968880), (723, -15968880), (786, -15968880), (792, 15968880), (1119, 20396280), (1120, -21388080), (1121, -10263960), (1123, 20396280), (1126, -20396280), (1127, 21388080), (1129, -20396280), (1131, 10263960), (1149, -86492592), (1150, 79440684), (1151, -59629680), (1154, 146467092), (1155, 171888636), (1157, -118588488), (1161, 54886188), (1168, 86492592), (1169, -79440684), (1170, 59629680), (1173, -83232972), (1174, -66882300), (1176, 102540540), (1181, 12558384), (1183, 16047948), (1185, 8347932), (1192, -63234120), (1193, -105006336), (1195, -54886188), (1199, -12558384), (1201, -8347932), (1206, 16047948), (1209, -16047948), (1235, 86492592), (1236, -79440684), (1237, 59629680), (1240, -146467092), (1241, -171888636), (1243, 118588488), (1247, -54886188), (1262, -86492592), (1263, 79440684), (1264, -59629680), (1267, 136623552), (1268, 78991800), (1270, -124841340), (1282, -15916680), (1285, -448884), (1287, -38348748), (1289, 45042648), (1296, 9843540), (1297, 92896836), (1299, 54886188), (1306, 448884), (1308, -45042648), (1313, 6252852), (1319, 15916680), (1321, 38348748), (1367, -20396280), (1368, 21388080), (1370, 10263960), (1372, -20396280), (1377, -86492592), (1378, 79440684), (1379, -59629680), (1382, 83232972), (1383, 66882300), (1385, -102540540), (1391, -12558384), (1393, -16047948), (1395, -8347932), (1403, 86492592), (1404, -79440684), (1405, 59629680), (1408, -136623552), (1409, -78991800), (1411, 124841340), (1420, 15916680), (1424, 448884), (1426, 38348748), (1428, -45042648), (1472, 20396280), (1473, -21388080), (1475, 20396280), (1479, 53390580), (1480, 12109500), (1482, 12558384), (1484, 8347932), (1490, -448884), (1492, 45042648), (1501, -10263960), (1504, -22300800), (1506, 16047948), (1509, -15916680), (1511, -38348748), (1582, 20396280), (1583, -21388080), (1585, 20396280), (1589, 63234120), (1590, 105006336), (1592, 54886188), (1596, 12558384), (1598, 8347932), (1604, -9843540), (1605, -92896836), (1607, -54886188), (1613, -448884), (1615, 45042648), (1620, -20396280), (1621, 21388080), (1623, -20396280), (1626, -53390580), (1627, -12109500), (1629, -12558384), (1631, -8347932), (1637, 448884), (1639, -45042648), (1698, -10263960), (1701, -16047948), (1704, 16047948), (1708, -6252852), (1711, -15916680), (1713, -38348748), (1716, 10263960), (1719, 22300800), (1721, -16047948), (1724, 15916680), (1726, 38348748)]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node160 : Integer.Sparse (Fin 2886) := [(15, -58283520), (24, 58283520), (36, 58283520), (63, -58283520), (96, -58283520), (117, 58283520), (902, 17371800), (909, -17371800), (977, -17371800), (992, 17371800), (1057, 17371800), (1063, -17371800)]

def node161 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (77, -20908800), (132, 20908800), (147, 20908800), (162, -20908800), (862, -43985400), (879, 43985400), (896, 43985400), (932, -43985400), (984, -43985400), (1011, 43985400)]

def node162 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (77, -20908800), (132, 20908800), (147, 20908800), (162, -20908800), (862, -43985400), (869, 53449680), (879, 43985400), (883, -53449680), (896, 43985400), (904, -53449680), (932, -43985400), (936, 53449680), (984, -43985400), (988, 53449680), (1011, 43985400), (1015, -53449680)]

def node163 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (15, -58283520), (24, 58283520), (36, 58283520), (63, -58283520), (77, -20908800), (96, -58283520), (117, 58283520), (132, 20908800), (147, 20908800), (162, -20908800), (862, -43985400), (869, 53449680), (879, 43985400), (883, -53449680), (896, 43985400), (902, 17371800), (904, -53449680), (909, -17371800), (932, -43985400), (936, 53449680), (977, -17371800), (984, -43985400), (988, 53449680), (992, 17371800), (1011, 43985400), (1015, -53449680), (1057, 17371800), (1063, -17371800)]

def node164 : Integer.Sparse (Fin 2886) := [(328, -15109920), (332, 15109920), (377, 15109920), (399, -15109920), (404, -15109920), (421, 15109920), (917, 133529400), (921, -133529400), (1001, -133529400), (1007, 133529400), (1102, 133529400), (1104, -133529400)]

def node165 : Integer.Sparse (Fin 2886) := [(1, 68950800), (4, -68950800), (76, -68950800), (130, 110321280), (145, 27580320), (160, -68950800), (867, 50370840), (874, -50370840), (977, -50370840), (1020, 50370840), (1057, 50370840), (1076, -50370840)]

def node166 : Integer.Sparse (Fin 2886) := [(1, 68950800), (4, -68950800), (76, -68950800), (130, 110321280), (145, 27580320), (160, -68950800), (184, -23917920), (189, 23917920), (332, 23917920), (404, -23917920), (495, -23917920), (518, 23917920), (867, 50370840), (874, -50370840), (977, -50370840), (1020, 50370840), (1057, 50370840), (1076, -50370840)]

def node167 : Integer.Sparse (Fin 2886) := [(1, 68950800), (4, -68950800), (76, -68950800), (130, 110321280), (145, 27580320), (160, -68950800), (184, -23917920), (189, 23917920), (328, -15109920), (332, 39027840), (377, 15109920), (399, -15109920), (404, -39027840), (421, 15109920), (495, -23917920), (518, 23917920), (867, 50370840), (874, -50370840), (917, 133529400), (921, -133529400), (977, -50370840), (1001, -133529400), (1007, 133529400), (1020, 50370840), (1057, 50370840), (1076, -50370840), (1102, 133529400), (1104, -133529400)]

def node168 : Integer.Sparse (Fin 2886) := [(1, 68950800), (2, 20908800), (4, -68950800), (6, -20908800), (15, -58283520), (24, 58283520), (36, 58283520), (63, -58283520), (76, -68950800), (77, -20908800), (96, -58283520), (117, 58283520), (130, 110321280), (132, 20908800), (145, 27580320), (147, 20908800), (160, -68950800), (162, -20908800), (184, -23917920), (189, 23917920), (328, -15109920), (332, 39027840), (377, 15109920), (399, -15109920), (404, -39027840), (421, 15109920), (495, -23917920), (518, 23917920), (862, -43985400), (867, 50370840), (869, 53449680), (874, -50370840), (879, 43985400), (883, -53449680), (896, 43985400), (902, 17371800), (904, -53449680), (909, -17371800), (917, 133529400), (921, -133529400), (932, -43985400), (936, 53449680), (977, -67742640), (984, -43985400), (988, 53449680), (992, 17371800), (1001, -133529400), (1007, 133529400), (1011, 43985400), (1015, -53449680), (1020, 50370840), (1057, 67742640), (1063, -17371800), (1076, -50370840), (1102, 133529400), (1104, -133529400)]

def node169 : Integer.Sparse (Fin 2886) := [(843, -44915160), (844, -22118760), (847, 44915160), (850, 22118760), (951, 44915160), (952, 22118760), (1027, -44915160), (1029, -22118760), (1045, -44915160), (1082, 44915160), (1092, -22118760), (1109, 22118760)]

def node170 : Integer.Sparse (Fin 2886) := [(632, 21023280), (633, -21023280), (803, -21023280), (818, 21023280), (836, 21023280), (839, -21023280), (848, -26193840), (854, 26193840), (956, 26193840), (1034, -26193840), (1048, -26193840), (1084, 26193840)]

def node171 : Integer.Sparse (Fin 2886) := [(632, 21023280), (633, -21023280), (803, -21023280), (818, 21023280), (836, 21023280), (839, -21023280), (848, -26193840), (854, 26193840), (866, -378221400), (881, 378221400), (901, 378221400), (934, -378221400), (956, 26193840), (986, -378221400), (1013, 378221400), (1034, -26193840), (1048, -26193840), (1084, 26193840)]

def node172 : Integer.Sparse (Fin 2886) := [(632, 21023280), (633, -21023280), (803, -21023280), (818, 21023280), (836, 21023280), (839, -21023280), (843, -44915160), (844, -22118760), (847, 44915160), (848, -26193840), (850, 22118760), (854, 26193840), (866, -378221400), (881, 378221400), (901, 378221400), (934, -378221400), (951, 44915160), (952, 22118760), (956, 26193840), (986, -378221400), (1013, 378221400), (1027, -44915160), (1029, -22118760), (1034, -26193840), (1045, -44915160), (1048, -26193840), (1082, 44915160), (1084, 26193840), (1092, -22118760), (1109, 22118760)]

def node173 : Integer.Sparse (Fin 2886) := [(16, -2565312), (18, 2565312), (28, -2565312), (37, -23087808), (40, 15391872), (91, 16246976), (100, -17957184), (119, -2565312), (151, -7695936), (153, 12826560), (157, 2565312), (180, 2565312), (182, -2565312), (187, 2565312), (327, -2565312), (330, 10261248), (376, 9406144), (397, -17957184), (402, -7695936), (419, 12826560), (516, 2565312), (533, -2565312), (863, 82994640), (881, -82994640), (897, -82994640), (934, 82994640), (1061, 82994640), (1074, -82994640)]

def node174 : Integer.Sparse (Fin 2886) := [(16, -2565312), (18, 2565312), (28, -2565312), (37, -23087808), (40, 15391872), (91, 16246976), (100, -17957184), (119, -2565312), (151, -7695936), (153, 12826560), (157, 2565312), (180, 2565312), (182, -2565312), (187, 2565312), (327, -2565312), (330, 10261248), (376, 9406144), (397, -17957184), (402, -7695936), (419, 12826560), (516, 2565312), (533, -2565312), (863, 82994640), (881, -82994640), (897, -82994640), (898, 189084120), (904, -189084120), (934, 82994640), (973, -189084120), (988, 189084120), (1061, 82994640), (1074, -82994640), (1096, 189084120), (1099, -189084120)]

def node175 : Integer.Sparse (Fin 2886) := [(196, 51264600), (198, -51264600), (432, -51264600), (482, 51264600), (541, 51264600), (562, -51264600), (874, 79317120), (887, -79317120), (909, -79317120), (941, 79317120), (992, 79317120), (1020, -79317120)]

def node176 : Integer.Sparse (Fin 2886) := [(196, 51264600), (198, -51264600), (432, -51264600), (482, 51264600), (541, 51264600), (562, -51264600), (874, 79317120), (887, -79317120), (897, 156827520), (901, -156827520), (909, -79317120), (941, 79317120), (972, -156827520), (986, 156827520), (992, 79317120), (1020, -79317120), (1054, 156827520), (1061, -156827520)]

def node177 : Integer.Sparse (Fin 2886) := [(16, -2565312), (18, 2565312), (28, -2565312), (37, -23087808), (40, 15391872), (91, 16246976), (100, -17957184), (119, -2565312), (151, -7695936), (153, 12826560), (157, 2565312), (180, 2565312), (182, -2565312), (187, 2565312), (196, 51264600), (198, -51264600), (327, -2565312), (330, 10261248), (376, 9406144), (397, -17957184), (402, -7695936), (419, 12826560), (432, -51264600), (482, 51264600), (516, 2565312), (533, -2565312), (541, 51264600), (562, -51264600), (863, 82994640), (874, 79317120), (881, -82994640), (887, -79317120), (897, 73832880), (898, 189084120), (901, -156827520), (904, -189084120), (909, -79317120), (934, 82994640), (941, 79317120), (972, -156827520), (973, -189084120), (986, 156827520), (988, 189084120), (992, 79317120), (1020, -79317120), (1054, 156827520), (1061, -73832880), (1074, -82994640), (1096, 189084120), (1099, -189084120)]

def node178 : Integer.Sparse (Fin 2886) := [(16, -2565312), (18, 2565312), (28, -2565312), (37, -23087808), (40, 15391872), (91, 16246976), (100, -17957184), (119, -2565312), (151, -7695936), (153, 12826560), (157, 2565312), (180, 2565312), (182, -2565312), (187, 2565312), (196, 51264600), (198, -51264600), (327, -2565312), (330, 10261248), (376, 9406144), (397, -17957184), (402, -7695936), (419, 12826560), (432, -51264600), (482, 51264600), (516, 2565312), (533, -2565312), (541, 51264600), (562, -51264600), (632, 21023280), (633, -21023280), (803, -21023280), (818, 21023280), (836, 21023280), (839, -21023280), (843, -44915160), (844, -22118760), (847, 44915160), (848, -26193840), (850, 22118760), (854, 26193840), (863, 82994640), (866, -378221400), (874, 79317120), (881, 295226760), (887, -79317120), (897, 73832880), (898, 189084120), (901, 221393880), (904, -189084120), (909, -79317120), (934, -295226760), (941, 79317120), (951, 44915160), (952, 22118760), (956, 26193840), (972, -156827520), (973, -189084120), (986, -221393880), (988, 189084120), (992, 79317120), (1013, 378221400), (1020, -79317120), (1027, -44915160), (1029, -22118760), (1034, -26193840), (1045, -44915160), (1048, -26193840), (1054, 156827520), (1061, -73832880), (1074, -82994640), (1082, 44915160), (1084, 26193840), (1092, -22118760), (1096, 189084120), (1099, -189084120), (1109, 22118760)]

def node179 : Integer.Sparse (Fin 2886) := [(1, 68950800), (2, 20908800), (4, -68950800), (6, -20908800), (15, -58283520), (16, -2565312), (18, 2565312), (24, 58283520), (28, -2565312), (36, 58283520), (37, -23087808), (40, 15391872), (63, -58283520), (76, -68950800), (77, -20908800), (91, 16246976), (96, -58283520), (100, -17957184), (117, 58283520), (119, -2565312), (130, 110321280), (132, 20908800), (145, 27580320), (147, 20908800), (151, -7695936), (153, 12826560), (157, 2565312), (160, -68950800), (162, -20908800), (180, 2565312), (182, -2565312), (184, -23917920), (187, 2565312), (189, 23917920), (196, 51264600), (198, -51264600), (327, -2565312), (328, -15109920), (330, 10261248), (332, 39027840), (376, 9406144), (377, 15109920), (397, -17957184), (399, -15109920), (402, -7695936), (404, -39027840), (419, 12826560), (421, 15109920), (432, -51264600), (482, 51264600), (495, -23917920), (516, 2565312), (518, 23917920), (533, -2565312), (541, 51264600), (562, -51264600), (632, 21023280), (633, -21023280), (803, -21023280), (818, 21023280), (836, 21023280), (839, -21023280), (843, -44915160), (844, -22118760), (847, 44915160), (848, -26193840), (850, 22118760), (854, 26193840), (862, -43985400), (863, 82994640), (866, -378221400), (867, 50370840), (869, 53449680), (874, 28946280), (879, 43985400), (881, 295226760), (883, -53449680), (887, -79317120), (896, 43985400), (897, 73832880), (898, 189084120), (901, 221393880), (902, 17371800), (904, -242533800), (909, -96688920), (917, 133529400), (921, -133529400), (932, -43985400), (934, -295226760), (936, 53449680), (941, 79317120), (951, 44915160), (952, 22118760), (956, 26193840), (972, -156827520), (973, -189084120), (977, -67742640), (984, -43985400), (986, -221393880), (988, 242533800), (992, 96688920), (1001, -133529400), (1007, 133529400), (1011, 43985400), (1013, 378221400), (1015, -53449680), (1020, -28946280), (1027, -44915160), (1029, -22118760), (1034, -26193840), (1045, -44915160), (1048, -26193840), (1054, 156827520), (1057, 67742640), (1061, -73832880), (1063, -17371800), (1074, -82994640), (1076, -50370840), (1082, 44915160), (1084, 26193840), (1092, -22118760), (1096, 189084120), (1099, -189084120), (1102, 133529400), (1104, -133529400), (1109, 22118760)]

def node180 : Integer.Sparse (Fin 2886) := [(1171, -141056280), (1190, 141056280), (1380, 141056280), (1477, -141056280), (1587, -141056280), (1625, 141056280), (2365, -75047124), (2368, 75047124), (2381, 75047124), (2391, -112570686), (2398, -37523562), (2403, 75047124), (2420, -300188496), (2423, 300188496), (2455, 75047124), (2478, -112570686), (2487, -112570686), (2497, -287680642), (2499, 262664934), (2535, 150094248), (2545, -112570686), (2558, 75047124), (2580, -112570686), (2645, -75047124), (2652, 262664934), (2661, -262664934), (2686, -112570686), (2691, 137586394), (2692, 112570686), (2698, -37523562), (2707, 75047124), (2723, 262664934), (2730, -75047124), (2739, -262664934), (2744, -112570686), (2746, -112570686), (2749, 375235620)]

def node181 : Integer.Sparse (Fin 2886) := [(867, -126861240), (875, 126861240), (977, 126861240), (1021, -126861240), (1058, -126861240), (1077, 126861240), (2379, 31560960), (2387, -31560960), (2453, -31560960), (2473, 31560960), (2606, 31560960), (2616, -31560960)]

def node182 : Integer.Sparse (Fin 2886) := [(867, -126861240), (875, 126861240), (977, 126861240), (1021, -126861240), (1058, -126861240), (1077, 126861240), (2364, 5100168), (2366, -5100168), (2376, -30601008), (2379, 31560960), (2387, -31560960), (2388, 6800224), (2389, -20400672), (2394, 18700616), (2396, 5100168), (2401, 17000560), (2408, 3400112), (2415, 2550084), (2419, -7650252), (2421, 2550084), (2424, 2550084), (2453, -31560960), (2454, 12750420), (2473, 31560960), (2474, -15300504), (2476, -5100168), (2480, -2550084), (2483, 2550084), (2485, -2550084), (2495, 5100168), (2501, 7650252), (2506, -12750420), (2530, 17850588), (2534, 5100168), (2542, -2550084), (2543, 12750420), (2546, -2550084), (2557, -5100168), (2576, 2550084), (2578, 5100168), (2582, 2550084), (2606, 31560960), (2607, -7650252), (2616, -31560960), (2617, 7650252), (2639, -17850588), (2643, -12750420), (2650, -5100168), (2666, -7650252), (2669, 7650252), (2682, -10200336), (2684, -2550084), (2689, -7650252), (2694, -2550084), (2696, 2550084), (2705, -5100168), (2717, 17850588), (2721, 12750420), (2728, 5100168)]

def node183 : Integer.Sparse (Fin 2886) := [(867, -126861240), (875, 126861240), (977, 126861240), (1021, -126861240), (1058, -126861240), (1077, 126861240), (1171, -141056280), (1190, 141056280), (1380, 141056280), (1477, -141056280), (1587, -141056280), (1625, 141056280), (2364, 5100168), (2365, -75047124), (2366, -5100168), (2368, 75047124), (2376, -30601008), (2379, 31560960), (2381, 75047124), (2387, -31560960), (2388, 6800224), (2389, -20400672), (2391, -112570686), (2394, 18700616), (2396, 5100168), (2398, -37523562), (2401, 17000560), (2403, 75047124), (2408, 3400112), (2415, 2550084), (2419, -7650252), (2420, -300188496), (2421, 2550084), (2423, 300188496), (2424, 2550084), (2453, -31560960), (2454, 12750420), (2455, 75047124), (2473, 31560960), (2474, -15300504), (2476, -5100168), (2478, -112570686), (2480, -2550084), (2483, 2550084), (2485, -2550084), (2487, -112570686), (2495, 5100168), (2497, -287680642), (2499, 262664934), (2501, 7650252), (2506, -12750420), (2530, 17850588), (2534, 5100168), (2535, 150094248), (2542, -2550084), (2543, 12750420), (2545, -112570686), (2546, -2550084), (2557, -5100168), (2558, 75047124), (2576, 2550084), (2578, 5100168), (2580, -112570686), (2582, 2550084), (2606, 31560960), (2607, -7650252), (2616, -31560960), (2617, 7650252), (2639, -17850588), (2643, -12750420), (2645, -75047124), (2650, -5100168), (2652, 262664934), (2661, -262664934), (2666, -7650252), (2669, 7650252), (2682, -10200336), (2684, -2550084), (2686, -112570686), (2689, -7650252), (2691, 137586394), (2692, 112570686), (2694, -2550084), (2696, 2550084), (2698, -37523562), (2705, -5100168), (2707, 75047124), (2717, 17850588), (2721, 12750420), (2723, 262664934), (2728, 5100168), (2730, -75047124), (2739, -262664934), (2744, -112570686), (2746, -112570686), (2749, 375235620)]

def node184 : Integer.Sparse (Fin 2886) := [(1154, -36212232), (1161, 36212232), (1173, 36212232), (1185, -36212232), (1195, -36212232), (1201, 36212232), (1240, -144848928), (1247, 144848928), (1267, 144848928), (1289, -144848928), (1299, -144848928), (1308, 144848928), (1382, -36212232), (1395, 36212232), (1408, 36212232), (1428, -36212232), (1484, -36212232), (1492, 36212232), (1589, -181061160), (1592, 217273392), (1598, -36212232), (1607, -36212232), (1615, 36212232), (1626, 181061160), (1631, 36212232), (1639, -217273392), (1649, -181061160), (1653, 181061160), (2441, 258197328), (2443, -150615108), (2467, 21516444), (2481, -21516444), (2504, -21516444), (2507, 43032888), (2569, -172131552), (2583, 172131552), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

def node185 : Integer.Sparse (Fin 2886) := [(867, 50370840), (874, -50370840), (977, -50370840), (1020, 50370840), (1057, 50370840), (1076, -50370840), (2365, 794219904), (2368, -794219904), (2381, 198554976), (2391, -529479936), (2398, 132369984), (2403, 1191329856), (2404, -992774880), (2420, 198554976), (2423, -198554976), (2478, 198554976), (2497, 264739968), (2535, -397109952), (2545, 397109952), (2558, -794219904), (2580, 992774880), (2645, -1191329856), (2661, 1389884832), (2686, 198554976), (2691, -661849920), (2698, 595664928), (2707, -794219904), (2723, 397109952), (2730, -198554976), (2744, 595664928), (2749, -992774880)]

def node186 : Integer.Sparse (Fin 2886) := [(867, 50370840), (874, -50370840), (977, -50370840), (1020, 50370840), (1057, 50370840), (1076, -50370840), (1154, -12646824), (1161, 12646824), (1173, 75880944), (1185, 50587296), (1192, -63234120), (1195, -12646824), (1201, -50587296), (1240, 12646824), (1247, -12646824), (1267, -12646824), (1289, 12646824), (1299, 12646824), (1308, -12646824), (1382, -75880944), (1395, -50587296), (1408, 12646824), (1428, -12646824), (1479, 63234120), (1484, 50587296), (1492, 12646824), (1589, 63234120), (1592, 12646824), (1598, 50587296), (1607, -12646824), (1615, 12646824), (1626, -63234120), (1631, -50587296), (1639, -12646824), (2365, 794219904), (2368, -794219904), (2381, 198554976), (2391, -529479936), (2398, 132369984), (2403, 1191329856), (2404, -992774880), (2420, 198554976), (2423, -198554976), (2478, 198554976), (2497, 264739968), (2535, -397109952), (2545, 397109952), (2558, -794219904), (2580, 992774880), (2645, -1191329856), (2661, 1389884832), (2686, 198554976), (2691, -661849920), (2698, 595664928), (2707, -794219904), (2723, 397109952), (2730, -198554976), (2744, 595664928), (2749, -992774880)]

def node187 : Integer.Sparse (Fin 2886) := [(867, 50370840), (874, -50370840), (977, -50370840), (1020, 50370840), (1057, 50370840), (1076, -50370840), (1154, -48859056), (1161, 48859056), (1173, 112093176), (1185, 14375064), (1192, -63234120), (1195, -48859056), (1201, -14375064), (1240, -132202104), (1247, 132202104), (1267, 132202104), (1289, -132202104), (1299, -132202104), (1308, 132202104), (1382, -112093176), (1395, -14375064), (1408, 48859056), (1428, -48859056), (1479, 63234120), (1484, 14375064), (1492, 48859056), (1589, -117827040), (1592, 229920216), (1598, 14375064), (1607, -48859056), (1615, 48859056), (1626, 117827040), (1631, -14375064), (1639, -229920216), (1649, -181061160), (1653, 181061160), (2365, 794219904), (2368, -794219904), (2381, 198554976), (2391, -529479936), (2398, 132369984), (2403, 1191329856), (2404, -992774880), (2420, 198554976), (2423, -198554976), (2441, 258197328), (2443, -150615108), (2467, 21516444), (2478, 198554976), (2481, -21516444), (2497, 264739968), (2504, -21516444), (2507, 43032888), (2535, -397109952), (2545, 397109952), (2558, -794219904), (2569, -172131552), (2580, 992774880), (2583, 172131552), (2645, -1191329856), (2661, 1389884832), (2686, 198554976), (2691, -661849920), (2698, 595664928), (2707, -794219904), (2723, 397109952), (2730, -198554976), (2744, 595664928), (2749, -992774880), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

def node188 : Integer.Sparse (Fin 2886) := [(867, -76490400), (874, -50370840), (875, 126861240), (977, 76490400), (1020, 50370840), (1021, -126861240), (1057, 50370840), (1058, -126861240), (1076, -50370840), (1077, 126861240), (1154, -48859056), (1161, 48859056), (1171, -141056280), (1173, 112093176), (1185, 14375064), (1190, 141056280), (1192, -63234120), (1195, -48859056), (1201, -14375064), (1240, -132202104), (1247, 132202104), (1267, 132202104), (1289, -132202104), (1299, -132202104), (1308, 132202104), (1380, 141056280), (1382, -112093176), (1395, -14375064), (1408, 48859056), (1428, -48859056), (1477, -141056280), (1479, 63234120), (1484, 14375064), (1492, 48859056), (1587, -141056280), (1589, -117827040), (1592, 229920216), (1598, 14375064), (1607, -48859056), (1615, 48859056), (1625, 141056280), (1626, 117827040), (1631, -14375064), (1639, -229920216), (1649, -181061160), (1653, 181061160), (2364, 5100168), (2365, 719172780), (2366, -5100168), (2368, -719172780), (2376, -30601008), (2379, 31560960), (2381, 273602100), (2387, -31560960), (2388, 6800224), (2389, -20400672), (2391, -642050622), (2394, 18700616), (2396, 5100168), (2398, 94846422), (2401, 17000560), (2403, 1266376980), (2404, -992774880), (2408, 3400112), (2415, 2550084), (2419, -7650252), (2420, -101633520), (2421, 2550084), (2423, 101633520), (2424, 2550084), (2441, 258197328), (2443, -150615108), (2453, -31560960), (2454, 12750420), (2455, 75047124), (2467, 21516444), (2473, 31560960), (2474, -15300504), (2476, -5100168), (2478, 85984290), (2480, -2550084), (2481, -21516444), (2483, 2550084), (2485, -2550084), (2487, -112570686), (2495, 5100168), (2497, -22940674), (2499, 262664934), (2501, 7650252), (2504, -21516444), (2506, -12750420), (2507, 43032888), (2530, 17850588), (2534, 5100168), (2535, -247015704), (2542, -2550084), (2543, 12750420), (2545, 284539266), (2546, -2550084), (2557, -5100168), (2558, -719172780), (2569, -172131552), (2576, 2550084), (2578, 5100168), (2580, 880204194), (2582, 2550084), (2583, 172131552), (2606, 31560960), (2607, -7650252), (2616, -31560960), (2617, 7650252), (2639, -17850588), (2643, -12750420), (2645, -1266376980), (2650, -5100168), (2652, 262664934), (2661, 1127219898), (2666, -7650252), (2669, 7650252), (2682, -10200336), (2684, -2550084), (2686, 85984290), (2689, -7650252), (2691, -524263526), (2692, 112570686), (2694, -2550084), (2696, 2550084), (2698, 558141366), (2705, -5100168), (2707, -719172780), (2717, 17850588), (2721, 12750420), (2723, 659774886), (2728, 5100168), (2730, -273602100), (2739, -262664934), (2744, 483094242), (2746, -112570686), (2749, -617539260), (2760, 86065776), (2763, -150615108), (2796, -43032888), (2797, -64549332), (2810, -21516444), (2814, 21516444), (2817, 21516444), (2818, -43032888), (2847, -43032888), (2852, 129098664), (2855, 43032888), (2856, -64549332)]

def node189 : Integer.Sparse (Fin 2886) := [(2124, 40887180), (2130, -49064616), (2158, -8177436), (2189, 8177436), (2218, -24532308), (2231, 8177436), (2255, 49064616), (2285, -8177436), (2287, 24532308), (2292, -8177436), (2303, -32709744), (2339, -17765580), (2342, 58652760), (2344, -32709744), (2523, 8177436), (2594, 1410708), (2624, 8177436), (2627, -58652760), (2630, 57242052), (2663, -8177436), (2672, 8177436), (2714, -58652760), (2735, 58652760), (2751, -8177436), (2765, 32709744), (2774, -49064616)]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

def AllTransitionsFourierZero (B : Fin 7 → Basis) : Prop :=
  ∀ r s, FourierZero (relativeMatrix B r s)

end MUB6

end

end OAI
end


