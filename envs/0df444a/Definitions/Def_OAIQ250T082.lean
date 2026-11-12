-- Prove2me | Definitions.Def_OAIQ250T082
-- name    : OAIQ250T082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:21:15.707242+00:00
-- url     : https://prove2.me/theorems/04074b2f-e77f-4aba-8d22-143c619f41b9
-- title:
--   Definitions bundle OAIQ250T082 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 4 declarations of OpenAI's Lean: 1 definition and 3 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.tr1_6_1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_NearSigns`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/NearSigns.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean), [`Triangular_Taylor_TaylorRows16`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows16.lean).
--
--   **Imports.** It imports the bundles `OAIQ250T011`, `OAIQ250T045` and `OAIQ250T046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T111`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T045
import Definitions.Def_OAIQ250T046

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def tr1_6_1 : Fin 21 → Fin 8 → RI := ![tr1_6_1_0,tr1_6_1_1,tr1_6_1_2,tr1_6_1_3,tr1_6_1_4,tr1_6_1_5,tr1_6_1_6,tr1_6_1_7,tr1_6_1_8,tr1_6_1_9,tr1_6_1_10,tr1_6_1_11,tr1_6_1_12,tr1_6_1_13,tr1_6_1_14,tr1_6_1_15,tr1_6_1_16,tr1_6_1_17,tr1_6_1_18,tr1_6_1_19,tr1_6_1_20]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_NearSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_cell_cover {s : ℝ} (hs : s∈Icc 0 (29/2)) :
    ∃ (n : Fin 7) (y : Fin 2) (τ : ℝ),τ∈Icc 0 1 ∧ s=nearNode n+nearDisplacement n y*τ := by
  by_cases h0 : s ≤ 1
  · refine ⟨0,0,(s-1)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h1 : s ≤ 2
  · refine ⟨0,1,(s-1)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (0:Fin 7)=(1:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (0:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h2 : s ≤ 3
  · refine ⟨1,0,(s-3)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h3 : s ≤ (7/2)
  · refine ⟨1,1,(s-3)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (1:Fin 7)=(3:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (1:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h4 : s ≤ 4
  · refine ⟨2,0,(s-4)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h5 : s ≤ (11/2)
  · refine ⟨2,1,(s-4)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (2:Fin 7)=(4:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (2:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h6 : s ≤ 7
  · refine ⟨3,0,(s-7)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h7 : s ≤ 8
  · refine ⟨3,1,(s-7)/1,?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (3:Fin 7)=(7:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (3:Fin 7) (1:Fin 2)=(2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h8 : s ≤ 9
  · refine ⟨4,0,(s-9)/(-1),?_,?_⟩
    · constructor <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (0:Fin 2)=(-2:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h9 : s ≤ (21/2)
  · refine ⟨4,1,(s-9)/(3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (4:Fin 7)=(9:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (4:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h10 : s ≤ 12
  · refine ⟨5,0,(s-12)/(-3/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (0:Fin 2)=(-3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h11 : s ≤ (25/2)
  · refine ⟨5,1,(s-12)/(1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (5:Fin 7)=(12:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (5:Fin 7) (1:Fin 2)=(1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  by_cases h12 : s ≤ 13
  · refine ⟨6,0,(s-13)/(-1/2),?_,?_⟩
    · constructor <;> norm_num <;> linarith [hs.1,hs.2]
    · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (0:Fin 2)=(-1:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
      ring
  refine ⟨6,1,(s-13)/(3/2),?_,?_⟩
  · constructor <;> norm_num <;> linarith [hs.1,hs.2]
  · norm_num only [show nearNode (6:Fin 7)=(13:ℤ) by rfl,nearDisplacement,show nearDisplacementNum (6:Fin 7) (1:Fin 2)=(3:ℤ) by rfl,Int.cast_ofNat,Int.cast_neg]
    ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry28 (k : Fin 100) :
    0 ≤ cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0 ≤ cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0 ≤ cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry29 (k : Fin 100) :
    0 ≤ cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0 ≤ cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0 ≤ cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


