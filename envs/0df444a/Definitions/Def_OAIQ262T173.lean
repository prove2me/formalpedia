-- Prove2me | Definitions.Def_OAIQ262T173
-- name    : OAIQ262T173
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:11:21.006343+00:00
-- url     : https://prove2.me/theorems/38953e13-abd9-4dca-8a8a-363d8b11c62d
-- title:
--   Definitions bundle OAIQ262T173 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 25 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_SignBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SignBase.lean), [`Triangular_Taylor_TaylorWave015`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave015.lean), [`Triangular_Taylor_TaylorWave016`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave016.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T144` and `OAIQ262T148` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T144
import Definitions.Def_OAIQ262T148

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_5_4_calc (j : Fin 31) : taylorWaveBox 0 1 5 4 j = tw0_1_5_4 j := by
  revert j
  decide +kernel
lemma tw0_1_5_5_calc (j : Fin 31) : taylorWaveBox 0 1 5 5 j = tw0_1_5_5 j := by
  revert j
  decide +kernel
lemma tw0_1_5_6_calc (j : Fin 31) : taylorWaveBox 0 1 5 6 j = tw0_1_5_6 j := by
  revert j
  decide +kernel
lemma tw0_1_5_7_calc (j : Fin 31) : taylorWaveBox 0 1 5 7 j = tw0_1_5_7 j := by
  revert j
  decide +kernel
lemma tw0_1_5_8_calc (j : Fin 31) : taylorWaveBox 0 1 5 8 j = tw0_1_5_8 j := by
  revert j
  decide +kernel
lemma tw0_1_5_9_calc (j : Fin 31) : taylorWaveBox 0 1 5 9 j = tw0_1_5_9 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_1_6_0_calc (j : Fin 31) : taylorWaveBox 0 1 6 0 j = tw0_1_6_0 j := by
  revert j
  decide +kernel
lemma tw0_1_6_1_calc (j : Fin 31) : taylorWaveBox 0 1 6 1 j = tw0_1_6_1 j := by
  revert j
  decide +kernel
lemma tw0_1_6_2_calc (j : Fin 31) : taylorWaveBox 0 1 6 2 j = tw0_1_6_2 j := by
  revert j
  decide +kernel
lemma tw0_1_6_3_calc (j : Fin 31) : taylorWaveBox 0 1 6 3 j = tw0_1_6_3 j := by
  revert j
  decide +kernel
lemma tw0_1_6_4_calc (j : Fin 31) : taylorWaveBox 0 1 6 4 j = tw0_1_6_4 j := by
  revert j
  decide +kernel
lemma tw0_1_6_5_calc (j : Fin 31) : taylorWaveBox 0 1 6 5 j = tw0_1_6_5 j := by
  revert j
  decide +kernel
lemma tw0_1_6_6_calc (j : Fin 31) : taylorWaveBox 0 1 6 6 j = tw0_1_6_6 j := by
  revert j
  decide +kernel
lemma tw0_1_6_10_calc (j : Fin 31) : taylorWaveBox 0 1 6 10 j = tw0_1_6_10 j := by
  revert j
  decide +kernel
lemma tw0_1_6_11_calc (j : Fin 31) : taylorWaveBox 0 1 6 11 j = tw0_1_6_11 j := by
  revert j
  decide +kernel
lemma tw0_1_6_12_calc (j : Fin 31) : taylorWaveBox 0 1 6 12 j = tw0_1_6_12 j := by
  revert j
  decide +kernel
lemma tw0_1_6_13_calc (j : Fin 31) : taylorWaveBox 0 1 6 13 j = tw0_1_6_13 j := by
  revert j
  decide +kernel
lemma tw0_1_6_14_calc (j : Fin 31) : taylorWaveBox 0 1 6 14 j = tw0_1_6_14 j := by
  revert j
  decide +kernel
lemma tw0_1_6_15_calc (j : Fin 31) : taylorWaveBox 0 1 6 15 j = tw0_1_6_15 j := by
  revert j
  decide +kernel
lemma tw0_1_6_16_calc (j : Fin 31) : taylorWaveBox 0 1 6 16 j = tw0_1_6_16 j := by
  revert j
  decide +kernel
lemma tw0_1_6_17_calc (j : Fin 31) : taylorWaveBox 0 1 6 17 j = tw0_1_6_17 j := by
  revert j
  decide +kernel
lemma tw0_1_6_18_calc (j : Fin 31) : taylorWaveBox 0 1 6 18 j = tw0_1_6_18 j := by
  revert j
  decide +kernel
lemma tw0_1_6_19_calc (j : Fin 31) : taylorWaveBox 0 1 6 19 j = tw0_1_6_19 j := by
  revert j
  decide +kernel
lemma tw0_1_6_20_calc (j : Fin 31) : taylorWaveBox 0 1 6 20 j = tw0_1_6_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SignBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma ordinarySignValue_eq (side : Fin 2) (n : Fin 7) (y : Fin 2) (e : Fin 8 → ℝ) (τ : ℝ) :
    ordinarySignValue side n y e τ =
      ∑ l : Fin 21, (∑ r : Fin 8, ordinarySignRow side n y l r*e r)*τ^l.val := by
  have ht : (∑ l : Fin 21, (∑ r : Fin 8,
      taylorRow side (nearNode n) (nearDisplacement n y) l.val r*e r)*τ^l.val) =
      finiteTaylor side (nearNode n) (nearDisplacement n y) e τ := by
    rw [finiteTaylor,← Fin.sum_univ_eq_sum_range]
  unfold ordinarySignValue ordinarySignRow
  split_ifs with h
  · simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
      Finset.sum_ite_irrel,ht,Finset.sum_const_zero]
    congr 1
    symm
    rw [Finset.sum_eq_single (0:Fin 21)]
    · simp
    · intro b hb hb0
      have hne : b.val ≠ 0 := by intro hh; apply hb0; exact Fin.ext hh
      simp [hne]
    · simp
  · exact ht.symm
end AtomicTriangular.Construction
end

end OAI
end


