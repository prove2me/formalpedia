-- Prove2me | Definitions.Def_OAIQ262T166
-- name    : OAIQ262T166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T20:40:41.22191+00:00
-- url     : https://prove2.me/theorems/37463b94-c5d1-48fb-9a5c-4fed6fa0584d
-- title:
--   Definitions bundle OAIQ262T166 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_OrdinaryComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean), [`Triangular_Taylor_TaylorWave004`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave004.lean), [`Triangular_Taylor_TaylorWave005`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave005.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T146`, `OAIQ262T148` and `OAIQ262T149` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ262T261`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T146
import Definitions.Def_OAIQ262T148
import Definitions.Def_OAIQ262T149

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_4_1_calc (j : Fin 31) : taylorWaveBox 0 0 4 1 j = tw0_0_4_1 j := by
  revert j
  decide +kernel
lemma tw0_0_4_2_calc (j : Fin 31) : taylorWaveBox 0 0 4 2 j = tw0_0_4_2 j := by
  revert j
  decide +kernel
lemma tw0_0_4_3_calc (j : Fin 31) : taylorWaveBox 0 0 4 3 j = tw0_0_4_3 j := by
  revert j
  decide +kernel
lemma tw0_0_4_4_calc (j : Fin 31) : taylorWaveBox 0 0 4 4 j = tw0_0_4_4 j := by
  revert j
  decide +kernel
lemma tw0_0_4_5_calc (j : Fin 31) : taylorWaveBox 0 0 4 5 j = tw0_0_4_5 j := by
  revert j
  decide +kernel
lemma tw0_0_4_6_calc (j : Fin 31) : taylorWaveBox 0 0 4 6 j = tw0_0_4_6 j := by
  revert j
  decide +kernel
lemma tw0_0_4_7_calc (j : Fin 31) : taylorWaveBox 0 0 4 7 j = tw0_0_4_7 j := by
  revert j
  decide +kernel
lemma tw0_0_4_8_calc (j : Fin 31) : taylorWaveBox 0 0 4 8 j = tw0_0_4_8 j := by
  revert j
  decide +kernel
lemma tw0_0_4_9_calc (j : Fin 31) : taylorWaveBox 0 0 4 9 j = tw0_0_4_9 j := by
  revert j
  decide +kernel
lemma tw0_0_4_15_calc (j : Fin 31) : taylorWaveBox 0 0 4 15 j = tw0_0_4_15 j := by
  revert j
  decide +kernel
lemma tw0_0_4_16_calc (j : Fin 31) : taylorWaveBox 0 0 4 16 j = tw0_0_4_16 j := by
  revert j
  decide +kernel
lemma tw0_0_4_17_calc (j : Fin 31) : taylorWaveBox 0 0 4 17 j = tw0_0_4_17 j := by
  revert j
  decide +kernel
lemma tw0_0_4_18_calc (j : Fin 31) : taylorWaveBox 0 0 4 18 j = tw0_0_4_18 j := by
  revert j
  decide +kernel
lemma tw0_0_4_19_calc (j : Fin 31) : taylorWaveBox 0 0 4 19 j = tw0_0_4_19 j := by
  revert j
  decide +kernel
lemma tw0_0_4_20_calc (j : Fin 31) : taylorWaveBox 0 0 4 20 j = tw0_0_4_20 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_TaylorWave005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_5_0_calc (j : Fin 31) : taylorWaveBox 0 0 5 0 j = tw0_0_5_0 j := by
  revert j
  decide +kernel
lemma tw0_0_5_1_calc (j : Fin 31) : taylorWaveBox 0 0 5 1 j = tw0_0_5_1 j := by
  revert j
  decide +kernel
lemma tw0_0_5_10_calc (j : Fin 31) : taylorWaveBox 0 0 5 10 j = tw0_0_5_10 j := by
  revert j
  decide +kernel
lemma tw0_0_5_11_calc (j : Fin 31) : taylorWaveBox 0 0 5 11 j = tw0_0_5_11 j := by
  revert j
  decide +kernel
lemma tw0_0_5_12_calc (j : Fin 31) : taylorWaveBox 0 0 5 12 j = tw0_0_5_12 j := by
  revert j
  decide +kernel
lemma tw0_0_5_13_calc (j : Fin 31) : taylorWaveBox 0 0 5 13 j = tw0_0_5_13 j := by
  revert j
  decide +kernel
lemma tw0_0_5_14_calc (j : Fin 31) : taylorWaveBox 0 0 5 14 j = tw0_0_5_14 j := by
  revert j
  decide +kernel
lemma tw0_0_5_15_calc (j : Fin 31) : taylorWaveBox 0 0 5 15 j = tw0_0_5_15 j := by
  revert j
  decide +kernel
lemma tw0_0_5_16_calc (j : Fin 31) : taylorWaveBox 0 0 5 16 j = tw0_0_5_16 j := by
  revert j
  decide +kernel
lemma tw0_0_5_17_calc (j : Fin 31) : taylorWaveBox 0 0 5 17 j = tw0_0_5_17 j := by
  revert j
  decide +kernel
lemma tw0_0_5_18_calc (j : Fin 31) : taylorWaveBox 0 0 5 18 j = tw0_0_5_18 j := by
  revert j
  decide +kernel
lemma tw0_0_5_19_calc (j : Fin 31) : taylorWaveBox 0 0 5 19 j = tw0_0_5_19 j := by
  revert j
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_OrdinaryComparison
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
lemma gaussian_ordinary_lower {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  rw [ordinaryOffset_actual]
  by_cases hn0 : n=0
  · subst n
    have hy : y=0 := by fin_cases y <;> simp_all
    subst y
    norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum]
    have hh := gaussian_deleted_left (m:=1) hz (neg_nonpos.mpr hτ.1)
    norm_num at hh
    have hd := div_le_div_of_nonneg_left Q_one_pos.le (show 0<2*z by positivity) (show 2*z ≤ 2*Z by linarith)
    exact hd.trans hh
  · have hnval : n.val≠0 := by exact fun hh => hn0 (Fin.ext hh)
    simp only [hnval,ite_false, if_false]
    by_cases hn1 : n=1
    · subst n
      simp only [Fin.val_one,ite_true, if_true]
      have hv : nearDisplacement 1 y*τ ≤ 1/2 := by
        fin_cases y <;> norm_num[nearDisplacement,nearDisplacementNum] <;> nlinarith [hτ.1,hτ.2]
      have hh := gaussian_deleted_three hz hzB hv
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      norm_num [nearNode,finiteNode,residue]
    · have hnval1 : n.val≠1 := by exact fun hh => hn1 (Fin.ext hh)
      simp only [hnval1,ite_false, if_false]
      exact gaussian_deleted_nonneg hz _ _
end AtomicTriangular.Construction
end

end OAI
end


