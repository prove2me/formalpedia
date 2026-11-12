-- Prove2me | Definitions.Def_OAIQ250T064
-- name    : OAIQ250T064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:19:01.952101+00:00
-- url     : https://prove2.me/theorems/7a3df713-c651-4dac-a8fe-fedfeb7f076d
-- title:
--   Definitions bundle OAIQ250T064 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 4 definitions and 11 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.rawRemainderColumn`, `OAI.AtomicTriangular.Construction.rawRemainderConstant`, `OAI.AtomicTriangular.Construction.remainderWave`, `OAI.AtomicTriangular.FiniteCertificate.remainderExpInput`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_ExceptionalSign0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalSign0.lean), [`Triangular_Signs_RemainderBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean), [`Triangular_Signs_RemainderNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean), [`Triangular_Signs_SineBarrierBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineBarrierBase.lean), [`Triangular_Signs_SineGrid2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid2.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012` and `OAIQ250T013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T086` and `OAIQ250T099`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T010
import Definitions.Def_OAIQ250T011
import Definitions.Def_OAIQ250T012
import Definitions.Def_OAIQ250T013

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalSign0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ex0b0_calc (r : Fin 8) : bernsteinRowsBox 22 ex0r 0 r = ex0b0 r := by
  revert r
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.Construction

def remainderWave (q br : Fin 2) (m Y t : ℝ) : ℝ :=
  curvatureWave q br m t * (Y*‖taylorPhase q br t‖)^21 / (23).factorial /
    (1-Y*‖taylorPhase q br t‖/24)
def rawRemainderColumn (br : Fin 2) (n : Fin 7) (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, remainderWave 1 br (nearNode n) (nearRadius n) (frequency j)*
    ‖finiteColumn ⟨c.val,by omega⟩ j‖
def rawRemainderConstant (br : Fin 2) (n : Fin 7) : ℝ :=
  ∑ j : Fin 31, remainderWave 0 br (nearNode n) (nearRadius n) (frequency j)*‖fourierCoeff j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def remainderExpInput (q br : Fin 2) (n : Fin 7) (j : Fin 31) : CI :=
  CI.ofReal ((taylorPhaseTable q br j).re.mul (RI.point (nearNode n)))
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorNorm00_check (j : Fin 31) : 0≤(taylorNorm00 j).lo ∧ (taylorNorm00 j).lo*(taylorNorm00 j).lo ≤ scale*max 0 (taylorPhaseTable 0 0 j).normSq.lo ∧ scale*(taylorPhaseTable 0 0 j).normSq.hi ≤ (taylorNorm00 j).hi*(taylorNorm00 j).hi ∧ 0≤(taylorNorm00 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm01_check (j : Fin 31) : 0≤(taylorNorm01 j).lo ∧ (taylorNorm01 j).lo*(taylorNorm01 j).lo ≤ scale*max 0 (taylorPhaseTable 0 1 j).normSq.lo ∧ scale*(taylorPhaseTable 0 1 j).normSq.hi ≤ (taylorNorm01 j).hi*(taylorNorm01 j).hi ∧ 0≤(taylorNorm01 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm10_check (j : Fin 31) : 0≤(taylorNorm10 j).lo ∧ (taylorNorm10 j).lo*(taylorNorm10 j).lo ≤ scale*max 0 (taylorPhaseTable 1 0 j).normSq.lo ∧ scale*(taylorPhaseTable 1 0 j).normSq.hi ≤ (taylorNorm10 j).hi*(taylorNorm10 j).hi ∧ 0≤(taylorNorm10 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm11_check (j : Fin 31) : 0≤(taylorNorm11 j).lo ∧ (taylorNorm11 j).lo*(taylorNorm11 j).lo ≤ scale*max 0 (taylorPhaseTable 1 1 j).normSq.lo ∧ scale*(taylorPhaseTable 1 1 j).normSq.hi ≤ (taylorNorm11 j).hi*(taylorNorm11 j).hi ∧ 0≤(taylorNorm11 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineBarrierBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

lemma sine_lower {d : ℚ} (hd : 0≤d) (hd18 : d≤18) :
    (sineLower d:ℝ)≤2*Real.sin (Real.pi*d/36) := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hd18' : (d:ℝ)≤18 := by exact_mod_cast hd18
  have hl : 0≤(piLow:ℝ)*d/36 := by
    have : (0:ℝ)≤piLow := by norm_num [piLow]
    positivity
  have hlay : (piLow:ℝ)*d/36≤Real.pi*d/36 := by nlinarith [sine_pi_bounds.1]
  have huay : Real.pi*d/36≤(piHigh:ℝ)*d/36 := by nlinarith [sine_pi_bounds.2]
  have hx : 0≤Real.pi*d/36 := by positivity
  have hx2 : Real.pi*d/36≤2 := by nlinarith [Real.pi_lt_four]
  have hs := sinePolynomial_lower hx hx2
  have h3 := pow_le_pow_left₀ hx huay 3
  have h5 := pow_le_pow_left₀ hl hlay 5
  have h7 := pow_le_pow_left₀ hx huay 7
  have h9 := pow_le_pow_left₀ hl hlay 9
  have h11 := pow_le_pow_left₀ hx huay 11
  unfold sineLower
  push_cast
  unfold sinePolynomial at hs
  linarith
lemma sine_arc_lower {d : ℚ} {t : ℝ} (hd : 0≤d) (hd18 : d≤18)
    (ht : t∈Icc (d:ℝ) (36-d)) : (sineLower d:ℝ)≤2*|Real.sin (Real.pi*t/36)| := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hx0 : 0≤Real.pi*d/36 := by positivity
  have hleft : -(Real.pi/2)≤Real.pi*d/36 := (neg_nonpos.mpr (by positivity)).trans hx0
  have hmon : Real.sin (Real.pi*d/36)≤Real.sin (Real.pi*t/36) := by
    by_cases h : t≤18
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.1])
    · rw [show Real.pi*t/36=Real.pi-(Real.pi*(36-t)/36) by ring,Real.sin_pi_sub]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.2])
  linarith [sine_lower hd hd18,le_abs_self (Real.sin (Real.pi*t/36))]

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
lemma cellFactors22 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors23 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors24 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors25 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end


