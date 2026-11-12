-- Prove2me | Definitions.Def_OAIQ262T097
-- name    : OAIQ262T097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:51:46.785085+00:00
-- url     : https://prove2.me/theorems/04d92f13-0830-4b4d-9dec-464da6563c48
-- title:
--   Definitions bundle OAIQ262T097 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 5 definitions and 13 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.frozenTaylor`, `OAI.AtomicTriangular.Construction.frozenTaylorRow`, `OAI.AtomicTriangular.Construction.taylorRow`, `OAI.AtomicTriangular.Construction.taylorWave`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Signs_Exceptional`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Exceptional.lean), [`Triangular_Signs_RemainderBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderBoxes.lean), [`Triangular_Signs_RemainderNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean), [`Triangular_Signs_SineGrid0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGrid0.lean), [`Triangular_Signs_SineGridAnalytic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGridAnalytic.lean), [`Triangular_Signs_SineGridDefs`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/SineGridDefs.lean), [`Triangular_Taylor_FiniteTaylorIdentity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/FiniteTaylorIdentity.lean), [`Triangular_Taylor_Taylor`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/Taylor.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T012`, `OAIQ262T013`, `OAIQ262T015` and `OAIQ262T016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T144`, `OAIQ262T146`, `OAIQ262T147`, `OAIQ262T148` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T012
import Definitions.Def_OAIQ262T013
import Definitions.Def_OAIQ262T015
import Definitions.Def_OAIQ262T016

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def taylorWave (q branch : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) : ℂ :=
  taylorAmplitude q branch t * exp (taylorPhase q branch t*m) *
    (taylorPhase q branch t)^(l+2) / ((l+2).factorial:ℂ)

def taylorRow (side : Fin 2) (m : ℤ) (y : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  y^l*(∑ q : Fin 2, ∑ j : Fin 31,
    (finiteSpectrum side q j r*taylorWave q 0 m l (frequency j) +
    finiteSpectrum (otherSide side) q j r*taylorWave q 1 m l (frequency j))).re

def finiteTaylor (side : Fin 2) (m : ℤ) (y : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l ∈ Finset.range 21, (∑ r : Fin 8, taylorRow side m y l r*e r)*τ^l

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_Exceptional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def frozenTaylorRow (z : ℝ) (l : ℕ) (r : Fin 8) : ℝ :=
  (if r.val=0 then 0 else -taylorRow 0 1 1 l r) -
    (if r.val=1 then z*taylorRow 0 1 1 l 0 else 0)

def frozenTaylor (z : ℝ) (e : Fin 8 → ℝ) (τ : ℝ) : ℝ :=
  ∑ l : Fin 21, (∑ r : Fin 8, frozenTaylorRow z l.val r*e r)*τ^l.val
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open AtomicTriangular.FiniteCertificate
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma nearRadiusBox_mem (n : Fin 7) : (nearRadiusBox n).Mem (nearRadius n) := by
  fin_cases n <;> (first | (simp [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; all_goals first | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | rfl | decide) | (norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale]; done) | norm_num [nearRadiusBox,nearRadius,RI.Mem,RI.point,RI.divNat,scale])
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderNorm
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
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

lemma local_geometry (u : Fin 30) :
    |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j := by
  exact (show ∀ u : Fin 30, |localHalf u|≤5/2 ∧ localPhase u (localPivot u)=0 ∧
    ∀ j : Fin 15,localCenter u-residue j=localPhase u j+36*localShift u j by decide +kernel) u
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors00 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors01 (k : Fin 100) :
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0 ≤ cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_SineGridAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction

lemma sin_abs_local (u : Fin 30) (j : Fin 15) (y : ℝ) :
    |Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|=
      |Real.sin (Real.pi*((localPhase u j:ℝ)+y)/36)| := by
  have he : (localCenter u:ℝ)-residue j=localPhase u j+36*(localShift u j:ℝ) := by
    exact_mod_cast (local_geometry u).2.2 j
  rw [show (localCenter u:ℝ)+y-residue j=(localPhase u j:ℝ)+y+36*(localShift u j:ℝ) by linarith,
    show Real.pi*((localPhase u j:ℝ)+y+36*(localShift u j:ℝ))/36=
      Real.pi*((localPhase u j:ℝ)+y)/36+(localShift u j:ℝ)*Real.pi by ring,
    Real.sin_add_int_mul_pi,abs_mul,abs_zpow]
  norm_num
lemma cell_factor_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (j : Fin 15) {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) :
    (cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1)≤
      2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)| := by
  rw [sin_abs_local]
  by_cases hj : j=localPivot u
  · subst j
    simpa only [cellFactor,ite_true, if_true,(local_geometry u).2.1,Int.cast_zero,zero_add] using
      sine_vanishing_lower hg.1 hg.2.1 (abs_cell_le u k hy)
  · have hsep : (cellSeparation u k j:ℝ)=
        min ((localPhase u j:ℝ)+(cellLo u k:ℝ)) (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))) := by
      unfold cellSeparation
      push_cast
      rfl
    have ht : (localPhase u j:ℝ)+y∈Icc (cellSeparation u k j:ℝ) (36-cellSeparation u k j) := by
      rw [hsep]
      constructor <;> linarith [min_le_left ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),
        min_le_right ((localPhase u j:ℝ)+(cellLo u k:ℝ))
        (36-((localPhase u j:ℝ)+(cellHi u k:ℝ))),hy.1,hy.2]
    simpa only [cellFactor,ite_eq_right hj,mul_one] using sine_arc_lower (hg.2.2 j hj).1 (hg.2.2 j hj).2 ht
lemma realP_cell_lower (u : Fin 30) (k : Fin 100)
    (hg : 0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
      (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18))
    (hn : ∀ j : Fin 15,0 ≤ cellFactor u k j)
    (hp : cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2)
    {y : ℝ} (hy : y∈Icc (cellLo u k:ℝ) (cellHi u k:ℝ)) (hy0 : y≠0) :
    (cellBarrier u:ℝ)*y^2 < realP ((localCenter u:ℝ)+y) := by
  have hc : (cellBarrier u:ℝ)<∏ j : Fin 15,(cellFactor u k j:ℝ)^2 := by
    exact_mod_cast hp
  calc
    _ < (∏ j : Fin 15,(cellFactor u k j:ℝ)^2)*y^2 := mul_lt_mul_of_pos_right hc (sq_pos_of_ne_zero hy0)
    _ = ∏ j : Fin 15,((cellFactor u k j:ℝ)*(if j=localPivot u then |y| else 1))^2 := by
      simp only [mul_pow]
      rw [Finset.prod_mul_distrib]
      simp only [ite_pow,one_pow,sq_abs]
      rw [Fintype.prod_ite_eq']
    _ ≤ ∏ j : Fin 15,(2*|Real.sin (Real.pi*((localCenter u:ℝ)+y-residue j)/36)|)^2 := by
      apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      intro j _
      have hnon : 0≤(cellFactor u k j:ℝ) := by exact_mod_cast hn j
      apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
      exact cell_factor_lower u k hg j hy
    _ = _ := by simp [realP,mul_pow,sq_abs]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_FiniteTaylorIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma hasDerivAt_finiteWaveJet (q br : Fin 2) (t : ℝ) (k : ℕ) (s : ℂ) :
    HasDerivAt (finiteWaveJet q br t k) (finiteWaveJet q br t (k+1) s) s := by
  unfold finiteWaveJet
  have hh := (((hasDerivAt_id s).const_mul (taylorPhase q br t)).cexp.const_mul
    (taylorAmplitude q br t)).mul_const ((taylorPhase q br t)^k)
  simpa only [finiteWaveJet,mul_one,one_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm,
    id_eq] using hh

lemma taylorWave_eq (q br : Fin 2) (m : ℤ) (l : ℕ) (t : ℝ) :
    taylorWave q br m l t = finiteWaveJet q br t (l+2) m / ((l+2).factorial:ℂ) := rfl
end AtomicTriangular.Construction
end

end OAI
end


