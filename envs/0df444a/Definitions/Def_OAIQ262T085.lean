-- Prove2me | Definitions.Def_OAIQ262T085
-- name    : OAIQ262T085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:48:35.440784+00:00
-- url     : https://prove2.me/theorems/c9e70013-e24b-4a44-b87d-e722e108850e
-- title:
--   Definitions bundle OAIQ262T085 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 1 definition and 66 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.columnNormTable`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Envelope_EnvelopeNorm0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm0.lean), [`Triangular_Envelope_EnvelopeNorm1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm1.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005` and `OAIQ262T006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T143`, `OAIQ262T144` and `OAIQ262T147`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006

section
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

lemma RI.mem_sqrt {a r : RI} {x : ℝ} (hx : a.Mem x) (h₀ : 0 ≤ x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.lo)
    (hr₂ : scale * a.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem (Real.sqrt x) := by
  have hs := Real.sq_sqrt h₀
  have hp := Real.sqrt_nonneg x
  have hrl : (0:ℝ) ≤ r.lo := by exact_mod_cast hr₀
  have hrh : (0:ℝ) ≤ r.hi := by exact_mod_cast hr₃
  have hrls : (r.lo:ℝ) * r.lo ≤ (scale:ℝ) * max (0:ℝ) (a.lo:ℝ) := by exact_mod_cast hr₁
  have hrhs : (scale:ℝ) * a.hi ≤ (r.hi:ℝ) * r.hi := by exact_mod_cast hr₂
  have hsl := mul_le_mul_of_nonneg_left (max_le (mul_nonneg scale_pos.le h₀) hx.1) scale_pos.le
  have hsh := mul_le_mul_of_nonneg_left hx.2 scale_pos.le
  have he : ((scale:ℝ) * Real.sqrt x)^2 = (scale:ℝ) * ((scale:ℝ)*x) := by
    rw [mul_pow, hs]
    ring
  constructor <;> nlinarith [mul_nonneg scale_pos.le hp]

lemma CI.mem_norm {a : CI} {r : RI} {x : ℂ} (hx : a.Mem x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.normSq.lo)
    (hr₂ : scale * a.normSq.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem ‖x‖ := by
  have hh := RI.mem_sqrt (CI.mem_normSq hx) (Complex.normSq_nonneg x) hr₀ hr₁ hr₂ hr₃
  simpa [Complex.normSq_eq_norm_sq] using hh

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

lemma restPolynomial_coeff (a : Fin 15) (n : ℕ) :
    (restPolynomial a).coeff n = phase (-(residue a:ℂ)) *
      (-(atomPolynomial.coeff n) +
        (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
        (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2))) := by
  have hh := coeff_atom_mul a (restPolynomial a) n
  rw [← atomPolynomial_factor] at hh
  have he : -(atomPolynomial.coeff n) +
      (if n=0 then 0 else 2*(restPolynomial a).coeff (n-1)) -
      (if n<2 then 0 else phase (-(residue a:ℂ))*(restPolynomial a).coeff (n-2)) =
      phase (residue a)*(restPolynomial a).coeff n := by
    linear_combination -hh
  rw [he, ← mul_assoc, phase_neg_mul, one_mul]

lemma recoverRest_mem (a : Fin 15) (e : CI) (he : e.Mem (phase (residue a)))
    (v : Fin 31 → CI) (hv : ∀ j, recoverRest e v j = v j) :
    ∀ j : Fin 31, (v j).Mem ((restPolynomial a).coeff j.val) := by
  have he' : e.conj.Mem (phase (-(residue a:ℂ))) := by
    simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
  suffices hs : ∀ n (hn : n<31), (v ⟨n,hn⟩).Mem ((restPolynomial a).coeff n) from
    fun j => hs j.val j.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [← hv, restPolynomial_coeff]
    simp only [recoverRest]
    apply CI.mem_mul he'
    apply CI.mem_sub
    · apply CI.mem_add (CI.mem_neg (atomPolynomial_coeff_mem ⟨n,hn⟩))
      split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul (by simpa using CI.mem_point 2) (ih (n-1) (by omega) (by omega))
    · split_ifs with hz
      · simpa using CI.mem_point 0
      · exact CI.mem_mul he' (ih (n-2) (by omega) (by omega))

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
lemma dCoeffBox_mem (a : Fin 15) (e : CI) (r : Fin 31 → CI)
    (he : e.Mem (phase (residue a)))
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (dCoeffBox e r j).Mem (dCoefficient a j) := by
  rw [dCoefficient_eq]
  apply CI.mem_mul (CI.mem_mul CI.mem_imag kappaBox_mem)
  apply CI.mem_sub (CI.mem_mul he (hr j))
  split_ifs
  · simpa using CI.mem_point 0
  · have hh : e.conj.Mem (phase (-(residue a:ℂ))) := by
      simpa only [← Complex.ofReal_intCast, phase_conj] using CI.mem_conj he
    exact CI.mem_mul hh (hr ⟨j.val-2,by omega⟩)

lemma restBox0_calc (j : Fin 31) : recoverRest phaseBox0 restBox0 j = restBox0 j := by
  revert j
  decide +kernel
lemma restBox0_mem (j : Fin 31) : (restBox0 j).Mem ((restPolynomial ⟨0,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨0,by norm_num⟩ phaseBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_calc
lemma cBox0_calc (j : Fin 31) : cCoeffBox restBox0 j = cBox0 j := by
  revert j
  decide +kernel
lemma cBox0_mem (j : Fin 31) : (cBox0 j).Mem (cCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← cBox0_calc]
  exact cCoeffBox_mem ⟨0,by norm_num⟩ restBox0 restBox0_mem j
lemma dBox0_calc (j : Fin 31) : dCoeffBox phaseBox0 restBox0 j = dBox0 j := by
  revert j
  decide +kernel
lemma dBox0_mem (j : Fin 31) : (dBox0 j).Mem (dCoefficient ⟨0,by norm_num⟩ j) := by
  rw [← dBox0_calc]
  apply dCoeffBox_mem ⟨0,by norm_num⟩ phaseBox0 restBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact restBox0_mem
lemma restBox1_calc (j : Fin 31) : recoverRest phaseBox1 restBox1 j = restBox1 j := by
  revert j
  decide +kernel
lemma restBox1_mem (j : Fin 31) : (restBox1 j).Mem ((restPolynomial ⟨1,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨1,by norm_num⟩ phaseBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_calc
lemma cBox1_calc (j : Fin 31) : cCoeffBox restBox1 j = cBox1 j := by
  revert j
  decide +kernel
lemma cBox1_mem (j : Fin 31) : (cBox1 j).Mem (cCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← cBox1_calc]
  exact cCoeffBox_mem ⟨1,by norm_num⟩ restBox1 restBox1_mem j
lemma dBox1_calc (j : Fin 31) : dCoeffBox phaseBox1 restBox1 j = dBox1 j := by
  revert j
  decide +kernel
lemma dBox1_mem (j : Fin 31) : (dBox1 j).Mem (dCoefficient ⟨1,by norm_num⟩ j) := by
  rw [← dBox1_calc]
  apply dCoeffBox_mem ⟨1,by norm_num⟩ phaseBox1 restBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact restBox1_mem
lemma restBox3_calc (j : Fin 31) : recoverRest phaseBox3 restBox3 j = restBox3 j := by
  revert j
  decide +kernel
lemma restBox3_mem (j : Fin 31) : (restBox3 j).Mem ((restPolynomial ⟨2,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨2,by norm_num⟩ phaseBox3
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact restBox3_calc
lemma cBox3_calc (j : Fin 31) : cCoeffBox restBox3 j = cBox3 j := by
  revert j
  decide +kernel
lemma cBox3_mem (j : Fin 31) : (cBox3 j).Mem (cCoefficient ⟨2,by norm_num⟩ j) := by
  rw [← cBox3_calc]
  exact cCoeffBox_mem ⟨2,by norm_num⟩ restBox3 restBox3_mem j
lemma restBox4_calc (j : Fin 31) : recoverRest phaseBox4 restBox4 j = restBox4 j := by
  revert j
  decide +kernel
lemma restBox4_mem (j : Fin 31) : (restBox4 j).Mem ((restPolynomial ⟨3,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨3,by norm_num⟩ phaseBox4
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact restBox4_calc
lemma cBox4_calc (j : Fin 31) : cCoeffBox restBox4 j = cBox4 j := by
  revert j
  decide +kernel
lemma cBox4_mem (j : Fin 31) : (cBox4 j).Mem (cCoefficient ⟨3,by norm_num⟩ j) := by
  rw [← cBox4_calc]
  exact cCoeffBox_mem ⟨3,by norm_num⟩ restBox4 restBox4_mem j
lemma restBox7_calc (j : Fin 31) : recoverRest phaseBox7 restBox7 j = restBox7 j := by
  revert j
  decide +kernel
lemma restBox7_mem (j : Fin 31) : (restBox7 j).Mem ((restPolynomial ⟨4,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨4,by norm_num⟩ phaseBox7
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact restBox7_calc
lemma cBox7_calc (j : Fin 31) : cCoeffBox restBox7 j = cBox7 j := by
  revert j
  decide +kernel
lemma cBox7_mem (j : Fin 31) : (cBox7 j).Mem (cCoefficient ⟨4,by norm_num⟩ j) := by
  rw [← cBox7_calc]
  exact cCoeffBox_mem ⟨4,by norm_num⟩ restBox7 restBox7_mem j
lemma restBox9_calc (j : Fin 31) : recoverRest phaseBox9 restBox9 j = restBox9 j := by
  revert j
  decide +kernel
lemma restBox9_mem (j : Fin 31) : (restBox9 j).Mem ((restPolynomial ⟨5,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨5,by norm_num⟩ phaseBox9
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact restBox9_calc
lemma cBox9_calc (j : Fin 31) : cCoeffBox restBox9 j = cBox9 j := by
  revert j
  decide +kernel
lemma cBox9_mem (j : Fin 31) : (cBox9 j).Mem (cCoefficient ⟨5,by norm_num⟩ j) := by
  rw [← cBox9_calc]
  exact cCoeffBox_mem ⟨5,by norm_num⟩ restBox9 restBox9_mem j
lemma restBox12_calc (j : Fin 31) : recoverRest phaseBox12 restBox12 j = restBox12 j := by
  revert j
  decide +kernel
lemma restBox12_mem (j : Fin 31) : (restBox12 j).Mem ((restPolynomial ⟨6,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨6,by norm_num⟩ phaseBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_calc
lemma cBox12_calc (j : Fin 31) : cCoeffBox restBox12 j = cBox12 j := by
  revert j
  decide +kernel
lemma cBox12_mem (j : Fin 31) : (cBox12 j).Mem (cCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← cBox12_calc]
  exact cCoeffBox_mem ⟨6,by norm_num⟩ restBox12 restBox12_mem j
lemma dBox12_calc (j : Fin 31) : dCoeffBox phaseBox12 restBox12 j = dBox12 j := by
  revert j
  decide +kernel
lemma dBox12_mem (j : Fin 31) : (dBox12 j).Mem (dCoefficient ⟨6,by norm_num⟩ j) := by
  rw [← dBox12_calc]
  apply dCoeffBox_mem ⟨6,by norm_num⟩ phaseBox12 restBox12
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact restBox12_mem
lemma restBox13_calc (j : Fin 31) : recoverRest phaseBox13 restBox13 j = restBox13 j := by
  revert j
  decide +kernel
lemma restBox13_mem (j : Fin 31) : (restBox13 j).Mem ((restPolynomial ⟨7,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨7,by norm_num⟩ phaseBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_calc
lemma cBox13_calc (j : Fin 31) : cCoeffBox restBox13 j = cBox13 j := by
  revert j
  decide +kernel
lemma cBox13_mem (j : Fin 31) : (cBox13 j).Mem (cCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← cBox13_calc]
  exact cCoeffBox_mem ⟨7,by norm_num⟩ restBox13 restBox13_mem j
lemma dBox13_calc (j : Fin 31) : dCoeffBox phaseBox13 restBox13 j = dBox13 j := by
  revert j
  decide +kernel
lemma dBox13_mem (j : Fin 31) : (dBox13 j).Mem (dCoefficient ⟨7,by norm_num⟩ j) := by
  rw [← dBox13_calc]
  apply dCoeffBox_mem ⟨7,by norm_num⟩ phaseBox13 restBox13
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact restBox13_mem
lemma restBox16_calc (j : Fin 31) : recoverRest phaseBox16 restBox16 j = restBox16 j := by
  revert j
  decide +kernel
lemma restBox16_mem (j : Fin 31) : (restBox16 j).Mem ((restPolynomial ⟨8,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨8,by norm_num⟩ phaseBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_calc
lemma cBox16_calc (j : Fin 31) : cCoeffBox restBox16 j = cBox16 j := by
  revert j
  decide +kernel
lemma cBox16_mem (j : Fin 31) : (cBox16 j).Mem (cCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← cBox16_calc]
  exact cCoeffBox_mem ⟨8,by norm_num⟩ restBox16 restBox16_mem j
lemma dBox16_calc (j : Fin 31) : dCoeffBox phaseBox16 restBox16 j = dBox16 j := by
  revert j
  decide +kernel
lemma dBox16_mem (j : Fin 31) : (dBox16 j).Mem (dCoefficient ⟨8,by norm_num⟩ j) := by
  rw [← dBox16_calc]
  apply dCoeffBox_mem ⟨8,by norm_num⟩ phaseBox16 restBox16
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact restBox16_mem
lemma restBox19_calc (j : Fin 31) : recoverRest phaseBox19 restBox19 j = restBox19 j := by
  revert j
  decide +kernel
lemma restBox19_mem (j : Fin 31) : (restBox19 j).Mem ((restPolynomial ⟨9,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨9,by norm_num⟩ phaseBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_calc
lemma cBox19_calc (j : Fin 31) : cCoeffBox restBox19 j = cBox19 j := by
  revert j
  decide +kernel
lemma cBox19_mem (j : Fin 31) : (cBox19 j).Mem (cCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← cBox19_calc]
  exact cCoeffBox_mem ⟨9,by norm_num⟩ restBox19 restBox19_mem j
lemma dBox19_calc (j : Fin 31) : dCoeffBox phaseBox19 restBox19 j = dBox19 j := by
  revert j
  decide +kernel
lemma dBox19_mem (j : Fin 31) : (dBox19 j).Mem (dCoefficient ⟨9,by norm_num⟩ j) := by
  rw [← dBox19_calc]
  apply dCoeffBox_mem ⟨9,by norm_num⟩ phaseBox19 restBox19
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact restBox19_mem
lemma restBox21_calc (j : Fin 31) : recoverRest phaseBox21 restBox21 j = restBox21 j := by
  revert j
  decide +kernel
lemma restBox21_mem (j : Fin 31) : (restBox21 j).Mem ((restPolynomial ⟨10,by norm_num⟩).coeff j.val) := by
  apply recoverRest_mem ⟨10,by norm_num⟩ phaseBox21
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact restBox21_calc
lemma cBox21_calc (j : Fin 31) : cCoeffBox restBox21 j = cBox21 j := by
  revert j
  decide +kernel
lemma cBox21_mem (j : Fin 31) : (cBox21 j).Mem (cCoefficient ⟨10,by norm_num⟩ j) := by
  rw [← cBox21_calc]
  exact cCoeffBox_mem ⟨10,by norm_num⟩ restBox21 restBox21_mem j
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm0_check (j : Fin 31) : 0≤(columnNorm0 j).lo ∧ (columnNorm0 j).lo*(columnNorm0 j).lo ≤ scale*max 0 (columnTable 0 j).normSq.lo ∧ scale*(columnTable 0 j).normSq.hi ≤ (columnNorm0 j).hi*(columnNorm0 j).hi ∧ 0≤(columnNorm0 j).hi := by
  revert j
  decide +kernel
lemma columnNorm1_check (j : Fin 31) : 0≤(columnNorm1 j).lo ∧ (columnNorm1 j).lo*(columnNorm1 j).lo ≤ scale*max 0 (columnTable 1 j).normSq.lo ∧ scale*(columnTable 1 j).normSq.hi ≤ (columnNorm1 j).hi*(columnNorm1 j).hi ∧ 0≤(columnNorm1 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm10_check (j : Fin 31) : 0≤(columnNorm10 j).lo ∧ (columnNorm10 j).lo*(columnNorm10 j).lo ≤ scale*max 0 (columnTable 10 j).normSq.lo ∧ scale*(columnTable 10 j).normSq.hi ≤ (columnNorm10 j).hi*(columnNorm10 j).hi ∧ 0≤(columnNorm10 j).hi := by
  revert j
  decide +kernel
lemma columnNorm11_check (j : Fin 31) : 0≤(columnNorm11 j).lo ∧ (columnNorm11 j).lo*(columnNorm11 j).lo ≤ scale*max 0 (columnTable 11 j).normSq.lo ∧ scale*(columnTable 11 j).normSq.hi ≤ (columnNorm11 j).hi*(columnNorm11 j).hi ∧ 0≤(columnNorm11 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def columnNormTable : Fin 23 → Fin 31 → RI := ![columnNorm0,columnNorm1,columnNorm2,columnNorm3,columnNorm4,columnNorm5,columnNorm6,columnNorm7,columnNorm8,columnNorm9,columnNorm10,columnNorm11,columnNorm12,columnNorm13,columnNorm14,columnNorm15,columnNorm16,columnNorm17,columnNorm18,columnNorm19,columnNorm20,columnNorm21,columnNorm22]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma boundC_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (envelopeSumBoxC j).mul (columnNormTable ⟨c.val,by omega⟩ j))=boundC c := by
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end


