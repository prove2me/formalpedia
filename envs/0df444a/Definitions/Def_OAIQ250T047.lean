-- Prove2me | Definitions.Def_OAIQ250T047
-- name    : OAIQ250T047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T13:57:44.144586+00:00
-- url     : https://prove2.me/theorems/29c03428-a310-45cb-ae42-575c129df5fd
-- title:
--   Definitions bundle OAIQ250T047 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 90 declarations of OpenAI's Lean: 8 definitions and 82 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.DTable`, `OAI.AtomicTriangular.FiniteCertificate.decayBox`, `OAI.AtomicTriangular.FiniteCertificate.decayExpBox`, `OAI.AtomicTriangular.FiniteCertificate.jetTable`, `OAI.AtomicTriangular.FiniteCertificate.lambdaBox`, `OAI.AtomicTriangular.FiniteCertificate.psiBox`, `OAI.AtomicTriangular.FiniteCertificate.psiTableD`, `OAI.AtomicTriangular.Interval.RI.inv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Certificate_WaveJetsData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean), [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopeNorms`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorms.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`; the bundles `OAIQ250T003`, `OAIQ250T004`, `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007` and `OAIQ250T008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T083`, `OAIQ250T084`, `OAIQ250T085`, `OAIQ250T087`, `OAIQ250T098` and `OAIQ250T151`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ250T003
import Definitions.Def_OAIQ250T004
import Definitions.Def_OAIQ250T005
import Definitions.Def_OAIQ250T006
import Definitions.Def_OAIQ250T007
import Definitions.Def_OAIQ250T008

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
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

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

noncomputable section
open scoped BigOperators

def RI.inv (a : RI) : RI := if a.hi < 0 then a.neg.invPos.neg else a.invPos

lemma RI.mem_inv {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo ∨ a.hi < 0) :
    a.inv.Mem x⁻¹ := by
  unfold RI.inv
  split_ifs with hh
  · have hp : 0 < a.neg.lo := by simpa [RI.neg] using neg_pos.mpr hh
    simpa using RI.mem_neg (RI.mem_invPos (RI.mem_neg hx) hp)
  · exact RI.mem_invPos hx (ha.resolve_right hh)

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
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma DBox0_calc : jetBox3_0.re.mul ((RI.point 6).mul QBox0).inv = DBox0 := by decide +kernel
lemma DBox0_mem : DBox0.Mem (D 0) := by
  rw [← DBox0_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_0_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox0_mem
  · left; decide +kernel
lemma DBox1_calc : jetBox3_1.re.mul ((RI.point 6).mul QBox1).inv = DBox1 := by decide +kernel
lemma DBox1_mem : DBox1.Mem (D 1) := by
  rw [← DBox1_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_1_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox1_mem
  · left; decide +kernel
lemma DBox3_calc : jetBox3_3.re.mul ((RI.point 6).mul QBox3).inv = DBox3 := by decide +kernel
lemma DBox3_mem : DBox3.Mem (D 3) := by
  rw [← DBox3_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_3_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox3_mem
  · left; decide +kernel
lemma DBox4_calc : jetBox3_4.re.mul ((RI.point 6).mul QBox4).inv = DBox4 := by decide +kernel
lemma DBox4_mem : DBox4.Mem (D 4) := by
  rw [← DBox4_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_4_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox4_mem
  · left; decide +kernel
lemma DBox7_calc : jetBox3_7.re.mul ((RI.point 6).mul QBox7).inv = DBox7 := by decide +kernel
lemma DBox7_mem : DBox7.Mem (D 7) := by
  rw [← DBox7_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_7_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox7_mem
  · left; decide +kernel
lemma DBox9_calc : jetBox3_9.re.mul ((RI.point 6).mul QBox9).inv = DBox9 := by decide +kernel
lemma DBox9_mem : DBox9.Mem (D 9) := by
  rw [← DBox9_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_9_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox9_mem
  · left; decide +kernel
lemma DBox12_calc : jetBox3_12.re.mul ((RI.point 6).mul QBox12).inv = DBox12 := by decide +kernel
lemma DBox12_mem : DBox12.Mem (D 12) := by
  rw [← DBox12_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_12_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox12_mem
  · left; decide +kernel
lemma DBox13_calc : jetBox3_13.re.mul ((RI.point 6).mul QBox13).inv = DBox13 := by decide +kernel
lemma DBox13_mem : DBox13.Mem (D 13) := by
  rw [← DBox13_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_13_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox13_mem
  · left; decide +kernel
lemma DBox16_calc : jetBox3_16.re.mul ((RI.point 6).mul QBox16).inv = DBox16 := by decide +kernel
lemma DBox16_mem : DBox16.Mem (D 16) := by
  rw [← DBox16_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_16_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox16_mem
  · left; decide +kernel
lemma DBox19_calc : jetBox3_19.re.mul ((RI.point 6).mul QBox19).inv = DBox19 := by decide +kernel
lemma DBox19_mem : DBox19.Mem (D 19) := by
  rw [← DBox19_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_19_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox19_mem
  · left; decide +kernel
lemma DBox21_calc : jetBox3_21.re.mul ((RI.point 6).mul QBox21).inv = DBox21 := by decide +kernel
lemma DBox25_calc : jetBox3_25.re.mul ((RI.point 6).mul QBox25).inv = DBox25 := by decide +kernel
lemma DBox25_mem : DBox25.Mem (D 25) := by
  rw [← DBox25_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_25_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox25_mem
  · left; decide +kernel
lemma DBox27_calc : jetBox3_27.re.mul ((RI.point 6).mul QBox27).inv = DBox27 := by decide +kernel
lemma DBox27_mem : DBox27.Mem (D 27) := by
  rw [← DBox27_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_27_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox27_mem
  · left; decide +kernel
lemma DBox28_calc : jetBox3_28.re.mul ((RI.point 6).mul QBox28).inv = DBox28 := by decide +kernel
lemma DBox28_mem : DBox28.Mem (D 28) := by
  rw [← DBox28_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_28_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox28_mem
  · left; decide +kernel
lemma DBox31_calc : jetBox3_31.re.mul ((RI.point 6).mul QBox31).inv = DBox31 := by decide +kernel
lemma DBox31_mem : DBox31.Mem (D 31) := by
  rw [← DBox31_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_31_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox31_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma realFrequencyBox_mem (j : Fin 31) : (realFrequencyBox j).Mem (frequency j) := by
  have hh := RI.mem_divNat (RI.mem_point ((j.val:ℤ)-15)) (by norm_num : 0<(18:ℕ))
  simpa only [realFrequencyBox, frequency, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_ofNat] using hh

lemma denBox_mem (q : Fin 2) (j : Fin 31) :
    (denBox q j).Mem (waveDen (damping q) (frequency j)) := by
  exact RI.mem_add (RI.mem_pow (dampingBox_mem q) 2) (RI.mem_pow (realFrequencyBox_mem j) 2)
lemma denBox_pos (q : Fin 2) (j : Fin 31) : 0 < (denBox q j).lo := by
  revert q j
  decide +kernel
lemma bdenBox_pos (q : Fin 2) (j : Fin 31) : 0 < (bBox.mul (denBox q j)).lo := by
  revert q j
  decide +kernel

lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

def lambdaBox (q : Fin 2) (j : Fin 31) : CI :=
  ((CI.ofReal (dampingBox q)).add (CI.imag.mul (CI.ofReal (realFrequencyBox j)))).mul
    (CI.ofReal (bBox.mul (denBox q j)).invPos)
lemma lambdaBox_mem (q : Fin 2) (j : Fin 31) :
    (lambdaBox q j).Mem (lambda (damping q) (frequency j)) := by
  unfold lambda
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  exact CI.mem_mul (CI.mem_add (CI.mem_ofReal (dampingBox_mem q))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal (realFrequencyBox_mem j))))
    (CI.mem_ofReal (RI.mem_invPos (RI.mem_mul bBox_mem (denBox_mem q j)) (bdenBox_pos q j)))

lemma zetaBox_mem (q v : Fin 2) (j : Fin 31) :
    (zetaBox q v j).Mem (zeta (damping q) (damping v) (frequency j)) := by
  have hh := CI.mem_add (CI.mem_ofReal (RI.mem_neg
    (RI.mem_mul (realFrequencyBox_mem j) (xwaveBox_mem q j))))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal
      (RI.mem_sub (RI.mem_mul (dampingBox_mem q) (xwaveBox_mem q j)) (dampingBox_mem v))))
  simpa only [zetaBox,zeta,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul] using hh

lemma wavePhaseBox_mem (q v : Fin 2) (j : Fin 31) :
    (wavePhaseBox q v j).Mem (I*Real.pi*zeta (damping q) (damping v) (frequency j)) :=
  CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (zetaBox_mem q v j)
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
end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaTable0_calc (j : Fin 31) : lambdaBox 0 j = lambdaTable0 j := by
  revert j
  decide +kernel
lemma lambdaTable0_mem (j : Fin 31) : (lambdaTable0 j).Mem (lambda (damping 0) (frequency j)) := by
  rw [← lambdaTable0_calc]
  exact lambdaBox_mem 0 j
lemma lambdaTable1_calc (j : Fin 31) : lambdaBox 1 j = lambdaTable1 j := by
  revert j
  decide +kernel
lemma lambdaTable1_mem (j : Fin 31) : (lambdaTable1 j).Mem (lambda (damping 1) (frequency j)) := by
  rw [← lambdaTable1_calc]
  exact lambdaBox_mem 1 j
lemma lambdaTable_mem (q : Fin 2) (j : Fin 31) : (lambdaTable q j).Mem (lambda (damping q) (frequency j)) := by
  fin_cases q
  · exact lambdaTable0_mem j
  · exact lambdaTable1_mem j
def DTable : Fin 10 → RI := ![DBox1,DBox3,DBox4,DBox7,DBox9,DBox12,DBox13,DBox16,DBox19,DBox21]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def jetTable : Fin 2 → Fin 20 → Fin 31 → CI :=
  ![![jetTable0_0,jetTable0_1,jetTable0_2,jetTable0_3,jetTable0_4,jetTable0_5,jetTable0_6,jetTable0_7,jetTable0_8,jetTable0_9,jetTable0_10,jetTable0_11,jetTable0_12,jetTable0_13,jetTable0_14,jetTable0_15,jetTable0_16,jetTable0_17,jetTable0_18,jetTable0_19],
  ![jetTable1_0,jetTable1_1,jetTable1_2,jetTable1_3,jetTable1_4,jetTable1_5,jetTable1_6,jetTable1_7,jetTable1_8,jetTable1_9,jetTable1_10,jetTable1_11,jetTable1_12,jetTable1_13,jetTable1_14,jetTable1_15,jetTable1_16,jetTable1_17,jetTable1_18,jetTable1_19]]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def decayBox (q v : Fin 2) (j : Fin 31) : RI := (wavePhaseBox q v j).re.neg
lemma decayBox_mem (q v : Fin 2) (j : Fin 31) :
    (decayBox q v j).Mem (frequencyDecay (damping q) (damping v) (frequency j)) := by
  have hh := RI.mem_neg (wavePhaseBox_mem q v j).1
  convert hh using 1
  · rfl
  · rw [wavePhase_re]
    unfold frequencyDecay
    ring

def decayExpBox (q v : Fin 2) (n : ℤ) (j : Fin 31) : RI :=
  (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).exp.re
lemma decayExpBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31)
    (hh : (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).normSq.hi ≤ scale*1024^2) :
    (decayExpBox q v n j).Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)) :=
  ri_exp_mem (RI.mem_mul (RI.mem_neg (decayBox_mem q v j)) (RI.mem_point n)) hh

def psiBox (_q _v : Fin 2) (_n : ℤ) (_j : Fin 31) (qb db lell dnorm ex : RI) : RI :=
  ((((RI.point 1).add db.abs).add dnorm).mul lell).mul qb.invPos |>.mul ex
lemma psiBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31) {qb db lell dnorm ex : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (hl : lell.Mem ‖lambda (damping q) (frequency j)‖)
    (hn : dnorm.Mem ‖I*Real.pi*zeta (damping q) (damping v) (frequency j)‖)
    (he : ex.Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)))
    (hqp : 0<qb.lo) :
    (psiBox q v n j qb db lell dnorm ex).Mem (normJetEnvelope (damping q) (damping v) n (frequency j)) := by
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul (RI.mem_add (RI.mem_add ri1_mem (RI.mem_abs hd)) hn) hl)
    (RI.mem_invPos hq hqp)) he
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fourierNorm_mem (j : Fin 31) : (columnNorm22 j).Mem ‖fourierCoeff j‖ := columnNorm22_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm1_mem (j : Fin 31) : (lambdaNorm1 j).Mem ‖lambda (damping 1) (frequency j)‖ := by
  have hh := lambdaNorm1_check j
  exact CI.mem_norm (lambdaTable_mem 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma envelopePhase10_calc (j : Fin 31) : wavePhaseBox 1 0 j=envelopePhase10 j := by
  revert j
  decide +kernel
lemma envelopePhase10_mem (j : Fin 31) : (envelopePhase10 j).Mem (I*Real.pi*zeta (damping 1) (damping 0) (frequency j)) := by
  rw [← envelopePhase10_calc]
  exact wavePhaseBox_mem 1 0 j
lemma phaseNorm10_mem (j : Fin 31) : (phaseNorm10 j).Mem ‖I*Real.pi*zeta (damping 1) (damping 0) (frequency j)‖ := by
  have hh := phaseNorm10_check j
  exact CI.mem_norm (envelopePhase10_mem j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC36_mem (j : Fin 31) : (envelopeExpC36 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*36)) := by
  rw [← envelopeExpC36_calc]
  have hh := decayExpBox_mem 1 0 36 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC36_pre j)
lemma psiC36_calc (j : Fin 31) : psiBox 1 0 36 j QBox0 DBox0 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC36 j)=psiC36 j := by
  revert j
  decide +kernel
lemma psiC36_mem (j : Fin 31) : (psiC36 j).Mem (normJetEnvelope (damping 1) (damping 0) 36 (frequency j)) := by
  rw [← psiC36_calc]
  apply psiBox_mem
  · convert QBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox0_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC36_mem j
  · decide +kernel
lemma envelopeExpC37_mem (j : Fin 31) : (envelopeExpC37 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*37)) := by
  rw [← envelopeExpC37_calc]
  have hh := decayExpBox_mem 1 0 37 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC37_pre j)
lemma psiC37_calc (j : Fin 31) : psiBox 1 0 37 j QBox1 DBox1 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC37 j)=psiC37 j := by
  revert j
  decide +kernel
lemma psiC37_mem (j : Fin 31) : (psiC37 j).Mem (normJetEnvelope (damping 1) (damping 0) 37 (frequency j)) := by
  rw [← psiC37_calc]
  apply psiBox_mem
  · convert QBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox1_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC37_mem j
  · decide +kernel
lemma envelopeExpC39_mem (j : Fin 31) : (envelopeExpC39 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*39)) := by
  rw [← envelopeExpC39_calc]
  have hh := decayExpBox_mem 1 0 39 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC39_pre j)
lemma psiC39_calc (j : Fin 31) : psiBox 1 0 39 j QBox3 DBox3 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC39 j)=psiC39 j := by
  revert j
  decide +kernel
lemma psiC39_mem (j : Fin 31) : (psiC39 j).Mem (normJetEnvelope (damping 1) (damping 0) 39 (frequency j)) := by
  rw [← psiC39_calc]
  apply psiBox_mem
  · convert QBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox3_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC39_mem j
  · decide +kernel
lemma envelopeExpC40_mem (j : Fin 31) : (envelopeExpC40 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*40)) := by
  rw [← envelopeExpC40_calc]
  have hh := decayExpBox_mem 1 0 40 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC40_pre j)
lemma psiC40_calc (j : Fin 31) : psiBox 1 0 40 j QBox4 DBox4 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC40 j)=psiC40 j := by
  revert j
  decide +kernel
lemma psiC40_mem (j : Fin 31) : (psiC40 j).Mem (normJetEnvelope (damping 1) (damping 0) 40 (frequency j)) := by
  rw [← psiC40_calc]
  apply psiBox_mem
  · convert QBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox4_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC40_mem j
  · decide +kernel
lemma envelopeExpC43_mem (j : Fin 31) : (envelopeExpC43 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*43)) := by
  rw [← envelopeExpC43_calc]
  have hh := decayExpBox_mem 1 0 43 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC43_pre j)
lemma psiC43_calc (j : Fin 31) : psiBox 1 0 43 j QBox7 DBox7 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC43 j)=psiC43 j := by
  revert j
  decide +kernel
lemma psiC43_mem (j : Fin 31) : (psiC43 j).Mem (normJetEnvelope (damping 1) (damping 0) 43 (frequency j)) := by
  rw [← psiC43_calc]
  apply psiBox_mem
  · convert QBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [Q_emod]
    norm_num
  · convert DBox7_mem using 1
    all_goals try with_reducible_and_instances rfl
    rw [D_emod]
    norm_num
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC43_mem j
  · decide +kernel
lemma envelopeExpC45_mem (j : Fin 31) : (envelopeExpC45 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*45)) := by
  rw [← envelopeExpC45_calc]
  have hh := decayExpBox_mem 1 0 45 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC45_pre j)
lemma envelopeExpC25_mem (j : Fin 31) : (envelopeExpC25 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*25)) := by
  rw [← envelopeExpC25_calc]
  have hh := decayExpBox_mem 1 0 25 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC25_pre j)
lemma psiC25_calc (j : Fin 31) : psiBox 1 0 25 j QBox25 DBox25 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC25 j)=psiC25 j := by
  revert j
  decide +kernel
lemma psiC25_mem (j : Fin 31) : (psiC25 j).Mem (normJetEnvelope (damping 1) (damping 0) 25 (frequency j)) := by
  rw [← psiC25_calc]
  apply psiBox_mem
  · exact QBox25_mem
  · exact DBox25_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC25_mem j
  · decide +kernel
lemma envelopeExpC27_mem (j : Fin 31) : (envelopeExpC27 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*27)) := by
  rw [← envelopeExpC27_calc]
  have hh := decayExpBox_mem 1 0 27 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC27_pre j)
lemma psiC27_calc (j : Fin 31) : psiBox 1 0 27 j QBox27 DBox27 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC27 j)=psiC27 j := by
  revert j
  decide +kernel
lemma psiC27_mem (j : Fin 31) : (psiC27 j).Mem (normJetEnvelope (damping 1) (damping 0) 27 (frequency j)) := by
  rw [← psiC27_calc]
  apply psiBox_mem
  · exact QBox27_mem
  · exact DBox27_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC27_mem j
  · decide +kernel
lemma envelopeExpC28_mem (j : Fin 31) : (envelopeExpC28 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*28)) := by
  rw [← envelopeExpC28_calc]
  have hh := decayExpBox_mem 1 0 28 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC28_pre j)
lemma psiC28_calc (j : Fin 31) : psiBox 1 0 28 j QBox28 DBox28 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC28 j)=psiC28 j := by
  revert j
  decide +kernel
lemma psiC28_mem (j : Fin 31) : (psiC28 j).Mem (normJetEnvelope (damping 1) (damping 0) 28 (frequency j)) := by
  rw [← psiC28_calc]
  apply psiBox_mem
  · exact QBox28_mem
  · exact DBox28_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC28_mem j
  · decide +kernel
lemma envelopeExpC31_mem (j : Fin 31) : (envelopeExpC31 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*31)) := by
  rw [← envelopeExpC31_calc]
  have hh := decayExpBox_mem 1 0 31 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC31_pre j)
lemma psiC31_calc (j : Fin 31) : psiBox 1 0 31 j QBox31 DBox31 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC31 j)=psiC31 j := by
  revert j
  decide +kernel
lemma psiC31_mem (j : Fin 31) : (psiC31 j).Mem (normJetEnvelope (damping 1) (damping 0) 31 (frequency j)) := by
  rw [← psiC31_calc]
  apply psiBox_mem
  · exact QBox31_mem
  · exact DBox31_mem
  · exact lambdaNorm1_mem j
  · exact phaseNorm10_mem j
  · simpa only [Int.cast_ofNat,Int.cast_one] using envelopeExpC31_mem j
  · decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodExpC_mem (j : Fin 31) : (periodExpC j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*36)) := by
  rw [← periodExpC_calc]
  have hh := decayExpBox_mem 1 0 36 j
  unfold decayExpBox decayBox RI.neg at hh
  rw [envelopePhase10_calc] at hh
  simp only [neg_neg] at hh
  exact hh (periodExpC_pre j)
lemma envelopeSumBoxC_calc (j : Fin 31) : (RI.sum (fun i : Fin 15 => psiTableC i j)).mul ((RI.point 1).sub (periodExpC j)).invPos=envelopeSumBoxC j := by
  revert j
  decide +kernel
def psiTableD : Fin 15 → Fin 31 → RI := ![psiD36,psiD37,psiD39,psiD40,psiD43,psiD45,psiD48,psiD49,psiD52,psiD55,psiD57,psiD25,psiD27,psiD28,psiD31]
end AtomicTriangular.FiniteCertificate
end

end OAI
end


