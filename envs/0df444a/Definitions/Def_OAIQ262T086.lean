-- Prove2me | Definitions.Def_OAIQ262T086
-- name    : OAIQ262T086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:49:35.245066+00:00
-- url     : https://prove2.me/theorems/2fd95bde-0025-4f59-a3d2-5eebc14a9067
-- title:
--   Definitions bundle OAIQ262T086 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 9 definitions and 80 theorems. The definitions and types are `OAI.AtomicTriangular.FiniteCertificate.decayBox`, `OAI.AtomicTriangular.FiniteCertificate.decayExpBox`, `OAI.AtomicTriangular.FiniteCertificate.denBox`, `OAI.AtomicTriangular.FiniteCertificate.lambdaBox`, `OAI.AtomicTriangular.FiniteCertificate.lambdaTable`, `OAI.AtomicTriangular.FiniteCertificate.psiBox`, `OAI.AtomicTriangular.FiniteCertificate.wavePhaseBox`, `OAI.AtomicTriangular.FiniteCertificate.xwaveBox`, `OAI.AtomicTriangular.FiniteCertificate.zetaBox`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveExpData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean), [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Envelope_EnvelopeBoxes`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeBoxes.lean), [`Triangular_Envelope_EnvelopeNorm0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm0.lean), [`Triangular_Envelope_EnvelopeNorm1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm1.lean), [`Triangular_Envelope_EnvelopeNorm2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm2.lean), [`Triangular_Envelope_EnvelopePsiC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeWaves`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeWaves.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007` and `OAIQ262T009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T137`, `OAIQ262T138`, `OAIQ262T139`, `OAIQ262T140`, `OAIQ262T141`, `OAIQ262T142`, `OAIQ262T143`, `OAIQ262T148` and `OAIQ262T149`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T005
import Definitions.Def_OAIQ262T006
import Definitions.Def_OAIQ262T007
import Definitions.Def_OAIQ262T009

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
namespace AtomicTriangular.Construction

theorem dBasis_node (n : Node) : dBasis n n.val = 0 := by
  simp [dBasis, dslope_same, deriv_P_node]

open Polynomial

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

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

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

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
lemma jetBox3_0_calc : waveDerivativeBox 3 0 = jetBox3_0 := by decide +kernel
lemma jetBox3_0_mem : jetBox3_0.Mem (waveDerivative 3 ((0:ℤ):ℂ)) := by
  rw [← jetBox3_0_calc]
  exact waveDerivativeBox_mem 3 0
lemma DBox0_calc : jetBox3_0.re.mul ((RI.point 6).mul QBox0).inv = DBox0 := by decide +kernel
lemma jetBox3_1_mem : jetBox3_1.Mem (waveDerivative 3 ((1:ℤ):ℂ)) := by
  rw [← jetBox3_1_calc]
  exact waveDerivativeBox_mem 3 1
lemma DBox1_calc : jetBox3_1.re.mul ((RI.point 6).mul QBox1).inv = DBox1 := by decide +kernel
lemma jetBox3_3_mem : jetBox3_3.Mem (waveDerivative 3 ((3:ℤ):ℂ)) := by
  rw [← jetBox3_3_calc]
  exact waveDerivativeBox_mem 3 3
lemma DBox3_calc : jetBox3_3.re.mul ((RI.point 6).mul QBox3).inv = DBox3 := by decide +kernel
lemma jetBox3_25_mem : jetBox3_25.Mem (waveDerivative 3 ((25:ℤ):ℂ)) := by
  rw [← jetBox3_25_calc]
  exact waveDerivativeBox_mem 3 25
lemma DBox25_calc : jetBox3_25.re.mul ((RI.point 6).mul QBox25).inv = DBox25 := by decide +kernel
lemma DBox25_mem : DBox25.Mem (D 25) := by
  rw [← DBox25_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_25_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox25_mem
  · left; decide +kernel
lemma jetBox3_27_mem : jetBox3_27.Mem (waveDerivative 3 ((27:ℤ):ℂ)) := by
  rw [← jetBox3_27_calc]
  exact waveDerivativeBox_mem 3 27
lemma DBox27_calc : jetBox3_27.re.mul ((RI.point 6).mul QBox27).inv = DBox27 := by decide +kernel
lemma DBox27_mem : DBox27.Mem (D 27) := by
  rw [← DBox27_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_27_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox27_mem
  · left; decide +kernel
lemma jetBox3_28_mem : jetBox3_28.Mem (waveDerivative 3 ((28:ℤ):ℂ)) := by
  rw [← jetBox3_28_calc]
  exact waveDerivativeBox_mem 3 28
lemma DBox28_calc : jetBox3_28.re.mul ((RI.point 6).mul QBox28).inv = DBox28 := by decide +kernel
lemma DBox28_mem : DBox28.Mem (D 28) := by
  rw [← DBox28_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_28_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox28_mem
  · left; decide +kernel
lemma jetBox3_31_mem : jetBox3_31.Mem (waveDerivative 3 ((31:ℤ):ℂ)) := by
  rw [← jetBox3_31_calc]
  exact waveDerivativeBox_mem 3 31
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
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
lemma dBox3_calc (j : Fin 31) : dCoeffBox phaseBox3 restBox3 j = dBox3 j := by
  revert j
  decide +kernel
lemma dBox4_calc (j : Fin 31) : dCoeffBox phaseBox4 restBox4 j = dBox4 j := by
  revert j
  decide +kernel
lemma dBox7_calc (j : Fin 31) : dCoeffBox phaseBox7 restBox7 j = dBox7 j := by
  revert j
  decide +kernel
lemma dBox9_calc (j : Fin 31) : dCoeffBox phaseBox9 restBox9 j = dBox9 j := by
  revert j
  decide +kernel
lemma dBox21_calc (j : Fin 31) : dCoeffBox phaseBox21 restBox21 j = dBox21 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators FourierTransform

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma bBox_mem : bBox.Mem b := by
  obtain ⟨hl,hu⟩ := Constants.bStar_bracket
  constructor <;> dsimp [RI.Mem, bBox]
  · have hr : (bBox.lo:ℝ)/(scale:ℝ) ≤ Constants.bStar := by norm_num [bBox,scale,Constants.bStar]
    simpa only [b, mul_comm, bBox] using (div_le_iff₀ scale_pos).mp (hr.trans hl.le)
  · have hr : Constants.bStar+Constants.eps ≤ (bBox.hi:ℝ)/(scale:ℝ) := by
      norm_num [bBox,scale,Constants.bStar,Constants.eps]
    simpa only [b,mul_comm,bBox] using (le_div_iff₀ scale_pos).mp (hu.le.trans hr)

lemma dampingBox_mem (q : Fin 2) : (dampingBox q).Mem (damping q) := by
  unfold dampingBox damping h H
  split_ifs
  · simpa using RI.mem_divNat (RI.mem_point 17) (by norm_num : 0<(50:ℕ))
  · simpa using RI.mem_divNat (RI.mem_point 27) (by norm_num : 0<(50:ℕ))
lemma realFrequencyBox_mem (j : Fin 31) : (realFrequencyBox j).Mem (frequency j) := by
  have hh := RI.mem_divNat (RI.mem_point ((j.val:ℤ)-15)) (by norm_num : 0<(18:ℕ))
  simpa only [realFrequencyBox, frequency, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_ofNat] using hh

def denBox (q : Fin 2) (j : Fin 31) : RI :=
  ((dampingBox q).pow 2).add ((realFrequencyBox j).pow 2)
lemma denBox_mem (q : Fin 2) (j : Fin 31) :
    (denBox q j).Mem (waveDen (damping q) (frequency j)) := by
  exact RI.mem_add (RI.mem_pow (dampingBox_mem q) 2) (RI.mem_pow (realFrequencyBox_mem j) 2)
lemma denBox_pos (q : Fin 2) (j : Fin 31) : 0 < (denBox q j).lo := by
  revert q j
  decide +kernel
lemma bdenBox_pos (q : Fin 2) (j : Fin 31) : 0 < (bBox.mul (denBox q j)).lo := by
  revert q j
  decide +kernel

def xwaveBox (q : Fin 2) (j : Fin 31) : RI :=
  ((RI.point 4).divNat 3).mul (denBox q j).invPos
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

def zetaBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.ofReal ((realFrequencyBox j).mul (xwaveBox q j)).neg).add
    (CI.imag.mul (CI.ofReal (((dampingBox q).mul (xwaveBox q j)).sub (dampingBox v))))
lemma zetaBox_mem (q v : Fin 2) (j : Fin 31) :
    (zetaBox q v j).Mem (zeta (damping q) (damping v) (frequency j)) := by
  have hh := CI.mem_add (CI.mem_ofReal (RI.mem_neg
    (RI.mem_mul (realFrequencyBox_mem j) (xwaveBox_mem q j))))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal
      (RI.mem_sub (RI.mem_mul (dampingBox_mem q) (xwaveBox_mem q j)) (dampingBox_mem v))))
  simpa only [zetaBox,zeta,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul] using hh

def wavePhaseBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.imag.mul (CI.ofReal piBox)).mul (zetaBox q v j)
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
-- module Solutions.OAIQ262_TG.Triangular_Certificate_WaveExpData
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
def lambdaTable : Fin 2 → Fin 31 → CI := ![lambdaTable0,lambdaTable1]
lemma lambdaTable_mem (q : Fin 2) (j : Fin 31) : (lambdaTable q j).Mem (lambda (damping q) (frequency j)) := by
  fin_cases q
  · exact lambdaTable0_mem j
  · exact lambdaTable1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

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
lemma columnNorm2_check (j : Fin 31) : 0≤(columnNorm2 j).lo ∧ (columnNorm2 j).lo*(columnNorm2 j).lo ≤ scale*max 0 (columnTable 2 j).normSq.lo ∧ scale*(columnTable 2 j).normSq.hi ≤ (columnNorm2 j).hi*(columnNorm2 j).hi ∧ 0≤(columnNorm2 j).hi := by
  revert j
  decide +kernel
lemma columnNorm3_check (j : Fin 31) : 0≤(columnNorm3 j).lo ∧ (columnNorm3 j).lo*(columnNorm3 j).lo ≤ scale*max 0 (columnTable 3 j).normSq.lo ∧ scale*(columnTable 3 j).normSq.hi ≤ (columnNorm3 j).hi*(columnNorm3 j).hi ∧ 0≤(columnNorm3 j).hi := by
  revert j
  decide +kernel
lemma columnNorm4_check (j : Fin 31) : 0≤(columnNorm4 j).lo ∧ (columnNorm4 j).lo*(columnNorm4 j).lo ≤ scale*max 0 (columnTable 4 j).normSq.lo ∧ scale*(columnTable 4 j).normSq.hi ≤ (columnNorm4 j).hi*(columnNorm4 j).hi ∧ 0≤(columnNorm4 j).hi := by
  revert j
  decide +kernel
lemma columnNorm5_check (j : Fin 31) : 0≤(columnNorm5 j).lo ∧ (columnNorm5 j).lo*(columnNorm5 j).lo ≤ scale*max 0 (columnTable 5 j).normSq.lo ∧ scale*(columnTable 5 j).normSq.hi ≤ (columnNorm5 j).hi*(columnNorm5 j).hi ∧ 0≤(columnNorm5 j).hi := by
  revert j
  decide +kernel
lemma columnNorm6_check (j : Fin 31) : 0≤(columnNorm6 j).lo ∧ (columnNorm6 j).lo*(columnNorm6 j).lo ≤ scale*max 0 (columnTable 6 j).normSq.lo ∧ scale*(columnTable 6 j).normSq.hi ≤ (columnNorm6 j).hi*(columnNorm6 j).hi ∧ 0≤(columnNorm6 j).hi := by
  revert j
  decide +kernel
lemma columnNorm7_check (j : Fin 31) : 0≤(columnNorm7 j).lo ∧ (columnNorm7 j).lo*(columnNorm7 j).lo ≤ scale*max 0 (columnTable 7 j).normSq.lo ∧ scale*(columnTable 7 j).normSq.hi ≤ (columnNorm7 j).hi*(columnNorm7 j).hi ∧ 0≤(columnNorm7 j).hi := by
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
lemma columnNorm8_check (j : Fin 31) : 0≤(columnNorm8 j).lo ∧ (columnNorm8 j).lo*(columnNorm8 j).lo ≤ scale*max 0 (columnTable 8 j).normSq.lo ∧ scale*(columnTable 8 j).normSq.hi ≤ (columnNorm8 j).hi*(columnNorm8 j).hi ∧ 0≤(columnNorm8 j).hi := by
  revert j
  decide +kernel
lemma columnNorm9_check (j : Fin 31) : 0≤(columnNorm9 j).lo ∧ (columnNorm9 j).lo*(columnNorm9 j).lo ≤ scale*max 0 (columnTable 9 j).normSq.lo ∧ scale*(columnTable 9 j).normSq.hi ≤ (columnNorm9 j).hi*(columnNorm9 j).hi ∧ 0≤(columnNorm9 j).hi := by
  revert j
  decide +kernel
lemma columnNorm12_check (j : Fin 31) : 0≤(columnNorm12 j).lo ∧ (columnNorm12 j).lo*(columnNorm12 j).lo ≤ scale*max 0 (columnTable 12 j).normSq.lo ∧ scale*(columnTable 12 j).normSq.hi ≤ (columnNorm12 j).hi*(columnNorm12 j).hi ∧ 0≤(columnNorm12 j).hi := by
  revert j
  decide +kernel
lemma columnNorm13_check (j : Fin 31) : 0≤(columnNorm13 j).lo ∧ (columnNorm13 j).lo*(columnNorm13 j).lo ≤ scale*max 0 (columnTable 13 j).normSq.lo ∧ scale*(columnTable 13 j).normSq.hi ≤ (columnNorm13 j).hi*(columnNorm13 j).hi ∧ 0≤(columnNorm13 j).hi := by
  revert j
  decide +kernel
lemma columnNorm14_check (j : Fin 31) : 0≤(columnNorm14 j).lo ∧ (columnNorm14 j).lo*(columnNorm14 j).lo ≤ scale*max 0 (columnTable 14 j).normSq.lo ∧ scale*(columnTable 14 j).normSq.hi ≤ (columnNorm14 j).hi*(columnNorm14 j).hi ∧ 0≤(columnNorm14 j).hi := by
  revert j
  decide +kernel
lemma columnNorm15_check (j : Fin 31) : 0≤(columnNorm15 j).lo ∧ (columnNorm15 j).lo*(columnNorm15 j).lo ≤ scale*max 0 (columnTable 15 j).normSq.lo ∧ scale*(columnTable 15 j).normSq.hi ≤ (columnNorm15 j).hi*(columnNorm15 j).hi ∧ 0≤(columnNorm15 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm16_check (j : Fin 31) : 0≤(columnNorm16 j).lo ∧ (columnNorm16 j).lo*(columnNorm16 j).lo ≤ scale*max 0 (columnTable 16 j).normSq.lo ∧ scale*(columnTable 16 j).normSq.hi ≤ (columnNorm16 j).hi*(columnNorm16 j).hi ∧ 0≤(columnNorm16 j).hi := by
  revert j
  decide +kernel
lemma columnNorm17_check (j : Fin 31) : 0≤(columnNorm17 j).lo ∧ (columnNorm17 j).lo*(columnNorm17 j).lo ≤ scale*max 0 (columnTable 17 j).normSq.lo ∧ scale*(columnTable 17 j).normSq.hi ≤ (columnNorm17 j).hi*(columnNorm17 j).hi ∧ 0≤(columnNorm17 j).hi := by
  revert j
  decide +kernel
lemma columnNorm18_check (j : Fin 31) : 0≤(columnNorm18 j).lo ∧ (columnNorm18 j).lo*(columnNorm18 j).lo ≤ scale*max 0 (columnTable 18 j).normSq.lo ∧ scale*(columnTable 18 j).normSq.hi ≤ (columnNorm18 j).hi*(columnNorm18 j).hi ∧ 0≤(columnNorm18 j).hi := by
  revert j
  decide +kernel
lemma columnNorm19_check (j : Fin 31) : 0≤(columnNorm19 j).lo ∧ (columnNorm19 j).lo*(columnNorm19 j).lo ≤ scale*max 0 (columnTable 19 j).normSq.lo ∧ scale*(columnTable 19 j).normSq.hi ≤ (columnNorm19 j).hi*(columnNorm19 j).hi ∧ 0≤(columnNorm19 j).hi := by
  revert j
  decide +kernel
lemma columnNorm20_check (j : Fin 31) : 0≤(columnNorm20 j).lo ∧ (columnNorm20 j).lo*(columnNorm20 j).lo ≤ scale*max 0 (columnTable 20 j).normSq.lo ∧ scale*(columnTable 20 j).normSq.hi ≤ (columnNorm20 j).hi*(columnNorm20 j).hi ∧ 0≤(columnNorm20 j).hi := by
  revert j
  decide +kernel
lemma columnNorm21_check (j : Fin 31) : 0≤(columnNorm21 j).lo ∧ (columnNorm21 j).lo*(columnNorm21 j).lo ≤ scale*max 0 (columnTable 21 j).normSq.lo ∧ scale*(columnTable 21 j).normSq.hi ≤ (columnNorm21 j).hi*(columnNorm21 j).hi ∧ 0≤(columnNorm21 j).hi := by
  revert j
  decide +kernel
lemma columnNorm22_check (j : Fin 31) : 0≤(columnNorm22 j).lo ∧ (columnNorm22 j).lo*(columnNorm22 j).lo ≤ scale*max 0 (columnTable 22 j).normSq.lo ∧ scale*(columnTable 22 j).normSq.hi ≤ (columnNorm22 j).hi*(columnNorm22 j).hi ∧ 0≤(columnNorm22 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaNorm1_check (j : Fin 31) : 0≤(lambdaNorm1 j).lo ∧ (lambdaNorm1 j).lo*(lambdaNorm1 j).lo ≤ scale*max 0 (lambdaTable 1 j).normSq.lo ∧ scale*(lambdaTable 1 j).normSq.hi ≤ (lambdaNorm1 j).hi*(lambdaNorm1 j).hi ∧ 0≤(lambdaNorm1 j).hi := by
  revert j
  decide +kernel
lemma envelopePhase10_calc (j : Fin 31) : wavePhaseBox 1 0 j=envelopePhase10 j := by
  revert j
  decide +kernel
lemma envelopePhase10_mem (j : Fin 31) : (envelopePhase10 j).Mem (I*Real.pi*zeta (damping 1) (damping 0) (frequency j)) := by
  rw [← envelopePhase10_calc]
  exact wavePhaseBox_mem 1 0 j
lemma phaseNorm10_check (j : Fin 31) : 0≤(phaseNorm10 j).lo ∧ (phaseNorm10 j).lo*(phaseNorm10 j).lo ≤ scale*max 0 (envelopePhase10 j).normSq.lo ∧ scale*(envelopePhase10 j).normSq.hi ≤ (phaseNorm10 j).hi*(phaseNorm10 j).hi ∧ 0≤(phaseNorm10 j).hi := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopePsiC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopeExpC25_calc (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 25))).exp.re=envelopeExpC25 j := by
  revert j
  decide +kernel
lemma envelopeExpC25_pre (j : Fin 31) : (CI.ofReal (((envelopePhase10 j).re.neg).neg.mul (RI.point 25))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma envelopeExpC25_mem (j : Fin 31) : (envelopeExpC25 j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*25)) := by
  rw [← envelopeExpC25_calc]
  have hh := decayExpBox_mem 1 0 25 j
  unfold decayExpBox decayBox at hh
  rw [envelopePhase10_calc] at hh
  simpa only [Int.cast_ofNat,Int.cast_one] using hh (envelopeExpC25_pre j)
lemma psiC25_calc (j : Fin 31) : psiBox 1 0 25 j QBox25 DBox25 (lambdaNorm1 j) (phaseNorm10 j) (envelopeExpC25 j)=psiC25 j := by
  revert j
  decide +kernel
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
lemma periodExpC_calc (j : Fin 31) : (CI.ofReal ((envelopePhase10 j).re.mul (RI.point 36))).exp.re=periodExpC j := by
  revert j
  decide +kernel
lemma periodExpC_pre (j : Fin 31) : (CI.ofReal ((envelopePhase10 j).re.mul (RI.point 36))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
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
end AtomicTriangular.FiniteCertificate
end

end OAI
end


