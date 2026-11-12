-- Prove2me | Definitions.Def_OAIQ262T005
-- name    : OAIQ262T005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:42:34.624206+00:00
-- url     : https://prove2.me/theorems/e3664e5f-72a0-4756-8c07-ca7dcf340932
-- title:
--   Definitions bundle OAIQ262T005 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 297 declarations of OpenAI's Lean: 60 definitions and 237 theorems. The definitions and types are `OAI.AtomicTriangular.Construction.tailFiniteEnvelope`, `OAI.AtomicTriangular.FiniteCertificate.QBox1`, `OAI.AtomicTriangular.FiniteCertificate.QBox12`, `OAI.AtomicTriangular.FiniteCertificate.QBox13`, `OAI.AtomicTriangular.FiniteCertificate.QBox16`, `OAI.AtomicTriangular.FiniteCertificate.QBox19`, `OAI.AtomicTriangular.FiniteCertificate.QBox21`, `OAI.AtomicTriangular.FiniteCertificate.QBox25`, `OAI.AtomicTriangular.FiniteCertificate.QBox27`, `OAI.AtomicTriangular.FiniteCertificate.QBox28`, `OAI.AtomicTriangular.FiniteCertificate.QBox3`, `OAI.AtomicTriangular.FiniteCertificate.QBox31`, `OAI.AtomicTriangular.FiniteCertificate.QBox4`, `OAI.AtomicTriangular.FiniteCertificate.QBox7`, `OAI.AtomicTriangular.FiniteCertificate.QBox9`, `OAI.AtomicTriangular.FiniteCertificate.boundC`, `OAI.AtomicTriangular.FiniteCertificate.cCoeffBox`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox1`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox2`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox3`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox4`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox5`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox6`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox7`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox8`, `OAI.AtomicTriangular.FiniteCertificate.columnNorm0`, `OAI.AtomicTriangular.FiniteCertificate.columnNorm1`, `OAI.AtomicTriangular.FiniteCertificate.columnNorm10`, `OAI.AtomicTriangular.FiniteCertificate.columnNorm11`, `OAI.AtomicTriangular.FiniteCertificate.columnNorm12`, `OAI.AtomicTriangular.FiniteCertificate.dCoeffBox`, `OAI.AtomicTriangular.FiniteCertificate.dampingBox`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_1`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_12`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_13`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_16`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_19`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_21`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_25`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_27` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Certificate_WaveIntervals`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveIntervals.lean), [`Triangular_Construction_PeriodicJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/PeriodicJets.lean), [`Triangular_Construction_TailEnumeration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/TailEnumeration.lean), [`Triangular_Envelope_EnvelopeNorm0`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm0.lean), [`Triangular_Envelope_EnvelopeNorm1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeNorm1.lean), [`Triangular_Envelope_EnvelopeSums`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean), [`Triangular_Envelope_EnvelopeSumsBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSumsBase.lean), [`Triangular_Envelope_JetEnvelopeAnalytic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/JetEnvelopeAnalytic.lean), [`Triangular_Envelope_KernelBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean), [`Triangular_Envelope_TailEnvelopeSeries`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/TailEnvelopeSeries.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`; the bundles `OAIQ262T000` and `OAIQ262T001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T085`, `OAIQ262T086`, `OAIQ262T087`, `OAIQ262T088`, `OAIQ262T089`, `OAIQ262T090`, `OAIQ262T091`, `OAIQ262T092`, `OAIQ262T093`, `OAIQ262T094`, `OAIQ262T095`, `OAIQ262T096`, `OAIQ262T097`, `OAIQ262T098`, `OAIQ262T099`, `OAIQ262T100`, `OAIQ262T101`, `OAIQ262T102`, `OAIQ262T103`, `OAIQ262T104`, `OAIQ262T105`, `OAIQ262T106`, `OAIQ262T107`, `OAIQ262T108`, `OAIQ262T109`, `OAIQ262T110`, `OAIQ262T111`, `OAIQ262T112`, `OAIQ262T113`, `OAIQ262T114`, `OAIQ262T115`, `OAIQ262T116`, `OAIQ262T134`, `OAIQ262T135` and `OAIQ262T136`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T000
import Definitions.Def_OAIQ262T001

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
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma phase_int_mod (n : ℤ) : phase (n:ℂ) = phase ((n%36:ℤ):ℂ) := by
  have hn : (n:ℂ) = ((n%36:ℤ):ℂ) + 36*((n/36:ℤ):ℂ) := by
    have h := congrArg (fun x : ℤ => (x:ℂ)) (Int.emod_add_mul_ediv n 36)
    push_cast at h
    exact h.symm
  rw [hn, phase_add]
  have hp : phase (36*((n/36:ℤ):ℂ)) = 1 := by
    unfold phase
    convert Complex.exp_int_mul_two_pi_mul_I (n/36) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  rw [hp, mul_one]

end AtomicTriangular.Construction

namespace AtomicTriangular.Interval

lemma scale_pos : (0:ℝ) < (scale:ℤ) := by norm_num [scale]
lemma scale_int_pos : 0 < scale := by norm_num [scale]

def RI.Mem (a : RI) (x : ℝ) : Prop := (a.lo:ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ a.hi

def RI.widen (a : RI) (r : ℤ) : RI := ⟨a.lo-r,a.hi+r⟩

lemma RI.mem_point (n : ℤ) : (RI.point n).Mem (n:ℝ) := by
  simp [RI.Mem,RI.point]

lemma RI.mem_add {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add b).Mem (x+y) := by
  rcases hx with ⟨hx₀,hx₁⟩; rcases hy with ⟨hy₀,hy₁⟩
  constructor <;> simp only [RI.add,Int.cast_add] <;> nlinarith

lemma RI.mem_neg {a : RI} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  rcases hx with ⟨hx₀,hx₁⟩
  constructor <;> simp only [RI.neg,Int.cast_neg] <;> nlinarith

lemma RI.mem_sub {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub b).Mem (x-y) := by simpa [RI.sub,sub_eq_add_neg] using RI.mem_add hx (RI.mem_neg hy)

lemma RI.mem_mul {a b : RI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x*y) := by
  have hh := four_bounds hx hy
  have hl := (div_floor_bounds (imin4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) scale scale_int_pos).1
  have hu := (div_floor_bounds (imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) scale scale_int_pos).2
  simp only [imin4,imax4,Int.cast_min,Int.cast_max,Int.cast_mul] at hl hu
  constructor
  · apply (mul_le_mul_iff_right₀ scale_pos).mp
    dsimp only [RI.mul,imin4,imax4]
    nlinarith [hh.1]
  · apply (mul_le_mul_iff_right₀ scale_pos).mp
    dsimp only [RI.mul,imin4,imax4]
    nlinarith [hh.2]

lemma RI.mem_divNat {a : RI} {x : ℝ} (hx : a.Mem x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem (x/n) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hnl : (0:ℤ) < n := by exact_mod_cast hn
  have hl := (div_floor_bounds a.lo n hnl).1
  have hu := (div_floor_bounds a.hi n hnl).2
  constructor
  · simpa only [RI.divNat,mul_div_assoc,Int.cast_natCast] using
      (le_div_iff₀ hn').mpr (hl.trans hx.1)
  · change (scale:ℝ)*(x/(n:ℝ)) ≤ ((a.hi/(n:ℤ)+1:ℤ):ℝ)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hn').mpr (hx.2.trans hu)

lemma RI.mem_widen {a : RI} {x y : ℝ} {r : ℤ} (hx : a.Mem x)
    (hxy : |y-x| ≤ (r:ℝ)/(scale:ℝ)) : (a.widen r).Mem y := by
  have hh := abs_le.mp hxy
  have hl := (div_le_iff₀ scale_pos).mp (show -(r:ℝ)/(scale:ℝ) ≤ y-x by simpa only [neg_div] using hh.1)
  have hu := (le_div_iff₀ scale_pos).mp hh.2
  rcases hx with ⟨hx₀,hx₁⟩
  constructor <;> simp only [RI.widen,Int.cast_sub,Int.cast_add] <;> nlinarith

def RI.invPos (a : RI) : RI := ⟨scale^2/a.hi,scale^2/a.lo+1⟩

def CI.Mem (a : CI) (z : ℂ) : Prop := a.re.Mem z.re ∧ a.im.Mem z.im

def CI.widen (a : CI) (r : ℤ) : CI := ⟨a.re.widen r,a.im.widen r⟩
def CI.normSq (a : CI) : RI := (a.re.mul a.re).add (a.im.mul a.im)

lemma CI.mem_ofReal {a : RI} {x : ℝ} (h : a.Mem x) : (CI.ofReal a).Mem (x:ℂ) := by
  exact ⟨h,by simpa [CI.ofReal] using RI.mem_point 0⟩
lemma CI.mem_point (n : ℤ) : (CI.point n).Mem (n:ℂ) := by
  exact CI.mem_ofReal (RI.mem_point n)
lemma CI.mem_imag : CI.imag.Mem Complex.I := by
  exact ⟨by simpa [CI.imag] using RI.mem_point 0,by simpa [CI.imag] using RI.mem_point 1⟩
lemma CI.mem_add {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add b).Mem (x+y) := by exact ⟨RI.mem_add hx.1 hy.1,RI.mem_add hx.2 hy.2⟩
lemma CI.mem_neg {a : CI} {x : ℂ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  exact ⟨RI.mem_neg hx.1,RI.mem_neg hx.2⟩
lemma CI.mem_sub {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub b).Mem (x-y) := by simpa [sub_eq_add_neg,CI.sub] using CI.mem_add hx (CI.mem_neg hy)
lemma CI.mem_mul {a b : CI} {x y : ℂ} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul b).Mem (x*y) := by
  exact ⟨RI.mem_sub (RI.mem_mul hx.1 hy.1) (RI.mem_mul hx.2 hy.2),
    RI.mem_add (RI.mem_mul hx.1 hy.2) (RI.mem_mul hx.2 hy.1)⟩
lemma CI.mem_divNat {a : CI} {x : ℂ} (hx : a.Mem x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem (x/n) := by
  simpa only [CI.Mem,CI.divNat,Complex.div_natCast_re,Complex.div_natCast_im] using
    And.intro (RI.mem_divNat hx.1 hn) (RI.mem_divNat hx.2 hn)
lemma CI.mem_conj {a : CI} {x : ℂ} (hx : a.Mem x) : a.conj.Mem (starRingEnd ℂ x) := by
  exact ⟨hx.1,RI.mem_neg hx.2⟩
lemma CI.mem_normSq {a : CI} {x : ℂ} (hx : a.Mem x) : a.normSq.Mem (Complex.normSq x) := by
  exact RI.mem_add (RI.mem_mul hx.1 hx.1) (RI.mem_mul hx.2 hx.2)
lemma CI.mem_pow {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [CI.pow] using CI.mem_point 1
  | succ n ih => simpa [CI.pow,pow_succ] using CI.mem_mul ih hx

noncomputable section
open scoped BigOperators

lemma CI.mem_widen {a : CI} {x y : ℂ} {r : ℤ} (hx : a.Mem x)
    (hxy : ‖y-x‖ ≤ (r:ℝ)/(scale:ℝ)) : (a.widen r).Mem y := by
  constructor
  · apply RI.mem_widen hx.1
    exact (Complex.abs_re_le_norm (y-x)).trans hxy
  · apply RI.mem_widen hx.2
    exact (Complex.abs_im_le_norm (y-x)).trans hxy

def CI.taylor (a : CI) : ℕ → CI × CI
  | 0 => (CI.point 1, CI.point 1)
  | n+1 =>
    let previous := a.taylor n
    let term := (previous.1.mul a).divNat (n+1)
    (term, previous.2.add term)

lemma CI.mem_taylor {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) :
    (a.taylor n).1.Mem (x^n/(n.factorial : ℂ)) ∧
    (a.taylor n).2.Mem (∑ j ∈ Finset.range (n+1), x^j/(j.factorial : ℂ)) := by
  induction n with
  | zero => simpa [CI.taylor] using And.intro (CI.mem_point 1) (CI.mem_point 1)
  | succ n ih =>
    have hf : x^(n+1)/((n+1).factorial : ℂ) = (x^n/(n.factorial : ℂ))*x/((n+1:ℕ):ℂ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp
    constructor
    · rw [hf]
      exact CI.mem_divNat (CI.mem_mul ih.1 hx) (Nat.succ_pos n)
    · rw [Finset.sum_range_succ, hf]
      exact CI.mem_add ih.2 (CI.mem_divNat (CI.mem_mul ih.1 hx) (Nat.succ_pos n))

lemma small_taylor_error {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.exp x - ∑ j ∈ Finset.range 61, x^j/(j.factorial : ℂ)‖ ≤
      (1:ℝ)/(scale:ℝ) := by
  have hh := Complex.exp_bound' (n := 61) (x := x) (by norm_num; linarith : ‖x‖ / 62 ≤ 1/2)
  calc
    _ ≤ ‖x‖^61/(Nat.factorial 61 : ℝ)*2 := hh
    _ ≤ (1:ℝ)^61/(Nat.factorial 61 : ℝ)*2 := by gcongr
    _ ≤ _ := by norm_num [scale]

def CI.square (a : CI) : ℕ → CI
  | 0 => a
  | n+1 => (a.square n).mul (a.square n)

lemma CI.mem_square {a : CI} {x : ℂ} (hx : a.Mem x) (n : ℕ) :
    (a.square n).Mem (x^(2^n)) := by
  induction n with
  | zero => simpa [CI.square] using hx
  | succ n ih =>
    rw [CI.square, show 2^(n+1) = 2^n*2 by rw [pow_succ], pow_mul, pow_two]
    exact CI.mem_mul ih ih

def CI.exp (a : CI) : CI :=
  (((a.divNat 1024).taylor 60).2.widen 1).square 10

lemma CI.mem_exp {a : CI} {x : ℂ} (hx : a.Mem x) (hn : ‖x/1024‖ ≤ 1) :
    a.exp.Mem (Complex.exp x) := by
  have hs := CI.mem_taylor (CI.mem_divNat hx (by norm_num : 0 < (1024:ℕ))) 60
  have he := CI.mem_widen (r := 1) hs.2 (by simpa only [Int.cast_one, Nat.cast_ofNat] using small_taylor_error hn)
  have hh := CI.mem_square he 10
  have hpow : Complex.exp (x/1024) ^ (2^10) = Complex.exp x := by
    rw [← Complex.exp_nat_mul]
    norm_num
    congr 1
    ring
  simpa only [hpow, CI.exp] using hh

lemma CI.norm_le_of_mem {a : CI} {x : ℂ} (hx : a.Mem x)
    (ha : a.normSq.hi ≤ scale * 1024^2) : ‖x / 1024‖ ≤ 1 := by
  have hh := (CI.mem_normSq hx).2
  have hu : (a.normSq.hi : ℝ) ≤ (scale : ℝ) * 1024^2 := by exact_mod_cast ha
  rw [Complex.normSq_eq_norm_sq] at hh
  have hn : ‖x‖ ≤ 1024 := by
    have hns : ‖x‖^2 ≤ 1024^2 := by nlinarith [scale_pos]
    nlinarith [norm_nonneg x]
  simpa using (div_le_one (by norm_num : (0:ℝ) < 1024)).mpr hn

lemma CI.mem_exp_checked {a : CI} {x : ℂ} (hx : a.Mem x)
    (ha : a.normSq.hi ≤ scale * 1024^2) : a.exp.Mem (Complex.exp x) :=
  CI.mem_exp hx (CI.norm_le_of_mem hx ha)

def RI.inv (a : RI) : RI := if a.hi < 0 then a.neg.invPos.neg else a.invPos

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval

lemma RI.mem_sum {ι : Type*} [Fintype ι] {v : ι → RI} {x : ι → ℝ}
    (hv : ∀ i, (v i).Mem (x i)) : (RI.sum v).Mem (∑ i, x i) := by
  constructor
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).1
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2

lemma CI.mem_sum {ι : Type*} [Fintype ι] {v : ι → CI} {x : ι → ℂ}
    (hv : ∀ i, (v i).Mem (x i)) : (CI.sum v).Mem (∑ i, x i) := by
  constructor
  · simp only [Complex.re_sum]
    exact RI.mem_sum fun i => (hv i).1
  · simp only [Complex.im_sum]
    exact RI.mem_sum fun i => (hv i).2

end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial

lemma piBox_mem : piBox.Mem Real.pi := by
  obtain ⟨hl,hu⟩ := Constants.pStar_bracket
  constructor <;> dsimp [RI.Mem, piBox]
  · have hstar : (piBox.lo:ℝ) / (scale:ℝ) ≤ Constants.pStar := by
      norm_num [piBox,scale,Constants.pStar]
    have hpi := hstar.trans hl.le
    simpa only [mul_comm, piBox] using (div_le_iff₀ scale_pos).mp hpi
  · have hstar : Constants.pStar + Constants.eps ≤ (piBox.hi:ℝ) / (scale:ℝ) := by
      norm_num [piBox,scale,Constants.pStar,Constants.eps]
    have hpi := hu.le.trans hstar
    simpa only [mul_comm, piBox] using (le_div_iff₀ scale_pos).mp hpi

lemma phase_conj (s : ℝ) : starRingEnd ℂ (phase (s:ℂ)) = phase (-(s:ℂ)) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma partialPolynomial_zero : partialPolynomial 0 = 1 := by simp [partialPolynomial]
lemma partialPolynomial_fifteen : partialPolynomial 15 = atomPolynomial := by simp [partialPolynomial, atomPolynomial]
lemma partialPolynomial_succ {n : ℕ} (hn : n < 15) :
    partialPolynomial (n+1) = atomFactor ⟨n,hn⟩ * partialPolynomial n := by
  have he : Finset.univ.filter (fun a : Fin 15 => a.val < n+1) =
      insert ⟨n,hn⟩ (Finset.univ.filter (fun a : Fin 15 => a.val < n)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    simp only [Fin.ext_iff]
    omega
  rw [partialPolynomial, he, Finset.prod_insert]
  · rfl
  · simp

lemma coeff_atom_mul (a : Fin 15) (p : Polynomial ℂ) (n : ℕ) :
    (atomFactor a*p).coeff n =
      -(phase (residue a))*p.coeff n +
        (if n=0 then 0 else 2*p.coeff (n-1)) -
        (if n<2 then 0 else phase (-(residue a : ℂ))*p.coeff (n-2)) := by
  unfold atomFactor
  rw [sub_mul, add_mul, neg_mul, mul_assoc, mul_assoc, coeff_sub, coeff_add,
    coeff_neg, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_X_mul', coeff_X_sq_mul]
  split_ifs <;> ring

lemma coeffStep_mem (a : Fin 15) (p : Polynomial ℂ) (e : CI)
    (v : Fin 31 → CI) (he : e.Mem (phase (residue a)))
    (hv : ∀ j : Fin 31, (v j).Mem (p.coeff j.val)) (j : Fin 31) :
    (coeffStep e v j).Mem ((atomFactor a*p).coeff j.val) := by
  rw [coeff_atom_mul]
  apply CI.mem_sub
  · apply CI.mem_add
    · exact CI.mem_mul (CI.mem_neg he) (hv j)
    · split_ifs with hn
      · simpa using CI.mem_point 0
      · exact CI.mem_mul (CI.mem_point 2) (hv ⟨j.val-1,by omega⟩)
  · split_ifs with hn
    · simpa using CI.mem_point 0
    · have he' : e.conj.Mem (phase (-(residue a : ℂ))) := by
        have hh := CI.mem_conj he
        simpa only [← Complex.ofReal_intCast, phase_conj] using hh
      exact CI.mem_mul he' (hv ⟨j.val-2,by omega⟩)

def phaseInputBox (n : ℤ) : CI :=
  (CI.imag.mul (CI.ofReal (piBox.mul (RI.point n)))).divNat 18

lemma phaseInputBox_mem (n : ℤ) :
    (phaseInputBox n).Mem ((Real.pi : ℂ) * Complex.I * (n:ℂ) / 18) := by
  have hp := CI.mem_mul CI.mem_imag (CI.mem_ofReal (RI.mem_mul piBox_mem (RI.mem_point n)))
  have hh := CI.mem_divNat hp (by norm_num : 0 < (18:ℕ))
  change ((CI.imag.mul (CI.ofReal (piBox.mul (RI.point n)))).divNat 18).Mem _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial
lemma phaseBox0_calc : (phaseInputBox 0).exp = phaseBox0 := by decide +kernel
lemma phaseBox0_mem : phaseBox0.Mem (phase ((0:ℤ):ℂ)) := by
  rw [← phaseBox0_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 0) (by decide +kernel)
lemma phaseBox1_calc : (phaseInputBox 1).exp = phaseBox1 := by decide +kernel
lemma phaseBox1_mem : phaseBox1.Mem (phase ((1:ℤ):ℂ)) := by
  rw [← phaseBox1_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 1) (by decide +kernel)
lemma phaseBox2_calc : (phaseInputBox 2).exp = phaseBox2 := by decide +kernel
lemma phaseBox2_mem : phaseBox2.Mem (phase ((2:ℤ):ℂ)) := by
  rw [← phaseBox2_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 2) (by decide +kernel)
lemma phaseBox3_calc : (phaseInputBox 3).exp = phaseBox3 := by decide +kernel
lemma phaseBox3_mem : phaseBox3.Mem (phase ((3:ℤ):ℂ)) := by
  rw [← phaseBox3_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 3) (by decide +kernel)
lemma phaseBox4_calc : (phaseInputBox 4).exp = phaseBox4 := by decide +kernel
lemma phaseBox4_mem : phaseBox4.Mem (phase ((4:ℤ):ℂ)) := by
  rw [← phaseBox4_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 4) (by decide +kernel)
lemma phaseBox5_calc : (phaseInputBox 5).exp = phaseBox5 := by decide +kernel
lemma phaseBox5_mem : phaseBox5.Mem (phase ((5:ℤ):ℂ)) := by
  rw [← phaseBox5_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 5) (by decide +kernel)
lemma phaseBox6_calc : (phaseInputBox 6).exp = phaseBox6 := by decide +kernel
lemma phaseBox6_mem : phaseBox6.Mem (phase ((6:ℤ):ℂ)) := by
  rw [← phaseBox6_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 6) (by decide +kernel)
lemma phaseBox7_calc : (phaseInputBox 7).exp = phaseBox7 := by decide +kernel
lemma phaseBox7_mem : phaseBox7.Mem (phase ((7:ℤ):ℂ)) := by
  rw [← phaseBox7_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 7) (by decide +kernel)
lemma phaseBox8_calc : (phaseInputBox 8).exp = phaseBox8 := by decide +kernel
lemma phaseBox8_mem : phaseBox8.Mem (phase ((8:ℤ):ℂ)) := by
  rw [← phaseBox8_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 8) (by decide +kernel)
lemma phaseBox9_calc : (phaseInputBox 9).exp = phaseBox9 := by decide +kernel
lemma phaseBox9_mem : phaseBox9.Mem (phase ((9:ℤ):ℂ)) := by
  rw [← phaseBox9_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 9) (by decide +kernel)
lemma phaseBox10_calc : (phaseInputBox 10).exp = phaseBox10 := by decide +kernel
lemma phaseBox10_mem : phaseBox10.Mem (phase ((10:ℤ):ℂ)) := by
  rw [← phaseBox10_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 10) (by decide +kernel)
lemma phaseBox11_calc : (phaseInputBox 11).exp = phaseBox11 := by decide +kernel
lemma phaseBox11_mem : phaseBox11.Mem (phase ((11:ℤ):ℂ)) := by
  rw [← phaseBox11_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 11) (by decide +kernel)
lemma phaseBox12_calc : (phaseInputBox 12).exp = phaseBox12 := by decide +kernel
lemma phaseBox12_mem : phaseBox12.Mem (phase ((12:ℤ):ℂ)) := by
  rw [← phaseBox12_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 12) (by decide +kernel)
lemma phaseBox13_calc : (phaseInputBox 13).exp = phaseBox13 := by decide +kernel
lemma phaseBox13_mem : phaseBox13.Mem (phase ((13:ℤ):ℂ)) := by
  rw [← phaseBox13_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 13) (by decide +kernel)
lemma phaseBox14_calc : (phaseInputBox 14).exp = phaseBox14 := by decide +kernel
lemma phaseBox14_mem : phaseBox14.Mem (phase ((14:ℤ):ℂ)) := by
  rw [← phaseBox14_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 14) (by decide +kernel)
lemma phaseBox15_calc : (phaseInputBox 15).exp = phaseBox15 := by decide +kernel
lemma phaseBox15_mem : phaseBox15.Mem (phase ((15:ℤ):ℂ)) := by
  rw [← phaseBox15_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 15) (by decide +kernel)
lemma phaseBox16_calc : (phaseInputBox 16).exp = phaseBox16 := by decide +kernel
lemma phaseBox16_mem : phaseBox16.Mem (phase ((16:ℤ):ℂ)) := by
  rw [← phaseBox16_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 16) (by decide +kernel)
lemma phaseBox17_calc : (phaseInputBox 17).exp = phaseBox17 := by decide +kernel
lemma phaseBox17_mem : phaseBox17.Mem (phase ((17:ℤ):ℂ)) := by
  rw [← phaseBox17_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 17) (by decide +kernel)
lemma phaseBox18_calc : (phaseInputBox 18).exp = phaseBox18 := by decide +kernel
lemma phaseBox18_mem : phaseBox18.Mem (phase ((18:ℤ):ℂ)) := by
  rw [← phaseBox18_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 18) (by decide +kernel)
lemma phaseBox19_calc : (phaseInputBox 19).exp = phaseBox19 := by decide +kernel
lemma phaseBox19_mem : phaseBox19.Mem (phase ((19:ℤ):ℂ)) := by
  rw [← phaseBox19_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 19) (by decide +kernel)
lemma phaseBox20_calc : (phaseInputBox 20).exp = phaseBox20 := by decide +kernel
lemma phaseBox20_mem : phaseBox20.Mem (phase ((20:ℤ):ℂ)) := by
  rw [← phaseBox20_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 20) (by decide +kernel)
lemma phaseBox21_calc : (phaseInputBox 21).exp = phaseBox21 := by decide +kernel
lemma phaseBox21_mem : phaseBox21.Mem (phase ((21:ℤ):ℂ)) := by
  rw [← phaseBox21_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 21) (by decide +kernel)
lemma phaseBox22_calc : (phaseInputBox 22).exp = phaseBox22 := by decide +kernel
lemma phaseBox22_mem : phaseBox22.Mem (phase ((22:ℤ):ℂ)) := by
  rw [← phaseBox22_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 22) (by decide +kernel)
lemma phaseBox23_calc : (phaseInputBox 23).exp = phaseBox23 := by decide +kernel
lemma phaseBox23_mem : phaseBox23.Mem (phase ((23:ℤ):ℂ)) := by
  rw [← phaseBox23_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 23) (by decide +kernel)
lemma phaseBox24_calc : (phaseInputBox 24).exp = phaseBox24 := by decide +kernel
lemma phaseBox24_mem : phaseBox24.Mem (phase ((24:ℤ):ℂ)) := by
  rw [← phaseBox24_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 24) (by decide +kernel)
lemma phaseBox25_calc : (phaseInputBox 25).exp = phaseBox25 := by decide +kernel
lemma phaseBox25_mem : phaseBox25.Mem (phase ((25:ℤ):ℂ)) := by
  rw [← phaseBox25_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 25) (by decide +kernel)
lemma phaseBox26_calc : (phaseInputBox 26).exp = phaseBox26 := by decide +kernel
lemma phaseBox26_mem : phaseBox26.Mem (phase ((26:ℤ):ℂ)) := by
  rw [← phaseBox26_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 26) (by decide +kernel)
lemma phaseBox27_calc : (phaseInputBox 27).exp = phaseBox27 := by decide +kernel
lemma phaseBox27_mem : phaseBox27.Mem (phase ((27:ℤ):ℂ)) := by
  rw [← phaseBox27_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 27) (by decide +kernel)
lemma phaseBox28_calc : (phaseInputBox 28).exp = phaseBox28 := by decide +kernel
lemma phaseBox28_mem : phaseBox28.Mem (phase ((28:ℤ):ℂ)) := by
  rw [← phaseBox28_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 28) (by decide +kernel)
lemma phaseBox29_calc : (phaseInputBox 29).exp = phaseBox29 := by decide +kernel
lemma phaseBox29_mem : phaseBox29.Mem (phase ((29:ℤ):ℂ)) := by
  rw [← phaseBox29_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 29) (by decide +kernel)
lemma phaseBox30_calc : (phaseInputBox 30).exp = phaseBox30 := by decide +kernel
lemma phaseBox30_mem : phaseBox30.Mem (phase ((30:ℤ):ℂ)) := by
  rw [← phaseBox30_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 30) (by decide +kernel)
lemma phaseBox31_calc : (phaseInputBox 31).exp = phaseBox31 := by decide +kernel
lemma phaseBox31_mem : phaseBox31.Mem (phase ((31:ℤ):ℂ)) := by
  rw [← phaseBox31_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 31) (by decide +kernel)
lemma phaseBox32_calc : (phaseInputBox 32).exp = phaseBox32 := by decide +kernel
lemma phaseBox32_mem : phaseBox32.Mem (phase ((32:ℤ):ℂ)) := by
  rw [← phaseBox32_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 32) (by decide +kernel)
lemma phaseBox33_calc : (phaseInputBox 33).exp = phaseBox33 := by decide +kernel
lemma phaseBox33_mem : phaseBox33.Mem (phase ((33:ℤ):ℂ)) := by
  rw [← phaseBox33_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 33) (by decide +kernel)
lemma phaseBox34_calc : (phaseInputBox 34).exp = phaseBox34 := by decide +kernel
lemma phaseBox34_mem : phaseBox34.Mem (phase ((34:ℤ):ℂ)) := by
  rw [← phaseBox34_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 34) (by decide +kernel)
lemma phaseBox35_calc : (phaseInputBox 35).exp = phaseBox35 := by decide +kernel
lemma phaseBox35_mem : phaseBox35.Mem (phase ((35:ℤ):ℂ)) := by
  rw [← phaseBox35_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 35) (by decide +kernel)
lemma coeffBox0_mem (j : Fin 31) : (coeffBox0 j).Mem ((partialPolynomial 0).coeff j.val) := by
  rw [partialPolynomial_zero]
  simp only [coeffBox0, coeff_one]
  split_ifs
  · simpa using CI.mem_point 1
  · simpa using CI.mem_point 0

def coeffBox1 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000000000066559,-999999999999999999999999999999999999999999999999999999935488⟩,⟨-68606,63488⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999999999999999999999998,2000000000000000000000000000000000000000000000000000000000002⟩,⟨0,4⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000000000066561,-999999999999999999999999999999999999999999999999999999935486⟩,⟨-63488,68610⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩,
  ⟨⟨-3,3⟩,⟨-2,4⟩⟩]
lemma coeffBox1_calc (j : Fin 31) : coeffStep phaseBox0 coeffBox0 j = coeffBox1 j := by
  revert j
  decide +kernel
lemma coeffBox1_mem (j : Fin 31) : (coeffBox1 j).Mem ((partialPolynomial 1).coeff j.val) := by
  rw [← coeffBox1_calc, partialPolynomial_succ (by norm_num : 0 < 15)]
  apply coeffStep_mem ⟨0,by norm_num⟩ (partialPolynomial 0) phaseBox0 coeffBox0
  · have hr : residue ⟨0,by norm_num⟩ = (0:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox0_mem
  · exact coeffBox0_mem
def coeffBox2 : Fin 31 → CI :=
  ![⟨⟨984807753012208059366743024589523013670643251719842378184993,984807753012208059366743024589523013670643251719842475238537⟩,⟨173648177666930348851716626769314796000375677184069062988405,173648177666930348851716626769314796000375677184069621659986⟩⟩,
  ⟨⟨-3969615506024416118733486049179046027341286503439684950457050,-3969615506024416118733486049179046027341286503439684756391850⟩,⟨-347296355333860697703433253538629592000751354368139243298945,-347296355333860697703433253538629592000751354368138125997284⟩⟩,
  ⟨⟨5969615506024416118733486049179046027341286503439684756371757,5969615506024416118733486049179046027341286503439684950478860⟩,⟨-558671585,558671592⟩⟩,
  ⟨⟨-3969615506024416118733486049179046027341286503439684950457058,-3969615506024416118733486049179046027341286503439684756391842⟩,⟨347296355333860697703433253538629592000751354368138125997278,347296355333860697703433253538629592000751354368139243298954⟩⟩,
  ⟨⟨984807753012208059366743024589523013670643251719842378184979,984807753012208059366743024589523013670643251719842475238550⟩,⟨-173648177666930348851716626769314796000375677184069621660000,-173648177666930348851716626769314796000375677184069062988392⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩,
  ⟨⟨-15,15⟩,⟨-14,16⟩⟩]
lemma coeffBox2_calc (j : Fin 31) : coeffStep phaseBox1 coeffBox1 j = coeffBox2 j := by
  revert j
  decide +kernel
lemma coeffBox2_mem (j : Fin 31) : (coeffBox2 j).Mem ((partialPolynomial 2).coeff j.val) := by
  rw [← coeffBox2_calc, partialPolynomial_succ (by norm_num : 1 < 15)]
  apply coeffStep_mem ⟨1,by norm_num⟩ (partialPolynomial 1) phaseBox1 coeffBox1
  · have hr : residue ⟨1,by norm_num⟩ = (1:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox1_mem
  · exact coeffBox1_mem
def coeffBox3 : Fin 31 → CI :=
  ![⟨⟨-766044443118978035202392650555416673935832457080396117377661,-766044443118978035202392650555416673935832457080394608865489⟩,⟨-642787609686539326322643409907263432907559884205682848189797,-642787609686539326322643409907263432907559884205680452962922⟩⟩,
  ⟨⟨5233755199831249482665717691795751742155756671410853883156340,5233755199831249482665717691795751742155756671410858805946723⟩,⟨2632871574706939350348720073353156457815871122779497054238603,2632871574706939350348720073353156457815871122779506443385298⟩⟩,
  ⟨⟨-14048762311877381627832475986574716402376432240109459794605323,-14048762311877381627832475986574716402376432240109452062046354⟩,⟨-3337380320354260721729509916984522616909062592941966588825188,-3337380320354260721729509916984522616909062592941950502964245⟩⟩,
  ⟨⟨19162103110330220360738301890668762668313016051557984971001343,19162103110330220360738301890668762668313016051557994816582159⟩,⟨-9389146712,9389146726⟩⟩,
  ⟨⟨-14048762311877381627832475986574716402376432240109459794605361,-14048762311877381627832475986574716402376432240109452062046323⟩,⟨3337380320354260721729509916984522616909062592941950502964210,3337380320354260721729509916984522616909062592941966588825220⟩⟩,
  ⟨⟨5233755199831249482665717691795751742155756671410853883156279,5233755199831249482665717691795751742155756671410858805946781⟩,⟨-2632871574706939350348720073353156457815871122779506443385357,-2632871574706939350348720073353156457815871122779497054238545⟩⟩,
  ⟨⟨-766044443118978035202392650555416673935832457080396117377731,-766044443118978035202392650555416673935832457080394608865417⟩,⟨642787609686539326322643409907263432907559884205680452962854,642787609686539326322643409907263432907559884205682848189871⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩,
  ⟨⟨-74,74⟩,⟨-72,76⟩⟩]
lemma coeffBox3_calc (j : Fin 31) : coeffStep phaseBox3 coeffBox2 j = coeffBox3 j := by
  revert j
  decide +kernel
lemma coeffBox3_mem (j : Fin 31) : (coeffBox3 j).Mem ((partialPolynomial 3).coeff j.val) := by
  rw [← coeffBox3_calc, partialPolynomial_succ (by norm_num : 2 < 15)]
  apply coeffStep_mem ⟨2,by norm_num⟩ (partialPolynomial 2) phaseBox3 coeffBox2
  · have hr : residue ⟨2,by norm_num⟩ = (3:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox3_mem
  · exact coeffBox2_mem
def coeffBox4 : Fin 31 → CI :=
  ![⟨⟨173648177666930348851716626769314796000375677184067055979553,173648177666930348851716626769314796000375677184072437144710⟩,⟨984807753012208059366743024589523013670643251719839555037241,984807753012208059366743024589523013670643251719845155832624⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702771968629488887413,-3849000747596232886841704603828508967213702771968602523815191⟩,⟨-6666664853207267609891776724753869180900487454540783066994312,-6666664853207267609891776724753869180900487454540751449734765⟩⟩,
  ⟨⟨20084259982640082076513803988265308500673999989471170101688802,20084259982640082076513803988265308500673999989471230625140459⟩,⟨16852695143901897122188587307880678000655273393900321520999821,16852695143901897122188587307880678000655273393900401814969538⟩⟩,
  ⟨⟨-48478213543489407248647662562791111952021410423330865453927342,-48478213543489407248647662562791111952021410423330777721731770⟩,⟨-17644626740230823652168816539857840513291657431057853768631887,-17644626740230823652168816539857840513291657431057728196598947⟩⟩,
  ⟨⟨64138612261557255420247693103169995245121475057288279826121600,64138612261557255420247693103169995245121475057288390110694792⟩,⟨-74693174411,74693174447⟩⟩,
  ⟨⟨-48478213543489407248647662562791111952021410423330865453927510,-48478213543489407248647662562791111952021410423330777721731632⟩,⟨17644626740230823652168816539857840513291657431057728196598787,17644626740230823652168816539857840513291657431057853768632026⟩⟩,
  ⟨⟨20084259982640082076513803988265308500673999989471170101688538,20084259982640082076513803988265308500673999989471230625140728⟩,⟨-16852695143901897122188587307880678000655273393900401814969806,-16852695143901897122188587307880678000655273393900321520999559⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702771968629488887740,-3849000747596232886841704603828508967213702771968602523814856⟩,⟨6666664853207267609891776724753869180900487454540751449734441,6666664853207267609891776724753869180900487454540783066994648⟩⟩,
  ⟨⟨173648177666930348851716626769314796000375677184067055979197,173648177666930348851716626769314796000375677184072437145063⟩,⟨-984807753012208059366743024589523013670643251719845155832977,-984807753012208059366743024589523013670643251719839555036885⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩,
  ⟨⟨-359,359⟩,⟨-358,362⟩⟩]
lemma coeffBox4_calc (j : Fin 31) : coeffStep phaseBox4 coeffBox3 j = coeffBox4 j := by
  revert j
  decide +kernel
lemma coeffBox4_mem (j : Fin 31) : (coeffBox4 j).Mem ((partialPolynomial 4).coeff j.val) := by
  rw [← coeffBox4_calc, partialPolynomial_succ (by norm_num : 3 < 15)]
  apply coeffStep_mem ⟨3,by norm_num⟩ (partialPolynomial 3) phaseBox4 coeffBox3
  · have hr : residue ⟨3,by norm_num⟩ = (4:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox4_mem
  · exact coeffBox3_mem
def coeffBox5 : Fin 31 → CI :=
  ![⟨⟨866025403784438646763723170752936183471402626905183735048403,866025403784438646763723170752936183471402626905196208881899⟩,⟨-500000000000000000000000000000000000000000000000006583676919,-499999999999999999999999999999999999999999999999994601281521⟩⟩,
  ⟨⟨-4600883625124310132316997618442595284339885548631398205006316,-4600883625124310132316997618442595284339885548631300770460832⟩,⟨7866626774538188833014437765148908199971627794190314318391088,7866626774538188833014437765148908199971627794190408160613198⟩⟩,
  ⟨⟨284322541021897412154482253411142429365827116374327333764321,284322541021897412154482253411142429365827116374654661624875⟩,⟨-38143969992255195427604056742112035636044052309928576801899610,-38143969992255195427604056742112035636044052309928251042517266⟩⟩,
  ⟨⟨47749571520445274333396758921864998335504508004721094284979159,47749571520445274333396758921864998335504508004721739415601413⟩,⟨83958083658808470377564491603083021265181338999591417977106533,83958083658808470377564491603083021265181338999592089692084061⟩⟩,
  ⟨⟨-141598699190317800022480092434120163989670454080447340694763832,-141598699190317800022480092434120163989670454080446453087511678⟩,⟨-82450764439004109804374564040425568422117032246160186905322725,-82450764439004109804374564040425568422117032246159228891032639⟩⟩,
  ⟨⟨194599326700380999524964251413067364651337203762153749421765467,194599326700380999524964251413067364651337203762154844813919778⟩,⟨-577872755749,577872755858⟩⟩,
  ⟨⟨-141598699190317800022480092434120163989670454080447340694764545,-141598699190317800022480092434120163989670454080446453087511097⟩,⟨82450764439004109804374564040425568422117032246159228891031967,82450764439004109804374564040425568422117032246160186905323332⟩⟩,
  ⟨⟨47749571520445274333396758921864998335504508004721094284978035,47749571520445274333396758921864998335504508004721739415602586⟩,⟨-83958083658808470377564491603083021265181338999592089692085231,-83958083658808470377564491603083021265181338999591417977105406⟩⟩,
  ⟨⟨284322541021897412154482253411142429365827116374327333762875,284322541021897412154482253411142429365827116374654661626344⟩,⟨38143969992255195427604056742112035636044052309928251042515828,38143969992255195427604056742112035636044052309928576801901082⟩⟩,
  ⟨⟨-4600883625124310132316997618442595284339885548631398205007919,-4600883625124310132316997618442595284339885548631300770459247⟩,⟨-7866626774538188833014437765148908199971627794190408160614786,-7866626774538188833014437765148908199971627794190314318389487⟩⟩,
  ⟨⟨866025403784438646763723170752936183471402626905183735046769,866025403784438646763723170752936183471402626905196208883536⟩,⟨499999999999999999999999999999999999999999999999994601279887,500000000000000000000000000000000000000000000000006583678559⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩,
  ⟨⟨-1643,1643⟩,⟨-1640,1648⟩⟩]
lemma coeffBox5_calc (j : Fin 31) : coeffStep phaseBox7 coeffBox4 j = coeffBox5 j := by
  revert j
  decide +kernel
lemma coeffBox5_mem (j : Fin 31) : (coeffBox5 j).Mem ((partialPolynomial 5).coeff j.val) := by
  rw [← coeffBox5_calc, partialPolynomial_succ (by norm_num : 4 < 15)]
  apply coeffStep_mem ⟨4,by norm_num⟩ (partialPolynomial 4) phaseBox7 coeffBox4
  · have hr : residue ⟨4,by norm_num⟩ = (7:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox7_mem
  · exact coeffBox4_mem
def coeffBox6 : Fin 31 → CI :=
  ![⟨⟨-500000000000000000000000000000000000000000000000011399596808,-499999999999999999999999999999999999999999999999990496341924⟩,⟨-866025403784438646763723170752936183471402626905200464070792,-866025403784438646763723170752936183471402626905179069377810⟩⟩,
  ⟨⟨9598677582107066126541884106654780566914433048000642967408834,9598677582107066126541884106654780566914433048000843176653748⟩,⟨3600883625124310132316997618442595284339885548631243664311187,3600883625124310132316997618442595284339885548631446483003275⟩⟩,
  ⟨⟨-46845737242503815692238051978997226204723823407191509021720497,-46845737242503815692238051978997226204723823407190716533167499⟩,⟨16314956411838918900638116447639610154048831098911043634092672,16314956411838918900638116447639610154048831098911830997915191⟩⟩,
  ⟨⟨76660101966314076368859018344756397923941365438149176002703563,76660101966314076368859018344756397923941365438151537754771158⟩,⟨-128638395130079975320921870024531664891932498173210799686614747,-128638395130079975320921870024531664891932498173208464063535513⟩⟩,
  ⟨⟨51192348594141634290023010545416463884936036073209453655943824,51192348594141634290023010545416463884936036073213741807724123⟩,⟨309799189048956638189763557893697348949398959196002808819438913,309799189048956638189763557893697348949398959196007081301370058⟩⟩,
  ⟨⟨-367155482039444070422524676471323349244522247160488513912326776,-367155482039444070422524676471323349244522247160482780282282390⟩,⟨-311751284057943944800316620572053503160066760249755224280743448,-311751284057943944800316620572053503160066760249749436774335611⟩⟩,
  ⟨⟨554100182278770218658677630906985866146908472016624609713747195,554100182278770218658677630906985866146908472016631642846714388⟩,⟨-3506512802851,3506512803203⟩⟩,
  ⟨⟨-367155482039444070422524676471323349244522247160488513912329481,-367155482039444070422524676471323349244522247160482780282280210⟩,⟨311751284057943944800316620572053503160066760249749436774333096,311751284057943944800316620572053503160066760249755224280745788⟩⟩,
  ⟨⟨51192348594141634290023010545416463884936036073209453655939531,51192348594141634290023010545416463884936036073213741807728613⟩,⟨-309799189048956638189763557893697348949398959196007081301374578,-309799189048956638189763557893697348949398959196002808819434630⟩⟩,
  ⟨⟨76660101966314076368859018344756397923941365438149176002697956,76660101966314076368859018344756397923941365438151537754776867⟩,⟨128638395130079975320921870024531664891932498173208464063529930,128638395130079975320921870024531664891932498173210799686620469⟩⟩,
  ⟨⟨-46845737242503815692238051978997226204723823407191509021726809,-46845737242503815692238051978997226204723823407190716533161251⟩,⟨-16314956411838918900638116447639610154048831098911830997921448,-16314956411838918900638116447639610154048831098911043634086365⟩⟩,
  ⟨⟨9598677582107066126541884106654780566914433048000642967402323,9598677582107066126541884106654780566914433048000843176660260⟩,⟨-3600883625124310132316997618442595284339885548631446483009789,-3600883625124310132316997618442595284339885548631243664304675⟩⟩,
  ⟨⟨-500000000000000000000000000000000000000000000000011399603377,-499999999999999999999999999999999999999999999999990496335353⟩,⟨866025403784438646763723170752936183471402626905179069371251,866025403784438646763723170752936183471402626905200464077372⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩,
  ⟨⟨-6579,6579⟩,⟨-6570,6588⟩⟩]
lemma coeffBox6_calc (j : Fin 31) : coeffStep phaseBox9 coeffBox5 j = coeffBox6 j := by
  revert j
  decide +kernel
lemma coeffBox6_mem (j : Fin 31) : (coeffBox6 j).Mem ((partialPolynomial 6).coeff j.val) := by
  rw [← coeffBox6_calc, partialPolynomial_succ (by norm_num : 5 < 15)]
  apply coeffStep_mem ⟨5,by norm_num⟩ (partialPolynomial 5) phaseBox9 coeffBox5
  · have hr : residue ⟨5,by norm_num⟩ = (9:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox9_mem
  · exact coeffBox5_mem
def coeffBox7 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000021064579145,-999999999999999999999999999999999999999999999999978935435132⟩,⟨-19419482911,22703347133⟩⟩,
  ⟨⟨6917795486482586948753916921160270903681923406438942996395084,6917795486482586948753916921160270903681923406439389871389727⟩,⟨-8244307623847633411984384969508491764631092645119045359892662,-8244307623847633411984384969508491764631092645118601301227783⟩⟩,
  ⟨⟨10403653257250540448686234131604908102467273346226538973686726,10403653257250540448686234131604908102467273346228678869857872⟩,⟨55062818563402723511256155041554773494989859649215310169708880,55062818563402723511256155041554773494989859649217442676911621⟩⟩,
  ⟨⟨-165084659490935790669487097141401509335117754010472993686228301,-165084659490935790669487097141401509335117754010465823162448457⟩,⟨-87965740059492470667549121704228599039092155747508840626619456,-87965740059492470667549121704228599039092155747501649940149410⟩⟩,
  ⟨⟨409658310682373061938766591695979016771084187651579803715918016,409658310682373061938766591695979016771084187651595505195632065⟩,⟨-179123190402696503470650774138165392847142764409030348970581920,-179123190402696503470650774138165392847142764409014583986566430⟩⟩,
  ⟨⟨-201443406420170187339928907039772853380241319507540216335880830,-201443406420170187339928907039772853380241319507511989283855915⟩,⟨783759108848314465844577513638772579929776019388219385226335817,783759108848314465844577513638772579929776019388247569157895248⟩⟩,
  ⟨⟨-699958666430646530314576599847496095627217909672167995896284820,-699958666430646530314576599847496095627217909672132157718356598⟩,⟨-904133933324497355691380683436857502048917864934765436894996171,-904133933324497355691380683436857502048917864934729617988374113⟩⟩,
  ⟨⟨1281013945831292637975571722559852525130687197571760813056944388,1281013945831292637975571722559852525130687197571803819863436107⟩,⟨-21437303759894,21437303760967⟩⟩,
  ⟨⟨-699958666430646530314576599847496095627217909672167995896296595,-699958666430646530314576599847496095627217909672132157718346589⟩,⟨904133933324497355691380683436857502048917864934729617988363113,904133933324497355691380683436857502048917864934765436895006887⟩⟩,
  ⟨⟨-201443406420170187339928907039772853380241319507540216335900433,-201443406420170187339928907039772853380241319507511989283835858⟩,⟨-783759108848314465844577513638772579929776019388247569157915623,-783759108848314465844577513638772579929776019388219385226316474⟩⟩,
  ⟨⟨409658310682373061938766591695979016771084187651579803715892372,409658310682373061938766591695979016771084187651595505195658228⟩,⟨179123190402696503470650774138165392847142764409014583986540750,179123190402696503470650774138165392847142764409030348970608014⟩⟩,
  ⟨⟨-165084659490935790669487097141401509335117754010472993686257580,-165084659490935790669487097141401509335117754010465823162419376⟩,⟨87965740059492470667549121704228599039092155747501649940120353,87965740059492470667549121704228599039092155747508840626648772⟩⟩,
  ⟨⟨10403653257250540448686234131604908102467273346226538973656122,10403653257250540448686234131604908102467273346228678869888423⟩,⟨-55062818563402723511256155041554773494989859649217442676942211,-55062818563402723511256155041554773494989859649215310169678311⟩⟩,
  ⟨⟨6917795486482586948753916921160270903681923406438942996364070,6917795486482586948753916921160270903681923406439389871420762⟩,⟨8244307623847633411984384969508491764631092645118601301196787,8244307623847633411984384969508491764631092645119045359923713⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000021064610266,-999999999999999999999999999999999999999999999999978935404011⟩,⟨-22703378225,19419514063⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩,
  ⟨⟨-31135,31135⟩,⟨-31108,31164⟩⟩]
lemma coeffBox7_calc (j : Fin 31) : coeffStep phaseBox12 coeffBox6 j = coeffBox7 j := by
  revert j
  decide +kernel
lemma coeffBox7_mem (j : Fin 31) : (coeffBox7 j).Mem ((partialPolynomial 7).coeff j.val) := by
  rw [← coeffBox7_calc, partialPolynomial_succ (by norm_num : 6 < 15)]
  apply coeffStep_mem ⟨6,by norm_num⟩ (partialPolynomial 6) phaseBox12 coeffBox6
  · have hr : residue ⟨6,by norm_num⟩ = (12:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox12_mem
  · exact coeffBox6_mem
def coeffBox8 : Fin 31 → CI :=
  ![⟨⟨-642787609686539326322643409907263432907559884205715205990796,-642787609686539326322643409907263432907559884205644950671034⟩,⟨766044443118978035202392650555416673935832457080361820302316,766044443118978035202392650555416673935832457080431544495687⟩⟩,
  ⟨⟨-3868832817555432838789551276936722917397080294821431008893657,-3868832817555432838789551276936722917397080294820558344285185⟩,⟨-10598677582107066126541884106654780566914433048001170265550136,-10598677582107066126541884106654780566914433048000296560859766⟩⟩,
  ⟨⟨62060708955477453960923877148516799656043731889319834405748786,62060708955477453960923877148516799656043731889324492277286679⟩,⟨10169377070305564859724257431925253462504015971578085941037352,10169377070305564859724257431925253462504015971582762313946973⟩⟩,
  ⟨⟨-141930554245348113630828032308910091907912775884948329464179964,-141930554245348113630828032308910091907912775884930430457098204⟩,⟨180044535386876843869158452121621522566314576656835597773329493,180044535386876843869158452121621522566314576656853439550084625⟩⟩,
  ⟨⟨-239555584085579127298262843034489804366753137625289066027813840,-239555584085579127298262843034489804366753137625242534997781282⟩,⟨-561522761700274177377124604258583402652768405083680639217263737,-561522761700274177377124604258583402652768405083634173646730087⟩⟩,
  ⟨⟨1251496898429272207070423830816425442487874994080484684714885271,1251496898429272207070423830816425442487874994080578981609054392⟩,⟨116853391598027836019101484059740395430096723577773211491488973,116853391598027836019101484059740395430096723577867906940471597⟩⟩,
  ⟨⟨-1144878735419732574051742458397655413283608858240397601100012363,-1144878735419732574051742458397655413283608858240245160313601803⟩,⟨1721229879768017096080962796089755917357404834773775078467099799,1721229879768017096080962796089755917357404834773927413539632397⟩⟩,
  ⟨⟨-1306377076422343307053265617545683906128011426452724152473114895,-1306377076422343307053265617545683906128011426452527952531204663⟩,⟨-2440105439355440960610695384981918413423708827380975627250822799,-2440105439355440960610695384981918413423708827380779815883036971⟩⟩,
  ⟨⟨3047391926430990866335726876017281919785344224824540086495050736,3047391926430990866335726876017281919785344224824761081240298219⟩,⟨-110476150741195,110476150744512⟩⟩,
  ⟨⟨-1306377076422343307053265617545683906128011426452724152473167476,-1306377076422343307053265617545683906128011426452527952531157758⟩,⟨2440105439355440960610695384981918413423708827380779815882987202,2440105439355440960610695384981918413423708827380975627250872373⟩⟩,
  ⟨⟨-1144878735419732574051742458397655413283608858240397601100103503,-1144878735419732574051742458397655413283608858240245160313510024⟩,⟨-1721229879768017096080962796089755917357404834773927413539725785,-1721229879768017096080962796089755917357404834773775078467010137⟩⟩,
  ⟨⟨1251496898429272207070423830816425442487874994080484684714765487,1251496898429272207070423830816425442487874994080578981609176368⟩,⟨-116853391598027836019101484059740395430096723577867906940592023,-116853391598027836019101484059740395430096723577773211491367713⟩⟩,
  ⟨⟨-239555584085579127298262843034489804366753137625289066027951977,-239555584085579127298262843034489804366753137625242534997643575⟩,⟨561522761700274177377124604258583402652768405083634173646592757,561522761700274177377124604258583402652768405083680639217402280⟩⟩,
  ⟨⟨-141930554245348113630828032308910091907912775884948329464326130,-141930554245348113630828032308910091907912775884930430456952416⟩,⟨-180044535386876843869158452121621522566314576656853439550230607,-180044535386876843869158452121621522566314576656835597773183514⟩⟩,
  ⟨⟨62060708955477453960923877148516799656043731889319834405599846,62060708955477453960923877148516799656043731889324492277435689⟩,⟨-10169377070305564859724257431925253462504015971582762314095896,-10169377070305564859724257431925253462504015971578085940888331⟩⟩,
  ⟨⟨-3868832817555432838789551276936722917397080294821431009043466,-3868832817555432838789551276936722917397080294820558344135361⟩,⟨10598677582107066126541884106654780566914433048000296560710054,10598677582107066126541884106654780566914433048001170265700058⟩⟩,
  ⟨⟨-642787609686539326322643409907263432907559884205715206140780,-642787609686539326322643409907263432907559884205644950521053⟩,⟨-766044443118978035202392650555416673935832457080431544645576,-766044443118978035202392650555416673935832457080361820152239⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩,
  ⟨⟨-150004,150004⟩,⟨-149910,150096⟩⟩]
lemma coeffBox8_calc (j : Fin 31) : coeffStep phaseBox13 coeffBox7 j = coeffBox8 j := by
  revert j
  decide +kernel
lemma coeffBox8_mem (j : Fin 31) : (coeffBox8 j).Mem ((partialPolynomial 8).coeff j.val) := by
  rw [← coeffBox8_calc, partialPolynomial_succ (by norm_num : 7 < 15)]
  apply coeffStep_mem ⟨7,by norm_num⟩ (partialPolynomial 7) phaseBox13 coeffBox7
  · have hr : residue ⟨7,by norm_num⟩ = (13:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox13_mem
  · exact coeffBox7_mem
lemma coeffBox9_calc (j : Fin 31) : coeffStep phaseBox16 coeffBox8 j = coeffBox9 j := by
  revert j
  decide +kernel
lemma coeffBox9_mem (j : Fin 31) : (coeffBox9 j).Mem ((partialPolynomial 9).coeff j.val) := by
  rw [← coeffBox9_calc, partialPolynomial_succ (by norm_num : 8 < 15)]
  apply coeffStep_mem ⟨8,by norm_num⟩ (partialPolynomial 8) phaseBox16 coeffBox8
  · have hr : residue ⟨8,by norm_num⟩ = (16:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox16_mem
  · exact coeffBox8_mem
lemma coeffBox10_mem (j : Fin 31) : (coeffBox10 j).Mem ((partialPolynomial 10).coeff j.val) := by
  rw [← coeffBox10_calc, partialPolynomial_succ (by norm_num : 9 < 15)]
  apply coeffStep_mem ⟨9,by norm_num⟩ (partialPolynomial 9) phaseBox19 coeffBox9
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact coeffBox9_mem
lemma coeffBox11_calc (j : Fin 31) : coeffStep phaseBox21 coeffBox10 j = coeffBox11 j := by
  revert j
  decide +kernel
lemma coeffBox11_mem (j : Fin 31) : (coeffBox11 j).Mem ((partialPolynomial 11).coeff j.val) := by
  rw [← coeffBox11_calc, partialPolynomial_succ (by norm_num : 10 < 15)]
  apply coeffStep_mem ⟨10,by norm_num⟩ (partialPolynomial 10) phaseBox21 coeffBox10
  · have hr : residue ⟨10,by norm_num⟩ = (21:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox21_mem
  · exact coeffBox10_mem
lemma coeffBox12_calc (j : Fin 31) : coeffStep phaseBox25 coeffBox11 j = coeffBox12 j := by
  revert j
  decide +kernel
lemma coeffBox12_mem (j : Fin 31) : (coeffBox12 j).Mem ((partialPolynomial 12).coeff j.val) := by
  rw [← coeffBox12_calc, partialPolynomial_succ (by norm_num : 11 < 15)]
  apply coeffStep_mem ⟨11,by norm_num⟩ (partialPolynomial 11) phaseBox25 coeffBox11
  · have hr : residue ⟨11,by norm_num⟩ = (25:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox25_mem
  · exact coeffBox11_mem
lemma coeffBox13_calc (j : Fin 31) : coeffStep phaseBox27 coeffBox12 j = coeffBox13 j := by
  revert j
  decide +kernel
lemma coeffBox13_mem (j : Fin 31) : (coeffBox13 j).Mem ((partialPolynomial 13).coeff j.val) := by
  rw [← coeffBox13_calc, partialPolynomial_succ (by norm_num : 12 < 15)]
  apply coeffStep_mem ⟨12,by norm_num⟩ (partialPolynomial 12) phaseBox27 coeffBox12
  · have hr : residue ⟨12,by norm_num⟩ = (27:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox27_mem
  · exact coeffBox12_mem
lemma coeffBox14_calc (j : Fin 31) : coeffStep phaseBox28 coeffBox13 j = coeffBox14 j := by
  revert j
  decide +kernel
lemma coeffBox14_mem (j : Fin 31) : (coeffBox14 j).Mem ((partialPolynomial 14).coeff j.val) := by
  rw [← coeffBox14_calc, partialPolynomial_succ (by norm_num : 13 < 15)]
  apply coeffStep_mem ⟨13,by norm_num⟩ (partialPolynomial 13) phaseBox28 coeffBox13
  · have hr : residue ⟨13,by norm_num⟩ = (28:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox28_mem
  · exact coeffBox13_mem
lemma coeffBox15_calc (j : Fin 31) : coeffStep phaseBox31 coeffBox14 j = coeffBox15 j := by
  revert j
  decide +kernel
lemma coeffBox15_mem (j : Fin 31) : (coeffBox15 j).Mem ((partialPolynomial 15).coeff j.val) := by
  rw [← coeffBox15_calc, partialPolynomial_succ (by norm_num : 14 < 15)]
  apply coeffStep_mem ⟨14,by norm_num⟩ (partialPolynomial 14) phaseBox31 coeffBox14
  · have hr : residue ⟨14,by norm_num⟩ = (31:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox31_mem
  · exact coeffBox14_mem
lemma atomPolynomial_coeff_mem (j : Fin 31) : (coeffBox15 j).Mem (atomPolynomial.coeff j.val) := by
  simpa only [partialPolynomial_fifteen] using coeffBox15_mem j
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma phaseTable_mem (j : Fin 36) : (phaseTable j).Mem (phase ((j.val:ℤ):ℂ)) := by
  fin_cases j
  · exact phaseBox0_mem
  · exact phaseBox1_mem
  · exact phaseBox2_mem
  · exact phaseBox3_mem
  · exact phaseBox4_mem
  · exact phaseBox5_mem
  · exact phaseBox6_mem
  · exact phaseBox7_mem
  · exact phaseBox8_mem
  · exact phaseBox9_mem
  · exact phaseBox10_mem
  · exact phaseBox11_mem
  · exact phaseBox12_mem
  · exact phaseBox13_mem
  · exact phaseBox14_mem
  · exact phaseBox15_mem
  · exact phaseBox16_mem
  · exact phaseBox17_mem
  · exact phaseBox18_mem
  · exact phaseBox19_mem
  · exact phaseBox20_mem
  · exact phaseBox21_mem
  · exact phaseBox22_mem
  · exact phaseBox23_mem
  · exact phaseBox24_mem
  · exact phaseBox25_mem
  · exact phaseBox26_mem
  · exact phaseBox27_mem
  · exact phaseBox28_mem
  · exact phaseBox29_mem
  · exact phaseBox30_mem
  · exact phaseBox31_mem
  · exact phaseBox32_mem
  · exact phaseBox33_mem
  · exact phaseBox34_mem
  · exact phaseBox35_mem
lemma phaseModBox_mem (n : ℤ) : (phaseModBox n).Mem (phase (n:ℂ)) := by
  rw [phase_int_mod]
  have hh := phaseTable_mem ⟨(n%36).toNat, by omega⟩
  simpa only [phaseModBox, Int.toNat_of_nonneg (show 0 ≤ n%36 by omega)] using hh

lemma frequencyBox_mem (j : Fin 31) :
    (frequencyBox j).Mem (Complex.I*Real.pi*(frequency j:ℂ)) := by
  have hh := CI.mem_divNat
    (CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem))
      (CI.mem_point ((j.val:ℤ)-15))) (by norm_num : 0 < (18:ℕ))
  change (((CI.imag.mul (CI.ofReal piBox)).mul (CI.point ((j.val:ℤ)-15))).divNat 18).Mem _
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold frequency
  push_cast
  ring

lemma waveDerivativeBox_mem (k : ℕ) (n : ℤ) :
    (waveDerivativeBox k n).Mem (waveDerivative k (n:ℂ)) := by
  apply CI.mem_sum
  intro j
  rw [wave_phase_integer]
  exact CI.mem_mul (CI.mem_mul (atomPolynomial_coeff_mem j)
    (CI.mem_pow (frequencyBox_mem j) k)) (phaseModBox_mem (((j.val:ℤ)-15)*n))

lemma jetBox2_0_mem : jetBox2_0.Mem (waveDerivative 2 ((0:ℤ):ℂ)) := by
  rw [← jetBox2_0_calc]
  exact waveDerivativeBox_mem 2 0
lemma QBox0_mem : QBox0.Mem (Q 0) := by
  rw [← QBox0_calc]
  exact RI.mem_divNat jetBox2_0_mem.1 (by norm_num)
lemma Q_0_bounds : (157/1000:ℝ) < Q 0 ∧ Q 0 < 40 := by
  have hh := QBox0_mem
  norm_num [RI.Mem, QBox0, scale] at hh
  constructor <;> linarith
def jetBox2_1 : CI := ⟨⟨649358508339545667567100424194258763912824850100094785805590,649358508339545667567100424194258763912843619077633365447908⟩,⟨-9384489787203357955,9384489786138007847⟩⟩
lemma jetBox2_1_calc : waveDerivativeBox 2 1 = jetBox2_1 := by decide +kernel
lemma jetBox2_1_mem : jetBox2_1.Mem (waveDerivative 2 ((1:ℤ):ℂ)) := by
  rw [← jetBox2_1_calc]
  exact waveDerivativeBox_mem 2 1
def QBox1 : RI := ⟨324679254169772833783550212097129381956412425050047392902795,324679254169772833783550212097129381956421809538816682723955⟩
lemma QBox1_calc : jetBox2_1.re.divNat 2 = QBox1 := by decide +kernel
lemma QBox1_mem : QBox1.Mem (Q 1) := by
  rw [← QBox1_calc]
  exact RI.mem_divNat jetBox2_1_mem.1 (by norm_num)
lemma Q_1_bounds : (157/1000:ℝ) < Q 1 ∧ Q 1 < 40 := by
  have hh := QBox1_mem
  norm_num [RI.Mem, QBox1, scale] at hh
  constructor <;> linarith
def jetBox2_3 : CI := ⟨⟨314935873091926165719798041528741690796860352768042068448118,314935873091926165719798041528741690796877767398780082367638⟩,⟨-8707279535569115420,8707279520646445484⟩⟩
lemma jetBox2_3_calc : waveDerivativeBox 2 3 = jetBox2_3 := by decide +kernel
lemma jetBox2_3_mem : jetBox2_3.Mem (waveDerivative 2 ((3:ℤ):ℂ)) := by
  rw [← jetBox2_3_calc]
  exact waveDerivativeBox_mem 2 3
def QBox3 : RI := ⟨157467936545963082859899020764370845398430176384021034224059,157467936545963082859899020764370845398438883699390041183820⟩
lemma QBox3_calc : jetBox2_3.re.divNat 2 = QBox3 := by decide +kernel
lemma QBox3_mem : QBox3.Mem (Q 3) := by
  rw [← QBox3_calc]
  exact RI.mem_divNat jetBox2_3_mem.1 (by norm_num)
lemma Q_3_bounds : (157/1000:ℝ) < Q 3 ∧ Q 3 < 40 := by
  have hh := QBox3_mem
  norm_num [RI.Mem, QBox3, scale] at hh
  constructor <;> linarith
def jetBox2_4 : CI := ⟨⟨480190930161026078211119768145913141800720940178075083063726,480190930161026078211119768145913141800738985786865741678330⟩,⟨-9022785599708981683,9022785611075412461⟩⟩
lemma jetBox2_4_calc : waveDerivativeBox 2 4 = jetBox2_4 := by decide +kernel
lemma jetBox2_4_mem : jetBox2_4.Mem (waveDerivative 2 ((4:ℤ):ℂ)) := by
  rw [← jetBox2_4_calc]
  exact waveDerivativeBox_mem 2 4
def QBox4 : RI := ⟨240095465080513039105559884072956570900360470089037541531863,240095465080513039105559884072956570900369492893432870839166⟩
lemma QBox4_calc : jetBox2_4.re.divNat 2 = QBox4 := by decide +kernel
lemma QBox4_mem : QBox4.Mem (Q 4) := by
  rw [← QBox4_calc]
  exact RI.mem_divNat jetBox2_4_mem.1 (by norm_num)
lemma Q_4_bounds : (157/1000:ℝ) < Q 4 ∧ Q 4 < 40 := by
  have hh := QBox4_mem
  norm_num [RI.Mem, QBox4, scale] at hh
  constructor <;> linarith
def jetBox2_7 : CI := ⟨⟨3189148019972792007764637656494857305488305163218904078244812,3189148019972792007764637656494857305488323055140130853335833⟩,⟨-8946107184572060955,8946107179335551303⟩⟩
lemma jetBox2_7_calc : waveDerivativeBox 2 7 = jetBox2_7 := by decide +kernel
lemma jetBox2_7_mem : jetBox2_7.Mem (waveDerivative 2 ((7:ℤ):ℂ)) := by
  rw [← jetBox2_7_calc]
  exact waveDerivativeBox_mem 2 7
def QBox7 : RI := ⟨1594574009986396003882318828247428652744152581609452039122406,1594574009986396003882318828247428652744161527570065426667917⟩
lemma QBox7_calc : jetBox2_7.re.divNat 2 = QBox7 := by decide +kernel
lemma QBox7_mem : QBox7.Mem (Q 7) := by
  rw [← QBox7_calc]
  exact RI.mem_divNat jetBox2_7_mem.1 (by norm_num)
lemma Q_7_bounds : (157/1000:ℝ) < Q 7 ∧ Q 7 < 40 := by
  have hh := QBox7_mem
  norm_num [RI.Mem, QBox7, scale] at hh
  constructor <;> linarith
def jetBox2_9 : CI := ⟨⟨4386490844928603830593107111056067171250526070359086629539213,4386490844928603830593107111056067171250540069410481046659986⟩,⟨-6999139762929181309,6999139749324919077⟩⟩
lemma jetBox2_9_calc : waveDerivativeBox 2 9 = jetBox2_9 := by decide +kernel
lemma jetBox2_9_mem : jetBox2_9.Mem (waveDerivative 2 ((9:ℤ):ℂ)) := by
  rw [← jetBox2_9_calc]
  exact waveDerivativeBox_mem 2 9
def QBox9 : RI := ⟨2193245422464301915296553555528033585625263035179543314769606,2193245422464301915296553555528033585625270034705240523329994⟩
lemma QBox9_calc : jetBox2_9.re.divNat 2 = QBox9 := by decide +kernel
lemma QBox9_mem : QBox9.Mem (Q 9) := by
  rw [← QBox9_calc]
  exact RI.mem_divNat jetBox2_9_mem.1 (by norm_num)
lemma Q_9_bounds : (157/1000:ℝ) < Q 9 ∧ Q 9 < 40 := by
  have hh := QBox9_mem
  norm_num [RI.Mem, QBox9, scale] at hh
  constructor <;> linarith
def jetBox2_12 : CI := ⟨⟨2193245422464301915296553555528033585625257827702944738164265,2193245422464301915296553555528033585625275242181781766130093⟩,⟨-8707354858304197389,8707354880361310085⟩⟩
lemma jetBox2_12_calc : waveDerivativeBox 2 12 = jetBox2_12 := by decide +kernel
lemma jetBox2_12_mem : jetBox2_12.Mem (waveDerivative 2 ((12:ℤ):ℂ)) := by
  rw [← jetBox2_12_calc]
  exact waveDerivativeBox_mem 2 12
def QBox12 : RI := ⟨1096622711232150957648276777764016792812628913851472369082132,1096622711232150957648276777764016792812637621090890883065047⟩
lemma QBox12_calc : jetBox2_12.re.divNat 2 = QBox12 := by decide +kernel
lemma QBox12_mem : QBox12.Mem (Q 12) := by
  rw [← QBox12_calc]
  exact RI.mem_divNat jetBox2_12_mem.1 (by norm_num)
lemma Q_12_bounds : (157/1000:ℝ) < Q 12 ∧ Q 12 < 40 := by
  have hh := QBox12_mem
  norm_num [RI.Mem, QBox12, scale] at hh
  constructor <;> linarith
def jetBox2_13 : CI := ⟨⟨2807621397887934342703697530467294183654949971789532816313407,2807621397887934342703697530467294183654968017377691935889251⟩,⟨-9022795908507912539,9022795903898093804⟩⟩
lemma jetBox2_13_calc : waveDerivativeBox 2 13 = jetBox2_13 := by decide +kernel
lemma jetBox2_13_mem : jetBox2_13.Mem (waveDerivative 2 ((13:ℤ):ℂ)) := by
  rw [← jetBox2_13_calc]
  exact waveDerivativeBox_mem 2 13
def QBox13 : RI := ⟨1403810698943967171351848765233647091827474985894766408156703,1403810698943967171351848765233647091827484008688845967944626⟩
lemma QBox13_calc : jetBox2_13.re.divNat 2 = QBox13 := by decide +kernel
lemma QBox13_mem : QBox13.Mem (Q 13) := by
  rw [← QBox13_calc]
  exact RI.mem_divNat jetBox2_13_mem.1 (by norm_num)
lemma Q_13_bounds : (157/1000:ℝ) < Q 13 ∧ Q 13 < 40 := by
  have hh := QBox13_mem
  norm_num [RI.Mem, QBox13, scale] at hh
  constructor <;> linarith
def jetBox2_16 : CI := ⟨⟨33007531783833052762588798763964826898017254795610847195476874,33007531783833052762588798763964826898017272687668020675686737⟩,⟨-8946039095198659698,8946039053156332177⟩⟩
lemma jetBox2_16_calc : waveDerivativeBox 2 16 = jetBox2_16 := by decide +kernel
lemma jetBox2_16_mem : jetBox2_16.Mem (waveDerivative 2 ((16:ℤ):ℂ)) := by
  rw [← jetBox2_16_calc]
  exact waveDerivativeBox_mem 2 16
def QBox16 : RI := ⟨16503765891916526381294399381982413449008627397805423597738437,16503765891916526381294399381982413449008636343834010337843369⟩
lemma QBox16_calc : jetBox2_16.re.divNat 2 = QBox16 := by decide +kernel
lemma QBox16_mem : QBox16.Mem (Q 16) := by
  rw [← QBox16_calc]
  exact RI.mem_divNat jetBox2_16_mem.1 (by norm_num)
lemma Q_16_bounds : (157/1000:ℝ) < Q 16 ∧ Q 16 < 40 := by
  have hh := QBox16_mem
  norm_num [RI.Mem, QBox16, scale] at hh
  constructor <;> linarith
def jetBox2_19 : CI := ⟨⟨41594368450902491745324397900324124587329585672093445575455224,41594368450902491745324397900324124587329604441070992504609025⟩,⟨-9384489826205149675,9384489757909251186⟩⟩
lemma jetBox2_19_calc : waveDerivativeBox 2 19 = jetBox2_19 := by decide +kernel
lemma jetBox2_19_mem : jetBox2_19.Mem (waveDerivative 2 ((19:ℤ):ℂ)) := by
  rw [← jetBox2_19_calc]
  exact waveDerivativeBox_mem 2 19
def QBox19 : RI := ⟨20797184225451245872662198950162062293664792836046722787727612,20797184225451245872662198950162062293664802220535496252304513⟩
lemma QBox19_calc : jetBox2_19.re.divNat 2 = QBox19 := by decide +kernel
lemma QBox19_mem : QBox19.Mem (Q 19) := by
  rw [← QBox19_calc]
  exact RI.mem_divNat jetBox2_19_mem.1 (by norm_num)
lemma Q_19_bounds : (157/1000:ℝ) < Q 19 ∧ Q 19 < 40 := by
  have hh := QBox19_mem
  norm_num [RI.Mem, QBox19, scale] at hh
  constructor <;> linarith
def jetBox2_21 : CI := ⟨⟨61095935955908527462583701513256198706710585210988786004672484,61095935955908527462583701513256198706710602625619514804300734⟩,⟨-8707279582232183985,8707279467511139628⟩⟩
lemma jetBox2_21_calc : waveDerivativeBox 2 21 = jetBox2_21 := by decide +kernel
lemma jetBox2_21_mem : jetBox2_21.Mem (waveDerivative 2 ((21:ℤ):ℂ)) := by
  rw [← jetBox2_21_calc]
  exact waveDerivativeBox_mem 2 21
def QBox21 : RI := ⟨30547967977954263731291850756628099353355292605494393002336242,30547967977954263731291850756628099353355301312809757402150368⟩
lemma QBox21_calc : jetBox2_21.re.divNat 2 = QBox21 := by decide +kernel
lemma QBox21_mem : QBox21.Mem (Q 21) := by
  rw [← QBox21_calc]
  exact RI.mem_divNat jetBox2_21_mem.1 (by norm_num)
lemma Q_21_bounds : (157/1000:ℝ) < Q 21 ∧ Q 21 < 40 := by
  have hh := QBox21_mem
  norm_num [RI.Mem, QBox21, scale] at hh
  constructor <;> linarith
def jetBox2_25 : CI := ⟨⟨29914105240374937967757202440552063373006499439127337250121405,29914105240374937967757202440552063373006517331048559738158075⟩,⟨-8946107202121091217,8946107153004074020⟩⟩
lemma jetBox2_25_calc : waveDerivativeBox 2 25 = jetBox2_25 := by decide +kernel
lemma jetBox2_25_mem : jetBox2_25.Mem (waveDerivative 2 ((25:ℤ):ℂ)) := by
  rw [← jetBox2_25_calc]
  exact waveDerivativeBox_mem 2 25
def QBox25 : RI := ⟨14957052620187468983878601220276031686503249719563668625060702,14957052620187468983878601220276031686503258665524279869079038⟩
lemma QBox25_calc : jetBox2_25.re.divNat 2 = QBox25 := by decide +kernel
lemma QBox25_mem : QBox25.Mem (Q 25) := by
  rw [← QBox25_calc]
  exact RI.mem_divNat jetBox2_25_mem.1 (by norm_num)
lemma Q_25_bounds : (157/1000:ℝ) < Q 25 ∧ Q 25 < 40 := by
  have hh := QBox25_mem
  norm_num [RI.Mem, QBox25, scale] at hh
  constructor <;> linarith
def jetBox2_27 : CI := ⟨⟨4386490844928603830593107111056067171250526070358973263547709,4386490844928603830593107111056067171250540069410367680668482⟩,⟨-6999139762929185781,6999139749324914605⟩⟩
lemma jetBox2_27_calc : waveDerivativeBox 2 27 = jetBox2_27 := by decide +kernel
lemma jetBox2_27_mem : jetBox2_27.Mem (waveDerivative 2 ((27:ℤ):ℂ)) := by
  rw [← jetBox2_27_calc]
  exact waveDerivativeBox_mem 2 27
def QBox27 : RI := ⟨2193245422464301915296553555528033585625263035179486631773854,2193245422464301915296553555528033585625270034705183840334242⟩
lemma QBox27_calc : jetBox2_27.re.divNat 2 = QBox27 := by decide +kernel
lemma QBox27_mem : QBox27.Mem (Q 27) := by
  rw [← QBox27_calc]
  exact RI.mem_divNat jetBox2_27_mem.1 (by norm_num)
lemma Q_27_bounds : (157/1000:ℝ) < Q 27 ∧ Q 27 < 40 := by
  have hh := QBox27_mem
  norm_num [RI.Mem, QBox27, scale] at hh
  constructor <;> linarith
def jetBox2_28 : CI := ⟨⟨5990694890363355634538045467393864501436794539821908259433758,5990694890363355634538045467393864501436813308861036652393856⟩,⟨-9384458612011244997,9384458614328773767⟩⟩
lemma jetBox2_28_calc : waveDerivativeBox 2 28 = jetBox2_28 := by decide +kernel
lemma jetBox2_28_mem : jetBox2_28.Mem (waveDerivative 2 ((28:ℤ):ℂ)) := by
  rw [← jetBox2_28_calc]
  exact waveDerivativeBox_mem 2 28
def QBox28 : RI := ⟨2995347445181677817269022733696932250718397269910954129716879,2995347445181677817269022733696932250718406654430518326196929⟩
lemma QBox28_calc : jetBox2_28.re.divNat 2 = QBox28 := by decide +kernel
lemma QBox28_mem : QBox28.Mem (Q 28) := by
  rw [← QBox28_calc]
  exact RI.mem_divNat jetBox2_28_mem.1 (by norm_num)
lemma Q_28_bounds : (157/1000:ℝ) < Q 28 ∧ Q 28 < 40 := by
  have hh := QBox28_mem
  norm_num [RI.Mem, QBox28, scale] at hh
  constructor <;> linarith
def jetBox2_31 : CI := ⟨⟨79759068799952036170234820045985819951626970713036857794209793,79759068799952036170234820045985819951626988758625018626937983⟩,⟨-9022795974534550414,9022795843574071670⟩⟩
lemma jetBox2_31_calc : waveDerivativeBox 2 31 = jetBox2_31 := by decide +kernel
lemma jetBox2_31_mem : jetBox2_31.Mem (waveDerivative 2 ((31:ℤ):ℂ)) := by
  rw [← jetBox2_31_calc]
  exact waveDerivativeBox_mem 2 31
def QBox31 : RI := ⟨39879534399976018085117410022992909975813485356518428897104896,39879534399976018085117410022992909975813494379312509313468992⟩
lemma QBox31_calc : jetBox2_31.re.divNat 2 = QBox31 := by decide +kernel
lemma QBox31_mem : QBox31.Mem (Q 31) := by
  rw [← QBox31_calc]
  exact RI.mem_divNat jetBox2_31_mem.1 (by norm_num)
lemma Q_31_bounds : (157/1000:ℝ) < Q 31 ∧ Q 31 < 40 := by
  have hh := QBox31_mem
  norm_num [RI.Mem, QBox31, scale] at hh
  constructor <;> linarith
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex

def recoverRest (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  e.conj.mul (((coeffBox15 j).neg.add
    (if h : j.val=0 then CI.point 0 else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩)))

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
def kappaBox : CI := (CI.ofReal piBox).divNat 36
lemma kappaBox_mem : kappaBox.Mem (kappa:ℂ) := by
  have hh := CI.mem_divNat (CI.mem_ofReal piBox_mem) (by norm_num : 0 < (36:ℕ))
  simpa only [kappaBox, kappa, Complex.ofReal_div, Complex.ofReal_ofNat, Nat.cast_ofNat] using hh

def cCoeffBox (r : Fin 31 → CI) (j : Fin 31) : CI := if h : j.val=0 then CI.point 0
    else ((CI.point 4).mul (kappaBox.pow 2)).mul (r ⟨j.val-1,by omega⟩)
def dCoeffBox (e : CI) (r : Fin 31 → CI) (j : Fin 31) : CI :=
  (CI.imag.mul kappaBox).mul ((e.mul (r j)).sub
    (if h : j.val<2 then CI.point 0 else e.conj.mul (r ⟨j.val-2,by omega⟩)))
lemma cCoeffBox_mem (a : Fin 15) (r : Fin 31 → CI)
    (hr : ∀ j, (r j).Mem ((restPolynomial a).coeff j.val)) (j : Fin 31) :
    (cCoeffBox r j).Mem (cCoefficient a j) := by
  rw [cCoefficient_eq]
  unfold cCoeffBox
  split_ifs
  · simpa using CI.mem_point 0
  · exact CI.mem_mul (CI.mem_mul (by simpa using CI.mem_point 4)
      (CI.mem_pow kappaBox_mem 2)) (hr ⟨j.val-1,by omega⟩)
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma damping_pos (q : Fin 2) : 0 < damping q := by
  unfold damping h H
  split_ifs <;> norm_num

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def dampingBox (q : Fin 2) : RI := (RI.point (if q.val=0 then 17 else 27)).divNat 50
def realFrequencyBox (j : Fin 31) : RI := (RI.point ((j.val:ℤ)-15)).divNat 18
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
-- module Solutions.OAIQ262_TG.Triangular_Construction_PeriodicJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma D_emod (n : ℤ) : D n = D (n%36) := by simp only [D,waveDerivative_emod 3 n,Q_emod n]
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction
lemma Q_node_bounds (n : ℤ) (hn : n%36 ∈ residues) : (157/1000:ℝ)<Q n ∧ Q n<40 := by
  rw [Q_emod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h]
  all_goals first
    | exact Q_0_bounds | exact Q_1_bounds | exact Q_3_bounds | exact Q_4_bounds
    | exact Q_7_bounds | exact Q_9_bounds | exact Q_12_bounds | exact Q_13_bounds
    | exact Q_16_bounds | exact Q_19_bounds | exact Q_21_bounds | exact Q_25_bounds
    | exact Q_27_bounds | exact Q_28_bounds | exact Q_31_bounds
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_TailEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma Q_enumerateTail (a : Fin 15) (l : ℕ) :
    Q (enumerateTail (a,l)).val.val=Q (tailBase a) := by
  rw [Q_emod,Q_emod (tailBase a)]
  congr 1
  change (tailBase a+36*(l:ℤ))%36=tailBase a%36
  simp
lemma D_enumerateTail (a : Fin 15) (l : ℕ) :
    D (enumerateTail (a,l)).val.val=D (tailBase a) := by
  rw [D_emod,D_emod (tailBase a)]
  congr 1
  change (tailBase a+36*(l:ℤ))%36=tailBase a%36
  simp
end AtomicTriangular.Construction
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
def columnNorm0 : Fin 31 → RI := ![⟨0,1414213562373095048801688724210⟩,⟨30461741978670859934674354937889355355906479651966740766348,30461741978670859934674354937889355355906479651988725086992⟩,⟨60923483957341719869348709875778710711812959303662492613972,60923483957341719869348709875778710711812959304248830887183⟩,⟨80594193777379703611772256853783743039592541138985169805798,80594193777379703611772256853783743039592541144467550808188⟩,⟨161188387554759407223544513707567486079185082262508894546759,161188387554759407223544513707567486079185082304396071275563⟩,⟨249340104141176892137268477371642448241473602306117850337604,249340104141176892137268477371642448241473602603879302080905⟩,⟨322376775109518814447089027415134972158370163922359756485119,322376775109518814447089027415134972158370165211451738485955⟩,⟨396002645722721179150766614192561619626784233411355774337015,396002645722721179150766614192561619626784237540073058469301⟩,⟨531118619716947992628349843654691070641921560837530936634942,531118619716947992628349843654691070641921580161594410433646⟩,⟨618305832450696531923388716864482209611157610857507079144435,618305832450696531923388716864482209611157676838623580233848⟩,⟨678415205674267566801669182193615172871929984145321772526738,678415205674267566801669182193615172871930160955753439410688⟩,⟨817941733422656715514021315119501776671662116761061847050906,817941733422656715514021315119501776671662497157515828331668⟩,⟨919924434195607205135573770923984020039013762902965090937134,919924434195607205135573770923984020039015040160281423385223⟩,⟨951167588422639911721266079932102166096410529674782502317791,951167588422639911721266079932102166096413985671545194086273⟩,⟨1006621157644537777887872050207869995059235167040430973542928,1006621157644537777887872050207869995059243166318493171506598⟩,⟨1096622711232150957648276777764016792812625919609624534145245,1096622711232150957648276777764016792812640615332794825920421⟩,⟨1006621157644537777887872050207869995059215525864000568979206,1006621157644537777887872050207869995059262807494923576030281⟩,⟨951167588422639911721266079932102166096351355179610139231461,951167588422639911721266079932102166096473160166717557104380⟩,⟨919924434195607205135573770923984020038877583869683197478009,919924434195607205135573770923984020039151219193563316739974⟩,⟨817941733422656715514021315119501776671406451821232216294948,817941733422656715514021315119501776671918162097345458949189⟩,⟨678415205674267566801669182193615172871146156033413640109018,678415205674267566801669182193615172872713989067661571670036⟩,⟨618305832450696531923388716864482209609095244856543911566661,618305832450696531923388716864482209613220042839586747645884⟩,⟨531118619716947992628349843654691070637272774878306320390454,531118619716947992628349843654691070646570366120819026538837⟩,⟨396002645722721179150766614192561619618249637172039253602498,396002645722721179150766614192561619635318833779389579120864⟩,⟨322376775109518814447089027415134972132156534594011690699993,322376775109518814447089027415134972184583794539799804257016⟩,⟨249340104141176892137268477371642448171208978685915357663512,249340104141176892137268477371642448311738226224081794866797⟩,⟨161188387554759407223544513707567485938563091491965219531946,161188387554759407223544513707567486219807073074939746529919⟩,⟨80594193777379703611772256853783742700101023778505468056120,80594193777379703611772256853783743379084058504947252865295⟩,⟨60923483957341719869348709875778709755675543602242666575828,60923483957341719869348709875778711667950375005668657263054⟩,⟨30461741978670859934674354937889353666098999095807345841892,30461741978670859934674354937889357045713960208148120136144⟩,⟨0,1414213562373095048801688724210⟩]
def columnNorm1 : Fin 31 → RI := ![⟨87266462599716478846184538424430635672143594427054898665106,87266462599716478846184538424430635672143594427117601337995⟩,⟨174532925199432957692369076848861271344287188853333471253250,174532925199432957692369076848861271344287188855012651161463⟩,⟨230885357835168934485899363490153922498509522301980569750590,230885357835168934485899363490153922498509522317758798707807⟩,⟨349065850398865915384738153697722542688574377637516152766500,349065850398865915384738153697722542688574377779179742804972⟩,⟨604599788078072616864692752547385244094688748942626554943070,604599788078072616864692752547385244094688749785875573385138⟩,⟨799810340988467126876038007198748545324860959557217215835297,799810340988467126876038007198748545324860963076211678134275⟩,⟨841567288458919067010225831306546319264563556747273074484901,841567288458919067010225831306546319264563574230557607340500⟩,⟨1047197551196597746154214461093167628065723102389279197529987,1047197551196597746154214461093167628065723163860815276146183⟩,⟨1360349523175663387945558693231616799213049613052745882550074,1360349523175663387945558693231616799213049759086393132190772⟩,⟨1396263401595463661538952614790890170754297214403941328507917,1396263401595463661538952614790890170754297807262854533371029⟩,⟨1468049128943225571497541917796366597876895808722092677338722,1468049128943225571497541917796366597876897509424596229132678⟩,⟨1847082862681351475887194907921231379988074159165407245474925,1847082862681351475887194907921231379988078197792525662564648⟩,⟨2057712840761618402094354610227796016361550307732177211323861,2057712840761618402094354610227796016361559960281342547182935⟩,⟨1982312971063989413952358469910289597780828498080522106287771,1982312971063989413952358469910289597780856615794145461973392⟩,⟨2226577756789257619293607026524269350002209065363977837374947,2226577756789257619293607026524269350002276711749921927899317⟩,⟨2418399152312290467458771010189540976378695332960241652105070,2418399152312290467458771010189540976378814661953788024188020⟩,⟨2226577756789257619293607026524269350002043893818239539302161,2226577756789257619293607026524269350002441883295660225922483⟩,⟨1982312971063989413952358469910289597780352993845568862374318,1982312971063989413952358469910289597781332120029098705817816⟩,⟨2057712840761618402094354610227796016360546983431155534306091,2057712840761618402094354610227796016362563284582364224129097⟩,⟨1847082862681351475887194907921231379985486371192532216667502,1847082862681351475887194907921231379990665985765400691329149⟩,⟨1468049128943225571497541917796366597869955823740943546159753,1468049128943225571497541917796366597883837494405745360313412⟩,⟨1396263401595463661538952614790890170738089596623265289376636,1396263401595463661538952614790890170770505425043530572549406⟩,⟨1360349523175663387945558693231616799184404948011463729859735,1360349523175663387945558693231616799241694424127675284978566⟩,⟨1047197551196597746154214461093167627971256272388227353634324,1047197551196597746154214461093167628160189993861867120158510⟩,⟨841567288458919067010225831306546319029770977253151334814972,841567288458919067010225831306546319499356153724679347120105⟩,⟨799810340988467126876038007198748544852890094178541058738768,799810340988467126876038007198748545796831828454887835295228⟩,⟨604599788078072616864692752547385242765439036288732193566005,604599788078072616864692752547385245423938462439769934718452⟩,⟨349065850398865915384738153697722539479481709497598129419816,349065850398865915384738153697722545897667045919097766027103⟩,⟨230885357835168934485899363490153915857375526686917617458237,230885357835168934485899363490153929139643517932821750832508⟩,⟨174532925199432957692369076848861252640324435398652272908656,174532925199432957692369076848861290048249942309693849318579⟩,⟨87266462599716478846184538424430602616125016144734836677462,87266462599716478846184538424430668728162172709437663280405⟩]
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
def columnNorm10 : Fin 31 → RI := ![⟨0,1414213562373095048801688724210⟩,⟨30461741978670859934674354937889355355906479651966641302814,30461741978670859934674354937889355355906479651988824550542⟩,⟨31536315884315853390999878428302333425440866305774550250524,31536315884315853390999878428302333425440866306300884579157⟩,⟨34560146196103600878982045286127366966856544266058332471169,34560146196103600878982045286127366966856544270887765994669⟩,⟨47492782818357154345708764325992805006950003584162300719976,47492782818357154345708764325992805006950003625554973521394⟩,⟨34560146196103600878982045286127366966856544159786191865407,34560146196103600878982045286127366966856544377159245823379⟩,⟨86158817279492339927871122668758089999010693986567965029715,86158817279492339927871122668758089999010695419556617554578⟩,⟨96673671384360999133402560474475656972214431682166833010678,96673671384360999133402560474475656972214437489879441585037⟩,⟨63072631768631706781999756856604666850881723613205870542097,63072631768631706781999756856604666850881741610945050975249⟩,⟨136229051554733983397184254583827937434461092518280531026319,136229051554733983397184254583827937434461157424986179812486⟩,⟨121846967914683439738697419751557421423625825170236288062517,121846967914683439738697419751557421423626012045584256757208⟩,⟨76815453016641648309168390699834085325375346232449246915743,76815453016641648309168390699834085325375834167309150041234⟩,⟨192656972297928369260602050149325671188621657935561722334247,192656972297928369260602050149325671188622804239226028825926⟩,⟨105837772972042716033726772861051122510681021429219709952551,105837772972042716033726772861051122510684281382227132133822⟩,⟨93572280610262067065966106768728772253805793671854167824016,93572280610262067065966106768728772253811821185612900191293⟩,⟨276342732482287226674012236396064904389240337319660244966485,276342732482287226674012236396064904389255033361541610817250⟩,⟨93572280610262067065966106768728772253790993896155031107606,93572280610262067065966106768728772253826620961312036919085⟩,⟨105837772972042716033726772861051122510625203642528625443744,105837772972042716033726772861051122510740099168918216649616⟩,⟨192656972297928369260602050149325671188499440928536484312526,192656972297928369260602050149325671188745021246251266877942⟩,⟨76815453016641648309168390699834085325047403662397215553816,76815453016641648309168390699834085325703776737361181463214⟩,⟨121846967914683439738697419751557421422797378525267907677953,121846967914683439738697419751557421424454458690552637174845⟩,⟨136229051554733983397184254583827937432432313547594269974308,136229051554733983397184254583827937436489936395672440905924⟩,⟨63072631768631706781999756856604666846552017026806064006577,63072631768631706781999756856604666855211448197344857603250⟩,⟨96673671384360999133402560474475656960209339343923335665641,96673671384360999133402560474475656984219529828122938962327⟩,⟨86158817279492339927871122668758089969871575172152876633099,86158817279492339927871122668758090028149814233971706001717⟩,⟨34560146196103600878982045286127366915563165627069402091933,34560146196103600878982045286127367018149922909876035715733⟩,⟨47492782818357154345708764325992804868007529718380489952115,47492782818357154345708764325992805145892477491336784275790⟩,⟨34560146196103600878982045286127366667896824583290926658062,34560146196103600878982045286127367265816263953655171948791⟩,⟨31536315884315853390999878428302332568178642134568934873611,31536315884315853390999878428302334282703090477506500093705⟩,⟨30461741978670859934674354937889353666114947901923378200483,30461741978670859934674354937889357045698011402032087616253⟩,⟨0,1414213562373095048801688724210⟩]
def columnNorm11 : Fin 31 → RI := ![⟨87266462599716478846184538424430635672143594427054328781000,87266462599716478846184538424430635672143594427118171222193⟩,⟨90344890078133842395787143554592910283026175443935726366896,90344890078133842395787143554592910283026175445444160571229⟩,⟨129889037239570551117414204759015323383473557580096472528134,129889037239570551117414204759015323383473557599100314341653⟩,⟨127766968839603350739977299424831350703057185757107410048084,127766968839603350739977299424831350703057185898795734197375⟩,⟨0,1414213562373095048801688724210⟩,⟨156481939819553171327317355893223406306675027680253771713903,156481939819553171327317355893223406306675031360998455630114⟩,⟨224974411845142149360084610202039951661305006376296462630395,224974411845142149360084610202039951661305022262170291874885⟩,⟨221298881559262564644760854272891191985517169380103859064391,221298881559262564644760854272891191985517214380686719633541⟩,⟨151149947019518154216173188136846311023672114322962264992941,151149947019518154216173188136846311023672260359166015903383⟩,⟨255533937679206701479954598849662701406114075224558512926942,255533937679206701479954598849662701406114668087248254753846⟩,⟨323215559830129485278637678619326986029415082391540264214554,323215559830129485278637678619326986029416652828740041796030⟩,⟨246826829897687013723104499447816316589699261007898817294852,246826829897687013723104499447816316589703148922740529147596⟩,⟨226186316238692936667076754722272155071634464753004140506536,226186316238692936667076754722272155071644642365833741922347⟩,⟨294248399340706193014777770771964116182524532830967762742705,294248399340706193014777770771964116182550650787111299239049⟩,⟨534450853538328206436105086411340363132813927829570423937793,534450853538328206436105086411340363132873561820264339413066⟩,⟨0,1414213562373095048801688724210⟩,⟨534450853538328206436105086411340363132668320047028112376436,534450853538328206436105086411340363133019169602806650907973⟩,⟨294248399340706193014777770771964116182082846793623273025881,294248399340706193014777770771964116182992336824455789027879⟩,⟨226186316238692936667076754722272155070576565207119085507519,226186316238692936667076754722272155072702541911718796907271⟩,⟨246826829897687013723104499447816316587208038801461655686149,246826829897687013723104499447816316592194371129177690697490⟩,⟨323215559830129485278637678619326986023006686872639960011424,323215559830129485278637678619326986035825048347640346033064⟩,⟨255533937679206701479954598849662701389906426388495690457874,255533937679206701479954598849662701422322316923311077182155⟩,⟨151149947019518154216173188136846310995026831483766479928073,151149947019518154216173188136846311052317543198361800898562⟩,⟨221298881559262564644760854272891191916363302003667254356914,221298881559262564644760854272891192054671081757123324340037⟩,⟨224974411845142149360084610202039951447969160480548751154795,224974411845142149360084610202039951874640868157918003323517⟩,⟨156481939819553171327317355893223405813019210942811295258592,156481939819553171327317355893223406800330848098440932017916⟩,⟨0,1414213562373095048801688724210⟩,⟨127766968839603350739977299424831347493958368650799960941190,127766968839603350739977299424831353912156003005103183334970⟩,⟨129889037239570551117414204759015315388841488673623372937077,129889037239570551117414204759015331378105626505573413886489⟩,⟨90344890078133842395787143554592893513260190416248267812566,90344890078133842395787143554592927052792160473131619059352⟩,⟨87266462599716478846184538424430602616437006733811546625016,87266462599716478846184538424430668727850182120360953386410⟩]
def columnNorm12 : Fin 31 → RI := ![⟨0,1414213562373095048801688724210⟩,⟨30461741978670859934674354937889355355906479651957104676602,30461741978670859934674354937889355355906479651998361176753⟩,⟨60923483957341719869348709875778710711812959303539005160295,60923483957341719869348709875778710711812959304371479952972⟩,⟨80594193777379703611772256853783743039592541137676284933993,80594193777379703611772256853783743039592541145774520633601⟩,⟨60923483957341719869348709875778710711812959266034619129042,60923483957341719869348709875778710711812959341875477242866⟩,⟨80594193777379703611772256853783743039592540895988471189822,80594193777379703611772256853783743039592541387462963944179⟩,⟨60923483957341719869348709875778710711812958064390975559946,60923483957341719869348709875778710711812960543518721239459⟩,⟨60923483957341719869348709875778710711812953708594539869494,60923483957341719869348709875778710711812964899316485383944⟩,⟨60923483957341719869348709875778710711812936643299237830289,60923483957341719869348709875778710711812981964612232196605⟩,⟨80594193777379703611772256853783743039592468462446857128088,80594193777379703611772256853783743039592613821003916265414⟩,⟨60923483957341719869348709875778710711812739369725119313472,60923483957341719869348709875778710711813179238186131255215⟩,⟨60923483957341719869348709875778710711812206372699793261594,60923483957341719869348709875778710711813712235211451430674⟩,⟨105522569588223266140388721305082390652624542336887334707103,105522569588223266140388721305082390652631446754155373455761⟩,⟨105522569588223266140388721305082390652619597619175011928417,105522569588223266140388721305082390652636391471868157673498⟩,⟨105522569588223266140388721305082390652590058426105521926473,105522569588223266140388721305082390652665930664934278997321⟩,⟨274155677808037739412069194441004198203066641363356585280102,274155677808037739412069194441004198203249992372241963175036⟩,⟨105522569588223266140388721305082390652214873593569600608888,105522569588223266140388721305082390653041115497470200345975⟩,⟨105522569588223266140388721305082390651630549450926697656654,105522569588223266140388721305082390653625439640116471983865⟩,⟨105522569588223266140388721305082390648134428114366174076777,105522569588223266140388721305082390657121560976676534080259⟩,⟨60923483957341719869348709875778710700964481014622315007670,60923483957341719869348709875778710722661437593288929741439⟩,⟨60923483957341719869348709875778710676035979809545267885120,60923483957341719869348709875778710747589938798365982657650⟩,⟨80594193777379703611772256853783742901432874270405802983047,80594193777379703611772256853783743177752208013044970371221⟩,⟨60923483957341719869348709875778710180278472153554724900632,60923483957341719869348709875778711243347446454356745171531⟩,⟨60923483957341719869348709875778708958877564075172727750445,60923483957341719869348709875778712464748354532738297435236⟩,⟨60923483957341719869348709875778704930847536079860246439425,60923483957341719869348709875778716492778382528049450291114⟩,⟨80594193777379703611772256853783723352817227834155334344315,80594193777379703611772256853783762726367854449296100755763⟩,⟨60923483957341719869348709875778647838073024834467091184905,60923483957341719869348709875778773585552893773443005112770⟩,⟨80594193777379703611772256853783565298413504662546847628721,80594193777379703611772256853783920780771577620903957909820⟩,⟨60923483957341719869348709875778026897452588438604045345585,60923483957341719869348709875779394526173330169306439769316⟩,⟨30461741978670859934674354937887100220216601328159578119852,30461741978670859934674354937891610491596357975795887820449⟩,⟨0,1414213562373095048801688724210⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def tailFiniteEnvelope (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, tailEnvelopeSum 1 0 j * ‖finiteColumn ⟨c.val,by omega⟩ j‖
end AtomicTriangular.Construction
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
def boundC : Fin 22 → RI := ![⟨6983430325648370090762786336118446593363754,6983430325648370090762786446578740417141912⟩,⟨6856113601763651669234484249463260417292237909,6856113601763651669234484249463263003483720803⟩,⟨6980275474701897361264833427827823165781882,6980275474701897361264833538288127294569656⟩,⟨6849926501624327130340125007838659162779128828,6849926501624327130340125007838751568239066090⟩,⟨6973598786895930262447651247794129162920230,6973598786895930262447651358254938264699275⟩,⟨6836835820083327838570406946101411437962929601,6836835820083327838570406946107411399810476915⟩,⟨6970127717751114871303779034145933886275183,6970127717751114871303779144607310934352254⟩,⟨6830032419816511259075261648126221145691191044,6830032419816511259075261648139565050473184385⟩,⟨6966603083247449730494732527001762407925335,6966603083247449730494732637462168998477775⟩,⟨6823126181462009803004838304747855282887858411,6823126181462009803004838304749027480297356046⟩,⟨6973598786155837885597122670431812071336839,6973598786155837885597122780892105895067075⟩,⟨6836835803450007218291346535708063526022658801,6836835803450007218291346535708066111748162278⟩,⟨6983430319365317341592722342903761446494632,6983430319365317341592722453364570599057920⟩,⟨6856113562673563870668110733543919108677854686,6856113562673563870668110733549917183576988372⟩,⟨6986430469537304015669954082576071774519466,6986430469537304015669954193037449039042045⟩,⟨6861998095658831191648932715642117935687677355,6861998095658831191648932715655459086026521348⟩,⟨6994280707523134943003159481072253806359477,6994280707523134943003159591532660388642822⟩,⟨6877399299610182510026301010869972298375284114,6877399299610182510026301010871144536623494991⟩,⟨7000003726719105447955797071924050152776533,7000003726719105447955797182384354282597204⟩,⟨6888630442760375097555168696099136027582442669,6888630442760375097555168696099228441876634200⟩,⟨7002436798840667900299665935692288640605379,7002436798840667900299666046153097865828986⟩,⟨6893406056783168904034913493915297148668338947,6893406056783168904034913493921298545869113913⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_JetEnvelopeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma norm_transformedWave (k v t : ℝ) (n : ℤ) :
    ‖transformedWave k v t n‖ = ‖lambda k t‖ * Real.exp (-frequencyDecay k v t*n) := by
  rw [transformedWave,norm_mul,Complex.norm_exp]
  congr 2
  rw [show I*Real.pi*zeta k v t*(n:ℂ) = (I*Real.pi*zeta k v t)*(n:ℂ) by rfl,
    Complex.mul_re,Complex.intCast_re,Complex.intCast_im,mul_zero,sub_zero,wavePhase_re]
  unfold frequencyDecay
  ring
lemma jetMultiplier_pair_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    (∑ d : Fin 2, ‖jetMultiplier k v n d t‖) ≤ normJetEnvelope k v n t := by
  have hqi : ‖(Q n:ℂ)⁻¹‖=(Q n)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hb : ‖(D n:ℂ)-I*Real.pi*zeta k v t‖ ≤ |D n|+‖I*Real.pi*zeta k v t‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (D n:ℂ) (I*Real.pi*zeta k v t)
  simp only [Fin.sum_univ_two,jetMultiplier,Fin.val_zero,Fin.val_one,one_ne_zero,
    ↓reduceIte,norm_mul,norm_neg,norm_one,mul_one,hqi,norm_transformedWave]
  calc
    _ ≤ (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n)) +
        (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n))*(|D n|+‖I*Real.pi*zeta k v t‖) := by
      gcongr
    _ = _ := by unfold normJetEnvelope; ring
lemma jet_pair_bound (k v : ℝ) (n : ℤ) (hQ : 0<Q n) (S : Fin 31 → ℂ) :
    (∑ d : Fin 2, |jet k v n d S|) ≤
      ∑ j : Fin 31, normJetEnvelope k v n (frequency j)*‖S j‖ := by
  calc
    _ ≤ ∑ d : Fin 2, ∑ j : Fin 31, ‖jetMultiplier k v n d (frequency j)‖*‖S j‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply (Complex.abs_re_le_norm _).trans
      simpa only [norm_mul] using norm_sum_le (s:=Finset.univ)
        (fun j : Fin 31 => jetMultiplier k v n d (frequency j)*S j)
    _ = ∑ j : Fin 31, (∑ d : Fin 2, ‖jetMultiplier k v n d (frequency j)‖)*‖S j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (jetMultiplier_pair_bound k v (frequency j) n hQ) (norm_nonneg _))
lemma normJetEnvelope_nonneg (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    0≤normJetEnvelope k v n t := by unfold normJetEnvelope; positivity
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_TailEnvelopeSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma frequencyDecay_pos (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    0 < frequencyDecay (damping q) (damping v) t := by
  have hx := Xwave_antitone (damping_pos q) (abs_nonneg t) ht
  have he : Xwave (damping q) |t|=Xwave (damping q) t := by simp [Xwave,waveDen,sq_abs]
  rw [he] at hx
  have hb : damping v < damping q * Xwave (damping q) (5/6) := by
    fin_cases q <;> fin_cases v <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  unfold frequencyDecay
  exact mul_pos Real.pi_pos (sub_pos.mpr (hb.trans_le (mul_le_mul_of_nonneg_left hx (damping_pos q).le)))
lemma normJetEnvelope_enumerateTail (a : Fin 15) (l : ℕ) (k v t : ℝ) :
    normJetEnvelope k v (enumerateTail (a,l)).val.val t =
      normJetEnvelope k v (tailBase a) t * (Real.exp (-frequencyDecay k v t*36))^l := by
  unfold normJetEnvelope
  rw [Q_enumerateTail,D_enumerateTail]
  change _ * Real.exp (-frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ)) = _
  rw [show -frequencyDecay k v t * ((tailBase a + 36*(l:ℤ):ℤ):ℝ) =
    -frequencyDecay k v t*(tailBase a:ℝ) + (l:ℝ)*(-frequencyDecay k v t*36) by push_cast; ring,
    Real.exp_add,Real.exp_nat_mul]
  ring
lemma summable_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun l : ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) := by
  simp_rw [normJetEnvelope_enumerateTail]
  apply Summable.mul_left
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma tsum_envelope_period (q v : Fin 2) (a : Fin 15) {t : ℝ} (ht : |t|≤5/6) :
    (∑' l : ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail (a,l)).val.val t) =
    normJetEnvelope (damping q) (damping v) (tailBase a) t *
      (1-Real.exp (-frequencyDecay (damping q) (damping v) t*36))⁻¹ := by
  simp_rw [normJetEnvelope_enumerateTail]
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
  have hh := frequencyDecay_pos q v ht
  nlinarith
lemma summable_tailEnvelope (q v : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    Summable (fun n : TailNode => normJetEnvelope (damping q) (damping v) n.val.val t) := by
  apply (tailEnumeration.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => normJetEnvelope_nonneg _ _ _ _ (by
    have hh := FiniteCertificate.Q_node_bounds (enumerateTail p).val.val (enumerateTail p).val.property.2
    change 0 < Q (enumerateTail p).val.val
    linarith [hh.1]))).mpr
  exact ⟨fun a => summable_envelope_period q v a ht, (hasSum_fintype _).summable⟩
lemma tsum_tailEnvelope (q v : Fin 2) (j : Fin 31) :
    (∑' n : TailNode, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)) =
    tailEnvelopeSum q v j := by
  have ht : |frequency j|≤5/6 := abs_le.mpr (frequency_mem j)
  rw [←tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_tailEnvelope q v ht)
  change Summable (fun p : Fin 15 × ℕ => normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) at hs
  change (∑' p : Fin 15 × ℕ, normJetEnvelope (damping q) (damping v) (enumerateTail p).val.val (frequency j)) = _
  rw [hs.tsum_prod]
  simp_rw [tsum_envelope_period q v _ ht]
  rw [tsum_fintype,←Finset.sum_mul]
  rfl
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma Node.Qpos (n : Node) : 0<Q n.val := by
  have hh := FiniteCertificate.Q_node_bounds _ n.property.2
  linarith [hh.1]
lemma tail_atom_column_bounds (q v : Fin 2) (S : Fin 31 → ℂ) :
    Summable (fun p : TailNode × Fin 2 => |jet (damping q) (damping v) p.1.val.val p.2 S|) ∧
    (∑' p : TailNode × Fin 2, |jet (damping q) (damping v) p.1.val.val p.2 S|)  ≤ 
      ∑ j : Fin 31, tailEnvelopeSum q v j*‖S j‖ := by
  have hs (j : Fin 31) : Summable (fun n : TailNode =>
      normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem j))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun j _ => hs j)
  have hh := paired_summable_bound (fun n d => jet (damping q) (damping v) n.val.val d S)
    (fun n : TailNode => ∑ j : Fin 31, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖)
    hsum (fun n => jet_pair_bound _ _ _ n.val.Qpos S)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun j _ => hs j)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
end AtomicTriangular.Construction
end

end OAI
end


