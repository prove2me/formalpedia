-- Prove2me | Definitions.Def_OAIQ257X000
-- name    : OAIQ257X000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T03:31:41.43049+00:00
-- url     : https://prove2.me/theorems/c2656b23-ccac-4067-b938-ff67384ea157
-- title:
--   Definitions bundle OAIQ257X000 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 482 declarations of OpenAI's Lean: 223 definitions, 2 inductive types or structures and 257 theorems. The definitions and types are `OAI.AtomicTriangular.Constants.arctanPoly`, `OAI.AtomicTriangular.Constants.bStar`, `OAI.AtomicTriangular.Constants.eps`, `OAI.AtomicTriangular.Constants.pStar`, `OAI.AtomicTriangular.Construction.Bkernel`, `OAI.AtomicTriangular.Construction.JetVector`, `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.finiteEnvelopeSum`, `OAI.AtomicTriangular.Construction.finiteTailEnvelope`, `OAI.AtomicTriangular.Construction.frequencyDecay`, `OAI.AtomicTriangular.Construction.frequencyDistance`, `OAI.AtomicTriangular.Construction.fullTailW`, `OAI.AtomicTriangular.Construction.jetEnvelope`, `OAI.AtomicTriangular.Construction.jetVector`, `OAI.AtomicTriangular.Construction.normJetEnvelope`, `OAI.AtomicTriangular.Construction.spectralCVector`, `OAI.AtomicTriangular.Construction.spectralDVector`, `OAI.AtomicTriangular.Construction.tailJet`, `OAI.AtomicTriangular.Construction.tailJetVector`, `OAI.AtomicTriangular.FiniteCertificate.DBox1`, `OAI.AtomicTriangular.FiniteCertificate.DBox12`, `OAI.AtomicTriangular.FiniteCertificate.DBox13`, `OAI.AtomicTriangular.FiniteCertificate.DBox16`, `OAI.AtomicTriangular.FiniteCertificate.DBox19`, `OAI.AtomicTriangular.FiniteCertificate.DBox21`, `OAI.AtomicTriangular.FiniteCertificate.DBox3`, `OAI.AtomicTriangular.FiniteCertificate.DBox4`, `OAI.AtomicTriangular.FiniteCertificate.DBox7`, `OAI.AtomicTriangular.FiniteCertificate.DBox9`, `OAI.AtomicTriangular.FiniteCertificate.QBox0`, `OAI.AtomicTriangular.FiniteCertificate.QBox1`, `OAI.AtomicTriangular.FiniteCertificate.QBox12`, `OAI.AtomicTriangular.FiniteCertificate.QBox13`, `OAI.AtomicTriangular.FiniteCertificate.QBox16`, `OAI.AtomicTriangular.FiniteCertificate.QBox19`, `OAI.AtomicTriangular.FiniteCertificate.QBox21`, `OAI.AtomicTriangular.FiniteCertificate.QBox25`, `OAI.AtomicTriangular.FiniteCertificate.QBox27`, `OAI.AtomicTriangular.FiniteCertificate.QBox28`, `OAI.AtomicTriangular.FiniteCertificate.QBox3` and 185 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Certificate_JetMatrix`, `Triangular_Certificate_WaveExpData`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_PeriodicJets`, `Triangular_Construction_TailJetVector`, `Triangular_Envelope_Analytic`, `Triangular_Envelope_EnvelopeBoxes`, `Triangular_Envelope_EnvelopeNorm2`, `Triangular_Envelope_EnvelopeNorms`, `Triangular_Envelope_EnvelopePsiB`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_EnvelopeSumsBase`, `Triangular_Envelope_EnvelopeWaves`, `Triangular_Schwartz_SpectralCLM`, `Triangular_Schwartz_SpectralEnvelope`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ257X001`, `OAIQ257X003`, `OAIQ257X009` and `OAIQ257X012`; the statements `OAI.AtomicTriangular.Construction.Bkernel_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.columnTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox13_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox16_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox19_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox21_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.dBox7_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.envelopeSumBoxB_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullWTable_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.psiB1_mem_x`; the proofs of `OAI.AtomicTriangular.Construction.actualFiniteError_norm_x`, `OAI.AtomicTriangular.Construction.actualTail_full_equations_x`, `OAI.AtomicTriangular.Construction.actualTail_norm_x`, `OAI.AtomicTriangular.Construction.actual_interpolation_x`, `OAI.AtomicTriangular.FiniteCertificate.fullWTable_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.psiB1_mem_x`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian

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
namespace AtomicTriangular.Construction

theorem phase_add (s t : ℂ) : phase (s+t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  ring

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_neg_mul (s : ℂ) : phase (-s) * phase s = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

theorem sineFactor_sq (a : Fin 15) (s : ℂ) :
    sineFactor a s ^ 2 = 2 - phase ((residue a : ℂ)-s) -
      phase (s-(residue a : ℂ)) := by
  let z : ℂ := (kappa : ℂ) * (s-(residue a : ℂ))
  have hpos : phase (s-(residue a : ℂ)) = Complex.exp ((2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  have hneg : phase ((residue a : ℂ)-s) = Complex.exp (-(2*z)*Complex.I) := by
    unfold phase z kappa
    push_cast
    congr 1
    ring
  change (2 * Complex.sin z)^2 = _
  rw [hpos,hneg]
  have hc := Complex.two_cos (2*z)
  rw [Complex.cos_two_mul] at hc
  have hs := Complex.sin_sq_add_cos_sq z
  linear_combination 4*hs - hc

open Polynomial

theorem eval_atomFactor (a : Fin 15) (s : ℂ) :
    phase (-s) * (atomFactor a).eval (phase s) = sineFactor a s ^ 2 := by
  simp only [atomFactor,eval_sub,eval_add,eval_neg,eval_C,eval_mul,eval_X,eval_pow]
  rw [sineFactor_sq]
  have h1 : phase (-s) * phase (residue a) = phase ((residue a : ℂ)-s) := by
    rw [← phase_add]
    congr 1
    ring
  have h2 : phase (-residue a) * phase s = phase (s-(residue a : ℂ)) := by
    rw [← phase_add]
    congr 1
    ring
  have h0 := phase_neg_mul s
  linear_combination -h1 - phase (-residue a) * phase s * h0 - h2 + 2*h0

theorem P_spectral (s : ℂ) :
    P s = phase (-s)^15 * atomPolynomial.eval (phase s) := by
  unfold P atomPolynomial
  simp only [Polynomial.eval_prod]
  calc
    (∏ a : Fin 15, sineFactor a s ^ 2) =
        ∏ a : Fin 15, phase (-s) * (atomFactor a).eval (phase s) := by
      apply Finset.prod_congr rfl
      intro a ha
      exact (eval_atomFactor a s).symm
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem atomFactor_degree (a : Fin 15) : (atomFactor a).natDegree ≤ 2 := by
  unfold atomFactor
  compute_degree!

theorem atomPolynomial_degree : atomPolynomial.natDegree ≤ 30 := by
  unfold atomPolynomial
  apply le_trans (Polynomial.natDegree_prod_le _ _) 
  calc
    ∑ a : Fin 15, (atomFactor a).natDegree ≤ ∑ a : Fin 15, 2 :=
      Finset.sum_le_sum (fun a _ => atomFactor_degree a)
    _ = 30 := by norm_num

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma phase_nat_mul (n : ℕ) (s : ℂ) : phase s ^ n = phase (n*s) := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma phase_offset (j : Fin 31) (s : ℂ) :
    phase (-s)^15 * phase s^j.val =
      Complex.exp (Complex.I * (Real.pi:ℂ) * (frequency j:ℂ) * s) := by
  rw [phase_nat_mul, phase_nat_mul, ← phase_add]
  unfold phase frequency
  push_cast
  congr 1
  ring

lemma P_fourier (s : ℂ) : P s = ∑ j : Fin 31,
    fourierCoeff j * Complex.exp (Complex.I * (Real.pi:ℂ) * (frequency j:ℂ) * s) := by
  rw [P_spectral, Polynomial.eval_eq_sum_range' (n := 31) (by have := atomPolynomial_degree; omega)]
  rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change phase (-s)^15 * (fourierCoeff j * phase s^j.val) = _
  rw [mul_left_comm, phase_offset]

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

lemma wave_phase_integer (j : Fin 31) (n : ℤ) :
    exp (I*Real.pi*frequency j*(n:ℂ)) = phase ((((j.val:ℤ)-15)*n : ℤ):ℂ) := by
  unfold phase frequency
  push_cast
  congr 1
  ring

lemma waveDerivative_zero : waveDerivative 0 = P := by
  ext s
  simp only [waveDerivative, pow_zero, mul_one, P_fourier]

lemma hasDerivAt_waveDerivative (k : ℕ) (s : ℂ) :
    HasDerivAt (waveDerivative k) (waveDerivative (k+1) s) s := by
  have hh (j : Fin 31) : HasDerivAt
      (fun x : ℂ => fourierCoeff j * (I*Real.pi*frequency j)^k * exp (I*Real.pi*frequency j*x))
      (fourierCoeff j * (I*Real.pi*frequency j)^(k+1) * exp (I*Real.pi*frequency j*s)) s := by
    have hj := ((hasDerivAt_id s).const_mul (I*(Real.pi:ℂ)*(frequency j:ℂ))).cexp.const_mul
      (fourierCoeff j * (I*Real.pi*frequency j)^k)
    simpa only [mul_one, one_mul, pow_succ, mul_assoc, id_eq, mul_comm, mul_left_comm] using hj
  exact HasDerivAt.sum (u := Finset.univ) (fun j _ => hh j)

lemma waveDerivative_eq_iterated (k : ℕ) : waveDerivative k = iteratedDeriv k P := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using waveDerivative_zero
  | succ k hk =>
    rw [iteratedDeriv_succ, ← hk]
    exact funext fun s => (hasDerivAt_waveDerivative k s).deriv.symm

end AtomicTriangular.Construction

namespace AtomicTriangular.Interval

def scale : ℤ := 10^60
lemma scale_pos : (0:ℝ) < (scale:ℤ) := by norm_num [scale]
lemma scale_int_pos : 0 < scale := by norm_num [scale]

structure RI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def RI.Mem (a : RI) (x : ℝ) : Prop := (a.lo:ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ a.hi

def RI.point (n : ℤ) : RI := ⟨scale*n,scale*n⟩
def RI.add (a b : RI) : RI := ⟨a.lo+b.lo,a.hi+b.hi⟩
def RI.neg (a : RI) : RI := ⟨-a.hi,-a.lo⟩
def RI.sub (a b : RI) : RI := a.add b.neg

def imin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def imax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)
def RI.mul (a b : RI) : RI :=
  ⟨imin4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) / scale,
   imax4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi) / scale + 1⟩

def RI.divNat (a : RI) (n : ℕ) : RI := ⟨a.lo/n,a.hi/n+1⟩
def RI.widen (a : RI) (r : ℤ) : RI := ⟨a.lo-r,a.hi+r⟩

def RI.pow (a : RI) : ℕ → RI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

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

lemma mul_bounds {a b x t : ℝ} (h : a ≤ x ∧ x ≤ b) :
    min (a*t) (b*t) ≤ x*t ∧ x*t ≤ max (a*t) (b*t) := by
  rcases le_total 0 t with ht | ht
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right h.1 ht),
      (mul_le_mul_of_nonneg_right h.2 ht).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right h.2 ht),
      (mul_le_mul_of_nonpos_right h.1 ht).trans (le_max_left _ _)⟩

lemma four_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hxy := mul_bounds (t := y) hx
  have ha := mul_bounds (t := a) hy
  have hb := mul_bounds (t := b) hy
  simp only [mul_comm c,mul_comm d,mul_comm y] at ha hb
  constructor
  · apply le_trans _ hxy.1
    exact le_min ((min_le_left _ _).trans ha.1) ((min_le_right _ _).trans hb.1)
  · apply le_trans hxy.2
    exact max_le (ha.2.trans (le_max_left _ _)) (hb.2.trans (le_max_right _ _))

lemma div_floor_bounds (a n : ℤ) (hn : 0 < n) :
    ((a/n:ℤ):ℝ)*(n:ℝ) ≤ a ∧ (a:ℝ) ≤ ((a/n+1:ℤ):ℝ)*(n:ℝ) := by
  constructor
  · exact_mod_cast Int.ediv_mul_le a (ne_of_gt hn)
  · exact_mod_cast (Int.lt_ediv_add_one_mul_self a hn).le

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

structure CI where
  re : RI
  im : RI
  deriving DecidableEq, Repr

def CI.Mem (a : CI) (z : ℂ) : Prop := a.re.Mem z.re ∧ a.im.Mem z.im

def CI.ofReal (a : RI) : CI := ⟨a,RI.point 0⟩
def CI.point (n : ℤ) : CI := .ofReal (.point n)
def CI.imag : CI := ⟨RI.point 0,RI.point 1⟩
def CI.add (a b : CI) : CI := ⟨a.re.add b.re,a.im.add b.im⟩
def CI.neg (a : CI) : CI := ⟨a.re.neg,a.im.neg⟩
def CI.sub (a b : CI) : CI := a.add b.neg

def CI.mul (a b : CI) : CI :=
  ⟨(a.re.mul b.re).sub (a.im.mul b.im), (a.re.mul b.im).add (a.im.mul b.re)⟩
def CI.conj (a : CI) : CI := ⟨a.re,a.im.neg⟩
def CI.divNat (a : CI) (n : ℕ) : CI := ⟨a.re.divNat n,a.im.divNat n⟩
def CI.widen (a : CI) (r : ℤ) : CI := ⟨a.re.widen r,a.im.widen r⟩
def CI.normSq (a : CI) : RI := (a.re.mul a.re).add (a.im.mul a.im)

def CI.pow (a : CI) : ℕ → CI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

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

def RI.abs (a : RI) : RI := ⟨max 0 (max a.lo (-a.hi)), max a.hi (-a.lo)⟩
def RI.inv (a : RI) : RI := if a.hi < 0 then a.neg.invPos.neg else a.invPos

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval

def RI.sum {ι : Type*} [Fintype ι] (v : ι → RI) : RI :=
  ⟨∑ i, (v i).lo, ∑ i, (v i).hi⟩

lemma RI.mem_sum {ι : Type*} [Fintype ι] {v : ι → RI} {x : ι → ℝ}
    (hv : ∀ i, (v i).Mem (x i)) : (RI.sum v).Mem (∑ i, x i) := by
  constructor
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).1
  · simp only [RI.sum, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hv i).2

def CI.sum {ι : Type*} [Fintype ι] (v : ι → CI) : CI :=
  ⟨RI.sum (fun i => (v i).re), RI.sum (fun i => (v i).im)⟩

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
namespace AtomicTriangular.Constants

def eps : ℝ := (10^80)⁻¹
def pStar : ℝ := 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899
def bStar : ℝ := 0.86602540378443864676372317075293618347140262690519031402790348972596650845440001

def arctanPoly (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (-1)^j*x^(2*j+1)/(2*j+1)

lemma arctan_bracket {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x < 1) (n : ℕ) :
    arctanPoly x (2*n) ≤ Real.arctan x ∧
      Real.arctan x ≤ arctanPoly x (2*n) + x^(4*n+1)/(4*n+1) := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/(2*j+1)) := by
    intro j k hjk
    apply div_le_div₀ (pow_nonneg h₀ _)
      (pow_le_pow_of_le_one h₀ h₁.le (by omega)) (by positivity)
    exact_mod_cast (by omega : 2*j+1 ≤ 2*k+1)
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n,
      (-1:ℝ)^j * (x^(2*j+1)/(2*j+1))) atTop (𝓝 (Real.arctan x)) := by
    simpa only [mul_div_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg h₀])).tendsto_sum_nat
  constructor
  · simpa only [arctanPoly, mul_div_assoc] using ha.alternating_series_le_tendsto ht n
  · have hh := ha.tendsto_le_alternating_series ht n
    simpa [arctanPoly, sum_range_succ, mul_div_assoc, ← mul_assoc, show (2:ℝ)*2=4 by norm_num] using hh

lemma arctanPoly_inv5 : arctanPoly (1/5) 66 =
    (1127735820047281249826929962540366709009681070146611148630124134909087293535356022585063476519722124011352752446574182801704731339148829291186 : ℝ) / 5713075921793397351900334790776425890382017146109705783051183673650632561398172069707387162692372481291591679308794482494704425334930419921875 := by
  norm_num [arctanPoly, Finset.sum_range_succ]

lemma arctanPoly_inv239 : arctanPoly (1/239) 66 =
    (1118499394876416155561248293203315319858384148339754901282838013788591793901685995599875876925744187341881465177415079642435790204501443414217256735370408712354720598117442228707319810097027336706847276448482833107456896007088774973302196447103862002632135039862371139157305730782208439937297739381319965159523409065323737874075361079721743262198339765260034519498 : ℝ) / 267322915339442907721699424219844204360421434646325545345832816547242287762014829735766747100513282387541656695398803852049344802256469797061373857157082424828915581864219799259751119529925859323776796465869821218865822100577138580956944108601031719877043720686956487215878943801043900609923763261313848030486279699763172497745026116723198663028174351830029321704625 := by
  norm_num [arctanPoly, Finset.sum_range_succ]

theorem pStar_bracket : pStar < Real.pi ∧ Real.pi < pStar + eps := by
  have h₅ := arctan_bracket (x := 1/5) (by norm_num) (by norm_num) 33
  have h₂₃₉ := arctan_bracket (x := 1/239) (by norm_num) (by norm_num) 33
  norm_num only [show 2*33 = (66:ℕ) by rfl, show 4*33+1 = (133:ℕ) by rfl] at h₅ h₂₃₉
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [inv_eq_one_div, inv_eq_one_div] at hm
  have hl : pStar < 16*arctanPoly (1/5) 66 -
      4*(arctanPoly (1/239) 66 + (1/239:ℝ)^133/133) := by
    rw [arctanPoly_inv5, arctanPoly_inv239]
    norm_num [pStar]
  have hu : 16*(arctanPoly (1/5) 66 +(1/5:ℝ)^133/133) -
      4*arctanPoly (1/239) 66 < pStar + eps := by
    rw [arctanPoly_inv5, arctanPoly_inv239]
    norm_num [pStar, eps]
  constructor <;> linarith

end AtomicTriangular.Constants

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial

def piBox : RI :=
  ⟨3141592653589793238462643383279502884197169399375100000000000,
   3141592653589793238462643383279502884197169399375110000000000⟩

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

def partialPolynomial (n : ℕ) : Polynomial ℂ :=
  ∏ a ∈ Finset.univ.filter (fun a : Fin 15 => a.val < n), atomFactor a

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

lemma coeff_X_mul' (p : Polynomial ℂ) (n : ℕ) :
    (X*p).coeff n = if n=0 then 0 else p.coeff (n-1) := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul]

lemma coeff_X_sq_mul (p : Polynomial ℂ) (n : ℕ) :
    (X^2*p).coeff n = if n<2 then 0 else p.coeff (n-2) := by
  rw [pow_two, mul_assoc, coeff_X_mul']
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n => simp [coeff_X_mul]

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

def coeffStep (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  ((e.neg.mul (v j)).add (if h : j.val=0 then CI.point 0
    else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩))

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
def phaseBox0 : CI := ⟨⟨999999999999999999999999999999999999999999999999999999935489,1000000000000000000000000000000000000000000000000000000066558⟩,⟨-63486,68606⟩⟩
lemma phaseBox0_calc : (phaseInputBox 0).exp = phaseBox0 := by decide +kernel
lemma phaseBox0_mem : phaseBox0.Mem (phase ((0:ℤ):ℂ)) := by
  rw [← phaseBox0_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 0) (by decide +kernel)
def phaseBox1 : CI := ⟨⟨984807753012208059366743024589523013670643251719842378260439,984807753012208059366743024589523013670643251719842475161964⟩,⟨173648177666930348851716626769314796000375677184069063062132,173648177666930348851716626769314796000375677184069621580864⟩⟩
lemma phaseBox1_calc : (phaseInputBox 1).exp = phaseBox1 := by decide +kernel
lemma phaseBox1_mem : phaseBox1.Mem (phase ((1:ℤ):ℂ)) := by
  rw [← phaseBox1_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 1) (by decide +kernel)
def phaseBox2 : CI := ⟨⟨939692620785908384054109277324731469936208134264464471960044,939692620785908384054109277324731469936208134264464856618258⟩,⟨342020143325668733044099614682259580763083367514159975976700,342020143325668733044099614682259580763083367514161109522372⟩⟩
lemma phaseBox2_calc : (phaseInputBox 2).exp = phaseBox2 := by decide +kernel
lemma phaseBox2_mem : phaseBox2.Mem (phase ((2:ℤ):ℂ)) := by
  rw [← phaseBox2_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 2) (by decide +kernel)
def phaseBox3 : CI := ⟨⟨866025403784438646763723170752936183471402626905189954512964,866025403784438646763723170752936183471402626905190810370953⟩,⟨499999999999999999999999999999999999999999999999999011153642,500000000000000000000000000000000000000000000000000751856976⟩⟩
lemma phaseBox3_calc : (phaseInputBox 3).exp = phaseBox3 := by decide +kernel
lemma phaseBox3_mem : phaseBox3.Mem (phase ((3:ℤ):ℂ)) := by
  rw [← phaseBox3_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 3) (by decide +kernel)
def phaseBox4 : CI := ⟨⟨766044443118978035202392650555416673935832457080394614080696,766044443118978035202392650555416673935832457080396112163801⟩,⟨642787609686539326322643409907263432907559884205680453940922,642787609686539326322643409907263432907559884205682847200174⟩⟩
lemma phaseBox4_calc : (phaseInputBox 4).exp = phaseBox4 := by decide +kernel
lemma phaseBox4_mem : phaseBox4.Mem (phase ((4:ℤ):ℂ)) := by
  rw [← phaseBox4_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 4) (by decide +kernel)
def phaseBox5 : CI := ⟨⟨642787609686539326322643409907263432907559884205680817903044,642787609686539326322643409907263432907559884205683112135181⟩,⟨766044443118978035202392650555416673935832457080393548649076,766044443118978035202392650555416673935832457080396649890976⟩⟩
lemma phaseBox5_calc : (phaseInputBox 5).exp = phaseBox5 := by decide +kernel
lemma phaseBox5_mem : phaseBox5.Mem (phase ((5:ℤ):ℂ)) := by
  rw [← phaseBox5_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 5) (by decide +kernel)
def phaseBox6 : CI := ⟨⟨499999999999999999999999999999999999999999999999998625582869,500000000000000000000000000000000000000000000000001848404295⟩,⟨866025403784438646763723170752936183471402626905188241914124,866025403784438646763723170752936183471402626905192112487718⟩⟩
lemma phaseBox6_calc : (phaseInputBox 6).exp = phaseBox6 := by decide +kernel
lemma phaseBox6_mem : phaseBox6.Mem (phase ((6:ℤ):ℂ)) := by
  rw [← phaseBox6_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 6) (by decide +kernel)
def phaseBox7 : CI := ⟨⟨342020143325668733044099614682259580763083367514158799320630,342020143325668733044099614682259580763083367514163057632021⟩,⟨939692620785908384054109277324731469936208134264462172730300,939692620785908384054109277324731469936208134264466875061792⟩⟩
lemma phaseBox7_calc : (phaseInputBox 7).exp = phaseBox7 := by decide +kernel
lemma phaseBox7_mem : phaseBox7.Mem (phase ((7:ℤ):ℂ)) := by
  rw [← phaseBox7_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 7) (by decide +kernel)
def phaseBox8 : CI := ⟨⟨173648177666930348851716626769314796000375677184067060768548,173648177666930348851716626769314796000375677184072432368187⟩,⟨984807753012208059366743024589523013670643251719839559295028,984807753012208059366743024589523013670643251719845151568286⟩⟩
lemma phaseBox8_calc : (phaseInputBox 8).exp = phaseBox8 := by decide +kernel
lemma phaseBox8_mem : phaseBox8.Mem (phase ((8:ℤ):ℂ)) := by
  rw [← phaseBox8_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 8) (by decide +kernel)
def phaseBox9 : CI := ⟨⟨-2854777273,3675745116⟩,⟨999999999999999999999999999999999999999999999999996734740088,1000000000000000000000000000000000000000000000000003265262478⟩⟩
lemma phaseBox9_calc : (phaseInputBox 9).exp = phaseBox9 := by decide +kernel
lemma phaseBox9_mem : phaseBox9.Mem (phase ((9:ℤ):ℂ)) := by
  rw [← phaseBox9_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 9) (by decide +kernel)
def phaseBox10 : CI := ⟨⟨-173648177666930348851716626769314796000375677184072788297342,-173648177666930348851716626769314796000375677184065087845911⟩,⟨984807753012208059366743024589523013670643251719838747234178,984807753012208059366743024589523013670643251719846248746530⟩⟩
lemma phaseBox10_calc : (phaseInputBox 10).exp = phaseBox10 := by decide +kernel
lemma phaseBox10_mem : phaseBox10.Mem (phase ((10:ℤ):ℂ)) := by
  rw [← phaseBox10_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 10) (by decide +kernel)
def phaseBox11 : CI := ⟨⟨-342020143325668733044099614682259580763083367514164579490877,-342020143325668733044099614682259580763083367514155734542861⟩,⟨939692620785908384054109277324731469936208134264460562604050,939692620785908384054109277324731469936208134264469046765440⟩⟩
lemma phaseBox11_calc : (phaseInputBox 11).exp = phaseBox11 := by decide +kernel
lemma phaseBox11_mem : phaseBox11.Mem (phase ((11:ℤ):ℂ)) := by
  rw [← phaseBox11_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 11) (by decide +kernel)
def phaseBox12 : CI := ⟨⟨-500000000000000000000000000000000000000000000000004489253604,-499999999999999999999999999999999999999999999999994562770708⟩,⟨866025403784438646763723170752936183471402626905185861538948,866025403784438646763723170752936183471402626905195313833830⟩⟩
lemma phaseBox12_calc : (phaseInputBox 12).exp = phaseBox12 := by decide +kernel
lemma phaseBox12_mem : phaseBox12.Mem (phase ((12:ℤ):ℂ)) := by
  rw [← phaseBox12_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 12) (by decide +kernel)
def phaseBox13 : CI := ⟨⟨-642787609686539326322643409907263432907559884205686789753345,-642787609686539326322643409907263432907559884205675882485247⟩,⟨766044443118978035202392650555416673935832457080390439298182,766044443118978035202392650555416673935832457080400814661650⟩⟩
lemma phaseBox13_calc : (phaseInputBox 13).exp = phaseBox13 := by decide +kernel
lemma phaseBox13_mem : phaseBox13.Mem (phase ((13:ℤ):ℂ)) := by
  rw [← phaseBox13_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 13) (by decide +kernel)
def phaseBox14 : CI := ⟨⟨-766044443118978035202392650555416673935832457080400710407312,-766044443118978035202392650555416673935832457080388960420236⟩,⟨642787609686539326322643409907263432907559884205676669856626,642787609686539326322643409907263432907559884205687889085620⟩⟩
lemma phaseBox14_calc : (phaseInputBox 14).exp = phaseBox14 := by decide +kernel
lemma phaseBox14_mem : phaseBox14.Mem (phase ((14:ℤ):ℂ)) := by
  rw [← phaseBox14_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 14) (by decide +kernel)
def phaseBox15 : CI := ⟨⟨-866025403784438646763723170752936183471402626905196181323615,-866025403784438646763723170752936183471402626905183762590658⟩,⟨499999999999999999999999999999999999999999999999994618824454,500000000000000000000000000000000000000000000000006566147044⟩⟩
lemma phaseBox15_calc : (phaseInputBox 15).exp = phaseBox15 := by decide +kernel
lemma phaseBox15_mem : phaseBox15.Mem (phase ((15:ℤ):ℂ)) := by
  rw [← phaseBox15_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 15) (by decide +kernel)
def phaseBox16 : CI := ⟨⟨-939692620785908384054109277324731469936208134264470823413628,-939692620785908384054109277324731469936208134264457943587609⟩,⟨342020143325668733044099614682259580763083367514155053298568,342020143325668733044099614682259580763083367514167575120924⟩⟩
lemma phaseBox16_calc : (phaseInputBox 16).exp = phaseBox16 := by decide +kernel
lemma phaseBox16_mem : phaseBox16.Mem (phase ((16:ℤ):ℂ)) := by
  rw [← phaseBox16_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 16) (by decide +kernel)
def phaseBox17 : CI := ⟨⟨-984807753012208059366743024589523013670643251719848835505828,-984807753012208059366743024589523013670643251719835732797643⟩,⟨173648177666930348851716626769314796000375677184063698304240,173648177666930348851716626769314796000375677184076603333880⟩⟩
lemma phaseBox17_calc : (phaseInputBox 17).exp = phaseBox17 := by decide +kernel
lemma phaseBox17_mem : phaseBox17.Mem (phase ((17:ℤ):ℂ)) := by
  rw [← phaseBox17_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 17) (by decide +kernel)
def phaseBox18 : CI := ⟨⟨-1000000000000000000000000000000000000000000000000006530375474,-999999999999999999999999999999999999999999999999993469625023⟩,⟨-5709403374,7351347078⟩⟩
lemma phaseBox18_calc : (phaseInputBox 18).exp = phaseBox18 := by decide +kernel
lemma phaseBox18_mem : phaseBox18.Mem (phase ((18:ℤ):ℂ)) := by
  rw [← phaseBox18_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 18) (by decide +kernel)
def phaseBox19 : CI := ⟨⟨-984807753012208059366743024589523013670643251719850175773758,-984807753012208059366743024589523013670643251719834962769522⟩,⟨-173648177666930348851716626769314796000375677184076234168892,-173648177666930348851716626769314796000375677184060833470644⟩⟩
lemma phaseBox19_calc : (phaseInputBox 19).exp = phaseBox19 := by decide +kernel
lemma phaseBox19_mem : phaseBox19.Mem (phase ((19:ℤ):ℂ)) := by
  rw [← phaseBox19_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 19) (by decide +kernel)
def phaseBox20 : CI := ⟨⟨-939692620785908384054109277324731469936208134264473669623711,-939692620785908384054109277324731469936208134264456220534602⟩,⟨-342020143325668733044099614682259580763083367514168657202328,-342020143325668733044099614682259580763083367514150885369606⟩⟩
lemma phaseBox20_calc : (phaseInputBox 20).exp = phaseBox20 := by decide +kernel
lemma phaseBox20_mem : phaseBox20.Mem (phase ((20:ℤ):ℂ)) := by
  rw [← phaseBox20_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 20) (by decide +kernel)
def phaseBox21 : CI := ⟨⟨-866025403784438646763723170752936183471402626905200655848102,-866025403784438646763723170752936183471402626905180930009073⟩,⟨-500000000000000000000000000000000000000000000000009235181440,-499999999999999999999999999999999999999999999999989105858860⟩⟩
lemma phaseBox21_calc : (phaseInputBox 21).exp = phaseBox21 := by decide +kernel
lemma phaseBox21_mem : phaseBox21.Mem (phase ((21:ℤ):ℂ)) := by
  rw [← phaseBox21_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 21) (by decide +kernel)
def phaseBox22 : CI := ⟨⟨-766044443118978035202392650555416673935832457080406888294869,-766044443118978035202392650555416673935832457080384893374795⟩,⟨-642787609686539326322643409907263432907559884205692234760934,-642787609686539326322643409907263432907559884205669808574574⟩⟩
lemma phaseBox22_calc : (phaseInputBox 22).exp = phaseBox22 := by decide +kernel
lemma phaseBox22_mem : phaseBox22.Mem (phase ((22:ℤ):ℂ)) := by
  rw [← phaseBox22_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 22) (by decide +kernel)
def phaseBox23 : CI := ⟨⟨-642787609686539326322643409907263432907559884205694695891306,-642787609686539326322643409907263432907559884205670491952222⟩,⟨-766044443118978035202392650555416673935832457080406878657306,-766044443118978035202392650555416673935832457080382264458734⟩⟩
lemma phaseBox23_calc : (phaseInputBox 23).exp = phaseBox23 := by decide +kernel
lemma phaseBox23_mem : phaseBox23.Mem (phase ((23:ℤ):ℂ)) := by
  rw [← phaseBox23_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 23) (by decide +kernel)
def phaseBox24 : CI := ⟨⟨-500000000000000000000000000000000000000000000000014096951365,-499999999999999999999999999999999999999999999999987799006330⟩,⟨-866025403784438646763723170752936183471402626905203089251490,-866025403784438646763723170752936183471402626905176444175326⟩⟩
lemma phaseBox24_calc : (phaseInputBox 24).exp = phaseBox24 := by decide +kernel
lemma phaseBox24_mem : phaseBox24.Mem (phase ((24:ℤ):ℂ)) := by
  rw [← phaseBox24_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 24) (by decide +kernel)
def phaseBox25 : CI := ⟨⟨-342020143325668733044099614682259580763083367514175810431770,-342020143325668733044099614682259580763083367514147589449286⟩,⟨-939692620785908384054109277324731469936208134264478478914456,-939692620785908384054109277324731469936208134264450007296924⟩⟩
lemma phaseBox25_calc : (phaseInputBox 25).exp = phaseBox25 := by decide +kernel
lemma phaseBox25_mem : phaseBox25.Mem (phase ((25:ℤ):ℂ)) := by
  rw [← phaseBox25_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 25) (by decide +kernel)
def phaseBox26 : CI := ⟨⟨-173648177666930348851716626769314796000375677184085513919999,-173648177666930348851716626769314796000375677184055596221926⟩,⟨-984807753012208059366743024589523013670643251719857237281372,-984807753012208059366743024589523013670643251719827188460900⟩⟩
lemma phaseBox26_calc : (phaseInputBox 26).exp = phaseBox26 := by decide +kernel
lemma phaseBox26_mem : phaseBox26.Mem (phase ((26:ℤ):ℂ)) := by
  rw [← phaseBox26_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 26) (by decide +kernel)
def phaseBox27 : CI := ⟨⟨-16899068771,14436150239⟩,⟨-1000000000000000000000000000000000000000000000000015667611120,-999999999999999999999999999999999999999999999999984332392110⟩⟩
lemma phaseBox27_calc : (phaseInputBox 27).exp = phaseBox27 := by decide +kernel
lemma phaseBox27_mem : phaseBox27.Mem (phase ((27:ℤ):ℂ)) := by
  rw [← phaseBox27_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 27) (by decide +kernel)
def phaseBox28 : CI := ⟨⟨173648177666930348851716626769314796000375677184051917148030,173648177666930348851716626769314796000375677184084341989196⟩,⟨-984807753012208059366743024589523013670643251719858787552808,-984807753012208059366743024589523013670643251719826493551508⟩⟩
lemma phaseBox28_calc : (phaseInputBox 28).exp = phaseBox28 := by decide +kernel
lemma phaseBox28_mem : phaseBox28.Mem (phase ((28:ℤ):ℂ)) := by
  rw [← phaseBox28_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 28) (by decide +kernel)
def phaseBox29 : CI := ⟨⟨342020143325668733044099614682259580763083367514142813650362,342020143325668733044099614682259580763083367514175957454200⟩,⟨-939692620785908384054109277324731469936208134264481532580062,-939692620785908384054109277324731469936208134264448638369502⟩⟩
lemma phaseBox29_calc : (phaseInputBox 29).exp = phaseBox29 := by decide +kernel
lemma phaseBox29_mem : phaseBox29.Mem (phase ((29:ℤ):ℂ)) := by
  rw [← phaseBox29_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 29) (by decide +kernel)
def phaseBox30 : CI := ⟨⟨499999999999999999999999999999999999999999999999982086571115,500000000000000000000000000000000000000000000000015543483824⟩,⟨-866025403784438646763723170752936183471402626905207554081534,-866025403784438646763723170752936183471402626905174442267480⟩⟩
lemma phaseBox30_calc : (phaseInputBox 30).exp = phaseBox30 := by decide +kernel
lemma phaseBox30_mem : phaseBox30.Mem (phase ((30:ℤ):ℂ)) := by
  rw [← phaseBox30_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 30) (by decide +kernel)
def phaseBox31 : CI := ⟨⟨642787609686539326322643409907263432907559884205664038197821,642787609686539326322643409907263432907559884205697376234924⟩,⟨-766044443118978035202392650555416673935832457080412620035652,-766044443118978035202392650555416673935832457080379689347294⟩⟩
lemma phaseBox31_calc : (phaseInputBox 31).exp = phaseBox31 := by decide +kernel
lemma phaseBox31_mem : phaseBox31.Mem (phase ((31:ℤ):ℂ)) := by
  rw [← phaseBox31_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 31) (by decide +kernel)
def phaseBox32 : CI := ⟨⟨766044443118978035202392650555416673935832457080377922011624,766044443118978035202392650555416673935832457080410693391161⟩,⟨-642787609686539326322643409907263432907559884205699080092946,-642787609686539326322643409907263432907559884205666736654508⟩⟩
lemma phaseBox32_calc : (phaseInputBox 32).exp = phaseBox32 := by decide +kernel
lemma phaseBox32_mem : phaseBox32.Mem (phase ((32:ℤ):ℂ)) := by
  rw [← phaseBox32_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 32) (by decide +kernel)
def phaseBox33 : CI := ⟨⟨866025403784438646763723170752936183471402626905173685228535,866025403784438646763723170752936183471402626905205437711262⟩,⟨-500000000000000000000000000000000000000000000000016979488526,-499999999999999999999999999999999999999999999999985627454324⟩⟩
lemma phaseBox33_calc : (phaseInputBox 33).exp = phaseBox33 := by decide +kernel
lemma phaseBox33_mem : phaseBox33.Mem (phase ((33:ℤ):ℂ)) := by
  rw [← phaseBox33_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 33) (by decide +kernel)
def phaseBox34 : CI := ⟨⟨939692620785908384054109277324731469936208134264448958204507,939692620785908384054109277324731469936208134264479247218206⟩,⟨-342020143325668733044099614682259580763083367514177069829976,-342020143325668733044099614682259580763083367514147101516694⟩⟩
lemma phaseBox34_calc : (phaseInputBox 34).exp = phaseBox34 := by decide +kernel
lemma phaseBox34_mem : phaseBox34.Mem (phase ((34:ℤ):ℂ)) := by
  rw [← phaseBox34_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 34) (by decide +kernel)
def phaseBox35 : CI := ⟨⟨984807753012208059366743024589523013670643251719827941038041,984807753012208059366743024589523013670643251719856342140171⟩,⟨-173648177666930348851716626769314796000375677184085066392648,-173648177666930348851716626769314796000375677184056852251010⟩⟩
lemma phaseBox35_calc : (phaseInputBox 35).exp = phaseBox35 := by decide +kernel
lemma phaseBox35_mem : phaseBox35.Mem (phase ((35:ℤ):ℂ)) := by
  rw [← phaseBox35_calc]
  exact CI.mem_exp_checked (phaseInputBox_mem 35) (by decide +kernel)
def coeffBox0 (j : Fin 31) : CI := if j.val=0 then CI.point 1 else CI.point 0
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
def coeffBox9 : Fin 31 → CI :=
  ![⟨⟨-342020143325668733044099614682259580763083367514211711020077,-342020143325668733044099614682259580763083367514103974270900⟩,⟨939692620785908384054109277324731469936208134264411915337969,939692620785908384054109277324731469936208134264519378773918⟩⟩,
  ⟨⟨-8546050094779084377999995279403332120772903723070439782024673,-8546050094779084377999995279403332120772903723068997865637239⟩,⟨-7104191472993727658220477472822081860370109043820363676439438,-7104191472993727658220477472822081860370109043818919791367384⟩⟩,
  ⟨⟨53192431010427477720931580224837648280116394338512048806212770,53192431010427477720931580224837648280116394338520804923691523⟩,⟨-32367279145103585003648839828133711987418689984026164839430940,-32367279145103585003648839828133711987418689984017414434627835⟩⟩,
  ⟨⟨52318628796553873942328933638360685806200044358742822194261277,52318628796553873942328933638360685806200044358780443681535818⟩,⟨226785666093013813713357576348077107247170054189914163336179144,226785666093013813713357576348077107247170054189951804297088302⟩⟩,
  ⟨⟨-646181960118240802195224849480853572707850039843872265453185230,-646181960118240802195224849480853572707850039843759830638340523⟩,⟨-54854788433103423019729288476666748903659658107071858586761288,-54854788433103423019729288476666748903659658106959469610007987⟩⟩,
  ⟨⟨541927493675297551999659729871028089280460199295238151919751795,541927493675297551999659729871028089280460199295496798444641212⟩,⟨-1320632989363895133292426257567093585605520632694305134173278950,-1320632989363895133292426257567093585605520632694046807128722444⟩⟩,
  ⟨⟨1982798468468676290624971051539277517788815640382742221282187773,1982798468468676290624971051539277517788815640383232196738845857⟩,⟨1633113758292559146271181035052996054187082431105413424990840548,1633113758292559146271181035052996054187082431105904416852759211⟩⟩,
  ⟨⟨-3215859394967511030987679175935174189434921531107857777705497725,-3215859394967511030987679175935174189434921531107115596460315526⟩,⟨2134161377520389784686638956331344866464578186393619252205296584,2134161377520389784686638956331344866464578186394361227660281172⟩⟩,
  ⟨⟨-1413671836478236560593936860673999082623840470010028390836039547,-1413671836478236560593936860673999082623840470009081855886079859⟩,⟨-4696624874642840501363796288174842396467577340902915864233076807,-4696624874642840501363796288174842396467577340901971079622760932⟩⟩,
  ⟨⟨5308728479702275905199987371421216990625111499351098268029990317,5308728479702275905199987371421216990625111499352137696612587995⟩,⟨-519845486379990,519845486388385⟩⟩,
  ⟨⟨-1413671836478236560593936860673999082623840470010028390836263428,-1413671836478236560593936860673999082623840470009081855885870274⟩,⟨4696624874642840501363796288174842396467577340901971079622545367,4696624874642840501363796288174842396467577340902915864233294501⟩⟩,
  ⟨⟨-3215859394967511030987679175935174189434921531107857777705900119,-3215859394967511030987679175935174189434921531107115596459914776⟩,⟨-2134161377520389784686638956331344866464578186394361227660687578,-2134161377520389784686638956331344866464578186393619252204899715⟩⟩,
  ⟨⟨1982798468468676290624971051539277517788815640382742221281655119,1982798468468676290624971051539277517788815640383232196739384780⟩,⟨-1633113758292559146271181035052996054187082431105904416853295136,-1633113758292559146271181035052996054187082431105413424990304947⟩⟩,
  ⟨⟨541927493675297551999659729871028089280460199295238151919134207,541927493675297551999659729871028089280460199295496798445259357⟩,⟨1320632989363895133292426257567093585605520632694046807128106615,1320632989363895133292426257567093585605520632694305134173898869⟩⟩,
  ⟨⟨-646181960118240802195224849480853572707850039843872265453845644,-646181960118240802195224849480853572707850039843759830637681582⟩,⟨54854788433103423019729288476666748903659658106959469609348825,54854788433103423019729288476666748903659658107071858587421509⟩⟩,
  ⟨⟨52318628796553873942328933638360685806200044358742822193584141,52318628796553873942328933638360685806200044358780443682212828⟩,⟨-226785666093013813713357576348077107247170054189951804297765240,-226785666093013813713357576348077107247170054189914163335501945⟩⟩,
  ⟨⟨53192431010427477720931580224837648280116394338512048805530022,53192431010427477720931580224837648280116394338520804924374394⟩,⟨32367279145103585003648839828133711987418689984017414433945386,32367279145103585003648839828133711987418689984026164840114109⟩⟩,
  ⟨⟨-8546050094779084377999995279403332120772903723070439782708922,-8546050094779084377999995279403332120772903723068997864952990⟩,⟨7104191472993727658220477472822081860370109043818919790683513,7104191472993727658220477472822081860370109043820363677124067⟩⟩,
  ⟨⟨-342020143325668733044099614682259580763083367514211711704585,-342020143325668733044099614682259580763083367514103973586396⟩,⟨-939692620785908384054109277324731469936208134264519379458060,-939692620785908384054109277324731469936208134264411914653102⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩,
  ⟨⟨-684534,684534⟩,⟨-684170,684894⟩⟩]
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
def coeffBox10 : Fin 31 → CI :=
  ![⟨⟨-500000000000000000000000000000000000000000000000068900041209,-499999999999999999999999999999999999999999999999924464149127⟩,⟨866025403784438646763723170752936183471402626905120178627774,866025403784438646763723170752936183471402626905264280639668⟩⟩,
  ⟨⟨-7866626774538188833014437765148908199971627794191447572472821,-7866626774538188833014437765148908199971627794189321939919936⟩,⟨-6600883625124310132316997618442595284339885548632392067331037,-6600883625124310132316997618442595284339885548630265113858998⟩⟩,
  ⟨⟨40739089132994957938266150337677580374796016120999326709445850,40739089132994957938266150337677580374796016121013805257717580⟩,⟨-35862353928348965355102339748684407766208223521464442119466510,-35862353928348965355102339748684407766208223521449960692840977⟩⟩,
  ⟨⟨108877889354584710277382157412267909524345878968498729683739106,108877889354584710277382157412267909524345878968566026875498444⟩,⟨162178501682506075077549880652292596695568517409507797601787543,162178501682506075077549880652292596695568517409575068285548190⟩⟩,
  ⟨⟨-475438513119195896047496353023017527047845748907274948211267956,-475438513119195896047496353023017527047845748907047336967802849⟩,⟨246229275274842394008708420720993397345433834098107007805216966,246229275274842394008708420720993397345433834098334731077378558⟩⟩,
  ⟨⟨-438439302020856399511006174874507873620850883672122444324611414,-438439302020856399511006174874507873620850883671521541758222176⟩,⟨-1101919214279253664965036074552028736211323059678545729369954823,-1101919214279253664965036074552028736211323059677945340737831230⟩⟩,
  ⟨⟨2107052625480202631622812170529616016695483076943670515473892952,2107052625480202631622812170529616016695483076944951833397253151⟩,⟨-630466648402993797186286626795947565118181981844940778313336508,-630466648402993797186286626795947565118181981843659135443493893⟩⟩,
  ⟨⟨732369323494674050945093748080595320877318083173653365613099094,732369323494674050945093748080595320877318083175903013653380885⟩,⟨3414863735263651370248900480843071354523797739444510657740251927,3414863735263651370248900480843071354523797739446761969382716412⟩⟩,
  ⟨⟨-4772090891587912160068984993141075852513232383268143574840789589,-4772090891587912160068984993141075852513232383264846052884953550⟩,⟨661562377266063277832866418891398493301858391615309584455957107,661562377266063277832866418891398493301858391618605548936594535⟩⟩,
  ⟨⟨-395676738216551395942468658603011383907053058832324840458132646,-395676738216551395942468658603011383907053058828205292091748011⟩,⟨-5811231928726367914873172624412156411733338670420282818800812792,-5811231928726367914873172624412156411733338670416165525757318008⟩⟩,
  ⟨⟨6201946288513195379238832782093209435634021294520380696586048632,6201946288513195379238832782093209435634021294524839658914149146⟩,⟨-2227707558823541,2227707558839947⟩⟩,
  ⟨⟨-395676738216551395942468658603011383907053058832324840459044147,-395676738216551395942468658603011383907053058828205292090862151⟩,⟨5811231928726367914873172624412156411733338670416165525756425041,5811231928726367914873172624412156411733338670420282818801716877⟩⟩,
  ⟨⟨-4772090891587912160068984993141075852513232383268143574842469856,-4772090891587912160068984993141075852513232383264846052883284048⟩,⟨-661562377266063277832866418891398493301858391618605548938276306,-661562377266063277832866418891398493301858391615309584454289056⟩⟩,
  ⟨⟨732369323494674050945093748080595320877318083173653365610851080,732369323494674050945093748080595320877318083175903013655638000⟩,⟨-3414863735263651370248900480843071354523797739446761969384971797,-3414863735263651370248900480843071354523797739444510657738002168⟩⟩,
  ⟨⟨2107052625480202631622812170529616016695483076943670515471275124,2107052625480202631622812170529616016695483076944951833399876575⟩,⟨630466648402993797186286626795947565118181981843659135440877045,630466648402993797186286626795947565118181981844940778315960920⟩⟩,
  ⟨⟨-438439302020856399511006174874507873620850883672122444327431830,-438439302020856399511006174874507873620850883671521541755403619⟩,⟨1101919214279253664965036074552028736211323059677945340735014857,1101919214279253664965036074552028736211323059678545729372777483⟩⟩,
  ⟨⟨-475438513119195896047496353023017527047845748907274948214178077,-475438513119195896047496353023017527047845748907047336964894250⟩,⟨-246229275274842394008708420720993397345433834098334731080286641,-246229275274842394008708420720993397345433834098107007802306327⟩⟩,
  ⟨⟨108877889354584710277382157412267909524345878968498729680796473,108877889354584710277382157412267909524345878968566026878441112⟩,⟨-162178501682506075077549880652292596695568517409575068288489601,-162178501682506075077549880652292596695568517409507797598843663⟩⟩,
  ⟨⟨40739089132994957938266150337677580374796016120999326706493436,40739089132994957938266150337677580374796016121013805260670111⟩,⟨35862353928348965355102339748684407766208223521449960689889965,35862353928348965355102339748684407766208223521464442122420444⟩⟩,
  ⟨⟨-7866626774538188833014437765148908199971627794191447575427510,-7866626774538188833014437765148908199971627794189321936965249⟩,⟨6600883625124310132316997618442595284339885548630265110905772,6600883625124310132316997618442595284339885548632392070287178⟩⟩,
  ⟨⟨-500000000000000000000000000000000000000000000000068902996253,-499999999999999999999999999999999999999999999999924461194087⟩,⟨-866025403784438646763723170752936183471402626905264283593264,-866025403784438646763723170752936183471402626905120175671299⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩,
  ⟨⟨-2955075,2955075⟩,⟨-2953630,2956506⟩⟩]
lemma coeffBox10_calc (j : Fin 31) : coeffStep phaseBox19 coeffBox9 j = coeffBox10 j := by
  revert j
  decide +kernel
lemma coeffBox10_mem (j : Fin 31) : (coeffBox10 j).Mem ((partialPolynomial 10).coeff j.val) := by
  rw [← coeffBox10_calc, partialPolynomial_succ (by norm_num : 9 < 15)]
  apply coeffStep_mem ⟨9,by norm_num⟩ (partialPolynomial 9) phaseBox19 coeffBox9
  · have hr : residue ⟨9,by norm_num⟩ = (19:ℤ) := by norm_num [residue]
    rw [hr]
    exact phaseBox19_mem
  · exact coeffBox9_mem
def coeffBox11 : Fin 31 → CI :=
  ![⟨⟨-866025403784438646763723170752936183471402626905300135331630,-866025403784438646763723170752936183471402626905075703749691⟩,⟨499999999999999999999999999999999999999999999999892066551761,500000000000000000000000000000000000000000000000116228239841⟩⟩,
  ⟨⟨-4512256816278756118456938628002619397688287391310210258601118,-4512256816278756118456938628002619397688287391306729011161763⟩,⟨-7917795486482586948753916921160270903681923406440902367120502,-7917795486482586948753916921160270903681923406437420793245015⟩⟩,
  ⟨⟨37479009531310300006850551367648045830356516272975173259066998,37479009531310300006850551367648045830356516273000953957285842⟩,⟨-22889932225210003527102216006623810505049214605872261630584365,-22889932225210003527102216006623810505049214605846475539188021⟩⟩,
  ⟨⟨84566805074835469890392359665795136636243630399272057735912200,84566805074835469890392359665795136636243630399401535878753250⟩,⟨121381719705828735132196132309283011763066550975407946779191505,121381719705828735132196132309283011763066550975537400464415412⟩⟩,
  ⟨⟨-299750780074938820892870618696196975276591632812947607225200506,-299750780074938820892870618696196975276591632812466394232953526⟩,⟨248451300240902940453703357514742017998730609444749611284910637,248451300240902940453703357514742017998730609445230907769899359⟩⟩,
  ⟨⟨-604236723733589874827210830126948470617931639818156534941066558,-604236723733589874827210830126948470617931639816752563109322821⟩,⟨-595039375217310207796535860555470977619951030889314574994364411,-595039375217310207796535860555470977619951030887910866129977077⟩⟩,
  ⟨⟨974488628275034602578873981907047468197760479003212676092985921,974488628275034602578873981907047468197760479006544524387294622⟩,⟨-1245352185471187400689490389926650304580367250250293562839532824,-1245352185471187400689490389926650304580367250246961894209428518⟩⟩,
  ⟨⟨2210264641720184399458528892806094123089498209837111502924387214,2210264641720184399458528892806094123089498209843682653112047789⟩,⟨1327539728668295680366779456141429382576698545712764835792456056,1327539728668295680366779456141429382576698545719335706635143205⟩⟩,
  ⟨⟨-1489266706352089832437996636617520920431595336759118253573183980,-1489266706352089832437996636617520920431595336748203057615419668⟩,⟨3417085403137856514915335216318419154734627839609709884206031347,3417085403137856514915335216318419154734627839620630210540134859⟩⟩,
  ⟨⟨-4639549619064101962223905076772006585891620777935289384345743994,-4639549619064101962223905076772006585891620777919786185490421580⟩,⟨-1316214008683221051638572465024791207886463407483165695530457535,-1316214008683221051638572465024791207886463407467669095640152811⟩⟩,
  ⟨⟨777718809675506040434076078185698975229654914678180647433936594,777718809675506040434076078185698975229654914697242535293211849⟩,⟨-5562515442501746475711344878311556406629592958595178622871523014,-5562515442501746475711344878311556406629592958576118953188695391⟩⟩,
  ⟨⟨5907328434335825745556963920158289517630770654238313011961097868,5907328434335825745556963920158289517630770654258733059173516545⟩,⟨-10203465802847119,10203465802876741⟩⟩,
  ⟨⟨777718809675506040434076078185698975229654914678180647429832615,777718809675506040434076078185698975229654914697242535297278488⟩,⟨5562515442501746475711344878311556406629592958576118953184627078,5562515442501746475711344878311556406629592958595178622875624720⟩⟩,
  ⟨⟨-4639549619064101962223905076772006585891620777935289384353412110,-4639549619064101962223905076772006585891620777919786185482780945⟩,⟨1316214008683221051638572465024791207886463407467669095632495781,1316214008683221051638572465024791207886463407483165695538109256⟩⟩,
  ⟨⟨-1489266706352089832437996636617520920431595336759118253583555359,-1489266706352089832437996636617520920431595336748203057605045205⟩,⟨-3417085403137856514915335216318419154734627839620630210550512005,-3417085403137856514915335216318419154734627839609709884195662599⟩⟩,
  ⟨⟨2210264641720184399458528892806094123089498209837111502912223146,2210264641720184399458528892806094123089498209843682653124223363⟩,⟨-1327539728668295680366779456141429382576698545719335706647307936,-1327539728668295680366779456141429382576698545712764835780281101⟩⟩,
  ⟨⟨974488628275034602578873981907047468197760479003212676079794002,974488628275034602578873981907047468197760479006544524400488857⟩,⟨1245352185471187400689490389926650304580367250246961894196244270,1245352185471187400689490389926650304580367250250293562852734855⟩⟩,
  ⟨⟨-604236723733589874827210830126948470617931639818156534954757873,-604236723733589874827210830126948470617931639816752563095634221⟩,⟨595039375217310207796535860555470977619951030887910866116293932,595039375217310207796535860555470977619951030889314575008061203⟩⟩,
  ⟨⟨-299750780074938820892870618696196975276591632812947607239093884,-299750780074938820892870618696196975276591632812466394219061477⟩,⟨-248451300240902940453703357514742017998730609445230907783786811,-248451300240902940453703357514742017998730609444749611271012680⟩⟩,
  ⟨⟨84566805074835469890392359665795136636243630399272057721951365,84566805074835469890392359665795136636243630399401535892714124⟩,⟨-121381719705828735132196132309283011763066550975537400478371018,-121381719705828735132196132309283011763066550975407946765225406⟩⟩,
  ⟨⟨37479009531310300006850551367648045830356516272975173245087868,37479009531310300006850551367648045830356516273000953971265088⟩,⟨22889932225210003527102216006623810505049214605846475525214243,22889932225210003527102216006623810505049214605872261644568939⟩⟩,
  ⟨⟨-4512256816278756118456938628002619397688287391310210272584080,-4512256816278756118456938628002619397688287391306728997178791⟩,⟨7917795486482586948753916921160270903681923406437420779267455,7917795486482586948753916921160270903681923406440902381108840⟩⟩,
  ⟨⟨-866025403784438646763723170752936183471402626905300149315147,-866025403784438646763723170752936183471402626905075689766175⟩,⟨-500000000000000000000000000000000000000000000000116242217967,-499999999999999999999999999999999999999999999999892052562895⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩,
  ⟨⟨-13983563,13983563⟩,⟨-13978174,13988910⟩⟩]
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
def coeffBox12 : Fin 31 → CI :=
  ![⟨⟨-766044443118978035202392650555416673935832457080562096652337,-766044443118978035202392650555416673935832457080236017549845⟩,⟨-642787609686539326322643409907263432907559884205840414350480,-642787609686539326322643409907263432907559884205514082201062⟩⟩,
  ⟨⟨4164960460944895420753505374463989805687536036937630069585979,4164960460944895420753505374463989805687536036942893971542901⟩,⟨-5948179980458170830020430871981224876340636903002152336580431,-5948179980458170830020430871981224876340636902996890023060468⟩⟩,
  ⟨⟨25477211159031679358278123031647999502929370960248315501705463,25477211159031679358278123031647999502929370960290362001457720⟩,⟨12539147570602880986363505153869713185588833690183522327102303,12539147570602880986363505153869713185588833690225570165954082⟩⟩,
  ⟨⟨-19163513165526571608310526597599643507403362702645028136533031,-19163513165526571608310526597599643507403362702416878403368227⟩,⟨76734020298984841702151163516356146062697505998502220494739912,76734020298984841702151163516356146062697505998730385356147211⟩⟩,
  ⟨⟨-175545972265297872977636312095087520787949684318523106819706685,-175545972265297872977636312095087520787949684317597004244411097⟩,⟨3017626026941955946172733161320399232757925021759570412525128,3017626026941955946172733161320399232757925022685587461900545⟩⟩,
  ⟨⟨-104023523936948958656788248009339890290094622406474404712293441,-104023523936948958656788248009339890290094622403506970033646322⟩,⟨-312361451936102397590849479031690449706967037533931724840415957,-312361451936102397590849479031690449706967037530963958312219338⟩⟩,
  ⟨⟨426016600509389744267675357995167981740501768593429106316840020,426016600509389744267675357995167981740501768601202700219568473⟩,⟨-333645564941496505330156441043791850901932563697869088192493758,-333645564941496505330156441043791850901932563690096017775894835⟩⟩,
  ⟨⟨691637758446381399752768983892442473125789657431896307916978934,691637758446381399752768983892442473125789657448915477516976156⟩,⟨404591669239809112237179302448884957676218351285791985628551978,404591669239809112237179302448884957676218351302811343572272978⟩⟩,
  ⟨⟨-136793385495221344071117481140581595312270513033450123604522478,-136793385495221344071117481140581595312270513001840275876863081⟩,⟨1082683256337036005873538115278089101822862201784558741076117848,1082683256337036005873538115278089101822862201816164520142611328⟩⟩,
  ⟨⟨-1325081930669853424216987020725719034212270184125814200847167152,-1325081930669853424216987020725719034212270184075428717067404263⟩,⟨401324516035198882288909637595247763921496262372573659196652356,401324516035198882288909637595247763921496262422974568891847956⟩⟩,
  ⟨⟨-1084398299482169539681976256669389237589600402521795869462639473,-1084398299482169539681976256669389237589600402452045083900697697⟩,⟨-1235938746085208377803587501985608315899680631093981910785557973,-1235938746085208377803587501985608315899680631024247746112040974⟩⟩,
  ⟨⟨752206920120831188962900784972055024446461760496889522806109841,752206920120831188962900784972055024446461760581373173903096310⟩,⟨-1664379109791823342528998810652508607724895010423173937634051990,-1664379109791823342528998810652508607724895010338680626505117385⟩⟩,
  ⟨⟨1892538437523115562971282965244989739504309015782542821407619223,1892538437523115562971282965244989739504309015872603120591642892⟩,⟨-45017160490578568,45017160490614147⟩⟩,
  ⟨⟨752206920120831188962900784972055024446461760496889522788116802,752206920120831188962900784972055024446461760581373173921065928⟩,⟨1664379109791823342528998810652508607724895010338680626487166361,1664379109791823342528998810652508607724895010423173937652062427⟩⟩,
  ⟨⟨-1084398299482169539681976256669389237589600402521795869496492968,-1084398299482169539681976256669389237589600402452045083866871608⟩,⟨1235938746085208377803587501985608315899680631024247746078218979,1235938746085208377803587501985608315899680631093981910819415889⟩⟩,
  ⟨⟨-1325081930669853424216987020725719034212270184125814200893328886,-1325081930669853424216987020725719034212270184075428717021256420⟩,⟨-401324516035198882288909637595247763921496262422974568937992022,-401324516035198882288909637595247763921496262372573659150486766⟩⟩,
  ⟨⟨-136793385495221344071117481140581595312270513033450123659066914,-136793385495221344071117481140581595312270513001840275822318386⟩,⟨-1082683256337036005873538115278089101822862201816164520197144414,-1082683256337036005873538115278089101822862201784558741021561822⟩⟩,
  ⟨⟨691637758446381399752768983892442473125789657431896307857450152,691637758446381399752768983892442473125789657448915477576509361⟩,⟨-404591669239809112237179302448884957676218351302811343631788890,-404591669239809112237179302448884957676218351285791985569005694⟩⟩,
  ⟨⟨426016600509389744267675357995167981740501768593429106254744724,426016600509389744267675357995167981740501768601202700281665515⟩,⟨333645564941496505330156441043791850901932563690096017713815451,333645564941496505330156441043791850901932563697869088254606691⟩⟩,
  ⟨⟨-104023523936948958656788248009339890290094622406474404775519580,-104023523936948958656788248009339890290094622403506969970420793⟩,⟨312361451936102397590849479031690449706967037530963958249009458,312361451936102397590849479031690449706967037533931724903657696⟩⟩,
  ⟨⟨-175545972265297872977636312095087520787949684318523106883352453,-175545972265297872977636312095087520787949684317597004180765943⟩,⟨-3017626026941955946172733161320399232757925022685587525531199,-3017626026941955946172733161320399232757925021759570348864841⟩⟩,
  ⟨⟨-19163513165526571608310526597599643507403362702645028200307351,-19163513165526571608310526597599643507403362702416878339593927⟩,⟨-76734020298984841702151163516356146062697505998730385419907086,-76734020298984841702151163516356146062697505998502220430951193⟩⟩,
  ⟨⟨25477211159031679358278123031647999502929370960248315437899460,25477211159031679358278123031647999502929370960290362065263834⟩,⟨-12539147570602880986363505153869713185588833690225570229745717,-12539147570602880986363505153869713185588833690183522263281852⟩⟩,
  ⟨⟨4164960460944895420753505374463989805687536036937630005773943,4164960460944895420753505374463989805687536036942894035354977⟩,⟨5948179980458170830020430871981224876340636902996889959262847,5948179980458170830020430871981224876340636903002152400406886⟩⟩,
  ⟨⟨-766044443118978035202392650555416673935832457080562160465188,-766044443118978035202392650555416673935832457080235953736992⟩,⟨642787609686539326322643409907263432907559884205514018402637,642787609686539326322643409907263432907559884205840478177725⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩,
  ⟨⟨-63812912,63812912⟩,⟨-63798486,63827304⟩⟩]
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
def coeffBox13 : Fin 31 → CI :=
  ![⟨⟨642787609686539326322643409907263432907559884205491065819110,642787609686539326322643409907263432907559884205861544029453⟩,⟨-766044443118978035202392650555416673935832457080584961250795,-766044443118978035202392650555416673935832457080214736087377⟩⟩,
  ⟨⟨4416091094220214759615645570870391528468971988835612510009246,4416091094220214759615645570870391528468971988841843879204807⟩,⟨2879385241571816768108218554649462939872416268525783467215086,2879385241571816768108218554649462939872416268532016930941459⟩⟩,
  ⟨⟨-4852014258399629471179137814848997007121321500556737708852509,-4852014258399629471179137814848997007121321500502600336949783⟩,⟨14346895641234315733439653938240966424183929611323643797525692,14346895641234315733439653938240966424183929611377776400408053⟩⟩,
  ⟨⟨-31727777961379653815615348325041371933179400981237586093399075,-31727777961379653815615348325041371933179400980916744051283054⟩,⟨1749821514734294943662978335675793058086768640777548782127838,1749821514734294943662978335675793058086768641098379962637368⟩⟩,
  ⟨⟨-28805504787392218176430281202649973061975816737795699501608560,-28805504787392218176430281202649973061975816736364548566665293⟩,⟨-47555142826359868931612108094023228165484043281812401964669468,-47555142826359868931612108094023228165484043280381136586420562⟩⟩,
  ⟨⟨38003527704491493337728018357871554193765174892411787226043433,38003527704491493337728018357871554193765174897475976250863618⟩,⟨-78824758717538475156132255089099448317175409660546701891908565,-78824758717538475156132255089099448317175409655483030896720717⟩⟩,
  ⟨⟨128616143094540543962752678186432469554501243898892387453858944,128616143094540543962752678186432469554501243913555743786915243⟩,⟨-23160331097517177936387287973125396885482622156852446028342108,-23160331097517177936387287973125396885482622142187816984137108⟩⟩,
  ⟨⟨135080079842867978707321934509760556097818148350092168791020538,135080079842867978707321934509760556097818148385673879172008278⟩,⟨128370152500337347749244349814198661612019152439641516092871830,128370152500337347749244349814198661612019152475221659308327233⟩⟩,
  ⟨⟨-33053304385769711698156588536996006473215450650271644710815224,-33053304385769711698156588536996006473215450576792439279750964⟩,⟨246373352475007136135565765762020338299664420936901061467521013,246373352475007136135565765762020338299664421010385235733328276⟩⟩,
  ⟨⟨-270319617785832458193965297427525996869818937204127834489685805,-270319617785832458193965297427525996869818937073399423482140873⟩,⟨148646823557837187777320225938016696307664561994344572281134593,148646823557837187777320225938016696307664562125049231707191204⟩⟩,
  ⟨⟨-331541858917462464756848424187740650701997535442878878768821570,-331541858917462464756848424187740650701997535240657046632136044⟩,⟨-144955881916550431033039500338312114434337364774863924340469611,-144955881916550431033039500338312114434337364572590550823327969⟩⟩,
  ⟨⟨-103092973137316854546044065091022103532809532332403069480718896,-103092973137316854546044065091022103532809532057877455956093534⟩,⟨-394588641379732142427287198273442573140629317615712047882835767,-394588641379732142427287198273442573140629317341244762082440806⟩⟩,
  ⟨⟨268475094156454000122214067958501732993242889854714963837750484,268475094156454000122214067958501732993242890183582763062357644⟩,⟨-351821482578361582404738399390638238355880602611827497651162635,-351821482578361582404738399390638238355880602282897779271403473⟩⟩,
  ⟨⟨456318655462584440884568309184962263558828010718663895895607726,456318655462584440884568309184962263558828011067922565062493381⟩,⟨-174593696348640465,174593696348688204⟩⟩,
  ⟨⟨268475094156454000122214067958501732993242889854714963767942069,268475094156454000122214067958501732993242890183582763132154454⟩,⟨351821482578361582404738399390638238355880602282897779201647932,351821482578361582404738399390638238355880602611827497721009600⟩⟩,
  ⟨⟨-103092973137316854546044065091022103532809532332403069612542500,-103092973137316854546044065091022103532809532057877455824286853⟩,⟨394588641379732142427287198273442573140629317341244761950665466,394588641379732142427287198273442573140629317615712048014692483⟩⟩,
  ⟨⟨-331541858917462464756848424187740650701997535442878878949523059,-331541858917462464756848424187740650701997535240657046451449356⟩,⟨144955881916550431033039500338312114434337364572590550642669314,144955881916550431033039500338312114434337364774863924521198983⟩⟩,
  ⟨⟨-270319617785832458193965297427525996869818937204127834704465027,-270319617785832458193965297427525996869818937073399423267369981⟩,⟨-148646823557837187777320225938016696307664562125049231921933999,-148646823557837187777320225938016696307664561994344572066327600⟩⟩,
  ⟨⟨-33053304385769711698156588536996006473215450650271644946518807,-33053304385769711698156588536996006473215450576792439044049144⟩,⟨-246373352475007136135565765762020338299664421010385235969000089,-246373352475007136135565765762020338299664420936901061231786965⟩⟩,
  ⟨⟨135080079842867978707321934509760556097818148350092168544072295,135080079842867978707321934509760556097818148385673879418958526⟩,⟨-128370152500337347749244349814198661612019152475221659555245343,-128370152500337347749244349814198661612019152439641515845891651⟩⟩,
  ⟨⟨128616143094540543962752678186432469554501243898892387201666995,128616143094540543962752678186432469554501243913555744039109888⟩,⟨23160331097517177936387287973125396885482622142187816731974540,23160331097517177936387287973125396885482622156852446280566038⟩⟩,
  ⟨⟨38003527704491493337728018357871554193765174892411786971753298,38003527704491493337728018357871554193765174897475976505155540⟩,⟨78824758717538475156132255089099448317175409655483030642459562,78824758717538475156132255089099448317175409660546702146229580⟩⟩,
  ⟨⟨-28805504787392218176430281202649973061975816737795699756608305,-28805504787392218176430281202649973061975816736364548311664771⟩,⟨47555142826359868931612108094023228165484043280381136331449657,47555142826359868931612108094023228165484043281812402219698790⟩⟩,
  ⟨⟨-31727777961379653815615348325041371933179400981237586348597411,-31727777961379653815615348325041371933179400980916743796084486⟩,⟨-1749821514734294943662978335675793058086768641098380217806972,-1749821514734294943662978335675793058086768640777548526900538⟩⟩,
  ⟨⟨-4852014258399629471179137814848997007121321500556737964095461,-4852014258399629471179137814848997007121321500502600081706755⟩,⟨-14346895641234315733439653938240966424183929611377776655622258,-14346895641234315733439653938240966424183929611323643542253924⟩⟩,
  ⟨⟨4416091094220214759615645570870391528468971988835612254758617,4416091094220214759615645570870391528468971988841844134455456⟩,⟨-2879385241571816768108218554649462939872416268532017186163297,-2879385241571816768108218554649462939872416268525783211935644⟩⟩,
  ⟨⟨642787609686539326322643409907263432907559884205490810567554,642787609686539326322643409907263432907559884205861799281011⟩,⟨766044443118978035202392650555416673935832457080214480864638,766044443118978035202392650555416673935832457080585216531170⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩,
  ⟨⟨-255251619,255251619⟩,⟨-255222800,255280438⟩⟩]
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
def coeffBox14 : Fin 31 → CI :=
  ![⟨⟨642787609686539326322643409907263432907559884205450996833679,642787609686539326322643409907263432907559884205925511237456⟩,⟨766044443118978035202392650555416673935832457080152454279948,766044443118978035202392650555416673935832457080627190072069⟩⟩,
  ⟨⟨-2316911861358276816436919302717675619342037857811904592355163,-2316911861358276816436919302717675619342037857803706628700402⟩,⟨2316911861358276816436919302717675619342037857803752185672144,2316911861358276816436919302717675619342037857811947743171944⟩⟩,
  ⟨⟨-5320233840503559348056640499798215665394454341561169511136765,-5320233840503559348056640499798215665394454341484900550899844⟩,⟨-2010843059532065689344682916953785201566447671125286878603763,-2010843059532065689344682916953785201566447671049008397171332⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702772212946019771931,-3849000747596232886841704603828508967213702771724458321926955⟩,⟨-7704824504620151700561164434554927892577748850961087228412744,-7704824504620151700561164434554927892577748850472606080485304⟩⟩,
  ⟨⟨3350618334479143229323154450619169638053167836900476341232371,3350618334479143229323154450619169638053167839265999885604826⟩,⟨-14323388547977786674655271161271114832315840465663052602267255,-14323388547977786674655271161271114832315840463297636048945315⟩⟩,
  ⟨⟨20649689227276910505519285647892239573321723705644426012368686,20649689227276910505519285647892239573321723714749391304555665⟩,⟨-13054432816245680790053223023741599995750160087097180291817853,-13054432816245680790053223023741599995750160077991555679094312⟩⟩,
  ⟨⟨34650920231336140889453197522086290546366560007430250801020899,34650920231336140889453197522086290546366560036212160384630619⟩,⟨9660155070742856944098328839855123822586247826602732959292736,9660155070742856944098328839855123822586247855382469935395477⟩⟩,
  ⟨⟨23129478202423733314021160428172685570569378041712087217341210,23129478202423733314021160428172685570569378118135532952750343⟩,⟨40677611644359167120709705604477237119124201289801032600985812,40677611644359167120709705604477237119124201366228719647835037⟩⟩,
  ⟨⟨-11873014388882054365633557151108253877307628421271330143326997,-11873014388882054365633557151108253877307628247978542810385229⟩,⟨58766445303134472372956339264977712973917686115537060117177540,58766445303134472372956339264977712973917686288821664342281817⟩⟩,
  ⟨⟨-62591132321930049398796132326675493332278272129412017369259849,-62591132321930049398796132326675493332278271789793503143591423⟩,⟨45402446581159540598010074247522168936488176517847320698825791,45402446581159540598010074247522168936488176857496293340483687⟩⟩,
  ⟨⟨-91943885868744270868448469111380909817943368805007762289403883,-91943885868744270868448469111380909817943368224083326984445685⟩,⟨-14271154518609465659180464386073774789042228127769770775875415,-14271154518609465659180464386073774789042227546938673938175168⟩⟩,
  ⟨⟨-63258804321523326560999460015259942968689732093376830127474469,-63258804321523326560999460015259942968689731219515418949094375⟩,⟨-82518319196160990928914593099031920866390976299640431529572296,-82518319196160990928914593099031920866390975425609335955906455⟩⟩,
  ⟨⟨8488329860743371322815627353293936177409191429859269337371577,8488329860743371322815627353293936177409192594301664757692089⟩,⟨-112011451382787227670045121456915246974862834403076913965405324,-112011451382787227670045121456915246974862833238843222101281880⟩⟩,
  ⟨⟨87019238990653242817878034046992465001508058966083036625388139,87019238990653242817878034046992465001508060346348483287452360⟩,⟨-84210457682694112133159822455607856199924578538509339816142758,-84210457682694112133159822455607856199924577158014946726396551⟩⟩,
  ⟨⟨126443841787877377679759560303609900616067107737665094907574481,126443841787877377679759560303609900616067109198302229144863183⟩,⟨-730197075238485835,730197075238554012⟩⟩,
  ⟨⟨87019238990653242817878034046992465001508058966083036333076816,87019238990653242817878034046992465001508060346348483579757299⟩,⟨84210457682694112133159822455607856199924577158014946434159596,84210457682694112133159822455607856199924578538509340108515189⟩⟩,
  ⟨⟨8488329860743371322815627353293936177409191429859268783548881,8488329860743371322815627353293936177409192594301665311505917⟩,⟨112011451382787227670045121456915246974862833238843221547526409,112011451382787227670045121456915246974862834403076914519292247⟩⟩,
  ⟨⟨-63258804321523326560999460015259942968689732093376830890376980,-63258804321523326560999460015259942968689731219515418186200163⟩,⟨82518319196160990928914593099031920866390975425609335193071141,82518319196160990928914593099031920866390976299640432292532231⟩⟩,
  ⟨⟨-91943885868744270868448469111380909817943368805007763201334195,-91943885868744270868448469111380909817943368224083326072520803⟩,⟨14271154518609465659180464386073774789042227546938673026307097,14271154518609465659180464386073774789042228127769771687861638⟩⟩,
  ⟨⟨-62591132321930049398796132326675493332278272129412018375552415,-62591132321930049398796132326675493332278271789793502137299189⟩,⟨-45402446581159540598010074247522168936488176857496294346720396,-45402446581159540598010074247522168936488176517847319692476356⟩⟩,
  ⟨⟨-11873014388882054365633557151108253877307628421271331202429326,-11873014388882054365633557151108253877307628247978541751278194⟩,⟨-58766445303134472372956339264977712973917686288821665401332616,-58766445303134472372956339264977712973917686115537059058019670⟩⟩,
  ⟨⟨23129478202423733314021160428172685570569378041712086132293345,23129478202423733314021160428172685570569378118135534037805116⟩,⟨-40677611644359167120709705604477237119124201366228720732835625,-40677611644359167120709705604477237119124201289801031515883883⟩⟩,
  ⟨⟨34650920231336140889453197522086290546366560007430249704880607,34650920231336140889453197522086290546366560036212161480776782⟩,⟨-9660155070742856944098328839855123822586247855382471031490356,-9660155070742856944098328839855123822586247826602731863100822⟩⟩,
  ⟨⟨20649689227276910505519285647892239573321723705644424912148919,20649689227276910505519285647892239573321723714749392404778766⟩,⟨13054432816245680790053223023741599995750160077991554578920411,13054432816245680790053223023741599995750160087097181392086646⟩⟩,
  ⟨⟨3350618334479143229323154450619169638053167836900475239741897,3350618334479143229323154450619169638053167839266000987096459⟩,⟨14323388547977786674655271161271114832315840463297634947501526,14323388547977786674655271161271114832315840465663053703805610⟩⟩,
  ⟨⟨-3849000747596232886841704603828508967213702772212947121590589,-3849000747596232886841704603828508967213702771724457220108098⟩,⟨7704824504620151700561164434554927892577748850472604978714005,7704824504620151700561164434554927892577748850961088330278944⟩⟩,
  ⟨⟨-5320233840503559348056640499798215665394454341561170613023497,-5320233840503559348056640499798215665394454341484899449013156⟩,⟨2010843059532065689344682916953785201566447671049007295332185,2010843059532065689344682916953785201566447671125287980538045⟩⟩,
  ⟨⟨-2316911861358276816436919302717675619342037857811905694252664,-2316911861358276816436919302717675619342037857803705526802935⟩,⟨-2316911861358276816436919302717675619342037857811948845021805,-2316911861358276816436919302717675619342037857803751083727038⟩⟩,
  ⟨⟨642787609686539326322643409907263432907559884205449894935006,642787609686539326322643409907263432907559884205926613136127⟩,⟨-766044443118978035202392650555416673935832457080628291923111,-766044443118978035202392650555416673935832457080151352333646⟩⟩,
  ⟨⟨-1101898745,1101898745⟩,⟨-1101851114,1101946376⟩⟩,
  ⟨⟨-1101898745,1101898745⟩,⟨-1101851114,1101946376⟩⟩]
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
def coeffBox15 : Fin 31 → CI :=
  ![⟨⟨-1000000000000000000000000000000000000000000000000357668187167,-999999999999999999999999999999999999999999999999642331844290⟩,⟨-347827970497,367531293270⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999993651414841229,1000000000000000000000000000000000000000000000006301693187769⟩,⟨-1732050807568877293527446341505872366942805253816719729498660,-1732050807568877293527446341505872366942805253804068711800391⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999937613287990976,500000000000000000000000000000000000000000000062425585717517⟩,⟨866025403784438646763723170752936183471402626842770407098962,866025403784438646763723170752936183471402626967575393807880⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999573590116305701,1000000000000000000000000000000000000000000000426403438220127⟩,⟨-1732050807568877293527446341505872366942805254236801333268779,-1732050807568877293527446341505872366942805253383966294401230⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999999997791129033444059,3000000000000000000000000000000000000000000002208932276369331⟩,⟨1732050807568877293527446341505872366942805251601454706010736,1732050807568877293527446341505872366942805256019259984594612⟩⟩,
  ⟨⟨-9124260591446541,9124350972912394⟩,⟨3464101615137754587054892683011744733885610498496628994962483,3464101615137754587054892683011744733885610516744944595527729⟩⟩,
  ⟨⟨-1500000000000000000000000000000000000000000031045869893592982,-1499999999999999999999999999999999999999999968954126738405517⟩,⟨866025403784438646763723170752936183471402595858574772131640,866025403784438646763723170752936183471402657951911834279273⟩⟩,
  ⟨⟨-89032996610118055,89032972484916236⟩,⟨3464101615137754587054892683011744733885610418590275204646281,3464101615137754587054892683011744733885610596651299102579322⟩⟩,
  ⟨⟨-6000000000000000000000000000000000000000000218766062218846020,-5999999999999999999999999999999999999999999781233989257513064⟩,⟨1732050807568877293527446341505872366942805035039511932291892,1732050807568877293527446341505872366942805472581352851209727⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000000466375630056524966,-1999999999999999999999999999999999999999999533624532919605091⟩,⟨-3464101615137754587054892683011744733885610973985977696155229,-3464101615137754587054892683011744733885610041255523607013701⟩⟩,
  ⟨⟨-2500000000000000000000000000000000000000000870865308128601628,-2499999999999999999999999999999999999999999129134785455383937⟩,⟨866025403784438646763723170752936183471401756003179879816604,866025403784438646763723170752936183471403497807120074975169⟩⟩,
  ⟨⟨-5000000000000000000000000000000000000000001435800045040879251,-4999999999999999999999999999999999999999998564200033688553946⟩,⟨-5196152422706631880582339024517617100828417197125514277083081,-5196152422706631880582339024517617100828414325736847984876077⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999997896786134701370754,2000000000000000000000000000000000000000002103213821259903458⟩,⟨-6928203230275509174109785366023489467771223118643747514259613,-6928203230275509174109785366023489467771218911839452891656829⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999997247556623475161820,3000000000000000000000000000000000000000002752443452126372415⟩,⟨-1732050807568877293527446341505872366942808006020615696087887,-1732050807568877293527446341505872366942802501600321429033324⟩⟩,
  ⟨⟨1499999999999999999999999999999999999999996770755461509639462,1500000000000000000000000000000000000000003229244711808191594⟩,⟨-6062177826491070527346062195270553284299821617837770478031202,-6062177826491070527346062195270553284299815158834963112515012⟩⟩,
  ⟨⟨11999999999999999999999999999999999999999996594619670830608816,12000000000000000000000000000000000000000003405380459998996233⟩,⟨-3405109190468067794,3405109190468112178⟩⟩,
  ⟨⟨1499999999999999999999999999999999999999996770755460144782377,1500000000000000000000000000000000000000003229244713173045367⟩,⟨6062177826491070527346062195270553284299815158834961747712830,6062177826491070527346062195270553284299821617837771842925403⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999997247556620880919775,3000000000000000000000000000000000000000002752443454720614479⟩,⟨1732050807568877293527446341505872366942802501600318834832012,1732050807568877293527446341505872366942808006020618290383453⟩⟩,
  ⟨⟨1999999999999999999999999999999999999999997896786131110583771,2000000000000000000000000000000000000000002103213824850693222⟩,⟨6928203230275509174109785366023489467771218911839449300915955,6928203230275509174109785366023489467771223118643751105091926⟩⟩,
  ⟨⟨-5000000000000000000000000000000000000000001435800049357225148,-4999999999999999999999999999999999999999998564200029372204250⟩,⟨5196152422706631880582339024517617100828414325736843668574096,5196152422706631880582339024517617100828417197125518593474909⟩⟩,
  ⟨⟨-2500000000000000000000000000000000000000000870865312918035125,-2499999999999999999999999999999999999999999129134780665942151⟩,⟨-866025403784438646763723170752936183471403497807124864370027,-866025403784438646763723170752936183471401756003175090333297⟩⟩,
  ⟨⟨-2000000000000000000000000000000000000000000466375635121079910,-1999999999999999999999999999999999999999999533624527855036240⟩,⟨3464101615137754587054892683011744733885610041255518542493621,3464101615137754587054892683011744733885610973985982760757402⟩⟩,
  ⟨⟨-6000000000000000000000000000000000000000000218766067425323507,-5999999999999999999999999999999999999999999781233984051020872⟩,⟨-1732050807568877293527446341505872366942805472581358057658275,-1732050807568877293527446341505872366942805035039506725770962⟩⟩,
  ⟨⟨-89033001881081646,89032977755889927⟩,⟨-3464101615137754587054892683011744733885610596651304373515719,-3464101615137754587054892683011744733885610418590269933644684⟩⟩,
  ⟨⟨-1500000000000000000000000000000000000000000031045875190131590,-1499999999999999999999999999999999999999999968954121441862869⟩,⟨-866025403784438646763723170752936183471402657951917130788193,-866025403784438646763723170752936183471402595858569475559699⟩⟩,
  ⟨⟨-9124265896733358,9124356278199251⟩,⟨-3464101615137754587054892683011744733885610516744949900782247,-3464101615137754587054892683011744733885610498496623689643227⟩⟩,
  ⟨⟨2999999999999999999999999999999999999999999997791123725616932,3000000000000000000000000000000000000000000002208937584195704⟩,⟨-1732050807568877293527446341505872366942805256019265292387869,-1732050807568877293527446341505872366942805251601449398150530⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999573584807865983,1000000000000000000000000000000000000000000000426408746659388⟩,⟨1732050807568877293527446341505872366942805253383960985995665,1732050807568877293527446341505872366942805254236806641742215⟩⟩,
  ⟨⟨499999999999999999999999999999999999999999999937607979432453,500000000000000000000000000000000000000000000062430894275904⟩,⟨-866025403784438646763723170752936183471402626967580702332263,-866025403784438646763723170752936183471402626842765098506436⟩⟩,
  ⟨⟨999999999999999999999999999999999999999999999993646106265121,1000000000000000000000000000000000000000000000006307001763882⟩,⟨1732050807568877293527446341505872366942805253804063403258327,1732050807568877293527446341505872366942805253816725038108817⟩⟩,
  ⟨⟨-1000000000000000000000000000000000000000000000000362976765098,-999999999999999999999999999999999999999999999999637023266358⟩,⟨-372839837171,353136582460⟩⟩]
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
def phaseTable : Fin 36 → CI := ![phaseBox0, phaseBox1, phaseBox2, phaseBox3, phaseBox4, phaseBox5, phaseBox6, phaseBox7, phaseBox8, phaseBox9, phaseBox10, phaseBox11, phaseBox12, phaseBox13, phaseBox14, phaseBox15, phaseBox16, phaseBox17, phaseBox18, phaseBox19, phaseBox20, phaseBox21, phaseBox22, phaseBox23, phaseBox24, phaseBox25, phaseBox26, phaseBox27, phaseBox28, phaseBox29, phaseBox30, phaseBox31, phaseBox32, phaseBox33, phaseBox34, phaseBox35]
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
def phaseModBox (n : ℤ) : CI := phaseTable ⟨(n%36).toNat, by omega⟩
lemma phaseModBox_mem (n : ℤ) : (phaseModBox n).Mem (phase (n:ℂ)) := by
  rw [phase_int_mod]
  have hh := phaseTable_mem ⟨(n%36).toNat, by omega⟩
  simpa only [phaseModBox, Int.toNat_of_nonneg (show 0 ≤ n%36 by omega)] using hh

def frequencyBox (j : Fin 31) : CI :=
  ((CI.imag.mul (CI.ofReal piBox)).mul (CI.point ((j.val:ℤ)-15))).divNat 18
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

def waveDerivativeBox (k : ℕ) (n : ℤ) : CI := CI.sum (fun j : Fin 31 =>
  ((coeffBox15 j).mul ((frequencyBox j).pow k)).mul (phaseModBox (((j.val:ℤ)-15)*n)))
lemma waveDerivativeBox_mem (k : ℕ) (n : ℤ) :
    (waveDerivativeBox k n).Mem (waveDerivative k (n:ℂ)) := by
  apply CI.mem_sum
  intro j
  rw [wave_phase_integer]
  exact CI.mem_mul (CI.mem_mul (atomPolynomial_coeff_mem j)
    (CI.mem_pow (frequencyBox_mem j) k)) (phaseModBox_mem (((j.val:ℤ)-15)*n))

def jetBox2_0 : CI := ⟨⟨2193245422464301915296553555528033585625259535611342042812338,2193245422464301915296553555528033585625273534273468147240545⟩,⟨-6999331474201310627,6999331474198725149⟩⟩
lemma jetBox2_0_calc : waveDerivativeBox 2 0 = jetBox2_0 := by decide +kernel
lemma jetBox2_0_mem : jetBox2_0.Mem (waveDerivative 2 ((0:ℤ):ℂ)) := by
  rw [← jetBox2_0_calc]
  exact waveDerivativeBox_mem 2 0
def QBox0 : RI := ⟨1096622711232150957648276777764016792812629767805671021406169,1096622711232150957648276777764016792812636767136734073620273⟩
lemma QBox0_calc : jetBox2_0.re.divNat 2 = QBox0 := by decide +kernel
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
def jetBox3_1 : CI := ⟨⟨639966476654750180084024766787116611503084547391679860744363,639966476654750180084024766787116611503099798483826564847070⟩,⟨-7625547005894580539,7625547004847671723⟩⟩
def QBox1 : RI := ⟨324679254169772833783550212097129381956412425050047392902795,324679254169772833783550212097129381956421809538816682723955⟩
lemma QBox1_calc : jetBox2_1.re.divNat 2 = QBox1 := by decide +kernel
lemma QBox1_mem : QBox1.Mem (Q 1) := by
  rw [← QBox1_calc]
  exact RI.mem_divNat jetBox2_1_mem.1 (by norm_num)
def DBox1 : RI := ⟨328512148751844566334421943996284209005041942242243381121812,328512148751844566334421943996284209005059266315738736466798⟩
lemma Q_1_bounds : (157/1000:ℝ) < Q 1 ∧ Q 1 < 40 := by
  have hh := QBox1_mem
  norm_num [RI.Mem, QBox1, scale] at hh
  constructor <;> linarith
def jetBox2_3 : CI := ⟨⟨314935873091926165719798041528741690796860352768042068448118,314935873091926165719798041528741690796877767398780082367638⟩,⟨-8707279535569115420,8707279520646445484⟩⟩
lemma jetBox2_3_calc : waveDerivativeBox 2 3 = jetBox2_3 := by decide +kernel
lemma jetBox2_3_mem : jetBox2_3.Mem (waveDerivative 2 ((3:ℤ):ℂ)) := by
  rw [← jetBox2_3_calc]
  exact waveDerivativeBox_mem 2 3
def jetBox3_3 : CI := ⟨⟨-1014910349844130235681633870102975669842297425304771309994680,-1014910349844130235681633870102975669842283153998726586069992⟩,⟨-7135672221752091992,7135672275674907079⟩⟩
def QBox3 : RI := ⟨157467936545963082859899020764370845398430176384021034224059,157467936545963082859899020764370845398438883699390041183820⟩
lemma QBox3_calc : jetBox2_3.re.divNat 2 = QBox3 := by decide +kernel
lemma QBox3_mem : QBox3.Mem (Q 3) := by
  rw [← QBox3_calc]
  exact RI.mem_divNat jetBox2_3_mem.1 (by norm_num)
def DBox3 : RI := ⟨-1074197888689855660750076301760101438086369445867264880330882,-1074197888689855660750076301760101438086294942250526538305496⟩
lemma Q_3_bounds : (157/1000:ℝ) < Q 3 ∧ Q 3 < 40 := by
  have hh := QBox3_mem
  norm_num [RI.Mem, QBox3, scale] at hh
  constructor <;> linarith
def jetBox2_4 : CI := ⟨⟨480190930161026078211119768145913141800720940178075083063726,480190930161026078211119768145913141800738985786865741678330⟩,⟨-9022785599708981683,9022785611075412461⟩⟩
lemma jetBox2_4_calc : waveDerivativeBox 2 4 = jetBox2_4 := by decide +kernel
lemma jetBox2_4_mem : jetBox2_4.Mem (waveDerivative 2 ((4:ℤ):ℂ)) := by
  rw [← jetBox2_4_calc]
  exact waveDerivativeBox_mem 2 4
def jetBox3_4 : CI := ⟨⟨2821037415057641454037448174285971970813200215885054810691223,2821037415057641454037448174285971970813214970229555343141501⟩,⟨-7377190765466621317,7377190749811915498⟩⟩
def QBox4 : RI := ⟨240095465080513039105559884072956570900360470089037541531863,240095465080513039105559884072956570900369492893432870839166⟩
lemma QBox4_calc : jetBox2_4.re.divNat 2 = QBox4 := by decide +kernel
lemma QBox4_mem : QBox4.Mem (Q 4) := by
  rw [← QBox4_calc]
  exact RI.mem_divNat jetBox2_4_mem.1 (by norm_num)
def DBox4 : RI := ⟨1958274815194615409462416280349205188070741451787576794058652,1958274815194615409462416280349205188070825285890898180544800⟩
lemma Q_4_bounds : (157/1000:ℝ) < Q 4 ∧ Q 4 < 40 := by
  have hh := QBox4_mem
  norm_num [RI.Mem, QBox4, scale] at hh
  constructor <;> linarith
def jetBox2_7 : CI := ⟨⟨3189148019972792007764637656494857305488305163218904078244812,3189148019972792007764637656494857305488323055140130853335833⟩,⟨-8946107184572060955,8946107179335551303⟩⟩
lemma jetBox2_7_calc : waveDerivativeBox 2 7 = jetBox2_7 := by decide +kernel
lemma jetBox2_7_mem : jetBox2_7.Mem (waveDerivative 2 ((7:ℤ):ℂ)) := by
  rw [← jetBox2_7_calc]
  exact waveDerivativeBox_mem 2 7
def jetBox3_7 : CI := ⟨⟨-1382299550539964033879229599493438562522051079640409546599351,-1382299550539964033879229599493438562522036475971189370307881⟩,⟨-7301729767200386216,7301729769468893611⟩⟩
def QBox7 : RI := ⟨1594574009986396003882318828247428652744152581609452039122406,1594574009986396003882318828247428652744161527570065426667917⟩
lemma QBox7_calc : jetBox2_7.re.divNat 2 = QBox7 := by decide +kernel
lemma QBox7_mem : QBox7.Mem (Q 7) := by
  rw [← QBox7_calc]
  exact RI.mem_divNat jetBox2_7_mem.1 (by norm_num)
def DBox7 : RI := ⟨-144479501723029361026896582559914730386716021226816443856874,-144479501723029361026896582559914730386713684268620369124310⟩
lemma Q_7_bounds : (157/1000:ℝ) < Q 7 ∧ Q 7 < 40 := by
  have hh := QBox7_mem
  norm_num [RI.Mem, QBox7, scale] at hh
  constructor <;> linarith
def jetBox2_9 : CI := ⟨⟨4386490844928603830593107111056067171250526070359086629539213,4386490844928603830593107111056067171250540069410481046659986⟩,⟨-6999139762929181309,6999139749324919077⟩⟩
lemma jetBox2_9_calc : waveDerivativeBox 2 9 = jetBox2_9 := by decide +kernel
lemma jetBox2_9_mem : jetBox2_9.Mem (waveDerivative 2 ((9:ℤ):ℂ)) := by
  rw [← jetBox2_9_calc]
  exact waveDerivativeBox_mem 2 9
def jetBox3_9 : CI := ⟨⟨6179663307388343146755102523626297746929090687276536865680881,6179663307388343146755102523626297746929102165152230001774040⟩,⟨-5739196860913024693,5739196877860715941⟩⟩
def QBox9 : RI := ⟨2193245422464301915296553555528033585625263035179543314769606,2193245422464301915296553555528033585625270034705240523329994⟩
lemma QBox9_calc : jetBox2_9.re.divNat 2 = QBox9 := by decide +kernel
lemma QBox9_mem : QBox9.Mem (Q 9) := by
  rw [← QBox9_calc]
  exact RI.mem_divNat jetBox2_9_mem.1 (by norm_num)
def DBox9 : RI := ⟨469598100611783043885383549212716193991642259249781619427619,469598100611783043885383549212716193991644630139606133123372⟩
lemma Q_9_bounds : (157/1000:ℝ) < Q 9 ∧ Q 9 < 40 := by
  have hh := QBox9_mem
  norm_num [RI.Mem, QBox9, scale] at hh
  constructor <;> linarith
def jetBox2_12 : CI := ⟨⟨2193245422464301915296553555528033585625257827702944738164265,2193245422464301915296553555528033585625275242181781766130093⟩,⟨-8707354858304197389,8707354880361310085⟩⟩
lemma jetBox2_12_calc : waveDerivativeBox 2 12 = jetBox2_12 := by decide +kernel
lemma jetBox2_12_mem : jetBox2_12.Mem (waveDerivative 2 ((12:ℤ):ℂ)) := by
  rw [← jetBox2_12_calc]
  exact waveDerivativeBox_mem 2 12
def jetBox3_12 : CI := ⟨⟨-9282250023375838495802108127145623981353442089922621766704147,-9282250023375838495802108127145623981353427818548128082380784⟩,⟨-7135636939508369437,7135637012310946188⟩⟩
def QBox12 : RI := ⟨1096622711232150957648276777764016792812628913851472369082132,1096622711232150957648276777764016792812637621090890883065047⟩
lemma QBox12_calc : jetBox2_12.re.divNat 2 = QBox12 := by decide +kernel
lemma QBox12_mem : QBox12.Mem (Q 12) := by
  rw [← QBox12_calc]
  exact RI.mem_divNat jetBox2_12_mem.1 (by norm_num)
def DBox12 : RI := ⟨-1410732838848836106017616422610565569554280433655814469824868,-1410732838848836106017616422610565569554267063377368789475445⟩
lemma Q_12_bounds : (157/1000:ℝ) < Q 12 ∧ Q 12 < 40 := by
  have hh := QBox12_mem
  norm_num [RI.Mem, QBox12, scale] at hh
  constructor <;> linarith
def jetBox2_13 : CI := ⟨⟨2807621397887934342703697530467294183654949971789532816313407,2807621397887934342703697530467294183654968017377691935889251⟩,⟨-9022795908507912539,9022795903898093804⟩⟩
lemma jetBox2_13_calc : waveDerivativeBox 2 13 = jetBox2_13 := by decide +kernel
lemma jetBox2_13_mem : jetBox2_13.Mem (waveDerivative 2 ((13:ℤ):ℂ)) := by
  rw [← jetBox2_13_calc]
  exact waveDerivativeBox_mem 2 13
def jetBox3_13 : CI := ⟨⟨16063736884637908466488652459875696207303396032822641395711849,16063736884637908466488652459875696207303410787163987127954303⟩,⟨-7377192311139094782,7377192284763907304⟩⟩
def QBox13 : RI := ⟨1403810698943967171351848765233647091827474985894766408156703,1403810698943967171351848765233647091827484008688845967944626⟩
lemma QBox13_calc : jetBox2_13.re.divNat 2 = QBox13 := by decide +kernel
lemma QBox13_mem : QBox13.Mem (Q 13) := by
  rw [← QBox13_calc]
  exact RI.mem_divNat jetBox2_13_mem.1 (by norm_num)
def DBox13 : RI := ⟨1907158481401378911137652754194682428075739824095418915998981,1907158481401378911137652754194682428075753833787153364714690⟩
lemma Q_13_bounds : (157/1000:ℝ) < Q 13 ∧ Q 13 < 40 := by
  have hh := QBox13_mem
  norm_num [RI.Mem, QBox13, scale] at hh
  constructor <;> linarith
def jetBox2_16 : CI := ⟨⟨33007531783833052762588798763964826898017254795610847195476874,33007531783833052762588798763964826898017272687668020675686737⟩,⟨-8946039095198659698,8946039053156332177⟩⟩
lemma jetBox2_16_calc : waveDerivativeBox 2 16 = jetBox2_16 := by decide +kernel
lemma jetBox2_16_mem : jetBox2_16.Mem (waveDerivative 2 ((16:ℤ):ℂ)) := by
  rw [← jetBox2_16_calc]
  exact waveDerivativeBox_mem 2 16
def jetBox3_16 : CI := ⟨⟨34108203020399732998460324303738196235955754478236087890457408,34108203020399732998460324303738196235955769081806548159520529⟩,⟨-7301779014900085682,7301778947873190120⟩⟩
def QBox16 : RI := ⟨16503765891916526381294399381982413449008627397805423597738437,16503765891916526381294399381982413449008636343834010337843369⟩
lemma QBox16_calc : jetBox2_16.re.divNat 2 = QBox16 := by decide +kernel
lemma QBox16_mem : QBox16.Mem (Q 16) := by
  rw [← QBox16_calc]
  exact RI.mem_divNat jetBox2_16_mem.1 (by norm_num)
def DBox16 : RI := ⟨344448687689171438118652015972695976450937488262806548151181,344448687689171438118652015972695976450937822451757900078321⟩
lemma Q_16_bounds : (157/1000:ℝ) < Q 16 ∧ Q 16 < 40 := by
  have hh := QBox16_mem
  norm_num [RI.Mem, QBox16, scale] at hh
  constructor <;> linarith
def jetBox2_19 : CI := ⟨⟨41594368450902491745324397900324124587329585672093445575455224,41594368450902491745324397900324124587329604441070992504609025⟩,⟨-9384489826205149675,9384489757909251186⟩⟩
lemma jetBox2_19_calc : waveDerivativeBox 2 19 = jetBox2_19 := by decide +kernel
lemma jetBox2_19_mem : jetBox2_19.Mem (waveDerivative 2 ((19:ℤ):ℂ)) := by
  rw [← jetBox2_19_calc]
  exact waveDerivativeBox_mem 2 19
def jetBox3_19 : CI := ⟨⟨-32819491150273111802401255112050382324380964413390713987725980,-32819491150273111802401255112050382324380949162298530836575429⟩,⟨-7625546992712991152,7625547046600646651⟩⟩
def QBox19 : RI := ⟨20797184225451245872662198950162062293664792836046722787727612,20797184225451245872662198950162062293664802220535496252304513⟩
lemma QBox19_calc : jetBox2_19.re.divNat 2 = QBox19 := by decide +kernel
lemma QBox19_mem : QBox19.Mem (Q 19) := by
  rw [← QBox19_calc]
  exact RI.mem_divNat jetBox2_19_mem.1 (by norm_num)
def DBox19 : RI := ⟨-263012296877102942861247435249124951652992134611952558172030,-263012296877102942861247435249124951652991893709886672401469⟩
lemma Q_19_bounds : (157/1000:ℝ) < Q 19 ∧ Q 19 < 40 := by
  have hh := QBox19_mem
  norm_num [RI.Mem, QBox19, scale] at hh
  constructor <;> linarith
def jetBox2_21 : CI := ⟨⟨61095935955908527462583701513256198706710585210988786004672484,61095935955908527462583701513256198706710602625619514804300734⟩,⟨-8707279582232183985,8707279467511139628⟩⟩
lemma jetBox2_21_calc : waveDerivativeBox 2 21 = jetBox2_21 := by decide +kernel
lemma jetBox2_21_mem : jetBox2_21.Mem (waveDerivative 2 ((21:ℤ):ℂ)) := by
  rw [← jetBox2_21_calc]
  exact waveDerivativeBox_mem 2 21
def jetBox3_21 : CI := ⟨⟨123010196371355150466223626398302605139058856838234045349168451,123010196371355150466223626398302605139058871109540066707038290⟩,⟨-7135672310732575004,7135672161010809294⟩⟩
def QBox21 : RI := ⟨30547967977954263731291850756628099353355292605494393002336242,30547967977954263731291850756628099353355301312809757402150368⟩
lemma QBox21_calc : jetBox2_21.re.divNat 2 = QBox21 := by decide +kernel
lemma QBox21_mem : QBox21.Mem (Q 21) := by
  rw [← QBox21_calc]
  exact RI.mem_divNat jetBox2_21_mem.1 (by norm_num)
def DBox21 : RI := ⟨671131363304473916173614466728511275356539559902564587441891,671131363304473916173614466728511275356539829062969650231253⟩
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

def restPolynomial (a : Fin 15) : Polynomial ℂ :=
  ∏ r ∈ Finset.univ.erase a, atomFactor r

def recoverRest (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  e.conj.mul (((coeffBox15 j).neg.add
    (if h : j.val=0 then CI.point 0 else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩)))

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
def kappaBox : CI := (CI.ofReal piBox).divNat 36

def cCoeffBox (r : Fin 31 → CI) (j : Fin 31) : CI := if h : j.val=0 then CI.point 0
    else ((CI.point 4).mul (kappaBox.pow 2)).mul (r ⟨j.val-1,by omega⟩)
def dCoeffBox (e : CI) (r : Fin 31 → CI) (j : Fin 31) : CI :=
  (CI.imag.mul kappaBox).mul ((e.mul (r j)).sub
    (if h : j.val<2 then CI.point 0 else e.conj.mul (r ⟨j.val-2,by omega⟩)))
def cBox0 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651966740766375,30461741978670859934674354937889355355906479651988725086961⟩,⟨-11195645515,10595447836⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651763885012090,30461741978670859934674354937889355355906479652193009253703⟩,⟨52761284794111633070194360652541195326313997272545860379138,52761284794111633070194360652541195326313997272975150502454⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953239823648828787981,15230870989335429967337177468944677677953239828330576803617⟩,⟨79141927191167449605291540978811792989470995906800505278779,79141927191167449605291540978811792989470995911482485993522⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906479669861979172758,-30461741978670859934674354937889355355906479634091373421386⟩,⟨158283854382334899210583081957623585978941991800397396158541,158283854382334899210583081957623585978941991836169152762599⟩⟩,
  ⟨⟨-167539580882689729640708952158391454457485638191275949896232,-167539580882689729640708952158391454457485637980478426044136⟩,⟨184664496779390715745680262283894183642098990349265973467019,184664496779390715745680262283894183642098990560064168401675⟩⟩,
  ⟨⟨-304617419786708599346743549378893553559064797026403957544993,-304617419786708599346743549378893553559064796013154194919287⟩,⟨105522569588223266140388721305082390652627994038904235867635,105522569588223266140388721305082390652627995052145176679232⟩⟩,
  ⟨⟨-396002645722721179150766614192561619626784237540073058469299,-396002645722721179150766614192561619626784233411355774337017⟩,⟨-2064372003158035,2064376766514151⟩⟩,
  ⟨⟨-487387871658733758954789679006229685694503681779089418267878,-487387871658733758954789679006229685694503667084209359986761⟩,⟨-211045139176446532280777442610164781305255996438436174227140,-211045139176446532280777442610164781305255981743648055710895⟩⟩,
  ⟨⟨-396002645722721179150766614192561619626784258898947334859268,-396002645722721179150766614192561619626784212052487025672644⟩,⟨-474851563147004697631749245872870757936825998878154882865656,-474851563147004697631749245872870757936825952031542877160927⟩⟩,
  ⟨⟨-243693935829366879477394839503114842847251905616335690635717,-243693935829366879477394839503114842847251768815318355933710⟩,⟨-633135417529339596842332327830494343915768035673436184600418,-633135417529339596842332327830494343915767898872832985243856⟩⟩,
  ⟨⟨-15230870989335429967337177468944677677953426578308723615810,-15230870989335429967337177468944677677953053073673493630087⟩,⟨-817799914308730312588012590114388527557867144480896772022716,-817799914308730312588012590114388527557866770974702041778144⟩⟩,
  ⟨⟨365540903744050319216092259254672264270877270181621175543864,365540903744050319216092259254672264270878241465848164031142⟩,⟨-844180556705786129123109770440659125221024442004423090698659,-844180556705786129123109770440659125221023470723938826503224⟩⟩,
  ⟨⟨685389194520094348530172986102510495507894570065403823455342,685389194520094348530172986102510495507897014273607482734414⟩,⟨-659516059926395413377429508156764941578926188016386617556272,-659516059926395413377429508156764941578923743802648137184295⟩⟩,
  ⟨⟨913852259360125798040230648136680660677191375864806652373917,913852259360125798040230648136680660677197403253877919922476⟩,⟨-422090278352893064561554885220329562610514991873180869451196,-422090278352893064561554885220329562610508964490999982384792⟩⟩,
  ⟨⟨1096622711232150957648276777764016792812625919609624534145246,1096622711232150957648276777764016792812640615332794825920420⟩,⟨-7347865283819770646,7347865283819703935⟩⟩,
  ⟨⟨913852259360125798040230648136680660677176576407824422701341,913852259360125798040230648136680660677212202710860149612455⟩,⟨422090278352893064561554885220329562610494165034874773428189,422090278352893064561554885220329562610529791329306078274633⟩⟩,
  ⟨⟨685389194520094348530172986102510495507852719636475308031328,685389194520094348530172986102510495507938864702535998191770⟩,⟨659516059926395413377429508156764941578881893373564320049679,659516059926395413377429508156764941578968038445470434557845⟩⟩,
  ⟨⟨365540903744050319216092259254672264270773713761941047576948,365540903744050319216092259254672264270981797885528292045131⟩,⟨844180556705786129123109770440659125220919914307946594403482,844180556705786129123109770440659125221127998420415322664279⟩⟩,
  ⟨⟨-15230870989335429967337177468944677678204460550161767322786,-15230870989335429967337177468944677677702019101820449865123⟩,⟨817799914308730312588012590114388527557615737006088893400812,817799914308730312588012590114388527558118178449509920262666⟩⟩,
  ⟨⟨-243693935829366879477394839503114842847858364462930915631641,-243693935829366879477394839503114842846645309968723130871386⟩,⟨633135417529339596842332327830494343915161440039734603754723,633135417529339596842332327830494343916374494506534565945411⟩⟩,
  ⟨⟨-396002645722721179150766614192561619628248537222168319379171,-396002645722721179150766614192561619625319933729266041079761⟩,⟨474851563147004697631749245872870757935361673737152278783225,474851563147004697631749245872870757938290277172545481088411⟩⟩,
  ⟨⟨-487387871658733758954789679006229685698038819378265594470704,-487387871658733758954789679006229685690968529485033183705727⟩,⟨211045139176446532280777442610164781301720844215955929603010,211045139176446532280777442610164781308791133966128300165084⟩⟩,
  ⟨⟨-396002645722721179150766614192561619635318833779389579120861,-396002645722721179150766614192561619618249637172039253602500⟩,⟨-8534598132011988586676,8534598132007225041597⟩⟩,
  ⟨⟨-304617419786708599346743549378893553579669140785842467794314,-304617419786708599346743549378893553538460452253715684581895⟩,⟨-105522569588223266140388721305082390673232338396654413253765,-105522569588223266140388721305082390632023650694394999504372⟩⟩,
  ⟨⟨-167539580882689729640708952158391454507228925867387958309946,-167539580882689729640708952158391454407742350304366417536438⟩,⟨-184664496779390715745680262283894183691842277234669775125708,-184664496779390715745680262283894183592355703674660366979207⟩⟩,
  ⟨⟨-30461741978670859934674354937889355475997399759002079490308,-30461741978670859934674354937889355235815559544951273002888⟩,⟨-158283854382334899210583081957623586099032909507359284279546,-158283854382334899210583081957623585858851074129207264904953⟩⟩,
  ⟨⟨15230870989335429967337177468944677388028111763141651750909,15230870989335429967337177468944677967878367888837753949337⟩,⟨-79141927191167449605291540978811793279396118134584059643984,-79141927191167449605291540978811792699545873683698931920482⟩⟩,
  ⟨⟨30461741978670859934674354937889354655965303406267787305561,30461741978670859934674354937889356055847655897689107076882⟩,⟨-52761284794111633070194360652541196026255159425710385465258,-52761284794111633070194360652541194626372835119810625738959⟩⟩,
  ⟨⟨30461741978670859934674354937889353666098999095807345841914,30461741978670859934674354937889357045713960208148120136120⟩,⟨-1689807446533242486228767,1689807446533243086071598⟩⟩,
  ⟨⟨-4079556137358243979696731,4079556137358243979829386⟩,⟨-4079556055219628132145969,4079556055219628131757017⟩⟩]
def dBox0 : Fin 31 → CI :=
  ![⟨⟨-30353728110,32073167388⟩,⟨87266462599716478846184538424430635672143594427054898665117,87266462599716478846184538424430635672143594427117601337988⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023672187341675814129132,-151149947019518154216173188136846311023672187340446469610477⟩,⟨87266462599716478846184538424430635672143594426473759726270,87266462599716478846184538424430635672143594427702832376369⟩⟩,
  ⟨⟨-226724920529277231324259782205269466535508281018331981224134,-226724920529277231324259782205269466535508281004857389245287⟩,⟨-43633231299858239423092269212215317836071797220277982157179,-43633231299858239423092269212215317836071797206803476013412⟩⟩,
  ⟨⟨-302299894039036308432346376273692622047344374733980056895279,-302299894039036308432346376273692622047344374630274583972932⟩,⟨-174532925199432957692369076848861271344287188906023535010153,-174532925199432957692369076848861271344287188802319503057679⟩⟩,
  ⟨⟨-302299894039036308432346376273692622047344374990780321669751,-302299894039036308432346376273692622047344374373478938831407⟩,⟨-523598775598298873077107230546583814032861566871169400957225,-523598775598298873077107230546583814032861566253868424927244⟩⟩,
  ⟨⟨151149947019518154216173188136846311023672185838457751561125,151149947019518154216173188136846311023672188843653432536882⟩,⟨-785398163397448309615660845819875721049292351346393469562707,-785398163397448309615660845819875721049292348341175093885552⟩⟩,
  ⟨⟨529024814568313539756606158478962088582852649477774322823855,529024814568313539756606158478962088582852661909658942706383⟩,⟨-654498469497873591346384038183229767541076964419051991037620,-654498469497873591346384038183229767541076951987266003600019⟩⟩,
  ⟨⟨906899682117108925297039128821077866142033101546284908714656,906899682117108925297039128821077866142033146546470500797662⟩,⟨-523598775598298873077107230546583814032861589062760897475544,-523598775598298873077107230546583814032861544062296535759882⟩⟩,
  ⟨⟨1360349523175663387945558693231616799213049613052745882550075,1360349523175663387945558693231616799213049759086393132190771⟩,⟨-73016564096571369,73016548260810557⟩⟩,
  ⟨⟨1209199576156145233729385505094770488189377281727355593179296,1209199576156145233729385505094770488189377715729670956614124⟩,⟨698131700797731830769476307395445085377148538414808640509039,698131700797731830769476307395445085377148972418574238235405⟩⟩,
  ⟨⟨982474655626868002405125722889501021653868615605885079972972,982474655626868002405125722889501021653869819827951255202748⟩,⟨1090830782496455985577306730305382945901794328230000570111444,1090830782496455985577306730305382945901795532447180947726563⟩⟩,
  ⟨⟨604599788078072616864692752547385244094687162155027795458020,604599788078072616864692752547385244094690336573486274137310⟩,⟨1745329251994329576923690768488612713442870301326551918860897,1745329251994329576923690768488612713442873475756938386161364⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071020598109672717748782,-453449841058554462648519564410538933071012525936697073941848⟩,⟨2007128639793479013462244383761904620459298635746673748806726,2007128639793479013462244383761904620459306707899344769765927⟩⟩,
  ⟨⟨-1209199576156145233729385505094770488189387523574321826698668,-1209199576156145233729385505094770488189367473882693623361613⟩,⟨1570796326794896619231321691639751442098574674826531273931836,1570796326794896619231321691639751442098594724548621990278003⟩⟩,
  ⟨⟨-1889374337743976927702164851710578887795926892925038698284974,-1889374337743976927702164851710578887795877790601553213756724⟩,⟨1178097245096172464423491268729813581573913973622470238953377,1178097245096172464423491268729813581573963075908885052955751⟩⟩,
  ⟨⟨-2418399152312290467458771010189540976378814661953788024188019,-2418399152312290467458771010189540976378695332960241652105071⟩,⟨-59664518955038107737,59664518955038158357⟩⟩,
  ⟨⟨-1889374337743976927702164851710578887796046785572904411810588,-1889374337743976927702164851710578887795757897953687500232942⟩,⟨-1178097245096172464423491268729813581574082968556305860041990,-1178097245096172464423491268729813581573794080975049431770421⟩⟩,
  ⟨⟨-1209199576156145233729385505094770488189726588171967799833196,-1209199576156145233729385505094770488189028409285047650225339⟩,⟨-1570796326794896619231321691639751442098933789159288190768408,-1570796326794896619231321691639751442098235610215865073355663⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071859650103336079928956,-453449841058554462648519564410538933070173473943033711750521⟩,⟨-2007128639793479013462244383761904620460145759901844842228617,-2007128639793479013462244383761904620458459583744173676273143⟩⟩,
  ⟨⟨604599788078072616864692752547385244092653118296886694919197,604599788078072616864692752547385244096724380431627374703718⟩,⟨-1745329251994329576923690768488612713444907519664310139155635,-1745329251994329576923690768488612713440836257419180165811646⟩⟩,
  ⟨⟨982474655626868002405125722889501021648954607945027633057576,982474655626868002405125722889501021658783827488808702167770⟩,⟨-1090830782496455985577306730305382945906709540199912984058611,-1090830782496455985577306730305382945896880320477268533737075⟩⟩,
  ⟨⟨1209199576156145233729385505094770488177512482131353740590625,1209199576156145233729385505094770488201242515325672809276267⟩,⟨-698131700797731830769476307395445085389013772258028418632780,-698131700797731830769476307395445085365283738575354460078598⟩⟩,
  ⟨⟨1360349523175663387945558693231616799184404948011463729859736,1360349523175663387945558693231616799241694424127675284978565⟩,⟨-28644738632254078130981,28644738632269913919509⟩⟩,
  ⟨⟨906899682117108925297039128821077866072878582865589039799025,906899682117108925297039128821077866211187665227166369832023⟩,⟨523598775598298873077107230546583813963707023988129138467709,523598775598298873077107230546583814102016109136928294795399⟩⟩,
  ⟨⟨529024814568313539756606158478962088415898813473339532266821,529024814568313539756606158478962088749806497914093733399211⟩,⟨654498469497873591346384038183229767374123112621896022025412,654498469497873591346384038183229767708030803784421972643490⟩⟩,
  ⟨⟨151149947019518154216173188136846310620609953153903873170292,151149947019518154216173188136846311426734421528207311077439⟩,⟨785398163397448309615660845819875720646230107541019991284768,785398163397448309615660845819875721452354592146548572200284⟩⟩,
  ⟨⟨-302299894039036308432346376273692623020422688178906309793345,-302299894039036308432346376273692621074266061185352950547209⟩,⟨523598775598298873077107230546583813059783233473702718086202,523598775598298873077107230546583815005939899651335107840473⟩⟩,
  ⟨⟨-302299894039036308432346376273692624396563236696277526961234,-302299894039036308432346376273692619698125512667977113737076⟩,⟨174532925199432957692369076848861268995068279540319661357124,174532925199432957692369076848861273693506098168023376755879⟩⟩,
  ⟨⟨-226724920529277231324259782205269472207024318734880386270074,-226724920529277231324259782205269460863992243288308984019743⟩,⟨43633231299858239423092269212215312164555645298812217286590,43633231299858239423092269212215323507587949128269240930116⟩⟩,
  ⟨⟨-151149947019518154216173188136846324715923124839546668173443,-151149947019518154216173188136846297331421249842575615376216⟩,⟨-87266462599716478846184538424430649364394807608160799538944,-87266462599716478846184538424430621979892381246015792517745⟩⟩,
  ⟨⟨-33056017912725732836921781,33056017912725734556562273⟩,⟨-87266462599716478846184538424430668728162172709437663280394,-87266462599716478846184538424430602616125016144734836677472⟩⟩]
def cBox1 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨29998959670852502253334400260293903887583974252636250420687,29998959670852502253334400260293903887583974252661687680853⟩,⟨-5289625983156427915144478140897837194877087266739372873631,-5289625983156427915144478140897837194877087266714078289949⟩⟩,
  ⟨⟨36412289592293591044594635370036879032997090597570579815332,36412289592293591044594635370036879032997090598075750874416⟩,⟨36412289592293591044594635370036879032997090597569716481448,36412289592293591044594635370036879032997090598074923703201⟩⟩,
  ⟨⟨38402992945183783072679524751971870167446745480084862608775,38402992945183783072679524751971870167446745485693359533024⟩,⟨50968177544918804122872932493175650349786646604338390837379,50968177544918804122872932493175650349786646609946851772242⟩⟩,
  ⟨⟨25833037625980735214305679088241204643242916042487596882031,25833037625980735214305679088241204643242916086253987469083⟩,⟨122537218299160116183036736211972226603476706118328900023201,122537218299160116183036736211972226603476706162096222639055⟩⟩,
  ⟨⟨-59240051660172877835280117946062529857582891401905659235794,-59240051660172877835280117946062529857582891137078169034699⟩,⟨161528817855142188049118274010326962840075429476452896709668,161528817855142188049118274010326962840075429741281491865022⟩⟩,
  ⟨⟨-145090868311839164547035042169459007435786558940932784430327,-145090868311839164547035042169459007435786557624649084652554⟩,⟨128492173124419354161201274990896540545587163684794076080978,128492173124419354161201274990896540545587165001071294714001⟩⟩,
  ⟨⟨-200309541600160793748134069426613698940469498888235470632013,-200309541600160793748134069426613698940469493291983371486502⟩,⟨97506677066578677226719567201531313276360803273568181323512,97506677066578677226719567201531313276360808869848998203869⟩⟩,
  ⟨⟨-286598960658293129956382401874164573017518273096364630117975,-286598960658293129956382401874164573017518252080186665417088⟩,⟨-12669154309694873691924785757906602296744271317032127469626,-12669154309694873691924785757906602296744250300934536283404⟩⟩,
  ⟨⟨-243177700521565346812336769081884319932887644337835195409863,-243177700521565346812336769081884319932887572695001864079290⟩,⟨-169252269564962717566763251966816636863469610616029977255517,-169252269564962717566763251966816636863469538973063953813524⟩⟩,
  ⟨⟨-185777510336774922443142335881866333568546523226014003364454,-185777510336774922443142335881866333568546296116376992932794⟩,⟨-241684479578345394784854522305757340442852915620391299861896,-241684479578345394784854522305757340442852688511099670832640⟩⟩,
  ⟨⟨-93029979014440055106215379400418445592445819575023903969084,-93029979014440055106215379400418445592445135772369937405145⟩,⟨-374836135644473539026813299217339788680138391086965768541989,-374836135644473539026813299217339788680137707282969325702396⟩⟩,
  ⟨⟨121302704189551844563774955811481578009262117237016166795833,121302704189551844563774955811481578009264107667134194351766⟩,⟨-412973583972345143427081836236749430808142395989435198796855,-412973583972345143427081836236749430808140405562590094436365⟩⟩,
  ⟨⟨287766244641925184999571079890553431412716506825232030628449,287766244641925184999571079890553431412722184593514085007126⟩,⟨-316696396451847336548801001834400465401944646120432080077270,-316696396451847336548801001834400465401938968347274773866101⟩⟩,
  ⟨⟨403224403637002120913307323409929281316674460903887621134964,403224403637002120913307323409929281316690481247651931602566⟩,⟨-226325503121247451356911273837859885637148418488787751569604,-226325503121247451356911273837859885637132398150798123055203⟩⟩,
  ⟨⟨540567959600913056773917034395921519750579614255447896976580,540567959600913056773917034395921519750624579572667357670754⟩,⟨-22482661873505043743,22482661873505012830⟩⟩,
  ⟨⟨403224403637002120913307323409929281316619510755578964830259,403224403637002120913307323409929281316745431395960587900205⟩,⟨226325503121247451356911273837859885637077448002905679778041,226325503121247451356911273837859885637203368636680194785487⟩⟩,
  ⟨⟨287766244641925184999571079890553431412543186059198870628151,287766244641925184999571079890553431412895505359547244991802⟩,⟨316696396451847336548801001834400465401765647580544126094068,316696396451847336548801001834400465402117966887162727789285⟩⟩,
  ⟨⟨121302704189551844563774955811481578008770374922610340954749,121302704189551844563774955811481578009755849981540020166385⟩,⟨412973583972345143427081836236749430807648663249398106007083,412973583972345143427081836236749430808634138302627187167615⟩⟩,
  ⟨⟨-93029979014440055106215379400418445593823591119743800715182,-93029979014440055106215379400418445591067364227650040699505⟩,⟨374836135644473539026813299217339788678759935736829773461244,374836135644473539026813299217339788681516162633105320726365⟩⟩,
  ⟨⟨-185777510336774922443142335881866333572400691417096105721093,-185777510336774922443142335881866333564692127925294890633737⟩,⟨241684479578345394784854522305757340438998520320941256510601,241684479578345394784854522305757340446707083810549714128887⟩⟩,
  ⟨⟨-243177700521565346812336769081884319943667126347026073202678,-243177700521565346812336769081884319922108090685810986363972⟩,⟨169252269564962717566763251966816636852690056963436417056422,169252269564962717566763251966816636874249092625657513959887⟩⟩,
  ⟨⟨-286598960658293129956382401874164573047665995508261586574708,-286598960658293129956382401874164572987370529668289709060293⟩,⟨12669154309694873691924785757906602266596527889158352207212,12669154309694873691924785757906602326891993728808311496905⟩⟩,
  ⟨⟨-200309541600160793748134069426613699024785473869583934577925,-200309541600160793748134069426613698856153518310634907664567⟩,⟨-97506677066578677226719567201531313360676783851374890676496,-97506677066578677226719567201531313192044828292042288893437⟩⟩,
  ⟨⟨-145090868311839164547035042169459007671598115298144863819963,-145090868311839164547035042169459007199975001267437005411255⟩,⟨-128492173124419354161201274990896540781398721358431846785394,-128492173124419354161201274990896540309775607327433524041853⟩⟩,
  ⟨⟨-59240051660172877835280117946062530517091226443667115926973,-59240051660172877835280117946062529198074556095316712515351⟩,⟨-161528817855142188049118274010326963499583764783424507157654,-161528817855142188049118274010326962180567094434309881434143⟩⟩,
  ⟨⟨25833037625980735214305679088241202798756371768915191004578,25833037625980735214305679088241206487729460359826393153383⟩,⟨-122537218299160116183036736211972228447963250436379773393770,-122537218299160116183036736211972224758990161844045349265148⟩⟩,
  ⟨⟨38402992945183783072679524751971865008860522315763032667024,38402992945183783072679524751971875326032968650015189263320⟩,⟨-50968177544918804122872932493175655508372869775673914274126,-50968177544918804122872932493175645191200423438611328306125⟩⟩,
  ⟨⟨36412289592293591044594635370036864605669385749080569144928,36412289592293591044594635370036893460324795446565761318901⟩,⟨-36412289592293591044594635370036893460324795449312834235839,-36412289592293591044594635370036864605669385746331805888273⟩⟩,
  ⟨⟨29998959670852502253334400260293863537810664609509287195509,29998959670852502253334400260293944237357283895788650670433⟩,⟨5289625983156427915144478140897796845103777618204634242553,5289625983156427915144478140897877544650396915248817017140⟩⟩,
  ⟨⟨-112848632778500337391816203,112848632778500337391576675⟩,⟨-112848632778510877589363037,112848632778510877589498217⟩⟩]
def dBox1 : Fin 31 → CI :=
  ![⟨⟨-41078466350,42797905629⟩,⟨87266462599716478846184538424430635672143594427044206261316,87266462599716478846184538424430635672143594427128293741945⟩⟩,
  ⟨⟨-120842622615757954989806784943385483777488657250454979128321,-120842622615757954989806784943385483777488657248778666141097⟩,⟨84614915292584877405267514585930721146779762463498237790715,84614915292584877405267514585930721146779762465174351426722⟩⟩,
  ⟨⟨-192745854186654778030905517416873603034825852314726806916004,-192745854186654778030905517416873603034825852296030283027681⟩,⟨986518410711267646848346420326177536587103883604397555515,986518410711267646848346420326177536587103902300530521149⟩⟩,
  ⟨⟨-273946262714078519363244623147248542328670506579953565591203,-273946262714078519363244623147248542328670506433027431786528⟩,⟨-108918766188261799001159249611462746692647109646154963228352,-108918766188261799001159249611462746692647109499230046101670⟩⟩,
  ⟨⟨-301555303566433744803763851245664044375061566772028019182001,-301555303566433744803763851245664044375061565874523449424623⟩,⟨-381186939982665997204627535420101085550660212905292066306987,-381186939982665997204627535420101085550660212007787876125167⟩⟩,
  ⟨⟨42526128733004569348934294027425715933541879674810855849377,42526128733004569348934294027425715933541884188432084780242⟩,⟨-607100304604663942637492387094525792213327545684508254174286,-607100304604663942637492387094525792213327541170871042109718⟩⟩,
  ⟨⟨309740452620390924462611119479835563004846063978111780002448,309740452620390924462611119479835563004846083429543008790431⟩,⟨-526855803397671773616560872029050303896874041140956332842642,-526855803397671773616560872029050303896874021689593723235379⟩⟩,
  ⟨⟨613004456196778685761592063819536537409760968296400831934949,613004456196778685761592063819536537409761042411604799453125⟩,⟨-456849968060734038620080407949651178552847648407384900168365,-456849968060734038620080407949651178552847574291984278979346⟩⟩,
  ⟨⟨973217603076608428958465219050453071392107198673660857745283,973217603076608428958465219050453071392107455009921322021447⟩,⟨-85251547340354678018038376846560435026242137270708542305871,-85251547340354678018038376846560435026241880934828837067870⟩⟩,
  ⟨⟨881104183903313356849043297310709158045419908512806056780455,881104183903313356849043297310709158045420731974629801378128⟩,⟨410976297997245055461030110569485862966928351105015857957293,410976297997245055461030110569485862966929174567823962094835⟩⟩,
  ⟨⟨747258535260107629183722599194757550390940690958699024136991,747258535260107629183722599194757550390943198083799088383764⟩,⟨694271868802801645833572922671994030574529998126355690101929,694271868802801645833572922671994030574532505248030938150679⟩⟩,
  ⟨⟨515326178143969869791379336022821403248060878803180267901860,515326178143969869791379336022821403248068238212617869365945⟩,⟨1192024815138059185542968415968115033644867714728197058047435,1192024815138059185542968415968115033644875074146050635023917⟩⟩,
  ⟨⟨-260902243696474705934731452710099736859428924177386095909747,-260902243696474705934731452710099736859407811812226546746985⟩,⟨1418341086086638108125565285911980755702865535116597169396061,1418341086086638108125565285911980755702886647467316647842496⟩⟩,
  ⟨⟨-787518037653591518317529097894762201208413534789144057194991,-787518037653591518317529097894762201208353761887031850160319⟩,⟨1113405382887101827566158704131505197060832890956619645866471,1113405382887101827566158704131505197060892663879759573895379⟩⟩,
  ⟨⟨-1305552494241480659616681533352383178504853387043380855649583,-1305552494241480659616681533352383178504685316193973235773930⟩,⟨870766477547492771885223515006479966583789104583413672925025,870766477547492771885223515006479966583957175406313822248496⟩⟩,
  ⟨⟨-1678229438519403166598170136390244418672365853545498562219756,-1678229438519403166598170136390244418671894789525608488010864⟩,⟨-235532024325923238987,235532024325923250068⟩⟩,
  ⟨⟨-1305552494241480659616681533352383178505428592179541918609272,-1305552494241480659616681533352383178504110111057812172812126⟩,⟨-870766477547492771885223515006479966584532380540854062464459,-870766477547492771885223515006479966583213899448873432691696⟩⟩,
  ⟨⟨-787518037653591518317529097894762201210227860433890504189687,-787518037653591518317529097894762201206539436242285403157428⟩,⟨-1113405382887101827566158704131505197062706989528293933847309,-1113405382887101827566158704131505197059018565308085285909172⟩⟩,
  ⟨⟨-260902243696474705934731452710099736864576583527203446692233,-260902243696474705934731452710099736854260152462409195946649⟩,⟨-1418341086086638108125565285911980755708034306812214179050904,-1418341086086638108125565285911980755697717875771699638199446⟩⟩,
  ⟨⟨515326178143969869791379336022821403233637967505998365720918,515326178143969869791379336022821403262491149509799771578144⟩,⟨-1192024815138059185542968415968115033659297985448199721059600,-1192024815138059185542968415968115033630444803426047972043374⟩⟩,
  ⟨⟨747258535260107629183722599194757550350594027238850253126245,747258535260107629183722599194757550431289861803647859441337⟩,⟨-694271868802801645833572922671994030614879168963566003786739,-694271868802801645833572922671994030534183334410820624516366⟩⟩,
  ⟨⟨881104183903313356849043297310709157932576753625880065166559,881104183903313356849043297310709158158263886861555793052812⟩,⟨-410976297997245055461030110569485863079772329457177071877569,-410976297997245055461030110569485862854085196215662748242890⟩⟩,
  ⟨⟨973217603076608428958465219050453071076510883519779787642753,973217603076608428958465219050453071707703770163802392195541⟩,⟨85251547340354678018038376846560434710645565782374784141937,85251547340354678018038376846560435341838452423162595147454⟩⟩,
  ⟨⟨613004456196778685761592063819536536527113457927827404204261,613004456196778685761592063819536538292408552780178227260656⟩,⟨456849968060734038620080407949651177670200063923475221344020,456849968060734038620080407949651179435495158775893957707135⟩⟩,
  ⟨⟨309740452620390924462611119479835560536292688316990889954393,309740452620390924462611119479835565473399459090663898914184⟩,⟨526855803397671773616560872029050301428320646029771808223524,526855803397671773616560872029050306365427416800778247748973⟩⟩,
  ⟨⟨42526128733004569348934294027425709029590463334956857750034,42526128733004569348934294027425722837493300528286082949395⟩,⟨607100304604663942637492387094525785309376124833014624433556,607100304604663942637492387094525799117278962022364671738379⟩⟩,
  ⟨⟨-301555303566433744803763851245664063683756870268597624130420,-301555303566433744803763851245664025066366262377953844416414⟩,⟨381186939982665997204627535420101066241964908515370418651668,381186939982665997204627535420101104859355516397709523662793⟩⟩,
  ⟨⟨-273946262714078519363244623147248596330457556985196009238792,-273946262714078519363244623147248488326883456027784988091771⟩,⟨108918766188261799001159249611462692690860059102025734585244,108918766188261799001159249611462800694434160043359274620738⟩⟩,
  ⟨⟨-192745854186654778030905517416873754064864843597441218223498,-192745854186654778030905517416873452004786861013315871686098⟩,⟨-986518410711267646848346420326328566626095169241646039328,-986518410711267646848346420326026506548112616663282167753⟩⟩,
  ⟨⟨-120842622615757954989806784943385906172263414945360694022736,-120842622615757954989806784943385061382713899553872951225784⟩,⟨-84614915292584877405267514585931143541554520129201171465061,-84614915292584877405267514585930298752005004799471417888058⟩⟩,
  ⟨⟨-1181336818385429267109384281,1181336818385429268828831583⟩,⟨-87266462599716478846184538424431817008961979795880611680030,-87266462599716478846184538424429454335325209058291888462391⟩⟩]
def cBox3 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨26380642397055816535097180326270597663156998636365217531135,26380642397055816535097180326270597663156998636395178123378⟩,⟨-15230870989335429967337177468944677677953239826004081156957,-15230870989335429967337177468944677677953239825974164336873⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651674003513703,30461741978670859934674354937889355355906479652282086066131⟩,⟨8162199163230086799154349223237515385498962030890499607046,8162199163230086799154349223237515385498962031498468358507⟩⟩,
  ⟨⟨34542841560285903334251529549508113048655960664120268414546,34542841560285903334251529549508113048655960671030560222546⟩,⟨-1093527337124743630971520977530353093044684239855755441141,-1093527337124743630971520977530353093044684232945717712125⟩⟩,
  ⟨⟨36436886467651459471885662206066164555316073182621529662938,36436886467651459471885662206066164555316073238122105867080⟩,⟨46786140305131033532983053384364386126904403686616934735997,46786140305131033532983053384364386126904403742117755097349⟩⟩,
  ⟨⟨-11950288977961199074422614536353618398819187290964186611494,-11950288977961199074422614536353618398819186942608126573401⟩,⟨75060827609552406205714366367193035296721514719366139531590,75060827609552406205714366367193035296721515067722750001698⟩⟩,
  ⟨⟨-57135394142610607594080444562662607698492735125683487744903,-57135394142610607594080444562662607698492733311043429215990⟩,⟨58736429283092232607405667920718004525723589923836891411945,58736429283092232607405667920718004525723591738473839599284⟩⟩,
  ⟨⟨-72873772935302918943771324412132329110632150516484158423908,-72873772935302918943771324412132329110632142325001767473263⟩,⟨65297593305840694393234793785900123083991692153810260682257,65297593305840694393234793785900123083991700345308157122355⟩⟩,
  ⟨⟨-135984311566894126075063076242971746008534490785121338932540,-135984311566894126075063076242971746008534457609879493953867⟩,⟨15738378792692311349690879849469721412139395614781260660934,15738378792692311349690879849469721412139428789978232901438⟩⟩,
  ⟨⟨-108002634029356684526640672558645751518146681012554241328537,-108002634029356684526640672558645751518146556884105933380720⟩,⟨-69593190923928688050856761479541269831498155775803644164493,-69593190923928688050856761479541269831498031647276921859138⟩⟩,
  ⟨⟨-96774350891225317092616553484839565908270740576307491628901,-96774350891225317092616553484839565908270300732327565069270⟩,⟨-77247882283801893467657408322253741482811103288246826794015,-77247882283801893467657408322253741482810663444445539842948⟩⟩,
  ⟨⟨-77833901817569755716275226919259050841670148116350408327648,-77833901817569755716275226919259050841668642336363041531516⟩,⟨-156682819241853274197257858599568189151711888095836259409370,-156682819241853274197257858599568189151710382315150078421154⟩⟩,
  ⟨⟨34835851327169834458560438848010767728082689539372298495118,34835851327169834458560438848010767728087743655788469957974⟩,⟨-177810322989758322835542227120209410404404156163529334656166,-177810322989758322835542227120209410404399102048981427742909⟩⟩,
  ⟨⟨109896678936722240664274805215203803024798335007706046668806,109896678936722240664274805215203803024815127974544783232856⟩,⟨-118644897633720189712046973035446627769172601867213477479660,-118644897633720189712046973035446627769155808897450297316481⟩⟩,
  ⟨⟨155510780174317549700022221405557570433966341780917105481829,155510780174317549700022221405557570434021881190027732119890⟩,⟨-104936550054455403891770902708077081293797252388411475274061,-104936550054455403891770902708077081293741712982612436066387⟩⟩,
  ⟨⟨264978463038093889848207440456716595349195339411431168236273,264978463038093889848207440456716595349378680756223401317563⟩,⟨-91670674242226092776,91670674242226102765⟩⟩,
  ⟨⟨155510780174317549700022221405557570433691701877454414662226,155510780174317549700022221405557570434296521093490422939854⟩,⟨104936550054455403891770902708077081293467073079387755755520,104936550054455403891770902708077081294071892291636155606841⟩⟩,
  ⟨⟨109896678936722240664274805215203803023809338896479465284800,109896678936722240664274805215203803025804124085771364620788⟩,⟨118644897633720189712046973035446627768166812785961697216292,118644897633720189712046973035446627770161597978702077606229⟩⟩,
  ⟨⟨34835851327169834458560438848010767724795870813138481440555,34835851327169834458560438848010767731374562382022287024605⟩,⟨177810322989758322835542227120209410401112283323405429648661,177810322989758322835542227120209410407690974889105332779984⟩⟩,
  ⟨⟨-77833901817569755716275226919259050852517302472949950343385,-77833901817569755716275226919259050830821487979763499492388⟩,⟨156682819241853274197257858599568189140863227957734846998077,156682819241853274197257858599568189162559042453251490860074⟩⟩,
  ⟨⟨-96774350891225317092616553484839565944045616947391994109868,-96774350891225317092616553484839565872495424361243062554168⟩,⟨77247882283801893467657408322253741447035787073810597324326,77247882283801893467657408322253741518585979658881769330557⟩⟩,
  ⟨⟨-108002634029356684526640672558645751636128506405768859898583,-108002634029356684526640672558645751400164731490891314771595⟩,⟨69593190923928688050856761479541269713516206253930679347684,69593190923928688050856761479541269949479981169149886676845⟩⟩,
  ⟨⟨-135984311566894126075063076242971746397624243015946764725521,-135984311566894126075063076242971745619444705379054068127023⟩,⟨-15738378792692311349690879849469721801229181020763604048659,-15738378792692311349690879849469721023049643383995889533120⟩⟩,
  ⟨⟨-72873772935302918943771324412132330393802371823329520275513,-72873772935302918943771324412132327827461921018156405604495⟩,⟨-65297593305840694393234793785900124367161921652177612931228,-65297593305840694393234793785900121800821470846940804909777⟩⟩,
  ⟨⟨-57135394142610607594080444562662611930230381450410414175244,-57135394142610607594080444562662603466755086986316502793667⟩,⟨-58736429283092232607405667920718008757461238063189760738102,-58736429283092232607405667920718000293985943599120970316478⟩⟩,
  ⟨⟨-11950288977961199074422614536353632354569682929643949327113,-11950288977961199074422614536353604443068691303928363892837⟩,⟨-75060827609552406205714366367193049252472010706406377323496,-75060827609552406205714366367193021340971019080682512245773⟩⟩,
  ⟨⟨36436886467651459471885662206066118530966708629436170124419,36436886467651459471885662206066210579665437791307465349850⟩,⟨-46786140305131033532983053384364432151253768295302589732578,-46786140305131033532983053384364340102555039133432100115236⟩⟩,
  ⟨⟨34542841560285903334251529549507961266010157176099065759718,34542841560285903334251529549508264831301764159051762814384⟩,⟨1093527337124743630971520977530201310398880744924279740179,1093527337124743630971520977530504875690487727877193429708⟩⟩,
  ⟨⟨30461741978670859934674354937888854795401330306269893243792,30461741978670859934674354937889855916411628997686196283165⟩,⟨-8162199163230086799154349223238015946004111376902792613822,-8162199163230086799154349223237014824993812685486175302651⟩⟩,
  ⟨⟨26380642397055816535097180326268946876151745348066001833047,26380642397055816535097180326272248450162251924694393795037⟩,⟨15230870989335429967337177468943026890947986537674806797702,15230870989335429967337177468946328464958493114303438769523⟩⟩,
  ⟨⟨-5444092589566305490864327246,5444092589566305490864337753⟩,⟨-5444092589566305491016417430,5444092589566305491016498934⟩⟩]
def dBox3 : Fin 31 → CI :=
  ![⟨⟨-57553376622,59272815901⟩,⟨87266462599716478846184538424430635672143594427027726413884,87266462599716478846184538424430635672143594427144773589200⟩⟩,
  ⟨⟨-63883484419801675369988649712415675351528592915164813409672,-63883484419801675369988649712415675351528592912785472412528⟩,⟨63883484419801675369988649712415675351528592912786995933470,63883484419801675369988649712415675351528592915166250872993⟩⟩,
  ⟨⟨-122340929869588684060478371492453076153066096710332673449973,-122340929869588684060478371492453076153066096683173685658060⟩,⟨43633231299858239423092269212215317836071797199965343974023,43633231299858239423092269212215317836071797227123982778611⟩⟩,
  ⟨⟨-191650453259405026109965949137247026054585778851715610668774,-191650453259405026109965949137247026054585778632141491428845⟩,⟨-63883484419801675369988649712415675351528593023760913061179,-63883484419801675369988649712415675351528592804187447272732⟩⟩,
  ⟨⟨-221298881559262564644760854272891191985517192575542895317234,-221298881559262564644760854272891191985517191185252375724027⟩,⟨-221298881559262564644760854272891191985517192575539518297850,-221298881559262564644760854272891191985517191185249036264460⟩⟩,
  ⟨⟨-3659279797584541,3659272000464133⟩,⟨-383300906518810052219931898274494052109171561143134271015312,-383300906518810052219931898274494052109171553824578137375556⟩⟩,
  ⟨⟨145723908049503487536674260204468036473681081500050632623718,145723908049503487536674260204468036473681114919674882969381⟩,⟨-352198575458837282914037661909537145493732600230833697931909,-352198575458837282914037661909537145493732566811225114870516⟩⟩,
  ⟨⟨383300906518810052219931898274494052109171489019659069759819,383300906518810052219931898274494052109171625948051654998898⟩,⟨-302299894039036308432346376273692622047344443146350316862233,-302299894039036308432346376273692622047344306217908767860475⟩⟩,
  ⟨⟨593747710138043283505694896682628694994706312193017759914422,593747710138043283505694896682628694994706830010695034001761⟩,⟨-81001012479773743787585522000801430061827441710522248269854,-81001012479773743787585522000801430061826923892945512845455⟩⟩,
  ⟨⟨564099281838185744970899991546984529063774232412984430263652,564099281838185744970899991546984529063776083513798132104895⟩,⟨185385003139462291051366932713617820444268441566046087580085,185385003139462291051366932713617820444270292667091668392013⟩⟩,
  ⟨⟨482258858208483932804214381054932167941619463445470994226505,482258858208483932804214381054932167941625841889534610612101⟩,⟨398964531818666889866429439333567066134959397325625750910310,398964531818666889866429439333567066134965775768874484005865⟩⟩,
  ⟨⟨338213772458836582025740297832965993588581449486187949731371,338213772458836582025740297832965993588602949405719485037438⟩,⟨691866250677789095710877290971815879766821593830501700478230,691866250677789095710877290971815879766843093752181852605590⟩⟩,
  ⟨⟨-140297869079488820857175332272089761923725814007919819228619,-140297869079488820857175332272089761923654204149408164759152⟩,⟨860133725757279318344647351397047945500767316092802267063981,860133725757279318344647351397047945500838925947517723913392⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071135124596116704132131,-453449841058554462648519564410538933070897999450265527544273⟩,⟨704397150917674565828075323819074290987346604466416153693731,704397150917674565828075323819074290987583729617700498008392⟩⟩,
  ⟨⟨-831324708607349848188952534752654710630588630641637432593240,-831324708607349848188952534752654710629805430110063082418413⟩,⟨554701106658271642383001466911540720647908940263036226791737,554701106658271642383001466911540720648692140787669199609009⟩⟩,
  ⟨⟨-966196538716824002366628939092366198005188065622451152095471,-966196538716824002366628939092366198002603835024186467293264⟩,⟨-1292115302852395923905,1292115302852395893723⟩⟩,
  ⟨⟨-831324708607349848188952534752654710634458942821596342067659,-831324708607349848188952534752654710625935117930104172965848⟩,⟨-554701106658271642383001466911540720652562452967353360051386,-554701106658271642383001466911540720644038628083352066405498⟩⟩,
  ⟨⟨-453449841058554462648519564410538933085072446039499986120912,-453449841058554462648519564410538933056960678006882245592743⟩,⟨-704397150917674565828075323819074291001521051062023133809238,-704397150917674565828075323819074290973409283022093517937295⟩⟩,
  ⟨⟨-140297869079488820857175332272089761970045103633426552130169,-140297869079488820857175332272089761877334914523901431900369⟩,⟨-860133725757279318344647351397047945547158215571894387637691,-860133725757279318344647351397047945454448026468425603368655⟩⟩,
  ⟨⟨338213772458836582025740297832965993435718407295472331422087,338213772458836582025740297832965993741465991596435103309007⟩,⟨-691866250677789095710877290971815879919706135944058652429430,-691866250677789095710877290971815879613958551638624900667879⟩⟩,
  ⟨⟨482258858208483932804214381054932167437463417010086688006308,482258858208483932804214381054932168445781888324918916808880⟩,⟨-398964531818666889866429439333567066639121822203265451152436,-398964531818666889866429439333567065630803350891234783765981⟩⟩,
  ⟨⟨564099281838185744970899991546984527401119821573169024549201,564099281838185744970899991546984530726430494353613537814436⟩,⟨-185385003139462291051366932713617822106924703507420476938893,-185385003139462291051366932713617818781614030725717279032108⟩⟩,
  ⟨⟨593747710138043283505694896682628689511473597878792263225304,593747710138043283505694896682628700477939544324920530702893⟩,⟨81001012479773743787585522000801424578594209578883299637399,81001012479773743787585522000801435545060156024584461474009⟩⟩,
  ⟨⟨383300906518810052219931898274494034026143299016833528034224,383300906518810052219931898274494070192199815950877196747072⟩,⟨302299894039036308432346376273692603964316116215029685358024,302299894039036308432346376273692640130372633149229399350435⟩⟩,
  ⟨⟨145723908049503487536674260204467976838077077791373129513586,145723908049503487536674260204468096109285118628352386104346⟩,⟨352198575458837282914037661909537085858128563102576928651814,352198575458837282914037661909537205129336603939481884124643⟩⟩,
  ⟨⟨-196670890247477338048124737,196670890247477330251024249⟩,⟨383300906518810052219931898274493855438281310006507796415149,383300906518810052219931898274494248780061804961204611940121⟩⟩,
  ⟨⟨-221298881559262564644760854272891840581933795336493790511131,-221298881559262564644760854272890543389100588424301480520059⟩,⟨221298881559262564644760854272890543389100588424302440206359,221298881559262564644760854272891840581933795336486114314525⟩⟩,
  ⟨⟨-191650453259405026109965949137249165045826934743286571274740,-191650453259405026109965949137244887063344622740570530824901⟩,⟨63883484419801675369988649712413536360287436912616160697714,63883484419801675369988649712417814342769748915332199593870⟩⟩,
  ⟨⟨-122340929869588684060478371492460130283204065679432215147624,-122340929869588684060478371492446022022928127714074143973211⟩,⟨-43633231299858239423092269212222371966209766196223128912221,-43633231299858239423092269212208263705933828230866197878557⟩⟩,
  ⟨⟨-63883484419801675369988649712438939005463196604387953178991,-63883484419801675369988649712392411697593989223562332663009⟩,⟨-63883484419801675369988649712438939005463196604389006695040,-63883484419801675369988649712392411697593989223564240141174⟩⟩,
  ⟨⟨-76720670558088461129672871711,76720670558088461131392289717⟩,⟨-87266462599716478846184538424507356342701682888216603652120,-87266462599716478846184538424353915001585505965955896370225⟩⟩]
def cBox4 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨23335048170484914988453136141165932166689530925471369991158,23335048170484914988453136141165932166689530925502263631162⟩,⟨-19580430313357954872034103663248574042515901359362555589565,-19580430313357954872034103663248574042515901359331658497519⟩⟩,
  ⟨⟨21158503932625711660577912563591348779508349066591077148821,21158503932625711660577912563591348779508349067220840391269⟩,⟨-315060531222,314579865845⟩⟩,
  ⟨⟨19022905560292027148203397875765926271331786028172343959152,19022905560292027148203397875765926271331786035364007135730⟩,⟨-11238735295230177498455422922862826664475463368651476346283,-11238735295230177498455422922862826664475463361459870150680⟩⟩,
  ⟨⟨21601658916489958016749400216749190355793343262982881056958,21601658916489958016749400216749190355793343321095554054087⟩,⟨39160860626715909744068207326497148085031802689637355611586,39160860626715909744068207326497148085031802747750191053237⟩⟩,
  ⟨⟨-12714850338646540342663470969621096897930737752393996691233,-12714850338646540342663470969621096897930737384785967542922⟩,⟨71236654636935182005124223443450634439643411686550076528697,71236654636935182005124223443450634439643412054158507291123⟩⟩,
  ⟨⟨-38045811120584054296406795751531852542663573030676277380368,-38045811120584054296406795751531852542663571096395596541509⟩,⟨59125074413913984959846074110538630118742239627151362529417,59125074413913984959846074110538630118742241561431113784116⟩⟩,
  ⟨⟨-32180910882802813847038356498544864745547522247747482630740,-32180910882802813847038356498544864745547513403236469549574⟩,⟨65024432948229564068934758643956150365648921792069863860970,65024432948229564068934758643956150365648930636586835700744⟩⟩,
  ⟨⟨-85159062445418130629484555687021558452327646340510013820065,-85159062445418130629484555687021558452327609938777758828528⟩,⟨12424443377411235872378929598988968147988953111195515492406,12424443377411235872378929598988968147988989512910164066197⟩⟩,
  ⟨⟨-66851116900632001562589444970425381813368137994664201440015,-66851116900632001562589444970425381813367999095083664717544⟩,⟨-72369723729060850949380130035345095086138671827902371781602,-72369723729060850949380130035345095086138532928289351221381⟩⟩,
  ⟨⟨-78407852239908397467773141127718887502641837277274721908420,-78407852239908397467773141127718887502641333625392925515468⟩,⟨-69283379607073882943713190525738676973741082716764745100086,-69283379607073882943713190525738676973740579064952845648613⟩⟩,
  ⟨⟨-84937484953486007451398811860442637664186015806762699234014,-84937484953486007451398811860442637664184246247391746937189⟩,⟨-127777551928136805667194335637589149099039311909684515108860,-127777551928136805667194335637589149099037542350054480434448⟩⟩,
  ⟨⟨5864900237781240449368439252986987797112999783897117405259,5864900237781240449368439252986987797119108692191705722769⟩,⟨-128408454020987867903559264636277307092486125938932354241285,-128408454020987867903559264636277307092480017031367772382309⟩⟩,
  ⟨⟨73479489509565178277798732860480570126029801955687251582191,73479489509565178277798732860480570126050707570018712588640⟩,⟨-64900873638724093122624175705008525364534325102598926976923,-64900873638724093122624175705008525364513419487029637423169⟩⟩,
  ⟨⟨118490521837470569544970834409744724402317446785651263385886,118490521837470569544970834409744724402388713029893319977031⟩,⟨-66664844823700824303245011295591144004499340279227755035756,-66664844823700824303245011295591144004428074036443550252889⟩⟩,
  ⟨⟨230688121433536691022465447089643199439542397220200823347795,230688121433536691022465447089643199439784972362506805973619⟩,⟨-121287571946129047987,121287571946129070351⟩⟩,
  ⟨⟨118490521837470569544970834409744724401940461236508263295864,118490521837470569544970834409744724402765698579036320090923⟩,⟨66664844823700824303245011295591144004051088487405460896076,66664844823700824303245011295591144004876325828265844429167⟩⟩,
  ⟨⟨73479489509565178277798732860480570124636762842644596406857,73479489509565178277798732860480570127443746683061367801926⟩,⟨64900873638724093122624175705008525363120380373835293453113,64900873638724093122624175705008525365927364215793270962566⟩⟩,
  ⟨⟨5864900237781240449368439252986987792342398576168191787787,5864900237781240449368439252986987801889709899920631376300⟩,⟨128408454020987867903559264636277307087709415823971984961494,128408454020987867903559264636277307097256727146328141652297⟩⟩,
  ⟨⟨-84937484953486007451398811860442637680421441146589008337286,-84937484953486007451398811860442637647948820907565437815142⟩,⟨127777551928136805667194335637589149082802117009811009426113,127777551928136805667194335637589149115274737249927986088470⟩⟩,
  ⟨⟨-78407852239908397467773141127718887557864904066543710445411,-78407852239908397467773141127718887447418266836123936985150⟩,⟨69283379607073882943713190525738676918517512275921534881333,69283379607073882943713190525738677028964149505796055834472⟩⟩,
  ⟨⟨-66851116900632001562589444970425382001194822779695601758422,-66851116900632001562589444970425381625541314310052264428698⟩,⟨72369723729060850949380130035345094898311848143195207453267,72369723729060850949380130035345095273965356612996515529493⟩⟩,
  ⟨⟨-85159062445418130629484555687021559091168022569418787150648,-85159062445418130629484555687021557813487233709868985537669⟩,⟨-12424443377411235872378929598988968786829365741804078330620,-12424443377411235872378929598988967509148576882301601223579⟩⟩,
  ⟨⟨-32180910882802813847038356498544866918385173841648787555553,-32180910882802813847038356498544862572709861809335164656712⟩,⟨-65024432948229564068934758643956152538486582230499002751681,-65024432948229564068934758643956148192811270198157696779245⟩⟩,
  ⟨⟨-38045811120584054296406795751531859932965614362710824467245,-38045811120584054296406795751531845152361529764361049463015⟩,⟨-59125074413913984959846074110538637509044282893459916221105,-59125074413913984959846074110538622728440198295122560045484⟩⟩,
  ⟨⟨-12714850338646540342663470969621122033984558809008616348506,-12714850338646540342663470969621071761876916328171347864182⟩,⟨-71236654636935182005124223443450659575697233110774752356574,-71236654636935182005124223443450609303589590629933831418804⟩⟩,
  ⟨⟨21601658916489958016749400216749104862507943426898758811011,21601658916489958016749400216749275849078743157179676344043⟩,⟨-39160860626715909744068207326497233578317202583834051577799,-39160860626715909744068207326497062591746402853553495064467⟩⟩,
  ⟨⟨19022905560292027148203397875765635489735739446905115233216,19022905560292027148203397875766217052927832616631235909325⟩,⟨11238735295230177498455422922862535882879416780192676489515,11238735295230177498455422922863117446071509949918669997263⟩⟩,
  ⟨⟨21158503932625711660577912563590359766906904161134952283649,21158503932625711660577912563592337792109793972676965285256⟩,⟨-989012601444905770726648235,989012601444905771207274557⟩⟩,
  ⟨⟨23335048170484914988453136141162568315816176093977176663676,23335048170484914988453136141169296017562885756996456952997⟩,⟨19580430313357954872034103663245210191642546527837496914500,19580430313357954872034103663251937893389256190856717122854⟩⟩,
  ⟨⟨-11441201741654861532390186640,11441201741654861532390146191⟩,⟨-11441201741654861532388702650,11441201741654861532388667269⟩⟩]
def dBox4 : Fin 31 → CI :=
  ![⟨⟨-61335988179,63055427458⟩,⟨87266462599716478846184538424430635672143594427023925048585,87266462599716478846184538424430635672143594427148574954246⟩⟩,
  ⟨⟨-38962345218975078297758095199889543471863545038551833303255,-38962345218975078297758095199889543471863545036010353287715⟩,⟨46433514890609389663463594161459210988561205761973717378190,46433514890609389663463594161459210988561205764515162728764⟩⟩,
  ⟨⟨-96306404382542279143365458941938201307087263235465373886153,-96306404382542279143365458941938201307087263206315402763496⟩,⟨47288741911422358256006940368167163902478793046216315502016,47288741911422358256006940368167163902478793075366093968368⟩⟩,
  ⟨⟨-164681427509327871503793225800508945836502570138465118564352,-164681427509327871503793225800508945836502569901380238169132⟩,⟨-71140272112867288409087347456432251929765918873828194412247,-71140272112867288409087347456432251929765918636743643071795⟩⟩,
  ⟨⟨-192612808765084558286730917883876402614174527198130001245637,-192612808765084558286730917883876402614174525685435577640316⟩,⟨-180133492380935258173111726747349057649266006709920564139917,-180133492380935258173111726747349057649266005197226057778012⟩⟩,
  ⟨⟨-13531480489809717287620037663662634812830386699517068165393,-13531480489809717287620037663662634812830378658207357022005⟩,⟨-311888413301322945034931880590702964071398988912407574160020,-311888413301322945034931880590702964071398980871096456491571⟩⟩,
  ⟨⟨96306404382542279143365458941938201307087244630796738802841,96306404382542279143365458941938201307087281810982107267203⟩,⟨-293637450281380315362594123400925662349090694886749434460276,-293637450281380315362594123400925662349090657706565244061075⟩⟩,
  ⟨⟨329362855018655743007586451601017891673005062677664649917670,329362855018655743007586451601017891673005217402022402347355⟩,⟨-235147574006953356145101883235782925836654326399248428436730,-235147574006953356145101883235782925836654171674884679339598⟩⟩,
  ⟨⟨483881738840902475204256891041046937967327014360385252523699,483881738840902475204256891041046937967327610656588115341453⟩,⟨-62559705377458580100560785129457594730939179583140563009939,-62559705377458580100560785129457594730938583286952430952939⟩⟩,
  ⟨⟨480512802038173897223759639737864202696676237551049044637938,480512802038173897223759639737864202696678417210771667622804⟩,⟨119518843573414859720378920360427403156897855940808174710755,119518843573414859720378920360427403156900035600560152533052⟩⟩,
  ⟨⟨401106814948169913348511469762771371473066580689739835917033,401106814948169913348511469762771371473074283243175278833362⟩,⟨328869830808985104064572417765409300727690396584432340267883,328869830808985104064572417765409300727698099137764832534003⟩⟩,
  ⟨⟨263337548820061230134588281073803078575467485477687884484926,263337548820061230134588281073803078575494173812005523839513⟩,⟨548981043878214482827861742569021830146611711013670732982564,548981043878214482827861742569021830146638399348272277133707⟩⟩,
  ⟨⟨-116887035656925234893274285599668630415636393688088877388385,-116887035656925234893274285599668630415544876535596590951387⟩,⟨702462722466953660607521737278861906616068768314366488566048,702462722466953660607521737278861906616160285466332237369951⟩⟩,
  ⟨⟨-364494186657385914538182970894237759433254026641385685056314,-364494186657385914538182970894237759432941740025025708960188⟩,⟨606381090603516228990069350198336579334251105177390491943041,606381090603516228990069350198336579334563391794524121607853⟩⟩,
  ⟨⟨-702538288711068969573160229280421806368935320615150504822212,-702538288711068969573160229280421806367871910553732132283435⟩,⟨464514864869249154222048529093835087626439164273373723793110,464514864869249154222048529093835087627502574333792982484521⟩⟩,
  ⟨⟨-728988373314771829076365941788475518868004913829704509216440,-728988373314771829076365941788475518864386619503120285591789⟩,⟨-1809147163842521171360,1809147163842521156582⟩⟩,
  ⟨⟨-702538288711068969573160229280421806374557635577040680039044,-702538288711068969573160229280421806362249595591841957072827⟩,⟨-464514864869249154222048529093835087633124889295629595671665,-464514864869249154222048529093835087620816849311537110633298⟩⟩,
  ⟨⟨-364494186657385914538182970894237759454029720422533539144787,-364494186657385914538182970894237759412166046243877854880625⟩,⟨-606381090603516228990069350198336579355339085575826652896376,-606381090603516228990069350198336579313475411396087960676875⟩⟩,
  ⟨⟨-116887035656925234893274285599668630486784991395373874717031,-116887035656925234893274285599668630344396278828311593630402⟩,⟨-702462722466953660607521737278861906687308883173416370793424,-702462722466953660607521737278861906544920170607282355160387⟩⟩,
  ⟨⟨263337548820061230134588281073803078333332649478902443346565,263337548820061230134588281073803078817629009810790964974087⟩,⟨-548981043878214482827861742569021830388773235347259276158244,-548981043878214482827861742569021829904476875014683733973347⟩⟩,
  ⟨⟨401106814948169913348511469762771370649470571000186738690862,401106814948169913348511469762771372296670292932728376060531⟩,⟨-328869830808985104064572417765409301551294108827148472882746,-328869830808985104064572417765409299904094386895048699935326⟩⟩,
  ⟨⟨480512802038173897223759639737864199895431646918507475251495,480512802038173897223759639737864205497923007843313237012761⟩,⟨-119518843573414859720378920360427405958144626233190893901638,-119518843573414859720378920360427400355653265308177433362533⟩⟩,
  ⟨⟨483881738840902475204256891041046928439670329510506639545240,483881738840902475204256891041046947494984295506466728321270⟩,⟨62559705377458580100560785129457585203281898437099808457455,62559705377458580100560785129457604258595864432993185480426⟩⟩,
  ⟨⟨329362855018655743007586451601017859267333807598702567288492,329362855018655743007586451601017924078676472480984484971906⟩,⟨235147574006953356145101883235782893430982916595915321445908,235147574006953356145101883235782958242325581478217786304444⟩⟩,
  ⟨⟨96306404382542279143365458941938091088222840407995347926217,96306404382542279143365458941938311525951686033783498133350⟩,⟨293637450281380315362594123400925552130226253483768262602661,293637450281380315362594123400925772567955099109546415897323⟩⟩,
  ⟨⟨-13531480489809717287620037663663009691596147243796956896614,-13531480489809717287620037663662259934064618113927468302674⟩,⟨311888413301322945034931880590702589192633220326814446887146,311888413301322945034931880590703338950164749456689583751452⟩⟩,
  ⟨⟨-192612808765084558286730917883877677659873417383717136350221,-192612808765084558286730917883875127568475635499848442543025⟩,⟨180133492380935258173111726747347782603567115011639484226100,180133492380935258173111726747350332694964896895507137686354⟩⟩,
  ⟨⟨-164681427509327871503793225800513282549282079572755888821349,-164681427509327871503793225800504609123723060467089467910986⟩,⟨71140272112867288409087347456427915216986409202452788121019,71140272112867288409087347456436588642545428308119049360167⟩⟩,
  ⟨⟨-96306404382542279143365458941952951427611035953798227593934,-96306404382542279143365458941923451186563490487982549046326⟩,⟨-47288741911422358256006940368181914023002565793698971292794,-47288741911422358256006940368152413781955020327883438184174⟩⟩,
  ⟨⟨-38962345218975078297758095199939711898164173859584310227619,-38962345218975078297758095199839375045562916214977876350022⟩,⟨-46433514890609389663463594161509379414861834585547632463264,-46433514890609389663463594161409042562260576940941247658600⟩⟩,
  ⟨⟨-170633927595723044306530696515,170633927595723044308250146856⟩,⟨-87266462599716478846184538424601269599739317471393781034627,-87266462599716478846184538424260001744547871382778718992105⟩⟩]
def cBox7 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨10418529357494547381300296597045329845068072893287803787370,10418529357494547381300296597045329845068072893315929507905⟩,⟨-28624674153641342903597614282063769361566618192227664229079,-28624674153641342903597614282063769361566618192199409496302⟩⟩,
  ⟨⟨-7509235714253920232838064955834716248347259132562987419194,-7509235714253920232838064955834716248347259131996996166254⟩,⟨7509235714253920232838064955834716248347259131997180212836,7509235714253920232838064955834716248347259132563144616826⟩⟩,
  ⟨⟨5357809752545419755764515889149380569211502603878860165129,5357809752545419755764515889149380569211502610248854289353⟩,⟨9308121521184528291954824159550550848464515168299328735854,9308121521184528291954824159550550848464515174669522142738⟩⟩,
  ⟨⟨49740112593028765574357163608292822474785977226868545977842,49740112593028765574357163608292822474785977277425481188632⟩,⟨43893402494059683888866544216759155523444029429723315439943,43893402494059683888866544216759155523444029480279583647177⟩⟩,
  ⟨⟨33803050874170489988303691437347767515820299955356646671301,33803050874170489988303691437347767515820300267903925244362⟩,⟨14946990867449402539614548792702473980315691853579131451891,14946990867449402539614548792702473980315692166127053709378⟩⟩,
  ⟨⟨-38055975734734274920007803100166521663631428322898542959083,-38055975734734274920007803100166521663631426726175794647268⟩,⟨-23798830240757874067377565132660970840774551580566094937794,-23798830240757874067377565132660970840774549983839203805733⟩⟩,
  ⟨⟨-63633993076468696976011006099943188745384411788441831054304,-63633993076468696976011006099943188745384404757598368864753⟩,⟨36460999732374240580091803746531394625031629001370789669331,36460999732374240580091803746531394625031636032180271047401⟩⟩,
  ⟨⟨-88017705578511054248272639605993386190225719676074503945904,-88017705578511054248272639605993386190225692077890887054495⟩,⟨65749864448585831403947273135173936122999424590181578278377,65749864448585831403947273135173936122999452188497020959013⟩⟩,
  ⟨⟨4110308832004035653488103502900775162587179721767121001310,4110308832004035653488103502900775162587279100996278610145⟩,⟨7628869807902457741455914363961597237620502005939169594733,7628869807902457741455914363961597237620601384820681908320⟩⟩,
  ⟨⟨27456368381303148941700505651964321648584504721212232143052,27456368381303148941700505651964321648584841226851067354720⟩,⟨-29874275681812530839267214391716508155935840223414489547522,-29874275681812530839267214391716508155935503716937081550632⟩⟩,
  ⟨⟨-37862446067635710723853266524430712285886367692057808841194,-37862446067635710723853266524430712285885273819752462812432⟩,⟨-144134589188816766120776605320194517972889934444950792350903,-144134589188816766120776605320194517972888840575107958728205⟩⟩,
  ⟨⟨-55717428759447322075265775556947068802152507916101316961383,-55717428759447322075265775556947068802149038942290786729173⟩,⟨-121659257037754796029528978434130885369024549572342570547865,-121659257037754796029528978434130885369021080591439936950606⟩⟩,
  ⟨⟨-25633465250757128519271554480928865854432441362051549245719,-25633465250757128519271554480928865854421587651221816132814⟩,⟨16174704993505614233285762222089071561655631438729284378839,16174704993505614233285762222089071561666485133345517146951⟩⟩,
  ⟨⟨66707017186790767952685539845954535442870471739582161628465,66707017186790767952685539845954535442904208095343648721099⟩,⟨34147880113207203937091553486344969025766748189463291879653,34147880113207203937091553486344969025800484575632243940518⟩⟩,
  ⟨⟨237674106408941864895840587583179054262162347063678734449317,237674106408941864895840587583179054262266910262475458636615⟩,⟨-52281573652975945245,52281573652975941876⟩⟩,
  ⟨⟨66707017186790767952685539845954535442725476186704471025250,66707017186790767952685539845954535443049203648221339317876⟩,⟨-34147880113207203937091553486344969025945480154448388136706,-34147880113207203937091553486344969025621752610647147689257⟩⟩,
  ⟨⟨-25633465250757128519271554480928865854927953838040817870702,-25633465250757128519271554480928865853926075175232547520827⟩,⟨-16174704993505614233285762222089071562161997554390992855835,-16174704993505614233285762222089071561160119017683808667676⟩⟩,
  ⟨⟨-55717428759447322075265775556947068803700909196237097577474,-55717428759447322075265775556947068800600637662155006121580⟩,⟨121659257037754796029528978434130885367472679220539430710539,121659257037754796029528978434130885370572950943243076804791⟩⟩,
  ⟨⟨-37862446067635710723853266524430712290682497538499498282761,-37862446067635710723853266524430712281089143973310773359217⟩,⟨144134589188816766120776605320194517968092710866119022052586,144134589188816766120776605320194517977686064153939729046808⟩⟩,
  ⟨⟨27456368381303148941700505651964321633742149572279371617639,27456368381303148941700505651964321663427196375783927906067⟩,⟨29874275681812530839267214391716508141093148367035067404713,29874275681812530839267214391716508170778195573316503692296⟩⟩,
  ⟨⟨4110308832004035653488103502900775116659570542200637705282,4110308832004035653488103502900775208514888280562761914647⟩,⟨-7628869807902457741455914363961597283548210273624276069280,-7628869807902457741455914363961597191692893117135575460645⟩⟩,
  ⟨⟨-88017705578511054248272639605993386332340970405815732282030,-88017705578511054248272639605993386048110441348149658745209⟩,⟨-65749864448585831403947273135173936265114703338068351997783,-65749864448585831403947273135173935980884173440610247258723⟩⟩,
  ⟨⟨-63633993076468696976011006099943189185135703392220535544335,-63633993076468696976011006099943188305633113153819664407565⟩,⟨-36460999732374240580091803746531395064782927030040077374200,-36460999732374240580091803746531394185280338003510983320702⟩⟩,
  ⟨⟨-38055975734734274920007803100166523024366321824760872083989,-38055975734734274920007803100166520302896533224313465514293⟩,⟨23798830240757874067377565132660969480039655607639587517554,23798830240757874067377565132660972201509445956765711270113⟩⟩,
  ⟨⟨33803050874170489988303691437347763305259753487084465797656,33803050874170489988303691437347771726380846736176106165498⟩,⟨-14946990867449402539614548792702478190876237372799367797300,-14946990867449402539614548792702469769755146646906817354136⟩⟩,
  ⟨⟨49740112593028765574357163608292809445929160933796126885211,49740112593028765574357163608292835503642793570497900308176⟩,⟨-43893402494059683888866544216759168552300847593726463738455,-43893402494059683888866544216759142494587211316276435392978⟩⟩,
  ⟨⟨5357809752545419755764515889149340253650637566079382875187,5357809752545419755764515889149420884772367648048331542649⟩,⟨-9308121521184528291954824159550591164025377585834874065046,-9308121521184528291954824159550510532903652757133976857084⟩⟩,
  ⟨⟨-7509235714253920232838064955834840997929707690794409166329,-7509235714253920232838064955834591498764810573765574478649⟩,⟨-7509235714253920232838064955834840997929711480788326232914,-7509235714253920232838064955834591498764806783771998575095⟩⟩,
  ⟨⟨10418529357494547381300296597044943828899916989465883810347,10418529357494547381300296597045715861236228797137849482920⟩,⟨28624674153641342903597614282063383345398467756993555540937,28624674153641342903597614282064155377734768627433518253615⟩⟩,
  ⟨⟨-1194460768109945792950781064,1194460768109945792950848207⟩,⟨-1194460768117836508286563994,1194460768117836508286592618⟩⟩]
def dBox7 : Fin 31 → CI :=
  ![⟨⟨-50906230822,52625670101⟩,⟨87266462599716478846184538424430635672143594427034322360779,87266462599716478846184538424430635672143594427138177642275⟩⟩,
  ⟨⟨12857354874567913519841347642504362883216142939672660061547,12857354874567913519841347642504362883216142941750919308168⟩,⟨-27572686507958198513147578351026046405028879840484576875770,-27572686507958198513147578351026046405028879838406316759717⟩⟩,
  ⟨⟨-79637379670349583992794578166399770257764864418094730890415,-79637379670349583992794578166399770257764864394601136846005⟩,⟨47041994810902043904089784075808370606840687191941990873560,47041994810902043904089784075808370606840687215435829944856⟩⟩,
  ⟨⟨-149336181839478271622650209607928595407769882778170655945566,-149336181839478271622650209607928595407769882590455731611585⟩,⟨-82283183723363853841780708012936955700962478189876136723454,-82283183723363853841780708012936955700962478002162557550507⟩⟩,
  ⟨⟨-110946913346870379921289029357933553247009749699602350298043,-110946913346870379921289029357933553247009748528589057016026⟩,⟨-37424184198063284701723429399378371912813499259205647570713,-37424184198063284701723429399378371912813498088191001470153⟩⟩,
  ⟨⟨34871958806900217767181397003796513891332384743442562863524,34871958806900217767181397003796513891332390791987987906139⟩,⟨-140118983056299762701352785020324224329480601749917678825444,-140118983056299762701352785020324224329480595701365773894360⟩⟩,
  ⟨⟨59225764535476959834945930558390873542060228968576877061987,59225764535476959834945930558390873542060255932275215471376⟩,⟨-233861722824026611984891540336725309174974970023971013679618,-233861722824026611984891540336725309174974943060328756222192⟩⟩,
  ⟨⟨251651802984221159988421230709758327497339493561837340036218,251651802984221159988421230709758327497339600760897062323279⟩,⟨-161886346707445246676559305981991369784561781298776643180508,-161886346707445246676559305981991369784561674099484048751043⟩⟩,
  ⟨⟨188489180423934660731141422275046334749853636937437277397718,188489180423934660731141422275046334749854027657462858952712⟩,⟨-52313937869636745271689587136145061116754932740448493428106,-52313937869636745271689587136145061116754542021076539910633⟩⟩,
  ⟨⟨256726413310086561297183187145562146834857678546172488283743,256726413310086561297183187145562146834859015476864498744458⟩,⟨16565451157827194514200858984828854779076553066644286286222,16565451157827194514200858984828854779077889998997245210405⟩⟩,
  ⟨⟨239561659206079747230586298432101351708054946035130098045539,239561659206079747230586298432101351708059327457031493346358⟩,⟨326350714114826777905596572153666713233787554907585910877682,326350714114826777905596572153666713233791936324674957807264⟩⟩,
  ⟨⟨166011720439607261140270631775496585393004052961139655851956,166011720439607261140270631775496585393018026067621103166372⟩,⟨326436482826874819126047531568882090998387794563617920545645,326436482826874819126047531568882090998401767683678167843043⟩⟩,
  ⟨⟨13858793513509547446850748240510488772503023037220484427199,13858793513509547446850748240510488772546892591918293575120⟩,⟨356452848551332215120554873932884519926223981295360249679320,356452848551332215120554873932884519926267850818081044990618⟩⟩,
  ⟨⟨-182246457101120321030550091126100444634115876962262167921662,-182246457101120321030550091126100444633979265034808020096722⟩,⟨355535843847510148051367987736493850798072964784689095281271,355535843847510148051367987736493850798209576776350441353578⟩⟩,
  ⟨⟨-554969644442649694436752473313240883218652065214051462336594,-554969644442649694436752473313240883218228273247757438588214⟩,⟨214450202981646454168531579929041947902953902226490751513736,214450202981646454168531579929041947903377694076862441149885⟩⟩,
  ⟨⟨-292236143387831555904771624423127477015099068958375160266568,-292236143387831555904771624423127477013786520121720529123568⟩,⟨-656274514802956987871,656274514802956997250⟩⟩,
  ⟨⟨-554969644442649694436752473313240883220471506003617041790804,-554969644442649694436752473313240883216408832458191859107989⟩,⟨-214450202981646454168531579929041947905197134772352954863538,-214450202981646454168531579929041947901134461531000237800455⟩⟩,
  ⟨⟨-182246457101120321030550091126100444640333753540604695623538,-182246457101120321030550091126100444627761388456465492377052⟩,⟨-355535843847510148051367987736493850804427453554512797282097,-355535843847510148051367987736493850791855088006526739384445⟩⟩,
  ⟨⟨13858793513509547446850748240510488753072977290209393107262,13858793513509547446850748240510488791976938338929384880817⟩,⟨-356452848551332215120554873932884519945697896235669707934543,-356452848551332215120554873932884519906793935877771586771996⟩⟩,
  ⟨⟨166011720439607261140270631775496585332819873373378158536069,166011720439607261140270631775496585453202205655382600452765⟩,⟨-326436482826874819126047531568882091058585947770948024867415,-326436482826874819126047531568882090938203614476348063529932⟩⟩,
  ⟨⟨239561659206079747230586298432101351521805665183530474562151,239561659206079747230586298432101351894308608308631116821575⟩,⟨-326350714114826777905596572153666713420041216443081393524805,-326350714114826777905596572153666713047538274789179475145665⟩⟩,
  ⟨⟨256726413310086561297183187145562146258534996560692474211663,256726413310086561297183187145562147411181697462344512836574⟩,⟨-16565451157827194514200858984828855355400573047413175544149,-16565451157827194514200858984828854202753870018228355949791⟩⟩,
  ⟨⟨188489180423934660731141422275046332966520075732009789612954,188489180423934660731141422275046336533187588862890346755386⟩,⟨52313937869636745271689587136145059333420982350952561999586,52313937869636745271689587136145062900088492410572471312133⟩⟩,
  ⟨⟨251651802984221159988421230709758321979119333525636952490332,251651802984221159988421230709758333015559760797097449857820⟩,⟨161886346707445246676559305981991364266341511847403106626424,161886346707445246676559305981991375302781943550857585271812⟩⟩,
  ⟨⟨59225764535476959834945930558390856466875038246887107545348,59225764535476959834945930558390890617245446653964984960480⟩,⟨233861722824026611984891540336725292099789755536214933117103,233861722824026611984891540336725326250160157548084836778154⟩⟩,
  ⟨⟨34871958806900217767181397003796461055102932204973042521349,34871958806900217767181397003796566727561843330457508240900⟩,⟨140118983056299762701352785020324171493251138548995911511508,140118983056299762701352785020324277165710058902287541227209⟩⟩,
  ⟨⟨-110946913346870379921289029357933716739651848511697757886028,-110946913346870379921289029357933389754367649716493649404917⟩,⟨37424184198063284701723429399378208420171405933551315748748,37424184198063284701723429399378535405455591413845333300490⟩⟩,
  ⟨⟨-149336181839478271622650209607929101307685400908173327637356,-149336181839478271622650209607928089507854364460453059896571⟩,⟨82283183723363853841780708012936449801046950266056423690372,82283183723363853841780708012937461600878005925982270559993⟩⟩,
  ⟨⟨-79637379670349583992794578166401335678209759664557109059879,-79637379670349583992794578166398204837319969148138758682943⟩,⟨-47041994810902043904089784075809936027285568601166108439314,-47041994810902043904089784075806805186395805806211712414112⟩⟩,
  ⟨⟨12857354874567913519841347642499518958372360996106785114326,12857354874567913519841347642509206808059924885316794228084⟩,⟨27572686507958198513147578351021202480185077895065798365325,27572686507958198513147578351030890329872681783825095258925⟩⟩,
  ⟨⟨-14988693912197598164293063394,14988693912197598166012490855⟩,⟨-87266462599716478846184538424445624366055763167396793605629,-87266462599716478846184538424415646978231425686775706381508⟩⟩]
def cBox9 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-11282604915,10707415501⟩,⟨-30461741978670859934674354937889355355906479651988824550517,-30461741978670859934674354937889355355906479651966641302835⟩⟩,
  ⟨⟨-8162199163230086799154349223237515385498962031409200157909,-8162199163230086799154349223237515385498962030979545279929⟩,⟨30461741978670859934674354937889355355906479651762702701727,30461741978670859934674354937889355355906479652192478417488⟩⟩,
  ⟨⟨34542841560285903334251529549508113048655960665233299002586,34542841560285903334251529549508113048655960669916881468076⟩,⟨1093527337124743630971520977530353093044684234058668344067,1093527337124743630971520977530353093044684238742302123769⟩⟩,
  ⟨⟨46786140305131033532983053384364386126904403696479074033154,46786140305131033532983053384364386126904403732255680415173⟩,⟨-8162199163230086799154349223237515385498962049082513957686,-8162199163230086799154349223237515385498962013307364643391⟩⟩,
  ⟨⟨-34542841560285903334251529549508113048655960772978914280032,-34542841560285903334251529549508113048655960562170627153898⟩,⟨-1093527337124743630971520977530353093044684341805486029478,-1093527337124743630971520977530353093044684130994787238694⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711812959810592436825510,-60923483957341719869348709875778710711812958797317720848540⟩,⟨60923483957341719869348709875778710711812958797317337343529,60923483957341719869348709875778710711812959810594608493941⟩⟩,
  ⟨⟨60923483957341719869348709875778710711812957239537907511361,60923483957341719869348709875778710711812961368372462135226⟩,⟨75060827609552406205714366367193035296721512829151680924666,75060827609552406205714366367193035296721516957935286629821⟩⟩,
  ⟨⟨-16324398326460173598308698446475030770997931409835760527768,-16324398326460173598308698446475030770997916714944806141195⟩,⟨-60923483957341719869348709875778710711812966651528051206931,-60923483957341719869348709875778710711812951956381540562509⟩⟩,
  ⟨⟨-113684768751453352939543070528319906038126980000424635193031,-113684768751453352939543070528319906038126933153008715492825⟩,⟨-75060827609552406205714366367193035296721538316821423411503,-75060827609552406205714366367193035296721491470264882184886⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813027704255239413088,-60923483957341719869348709875778710711812890903655854790298⟩,⟨105522569588223266140388721305082390652627926143919560347670,105522569588223266140388721305082390652628062947121589595266⟩⟩,
  ⟨⟨70979728027937362806137191755574277603971847121844173218071,70979728027937362806137191755574277603972220634046627578478⟩,⟨-29368214641546116303702833960359002262861982167528788736116,-29368214641546116303702833960359002262861608663626878875255⟩⟩,
  ⟨⟨38623941141900946733828704161126870741404956045219123054166,38623941141900946733828704161126870741405927321125056402189⟩,⟨-188745596361005759145257436895512941334848957121033972539901,-188745596361005759145257436895512941334847985819486224914892⟩⟩,
  ⟨⟨-95466325517627623203600239425286823760470142102471761831227,-95466325517627623203600239425286823760467697840587504793743⟩,⟨-45692612968006289902011532406834033033860941573382131086950,-45692612968006289902011532406834033033858497382552325331635⟩⟩,
  ⟨⟨-3013665897737017992,3013665899822216713⟩,⟨93572280610262067065966106768728772253805793671854167824026,93572280610262067065966106768728772253811821185612900191285⟩⟩,
  ⟨⟨276342732482287226674012236396064904389240337319660244966488,276342732482287226674012236396064904389255033361541610817247⟩,⟨-7347795630237217621,7347795630237236774⟩⟩,
  ⟨⟨-17812982716391769518,17812982718477005071⟩,⟨-93572280610262067065966106768728772253826620961312036919079,-93572280610262067065966106768728772253790993896155031107615⟩⟩,
  ⟨⟨-95466325517627623203600239425286823760511993433866034181660,-95466325517627623203600239425286823760425846509193232467982⟩,⟨45692612968006289902011532406834033033816647348484014610954,45692612968006289902011532406834033033902791607450441772284⟩⟩,
  ⟨⟨38623941141900946733828704161126870741301400604371896060208,38623941141900946733828704161126870741509482761972283359551⟩,⟨188745596361005759145257436895512941334744427168786873876219,188745596361005759145257436895512941334952515771733323616987⟩⟩,
  ⟨⟨70979728027937362806137191755574277603720807739369442616662,70979728027937362806137191755574277604223260016521358229091⟩,⟨29368214641546116303702833960359002262610577060936212888255,29368214641546116303702833960359002263113013770219454761294⟩⟩,
  ⟨⟨-60923483957341719869348709875778710712419480825790620554384,-60923483957341719869348709875778710711206437782120473611996⟩,⟨-105522569588223266140388721305082390653234534861115721981561,-105522569588223266140388721305082390652021454229925428020931⟩⟩,
  ⟨⟨-113684768751453352939543070528319906039591289875674582992085,-113684768751453352939543070528319906036662623277758767766540⟩,⟨75060827609552406205714366367193035295257226967157648424585,75060827609552406205714366367193035298185802819928657136776⟩⟩,
  ⟨⟨-16324398326460173598308698446475030774533035643293909776036,-16324398326460173598308698446475030767462812481486656928836⟩,⟨60923483957341719869348709875778710708277738183832123771789,60923483957341719869348709875778710715348180424077468083764⟩⟩,
  ⟨⟨60923483957341719869348709875778710703278177100607938343546,60923483957341719869348709875778710720347741507302431400138⟩,⟨-75060827609552406205714366367193035305256032645731912934640,-75060827609552406205714366367193035288186997141355054582574⟩⟩,
  ⟨⟨-60923483957341719869348709875778710732417109101260521583726,-60923483957341719869348709875778710691208809506649636054072⟩,⟨-60923483957341719869348709875778710732417747542873363871208,-60923483957341719869348709875778710691208171065038582073968⟩⟩,
  ⟨⟨-34542841560285903334251529549508113098400320294492655098416,-34542841560285903334251529549508112998911601040656886455582⟩,⟨1093527337124743630971520977530353043301865943889393979095,1093527337124743630971520977530353142787502528910879253607⟩⟩,
  ⟨⟨46786140305131033532983053384364386006814617054102021552635,46786140305131033532983053384364386246994190374632732858958⟩,⟨8162199163230086799154349223237515265405454260499180313796,8162199163230086799154349223237515505592469801890698419513⟩⟩,
  ⟨⟨34542841560285903334251529549508112758724585431978323177668,34542841560285903334251529549508113338587335903171857435288⟩,⟨-1093527337124743630971520977530353382967075916729026967663,-1093527337124743630971520977530352803122292556071943462162⟩⟩,
  ⟨⟨-8162199163230086799154349223237516085433532065106569647860,-8162199163230086799154349223237514685564391997282175752582⟩,⟨-30461741978670859934674354937889356055862737906856291947733,-30461741978670859934674354937889354655950221397098889324002⟩⟩,
  ⟨⟨-1689843891747255419737726,1689843891747254844383656⟩,⟨30461741978670859934674354937889353666114947901923378200508,30461741978670859934674354937889357045698011402032087616227⟩⟩,
  ⟨⟨-4079517633534213660319942,4079517633534213660281966⟩,⟨-4079644041749581830965399,4079644041749581831141998⟩⟩]
def dBox9 : Fin 31 → CI :=
  ![⟨⟨-30923612170,32643051449⟩,⟨87266462599716478846184538424430635672143594427054328781012,87266462599716478846184538424430635672143594427118171222183⟩⟩,
  ⟨⟨23382978179914803476195888712014960320615001512493879330783,23382978179914803476195888712014960320615001513725398056837⟩,⟨-87266462599716478846184538424430635672143594427701682524998,-87266462599716478846184538424430635672143594426470020971659⟩⟩,
  ⟨⟨-98957951689673880584282482780438115832451095190381487096765,-98957951689673880584282482780438115832451095176900093306985⟩,⟨84133737539745111316885030212616032866985388607667278962474,84133737539745111316885030212616032866985388621149380611832⟩⟩,
  ⟨⟨-110649440779631282322380427136445595992758595992060653530901,-110649440779631282322380427136445595992758595888336254749724⟩,⟨-63883484419801675369988649712415675351528592965834839693915,-63883484419801675369988649712415675351528592862114120068880⟩⟩,
  ⟨⟨-308670315674931,308668490113275⟩,⟨-308674620800051,308672460987551⟩⟩,
  ⟨⟨40500506239886871893792761000400715030913589898207068313620,40500506239886871893792761000400715030913592903519203619067⟩,⟨-151149947019518154216173188136846311023672188843720950533018,-151149947019518154216173188136846311023672185838404612762080⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836099886612463607379,-75574973509759077108086594068423155511836087454449782042997⟩,⟨-211900706379348462056862329637447383570042580658371758301655,-211900706379348462056862329637447383570042568226347339581214⟩⟩,
  ⟨⟨221298881559262564644760854272891191985517169380103859064395,221298881559262564644760854272891191985517214380686719633537⟩,⟨-22500663708280804,22500657069265169⟩⟩,
  ⟨⟨151149947019518154216173188136846311023672114322962264992947,151149947019518154216173188136846311023672260359166015903378⟩,⟨-73016799063760448,73016796756729058⟩⟩,
  ⟨⟨221298881559262564644760854272891191985516974879089072181829,221298881559262564644760854272891191985517408881703511438727⟩,⟨-127766968839603350739977299424831350703057402833350835278034,-127766968839603350739977299424831350703056968822550178143231⟩⟩,
  ⟨⟨122340929869588684060478371492453076153065494575954909619430,122340929869588684060478371492453076153066698817557867872334⟩,⟨299167168979064940903046868061878019242185566761763991564447,299167168979064940903046868061878019242186770977127729640718⟩⟩,
  ⟨⟨63883484419801675369988649712415675351527005711296013986330,63883484419801675369988649712415675351530180116658385794300⟩,⟨238416409619234633062357726561276946695814194525014296016601,238416409619234633062357726561276946695817369011288086584757⟩⟩,
  ⟨⟨70148934539744410428587666136044880961840968375261635995156,70148934539744410428587666136044880961849040703402836579816⟩,⟨215033431439319829586161837849261986375196744204636943283809,215033431439319829586161837849261986375204816305444954638309⟩⟩,
  ⟨⟨-110649440779631282322380427136445595992768620707298970573206,-110649440779631282322380427136445595992748571173099424898048⟩,⟨272651465739178769897551471138048456116402936479192028649604,272651465739178769897551471138048456116422986608126395192408⟩⟩,
  ⟨⟨-518172736628284206397608302614205539482895029107956725634870,-518172736628284206397608302614205539482845925754686927183863⟩,⟨130899693899574718269276807636645953508190840711239242239646,130899693899574718269276807636645953508239942570023985037102⟩⟩,
  ⟨⟨-59663953363056169541,59663953351548900629⟩,⟨-59665789231704591616,59665789231704624226⟩⟩,
  ⟨⟨-518172736628284206397608302614205539483014924340751483999223,-518172736628284206397608302614205539482726030521892168748916⟩,⟨-130899693899574718269276807636645953508359834086253630718743,-130899693899574718269276807636645953508070949195009596566146⟩⟩,
  ⟨⟨-110649440779631282322380427136445595993107682112276403077941,-110649440779631282322380427136445595992409509768121992394162⟩,⟨-272651465739178769897551471138048456116762058523248552125487,-272651465739178769897551471138048456116063864564069871793888⟩⟩,
  ⟨⟨70148934539744410428587666136044880961001898287098252159091,70148934539744410428587666136044880962688110791566220345462⟩,⟨-215033431439319829586161837849261986376043860389603604428436,-215033431439319829586161837849261986374357700120478293501828⟩⟩,
  ⟨⟨63883484419801675369988649712415675349492981009162290475544,63883484419801675369988649712415675353564204818792109303767⟩,⟨-238416409619234633062357726561276946697851456745399444478384,-238416409619234633062357726561276946693780106790902938062444⟩⟩,
  ⟨⟨122340929869588684060478371492453076148151380933028779949511,122340929869588684060478371492453076157980812460483997609579⟩,⟨-299167168979064940903046868061878019247100732350999989126742,-299167168979064940903046868061878019237271605387891732087520⟩⟩,
  ⟨⟨221298881559262564644760854272891191973652287026464386009995,221298881559262564644760854272891191997382096734328197607501⟩,⟨127766968839603350739977299424831350691191913327115769471290,127766968839603350739977299424831350714922458328785243873757⟩⟩,
  ⟨⟨151149947019518154216173188136846310995026831483766479928079,151149947019518154216173188136846311052317543198361800898556⟩,⟨-28644468277686892876731,28644468277689199901601⟩⟩,
  ⟨⟨221298881559262564644760854272891191916363302003667254356918,221298881559262564644760854272891192054671081757123324340032⟩,⟨-69156032683962588382257,69156032683969227459616⟩⟩,
  ⟨⟨-75574973509759077108086594068423155678793536696458167791148,-75574973509759077108086594068423155344878650644604077793285⟩,⟨211900706379348462056862329637447383403090304611013865642909,211900706379348462056862329637447383736994844273705232234849⟩⟩,
  ⟨⟨40500506239886871893792761000400714627855153295832860211370,40500506239886871893792761000400715433972029505893411722796⟩,⟨151149947019518154216173188136846310620601260039402258485372,151149947019518154216173188136846311426743114642723304739439⟩⟩,
  ⟨⟨-973099300531343411659438,973099300531341586034111⟩,⟨-973069148943430061604117,973069148943432221409344⟩⟩,
  ⟨⟨-110649440779631282322380427136445598341955332765537391914596,-110649440779631282322380427136445593643561859114859516367884⟩,⟨63883484419801675369988649712415673002259063716170864344294,63883484419801675369988649712415677700798122111778095476697⟩⟩,
  ⟨⟨-98957951689673880584282482780438121504089454308799651160693,-98957951689673880584282482780438110160812736058481929179051⟩,⟨-84133737539745111316885030212616038538448011406726535581033,-84133737539745111316885030212616027195522765822090123997197⟩⟩,
  ⟨⟨23382978179914803476195888712014946628493019065370330232431,23382978179914803476195888712014974012736983960848947156908⟩,⟨87266462599716478846184538424430621979597346941201405984972,87266462599716478846184538424430649364689841912970297442691⟩⟩,
  ⟨⟨-33056730854102404089591485,33056730854102405808968159⟩,⟨-87266462599716478846184538424430668727850182120360953386403,-87266462599716478846184538424430602616437006733811546625023⟩⟩]
def cBox12 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-15230870989335429967337177468944677677953239826004195004570,-15230870989335429967337177468944677677953239825974028831380⟩,⟨-26380642397055816535097180326270597663156998636395315306702,-26380642397055816535097180326270597663156998636365092852016⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651673526155498,30461741978670859934674354937889355355906479652282866717495⟩,⟨52761284794111633070194360652541195326313997272455438060074,52761284794111633070194360652541195326313997273064894213844⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953239822530562107067,15230870989335429967337177468944677677953239829446021068013⟩,⟨-79141927191167449605291540978811792989470995912598771568301,-79141927191167449605291540978811792989470995905682812690526⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906479679736683540186,-30461741978670859934674354937889355355906479624217217429494⟩,⟨52761284794111633070194360652541195326313997245001010552114,52761284794111633070194360652541195326313997300520311542997⟩⟩,
  ⟨⟨60923483957341719869348709875778710711812959129745915302957,60923483957341719869348709875778710711812959478165357871127⟩,⟨52761284794111633070194360652541195326313997098550656212948,52761284794111633070194360652541195326313997446970226693299⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906480559400665845742,-30461741978670859934674354937889355355906478744555249295417⟩,⟨-52761284794111633070194360652541195326313998180184175345121,-52761284794111633070194360652541195326313996365335522480955⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906483748072380417974,-30461741978670859934674354937889355355906475555882752907987⟩,⟨52761284794111633070194360652541195326313993176675957265611,52761284794111633070194360652541195326314001368845725908280⟩⟩,
  ⟨⟨-30461741978670859934674354937889355355906496240707508788551,-30461741978670859934674354937889355355906463063248326648490⟩,⟨52761284794111633070194360652541195326313980683996133288533,52761284794111633070194360652541195326314013861525658101473⟩⟩,
  ⟨⟨15230870989335429967337177468944677677953177757951280990422,15230870989335429967337177468944677677953301894024468383774⟩,⟨-79141927191167449605291540978811792989471057977096158949397,-79141927191167449605291540978811792989470933841185553009987⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813179238186131255203,-60923483957341719869348709875778710711812739369725119313489⟩,⟨-219934409964816087,219934409552088520⟩⟩,
  ⟨⟨-60923483957341719869348709875778710711813712235211451430658,-60923483957341719869348709875778710711812206372699793261609⟩,⟨-752930704541915487,752930703575227960⟩⟩,
  ⟨⟨91385225936012579804023064813668066067716911764402085750984,91385225936012579804023064813668066067721966147463305171717⟩,⟨-52761284794111633070194360652541195326316524465898070153161,-52761284794111633070194360652541195326311470079624940207701⟩⟩,
  ⟨⟨-8396929695075537912,8396929695756191977⟩,⟨-105522569588223266140388721305082390652636391471868157673493,-105522569588223266140388721305082390652619597619175011928424⟩⟩,
  ⟨⟨-91385225936012579804023064813668066067747210120857124549777,-91385225936012579804023064813668066067691667791006715873644⟩,⟨52761284794111633070194360652541195326286226102567012295809,52761284794111633070194360652541195326341768442952869130433⟩⟩,
  ⟨⟨274155677808037739412069194441004198203066641363356585280105,274155677808037739412069194441004198203249992372241963175034⟩,⟨-91675497273772422876,91675497273772398783⟩⟩,
  ⟨⟨-91385225936012579804023064813668066068021864479144999921784,-91385225936012579804023064813668066067417013432718840548403⟩,⟨-52761284794111633070194360652541195326616422804949885523343,-52761284794111633070194360652541195326011571740569995884040⟩⟩,
  ⟨⟨-997445104989165400686,997445104989846090585⟩,⟨105522569588223266140388721305082390651630549450926697656660,105522569588223266140388721305082390653625439640116471983856⟩⟩,
  ⟨⟨91385225936012579804023064813668066064429920025318621760098,91385225936012579804023064813668066071008957886546769184018⟩,⟨52761284794111633070194360652541195323024478330734361157201,52761284794111633070194360652541195329603516214788649154903⟩⟩,
  ⟨⟨-60923483957341719869348709875778710722661437593288929741425,-60923483957341719869348709875778710700964481014622315007686⟩,⟨-10848478277485382164713,10848478277486348853810⟩⟩,
  ⟨⟨-60923483957341719869348709875778710747589938798365982657641,-60923483957341719869348709875778710676035979809545267885131⟩,⟨-35776979505790055633500,35776979505790468416085⟩⟩,
  ⟨⟨15230870989335429967337177468944677559965141777167962374065,15230870989335429967337177468944677795941337874807787040211⟩,⟨79141927191167449605291540978811792871482897870648081597001,79141927191167449605291540978811793107459093947633630314715⟩⟩,
  ⟨⟨-30461741978670859934674354937889355745016730215305487938286,-30461741978670859934674354937889354966796229088650347563059⟩,⟨-52761284794111633070194360652541195715424247845288393075109,-52761284794111633070194360652541194937203746700233398330046⟩⟩,
  ⟨⟨-30461741978670859934674354937889356639144251350458424468389,-30461741978670859934674354937889354072668707953496708842081⟩,⟨-52761284794111633070194360652541196609551768963068931550623,-52761284794111633070194360652541194043076225582452751553959⟩⟩,
  ⟨⟨-30461741978670859934674354937889359587866886246340960367212,-30461741978670859934674354937889351123946073057614954716662⟩,⟨52761284794111633070194360652541191094353590671153722561235,52761284794111633070194360652541199558274403874365975218407⟩⟩,
  ⟨⟨60923483957341719869348709875778696755327830485855708631481,60923483957341719869348709875778724668298088122055564471093⟩,⟨-52761284794111633070194360652541209282799126084454235550375,-52761284794111633070194360652541181369828868461066647386620⟩⟩,
  ⟨⟨-30461741978670859934674354937889401382678573552346369007348,-30461741978670859934674354937889309329134385751607531957326⟩,⟨-52761284794111633070194360652541241353086091178791765564254,-52761284794111633070194360652541149299541903366729556448028⟩⟩,
  ⟨⟨15230870989335429967337177468944525887317572886335549592283,15230870989335429967337177468944829468588906765641033657058⟩,⟨79141927191167449605291540978811641198835328974490714665140,79141927191167449605291540978811944780106662843790869549803⟩⟩,
  ⟨⟨30461741978670859934674354937888854769051742967518648375050,30461741978670859934674354937889855942761216336437744419918⟩,⟨-52761284794111633070194360652541695913168733961640533615358,-52761284794111633070194360652540694739459260583879798705484⟩⟩,
  ⟨⟨-15230870989335429967337177468946328551856192652636350680894,-15230870989335429967337177468943026804050286999341873160674⟩,⟨26380642397055816535097180326268946789254045813639361718829,26380642397055816535097180326272248537059951459121046537029⟩⟩,
  ⟨⟨-5444379167495855480825544275,5444379167495855480825636505⟩,⟨-5444379167495858932794127859,5444379167495858932794085306⟩⟩]
def dBox12 : Fin 31 → CI :=
  ![⟨⟨-58547107015,60266546294⟩,⟨87266462599716478846184538424430635672143594427026719566435,87266462599716478846184538424430635672143594427145780436758⟩⟩,
  ⟨⟨-1195051335308,1191055070473⟩,⟨-174532925199432957692369076848861271344287188855365162313091,-174532925199432957692369076848861271344287188852978558297341⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836093684120708362741,-75574973509759077108086594068423155511836093656936456431401⟩,⟨218166156499291197115461346061076589180358986054122917910475,218166156499291197115461346061076589180358986081307603910109⟩⟩,
  ⟨⟨-109830230664856,109825466116866⟩,⟨-174532925199432957692369076848861271344287188963999663950375,-174532925199432957692369076848861271344287188744343821854377⟩⟩,
  ⟨⟨-695281373491471,695281482044894⟩,⟨-695282506156716,695280559828450⟩⟩,
  ⟨⟨-3659722639500399,3659722755389623⟩,⟨-3659724700841848,3659723556150935⟩⟩,
  ⟨⟨-75574973509759077108086594068423155511836110381819596497721,-75574973509759077108086594068423155511836076959242652267563⟩,⟨-130899693899574718269276807636645953508215408351907485574731,-130899693899574718269276807636645953508215374929351168413537⟩⟩,
  ⟨⟨302299894039036308432346376273692622047344306213072256927694,302299894039036308432346376273692622047344443151174454817804⟩,⟨-68469091669726268,68469086361468135⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023672446265956304480929,-151149947019518154216173188136846311023671928416162477585038⟩,⟨-258924799755137831,258924801593737981⟩⟩,
  ⟨⟨151149947019518154216173188136846311023671261737828896753851,151149947019518154216173188136846311023673112944295272188396⟩,⟨-87266462599716478846184538424430635672144520030544446372771,-87266462599716478846184538424430635672142668823628280552394⟩⟩,
  ⟨⟨226724920529277231324259782205269466535505091615037052361394,226724920529277231324259782205269466535511470408151623074597⟩,⟨305432619099007675961645884485507224852499391098907806547697,305432619099007675961645884485507224852505769890694966067366⟩⟩,
  ⟨⟨-151149947019518154216173188136846311023682937875568746956982,-151149947019518154216173188136846311023661436806552958839645⟩,⟨-87266462599716478846184538424430635672154344963463114034712,-87266462599716478846184538424430635672132843890702843447907⟩⟩,
  ⟨⟨-35806827096762438432,35806827097039407626⟩,⟨174532925199432957692369076848861271344251382031166780598908,174532925199432957692369076848861271344322995677180525843980⟩⟩,
  ⟨⟨151149947019518154216173188136846311023553618515143600891341,151149947019518154216173188136846311023790756166975795734394⟩,⟨261799387799149436538553615273291907016312214448135606268560,261799387799149436538553615273291907016549352114384055475480⟩⟩,
  ⟨⟨-529024814568313539756606158478962088583244276592286553643963,-529024814568313539756606158478962088582461034795145401516222⟩,⟨-130899693899574718269276807636645953508607012528169320111891,-130899693899574718269276807636645953507823770753085621609288⟩⟩,
  ⟨⟨302299894039036308432346376273692622046052191356680549619523,302299894039036308432346376273692622048636558007558337978784⟩,⟨-1292183340375393640764,1292183340375393660871⟩⟩,
  ⟨⟨-529024814568313539756606158478962088587114792507698120574329,-529024814568313539756606158478962088578590518879733834550362⟩,⟨130899693899574718269276807636645953503953254845062153060011,130899693899574718269276807636645953512477528436192788633964⟩⟩,
  ⟨⟨151149947019518154216173188136846311009615563418955684308100,151149947019518154216173188136846311037728811263163712283509⟩,⟨-261799387799149436538553615273291907030487407224744922753261,-261799387799149436538553615273291907002374159337774739014353⟩⟩,
  ⟨⟨-46357534712485639920928,46357534712485916889093⟩,⟨-174532925199432957692369076848861271390644723543336827242477,-174532925199432957692369076848861271297929654165010479167320⟩⟩,
  ⟨⟨-151149947019518154216173188136846311176554026787416975659353,-151149947019518154216173188136846310870790347894704730106007⟩,⟨87266462599716478846184538424430635519261754956826173791627,87266462599716478846184538424430635825025433897339783669109⟩⟩,
  ⟨⟨226724920529277231324259782205269466031322506315097564572456,226724920529277231324259782205269467039694055708091110834405⟩,⟨-305432619099007675961645884485507225356688355168046328914929,-305432619099007675961645884485507224348316805821556443724732⟩⟩,
  ⟨⟨151149947019518154216173188136846309360929328509262769580131,151149947019518154216173188136846312686415046172861399356895⟩,⟨87266462599716478846184538424430634009400735573707281013562,87266462599716478846184538424430637334886453280465445941829⟩⟩,
  ⟨⟨-151149947019518154216173188136846316507193798860257176971343,-151149947019518154216173188136846305540150575821861605064930⟩,⟨-5483521611499799384663152,5483521611499797546044634⟩⟩,
  ⟨⟨302299894039036308432346376273692603963364222640912838206726,302299894039036308432346376273692640131324526723333873511374⟩,⟨-18083980152058449148466366,18083980152058454456702930⟩⟩,
  ⟨⟨-75574973509759077108086594068423215150579342103364052325111,-75574973509759077108086594068423095873092845237698196444430⟩,⟨130899693899574718269276807636645893869472143223083593290696,130899693899574718269276807636646013146958640058175060726577⟩⟩,
  ⟨⟨-196681243035488620510877320,196681243035488620626797158⟩,⟨-196681243035502151614042649,196681243035502152758718153⟩⟩,
  ⟨⟨-648630558825536174642862142,648630558825536174751389928⟩,⟨-648630558825524210398953626,648630558825524212345258260⟩⟩,
  ⟨⟨-2139103838006827478422170310,2139103838006827473657617728⟩,⟨174532925199432957692369076848859132240449182016123234944913,174532925199432957692369076848863410448125195692220250889699⟩⟩,
  ⟨⟨-75574973509759077108086594068430210013304633633446857112423,-75574973509759077108086594068416101010367553707610307650154⟩,⟨-218166156499291197115461346061083643681827526021291548581864,-218166156499291197115461346061069534678890446114138973256377⟩⟩,
  ⟨⟨-23264878537174032626175113526,23264878537174032622178819825⟩,⟨174532925199432957692369076848838006465750014813292203511692,174532925199432957692369076848884536222824362895051517076865⟩⟩,
  ⟨⟨-76724709146808372605482454668,76724709146808372607201893177⟩,⟨-87266462599716478846184538424507360381290402792397911096354,-87266462599716478846184538424353910962996786061774588876945⟩⟩]
def cBox13 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-19580430313357954872034103663248574042515901359362675686604,-19580430313357954872034103663248574042515901359331519243016⟩,⟨-23335048170484914988453136141165932166689530925502406877438,-23335048170484914988453136141165932166689530925471242820010⟩⟩,
  ⟨⟨49418667375392148676379844238792133385413773971529833621446,49418667375392148676379844238792133385413773972161293029020⟩,⟨49418667375392148676379844238792133385413773971528779584589,49418667375392148676379844238792133385413773972160206438938⟩⟩,
  ⟨⟨-24616794848266757729821300182897265522355200689708846035122,-24616794848266757729821300182897265522355200682510546545444⟩,⟨-95389660067796766486550332777764559842356706726739447912613,-95389660067796766486550332777764559842356706719540687588378⟩⟩,
  ⟨⟨2748571034422318699473571956460269052034712091803621418638,2748571034422318699473571956460269052034712149940797829794⟩,⟨109680023760745019489955393763268478675276265989531292381066,109680023760745019489955393763268478675276266047669055720905⟩⟩,
  ⟨⟨84614714189971762236490100703485073297523149007559936634433,84614714189971762236490100703485073297523149375253455178964⟩,⟨-33614961311842518064331204109038671679705146777507723682087,-33614961311842518064331204109038671679705146409814488074231⟩⟩,
  ⟨⟨-132623644349389747063044049248511665268141227927079522528765,-132623644349389747063044049248511665268141225992507644289607⟩,⟨-2255179498256666641698735281523932059658868196293732895779,-2255179498256666641698735281523932059658866261721585096920⟩⟩,
  ⟨⟨99052061654351514124169269104978288693487545143439659380805,99052061654351514124169269104978288693487553988950735421549⟩,⟨98878588923601722798265571154258660966427594784104373029266,98878588923601722798265571154258660966427603629609128785127⟩⟩,
  ⟨⟨-81933839181737056678859311030386106895880925851922875448197,-81933839181737056678859311030386106895880889446827838967533⟩,⟨-80826640814924327272308978941164710039431112244352602723210,-80826640814924327272308978941164710039431075839237478147313⟩⟩,
  ⟨⟨-61824944753546762117752942748156556037288900635407776845961,-61824944753546762117752942748156556037288761724287012810200⟩,⟨42965510535683341256438101791449475845397669139727944934782,42965510535683341256438101791449475845397808050806900491014⟩⟩,
  ⟨⟨93155351139873366384907378193769418560875209697719936404903,93155351139873366384907378193769418560875713388649782132442⟩,⟨-8359100321989241898595993093700805108257950856059410432234,-8359100321989241898595993093700805108257447165042003279803⟩⟩,
  ⟨⟨-170147937080398503471648542021284028301549223875923609546263,-170147937080398503471648542021284028301547454183191969894190⟩,⟨-105009928772709810620909074317698163797551192201251254984705,-105009928772709810620909074317698163797549422508818102556235⟩⟩,
  ⟨⟨89147892399013556127599509751844042930252370797417099600352,89147892399013556127599509751844042930258480157553857335300⟩,⟨84070129797733054195663568217845295907894905121802695453260,84070129797733054195663568217845295907901014482807706615059⟩⟩,
  ⟨⟨82066935733860793592611363413259760554744295765701398224633,82066935733860793592611363413259760554765202921006732222787⟩,⟨-184319850112236357496544192525942586754381678137409120680980,-184319850112236357496544192525942586754360770983735674095188⟩⟩,
  ⟨⟨-190465548131430263825085779272647499309539206234723277514354,-190465548131430263825085779272647499309467934755980137953826⟩,⟨74119125188407506277224867176381668326210288306369327569065,74119125188407506277224867176381668326281559787279087369825⟩⟩,
  ⟨⟨361977890262483171833229981609085417805657015812970977097240,361977890262483171833229981609085417805899608767183252625568⟩,⟨-121296475861345764128,121296475861345819713⟩⟩,
  ⟨⟨-190465548131430263825085779272647499309916219453181723906269,-190465548131430263825085779272647499309090921537521691485988⟩,⟨-74119125188407506277224867176381668326658573005995141219524,-74119125188407506277224867176381668325833275087653273798583⟩⟩,
  ⟨⟨82066935733860793592611363413259760553351154407084523443643,82066935733860793592611363413259760556158344279623606892882⟩,⟨184319850112236357496544192525942586752967629625616199844226,184319850112236357496544192525942586755774819495528594937337⟩⟩,
  ⟨⟨89147892399013556127599509751844042925481419439675772329734,89147892399013556127599509751844042935029431515295184689540⟩,⟨-84070129797733054195663568217845295912671965841334969338521,-84070129797733054195663568217845295903123953763275432652929⟩⟩,
  ⟨⟨-170147937080398503471648542021284028317785840859261656023354,-170147937080398503471648542021284028285310837199853923422816⟩,⟨105009928772709810620909074317698163781312805526358711439767,105009928772709810620909074317698163813787809183710645986512⟩⟩,
  ⟨⟨93155351139873366384907378193769418505648089660857178278379,93155351139873366384907378193769418616102833425512540179013⟩,⟨8359100321989241898595993093700805053030327127554660030966,8359100321989241898595993093700805163485070893546753769345⟩⟩,
  ⟨⟨-61824944753546762117752942748156556225129371475529743743513,-61824944753546762117752942748156555849448290884165045790307⟩,⟨-42965510535683341256438101791449476033238278890631431536230,-42965510535683341256438101791449475657557198299903413892032⟩⟩,
  ⟨⟨-81933839181737056678859311030386107534768191524295646111784,-81933839181737056678859311030386106256993623774455068393970⟩,⟨80826640814924327272308978941164709400543810166747352368336,80826640814924327272308978941164710678318377916842728413784⟩⟩,
  ⟨⟨99052061654351514124169269104978286520490412163186433396295,99052061654351514124169269104978290866484686969203961404165⟩,⟨-98878588923601722798265571154258663139424736609810969414831,-98878588923601722798265571154258658793430461803902532267471⟩⟩,
  ⟨⟨-132623644349389747063044049248511672658985700772513032665281,-132623644349389747063044049248511657877296753147074134052677⟩,⟨2255179498256666641698735281523924668814393416263954137642,2255179498256666641698735281523939450503341041751363763627⟩⟩,
  ⟨⟨84614714189971762236490100703485048159624398252453908502764,84614714189971762236490100703485098435421900130359483169888⟩,⟨33614961311842518064331204109038646541806395654718393218153,33614961311842518064331204109038696817603897532603818527479⟩⟩,
  ⟨⟨2748571034422318699473571956460183552474297793221913888987,2748571034422318699473571956460354551595126448522505449827⟩,⟨-109680023760745019489955393763268564174836680346254185798002,-109680023760745019489955393763268393175715851690946162187909⟩⟩,
  ⟨⟨-24616794848266757729821300182897556325293961053585208919839,-24616794848266757729821300182896974719416440318634183635523⟩,⟨95389660067796766486550332777764269039417946355665308544692,95389660067796766486550332777764850645295467090614826806844⟩⟩,
  ⟨⟨49418667375392148676379844238791144300221033169020845607289,49418667375392148676379844238793122470606514774670280909792⟩,⟨-49418667375392148676379844238793122470606514774669475810263,-49418667375392148676379844238791144300221033169019510127739⟩⟩,
  ⟨⟨-19580430313357954872034103663251938140288328805824396555650,-19580430313357954872034103663245209944743473912869798215421⟩,⟨23335048170484914988453136141162568068917103479009576016360,23335048170484914988453136141169296264461958371964073726480⟩⟩,
  ⟨⟨-11442041500076375055380442254,11442041500076375055380367154⟩,⟨-11442041500076375055398472105,11442041500076375055398318010⟩⟩]
def dBox13 : Fin 31 → CI :=
  ![⟨⟨-62403109972,64122549251⟩,⟨87266462599716478846184538424430635672143594427022854019608,87266462599716478846184538424430635672143594427149645983688⟩⟩,
  ⟨⟨-17449969529192285706525055550956464362967387152009327851502,-17449969529192285706525055550956464362967387149459014652869⟩,⟨-199454064400259554764599631361387403223952236732141357604549,-199454064400259554764599631361387403223952236729590476563590⟩⟩,
  ⟨⟨-35691755575021880690632652555016546814720203052589639133049,-35691755575021880690632652555016546814720203023407517333674⟩,⟨269822200080984273853445433615046568555591386463261753849392,269822200080984273853445433615046568555591386492444505222983⟩⟩,
  ⟨⟨-3515582712801591269172999617852814154799638706789304100634,-3515582712801591269172999617852814154799638469593745939152⟩,⟨-263210246652608341982344575532768607236995722172921234093306,-263210246652608341982344575532768607236995721935725056861922⟩⟩,
  ⟨⟨-17913702388310802049758239027145398638305701765648211350435,-17913702388310802049758239027145398638305700252577760499729⟩,⟨81963367985453275964350490747430806621415929745046274620155,81963367985453275964350490747430806621415931258116917585046⟩⟩,
  ⟨⟨78894903178015150724851413936118612884647943077053228858507,78894903178015150724851413936118612884647951119646138792269⟩,⟨13531480489809717287620037663662634812830378657561649360297,13531480489809717287620037663662634812830386700154742064070⟩⟩,
  ⟨⟨-159086603581942902614981469893983888613689989785873256024490,-159086603581942902614981469893983888613689952601325491646657⟩,⟨-169810330253978055405292504988094187077236638427638688695388,-169810330253978055405292504988094187077236601243093028800645⟩⟩,
  ⟨⟨326172858356647899232637378931667217363271892003456629971013,326172858356647899232637378931667217363272046742646314846469⟩,⟨88984895086233237835393820183014048068347509662350003102838,88984895086233237835393820183014048068347664401546617262248⟩⟩,
  ⟨⟨-184658166843689753963979846368376659038083328726847309286164,-184658166843689753963979846368376659038082732380198581238576⟩,⟨-15037672036791746335724694693473638253093931677123700235227,-15037672036791746335724694693473638253093335330492434818040⟩⟩,
  ⟨⟨108819181856341709266850522493336923706585251380214666540503,108819181856341709266850522493336923706587431211502845214836⟩,⟨-126695065343300956952164063819954919071080892249051018313688,-126695065343300956952164063819954919071078712417724447169896⟩⟩,
  ⟨⟨236587904727616980696697421237547250207621484823505026510259,236587904727616980696697421237547250207629187960503707121559⟩,⟨335631397328104005734830019296362576600023403205450474352280,335631397328104005734830019296362576600031106342329626992271⟩⟩,
  ⟨⟨-229870732671268424244129766028553797505914209590530456147721,-229870732671268424244129766028553797505887519271454274686557⟩,⟨-158772531098149656329482146620440468616322987031944450952765,-158772531098149656329482146620440468616296296712530653994847⟩⟩,
  ⟨⟨47253338717496890611777665403712505595256961135764283732220,47253338717496890611777665403712505595348485039054086625957⟩,⟨170509014422273446120534918987054794222194429249124612969591,170509014422273446120534918987054794222285953151733043627222⟩⟩,
  ⟨⟨204022950441796539435409655519514609635307395843648514769738,204022950441796539435409655519514609635619705420526431912217⟩,⟨167739282615654754559132956965827017335393727990339025561819,167739282615654754559132956965827017335706037568288913701626⟩⟩,
  ⟨⟨-635065146950070759430295951592764626426121801514301266688196,-635065146950070759430295951592764626425058313358306757392904⟩,⟨-110942094184458769587637694457872359816207682868357969176138,-110942094184458769587637694457872359815144194713819459995609⟩⟩,
  ⟨⟨563001045948766460002503846225506152320508691072178650400694,563001045948766460002503846225506152324127251014597988877246⟩,⟨-1809279972065218456323,1809279972065218490184⟩⟩,
  ⟨⟨-635065146950070759430295951592764626431744529138748177731152,-635065146950070759430295951592764626419435585733859846301296⟩,⟨110942094184458769587637694457872359809521467089548183405623,110942094184458769587637694457872359821830410492629245714928⟩⟩,
  ⟨⟨204022950441796539435409655519514609614530177178342056071686,204022950441796539435409655519514609656396924085832890547458⟩,⟨-167739282615654754559132956965827017356483256233963852373372,-167739282615654754559132956965827017314616509324664086899225⟩⟩,
  ⟨⟨47253338717496890611777665403712505524103141287457150330451,47253338717496890611777665403712505666502304887361220062449⟩,⟨-170509014422273446120534918987054794293439772999554285060342,-170509014422273446120534918987054794151040609401303371490384⟩⟩,
  ⟨⟨-229870732671268424244129766028553797748066817734673766113212,-229870732671268424244129766028553797263734911127310964708014⟩,⟨158772531098149656329482146620440468374143688567889282353395,158772531098149656329482146620440468858475595176585822533164⟩⟩,
  ⟨⟨236587904727616980696697421237547249383965025047756247078164,236587904727616980696697421237547251031285647736252486504110⟩,⟨-335631397328104005734830019296362577423687566117663122874560,-335631397328104005734830019296362575776366943430116978448907⟩⟩,
  ⟨⟨108819181856341709266850522493336920905135055711813225470964,108819181856341709266850522493336926508037626879904286332133⟩,⟨126695065343300956952164063819954916269628516749061023383575,126695065343300956952164063819954921872531087917714442118772⟩⟩,
  ⟨⟨-184658166843689753963979846368376668566439322101613837573185,-184658166843689753963979846368376649509726739005432052968090⟩,⟨15037672036791746335724694693473628724737341955849076958595,15037672036791746335724694693473647781449925051767058039090⟩⟩,
  ⟨⟨326172858356647899232637378931667184955222133692005391956693,326172858356647899232637378931667249771321805054097552832360⟩,⟨-88984895086233237835393820183014080476397422713047811042217,-88984895086233237835393820183014015660297751350848809279095⟩⟩,
  ⟨⟨-159086603581942902614981469893983998840644210242632305902346,-159086603581942902614981469893983778386735732144566441718583⟩,⟨169810330253978055405292504988094076850282380786355630749541,169810330253978055405292504988094297304190858884376086735848⟩⟩,
  ⟨⟨78894903178015150724851413936118237978366926032716243210578,78894903178015150724851413936118987790928968163983124403565⟩,⟨-13531480489809717287620037663663009719111403744501453378872,-13531480489809717287620037663662259906549361613214938081121⟩⟩,
  ⟨⟨-17913702388310802049758239027146673777590072535672511878258,-17913702388310802049758239027144123499021329482553459973938⟩,⟨-81963367985453275964350490747432081760700302028137363194572,-81963367985453275964350490747429531482131558975025828964765⟩⟩,
  ⟨⟨-3515582712801591269172999617857151185884092019388622830257,-3515582712801591269172999617848477123715185156994427171220⟩,⟨263210246652608341982344575532764270205911268623124430188234,263210246652608341982344575532772944268080175485521860736665⟩⟩,
  ⟨⟨-35691755575021880690632652555031298017869578209241693375896,-35691755575021880690632652555001795611570827866755463135456⟩,⟨-269822200080984273853445433615061319758740761649096192911515,-269822200080984273853445433615031817352442011306610066178008⟩⟩,
  ⟨⟨-17449969529192285706525055551006636471517436210947157738759,-17449969529192285706525055550906292254417338090521184749197⟩,⟨199454064400259554764599631361337231115402187670652540950009,199454064400259554764599631361437575332502285791079293261297⟩⟩,
  ⟨⟨-170646451741431684825163837459,170646451741431684826883302404⟩,⟨-87266462599716478846184538424601282123885026111912385677699,-87266462599716478846184538424259989220402162742260114371743⟩⟩]
def cBox16 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-28624674153641342903597614282063769361566618192227784502755,-28624674153641342903597614282063769361566618192199280669248⟩,⟨-10418529357494547381300296597045329845068072893316067118486,-10418529357494547381300296597045329845068072893287689677013⟩⟩,
  ⟨⟨93340192681939659953812544564663728666758123701663536299024,93340192681939659953812544564663728666758123702232168215405⟩,⟨-285000283602,283018362573⟩⟩,
  ⟨⟨-154901683599415233601257511394191273285249104983283173365574,-154901683599415233601257511394191273285249104976903441796616⟩,⟨-7468850090336757826755954330336569721614730086471311426294,-7468850090336757826755954330336569721614730080092718531707⟩⟩,
  ⟨⟨261178304111933557075819270755055019638080463337904020762708,261178304111933557075819270755055019638080463388492584551201⟩,⟨20837058714989094762600593194090659690136145761308483228732,20837058714989094762600593194090659690136145811895580943977⟩⟩,
  ⟨⟨-294911972622324723531976328241186866285386290689339128454102,-294911972622324723531976328241186866285386290376690187923212⟩,⟨-31692010536379151917312252996160578363417072791731181985610,-31692010536379151917312252996160578363417072479083984281450⟩⟩,
  ⟨⟨309803367198830467202515022788382546570498209161665366154789,309803367198830467202515022788382546570498210758709397747470⟩,⟨176607656294061714192050696090030074373837647951850226226723,176607656294061714192050696090030074373837649548887808346365⟩⟩,
  ⟨⟨-307848400452903387052725543037386883971459528730073216028106,-307848400452903387052725543037386883971459521698273913835891⟩,⟨-320826655423514117295944595797029698565975891829001637404294,-320826655423514117295944595797029698565975884797180082348458⟩⟩,
  ⟨⟨199214604076119255887703525162118794322309092882697309509577,199214604076119255887703525162118794322309120484033056565874⟩,⟨578269289774269930757264685601738240405117617554728521658685,578269289774269930757264685601738240405117645156001152851324⟩⟩,
  ⟨⟨-139032805649945949855824076971497761700617892874150491853235,-139032805649945949855824076971497761700617793485685547898792⟩,⟨-792344755829520905029405736282398788388154034135956367763185,-792344755829520905029405736282398788388153934747379729603180⟩⟩,
  ⟨⟨-82760940715626804123523588282868054277004117436237098749000,-82760940715626804123523588282868054277003780900746608918646⟩,⟨893196586663468468944120596865350418724186665780808326445463,893196586663468468944120596865350418724187002316033589309566⟩⟩,
  ⟨⟨283133659791116204448706888257314439807969729533373843914499,283133659791116204448706888257314439807970823494595268470598⟩,⟨-926965431539214390869154465718170579554632088563982254418505,-926965431539214390869154465718170579554630994601704405122353⟩⟩,
  ⟨⟨-617651767651733854255240565825769430541959469804002641907474,-617651767651733854255240565825769430541956000544709343459155⟩,⟨716588930369406754752069900775320344350347450669746696488840,716588930369406754752069900775320344350350919926354523279213⟩⟩,
  ⟨⟨967677490209007579082037607943258413042295271772168364572309,967677490209007579082037607943258413042306126341152637559076⟩,⟨-573626559641585491538742490599162805805836617449089213633386,-573626559641585491538742490599162805805825762876085588398417⟩⟩,
  ⟨⟨-1173339835267653407322365386058602635768160983198890757088215,-1173339835267653407322365386058602635768127244138868151345925⟩,⟨245891035901135597135763886615768751347561610113543097931396,245891035901135597135763886615768751347595349168913892081192⟩⟩,
  ⟨⟨1369448924088595957991831509245547466286884315921547727343606,1369448924088595957991831509245547466286988887405638699606788⟩,⟨-52285744657483855590,52285744657483925991⟩⟩,
  ⟨⟨-1173339835267653407322365386058602635768305990284122240260142,-1173339835267653407322365386058602635767982237053636668193169⟩,⟨-245891035901135597135763886615768751347740356253828127523518,-245891035901135597135763886615768751347416603028628862643644⟩⟩,
  ⟨⟨967677490209007579082037607943258413041799719956917055328295,967677490209007579082037607943258413042801678156403946822408⟩,⟨573626559641585491538742490599162805805330211060391926040935,573626559641585491538742490599162805806332169264782876188070⟩⟩,
  ⟨⟨-617651767651733854255240565825769430543507994147330419398784,-617651767651733854255240565825769430540407476201381565954505⟩,⟨-716588930369406754752069900775320344351899444268767698661838,-716588930369406754752069900775320344348798926327333521355730⟩⟩,
  ⟨⟨283133659791116204448706888257314439803173218711321765417832,283133659791116204448706888257314439812767334316647346882125⟩,⟨926965431539214390869154465718170579549834483778572538088999,926965431539214390869154465718170579559428599387114121750326⟩⟩,
  ⟨⟨-82760940715626804123523588282868054291847651889598996775071,-82760940715626804123523588282868054262160246447384710700159⟩,⟨-893196586663468468944120596865350418739030536768720083203590,-893196586663468468944120596865350418709343131328121832868890⟩⟩,
  ⟨⟨-139032805649945949855824076971497761746549150791968175542253,-139032805649945949855824076971497761654686535567867864531232⟩,⟨792344755829520905029405736282398788342222676829342581063566,792344755829520905029405736282398788434085292053993516596087⟩⟩,
  ⟨⟨199214604076119255887703525162118794180182551085495303198571,199214604076119255887703525162118794464435662281235063328521⟩,⟨-578269289774269930757264685601738240547244186953085254949928,-578269289774269930757264685601738240262991075757644419768863⟩⟩,
  ⟨⟨-307848400452903387052725543037386884411245757655418098428508,-307848400452903387052725543037386883531673292772929031991457⟩,⟨320826655423514117295944595797029698126189655871839755761993,320826655423514117295944595797029699005762120754341964057551⟩⟩,
  ⟨⟨309803367198830467202515022788382545209655206739591603435134,309803367198830467202515022788382547931341213180783161076387⟩,⟨-176607656294061714192050696090030075734680651970873387806238,-176607656294061714192050696090030073012994645529864646639937⟩⟩,
  ⟨⟨-294911972622324723531976328241186870496281359669840057544830,-294911972622324723531976328241186862074491221396189259421848⟩,⟨31692010536379151917312252996160574152522003498674960313035,31692010536379151917312252996160582574312141772140205606715⟩⟩,
  ⟨⟨261178304111933557075819270755055006608188521693319600531754,261178304111933557075819270755055032667972405033077005266132⟩,⟨-20837058714989094762600593194090672720028087456334838549111,-20837058714989094762600593194090646660244204116869225055003⟩⟩,
  ⟨⟨-154901683599415233601257511394191313604012983600028265176995,-154901683599415233601257511394191232966485226360158350277972⟩,⟨7468850090336757826755954330336529402850851463553873646271,7468850090336757826755954330336610040378608703010155559573⟩⟩,
  ⟨⟨93340192681939659953812544564663603907264493499834654159023,93340192681939659953812544564663853426251753904061050384669⟩,⟨-124759493630201813573070226,124759493630201815555859838⟩⟩,
  ⟨⟨-28624674153641342903597614282064155408403215722437839044596,-28624674153641342903597614282063383314730020661989225847806⟩,⟨10418529357494547381300296597044943798231475363508037156734,10418529357494547381300296597045715891904670423095718753081⟩⟩,
  ⟨⟨-1194555666350364144385521532,1194555666350364144384925090⟩,⟨-1194555666350363523326214935,1194555666350363523327005771⟩⟩]
def dBox16 : Fin 31 → CI :=
  ![⟨⟨-51827941654,53547380933⟩,⟨87266462599716478846184538424430635672143594427033405136294,87266462599716478846184538424430635672143594427139094866778⟩⟩,
  ⟨⟨-91456170927759873883136228063441721756557472754468701734531,-91456170927759873883136228063441721756557472752379371969706⟩,⟨-251273764493802546582199074203781309579031924709903813854885,-251273764493802546582199074203781309579031924707813847030483⟩⟩,
  ⟨⟨187762575310302153026501687005379923063644735962547860162886,187762575310302153026501687005379923063644735986080837714502⟩,⟨357466701171119366105852128545454222146042603345675412360282,357466701171119366105852128545454222146042603369209460526278⟩⟩,
  ⟨⟨-291268930075817916917525973157170535353152786160628234151195,-291268930075817916917525973157170535353152785972781123499439⟩,⟨-472240204583844893938031745214101791911880319420195626268930,-472240204583844893938031745214101791911880319232347674286498⟩⟩,
  ⟨⟨375525150620604306053003374010759846127289471362910749752655,375525150620604306053003374010759846127289472534339445503007⟩,⟨415281066387888614318213609983131983485920254404913612294509,415281066387888614318213609983131983485920255576343313267848⟩⟩,
  ⟨⟨-140118983056299762701352785020324224329480601750559470784084,-140118983056299762701352785020324224329480595700721849772709⟩,⟨-324359093176608016639114400402749501747369667741221701316476,-324359093176608016639114400402749501747369661691373629349324⟩⟩,
  ⟨⟨-187762575310302153026501687005379923063644749458155446952510,-187762575310302153026501687005379923063644722490460968107522⟩,⟨380228401823439083203647903097891322848675481613506502721070,380228401823439083203647903097891322848675508581164005760027⟩⟩,
  ⟨⟨582537860151635833835051946314341070706305518527635944714130,582537860151635833835051946314341070706305625739159960766820⟩,⟨-441932880180084694711665342020640964665696842840655237799204,-441932880180084694711665342020640964665696735629010131384827⟩⟩,
  ⟨⟨-831475508205750094474322572968439327316945023414347321292541,-831475508205750094474322572968439327316944632656127969866805⟩,⟨636247506477930961674046280993452465818768454229054543571711,636247506477930961674046280993452465818768844987050508027601⟩⟩,
  ⟨⟨733687807171153988051225134451187381729977090949416429886203,733687807171153988051225134451187381729978427999497031783251⟩,⟨-682681021368540351337509875154911676807330523896621262348090,-682681021368540351337509875154911676807329186845966886621520⟩⟩,
  ⟨⟨-503593949839148178746468100942735179923821684229410347089265,-503593949839148178746468100942735179923817302441166731323818⟩,⟨548125816857401514235318396362313877232705276990288960099566,548125816857401514235318396362313877232709658776545466722127⟩⟩,
  ⟨⟨210843723111276434549210148210250900290779914804360714895439,210843723111276434549210148210250900290793889053036803851779⟩,⟨-137355488101889987342562803741841692727118783164445062276136,-137355488101889987342562803741841692727104808910708025030880⟩⟩,
  ⟨⟨-274368512783279621649408684190325165269694354792371435016301,-274368512783279621649408684190325165269650481728155098156608⟩,⟨-372503062108843343487664686977624618563787981602400698185687,-372503062108843343487664686977624618563744108546872355859917⟩⟩,
  ⟨⟨487712752421147381971418466947716613679029802827960042122948,487712752421147381971418466947716613679166425676843013960114⟩,⟨552871157018090846123517700054093710623700386254549234813696,552871157018090846123517700054093710623837009115987169723273⟩⟩,
  ⟨⟨-745737991008909878059113192539536272263140249628853250133353,-745737991008909878059113192539536272262716423998006291597924⟩,⟨-519528946495267252194038685582268955814571025194565349312008,-519528946495267252194038685582268955814147199579563035848909⟩⟩,
  ⟨⟨975425504842294763942836933895433227357539901880496759083580,975425504842294763942836933895433227358852555129109354681592⟩,⟨-656326632803637980808,656326632803638183559⟩⟩,
  ⟨⟨-745737991008909878059113192539536272264959834920786478906111,-745737991008909878059113192539536272260896838706073062691931⟩,⟨519528946495267252194038685582268955812327614288387206415115,519528946495267252194038685582268955816390610485741178363089⟩⟩,
  ⟨⟨487712752421147381971418466947716613672811432154430502020559,487712752421147381971418466947716613685384796350372553812277⟩,⟨-552871157018090846123517700054093710630055379791625889985887,-552871157018090846123517700054093710617482015578910514242972⟩⟩,
  ⟨⟨-274368512783279621649408684190325165289125944059523963683945,-274368512783279621649408684190325165250218892461002569151630⟩,⟨372503062108843343487664686977624618544312519282326046744591,372503062108843343487664686977624618583219570866947007096722⟩⟩,
  ⟨⟨210843723111276434549210148210250900230590953425631818185635,210843723111276434549210148210250900350982850431765700177187⟩,⟨137355488101889987342562803741841692666915847529256710419065,137355488101889987342562803741841692787307744545896376961268⟩⟩,
  ⟨⟨-503593949839148178746468100942735180110085761954910665096901,-503593949839148178746468100942735179737553224715666412932085⟩,⟨-548125816857401514235318396362313877418973736499821195211372,-548125816857401514235318396362313877046441199267013231553637⟩⟩,
  ⟨⟨733687807171153988051225134451187381153608620406462762869432,733687807171153988051225134451187382306346898542450698461933⟩,⟨682681021368540351337509875154911676230960716301654911750575,682681021368540351337509875154911677383698994440933237036334⟩⟩,
  ⟨⟨-831475508205750094474322572968439329100420267205491447023085,-831475508205750094474322572968439325533469388864983843886677⟩,⟨-636247506477930961674046280993452467602244088777826664244165,-636247506477930961674046280993452464035293210438278387076122⟩⟩,
  ⟨⟨582537860151635833835051946314341065187646942515669395978917,582537860151635833835051946314341076224964201751126509366523⟩,⟨441932880180084694711665342020640959147038159616690717458407,441932880180084694711665342020640970184355418852974651381155⟩⟩,
  ⟨⟨-187762575310302153026501687005379940140186538148104757251849,-187762575310302153026501687005379905987102933800511657800988⟩,⟨-380228401823439083203647903097891339925217297271278476088102,-380228401823439083203647903097891305772133692923392032028120⟩⟩,
  ⟨⟨-140118983056299762701352785020324277169907821085461274618368,-140118983056299762701352785020324171489053376365820045820378⟩,⟨324359093176608016639114400402749448906942442356072288829022,324359093176608016639114400402749554587796887076523041492664⟩⟩,
  ⟨⟨375525150620604306053003374010759682621658114260562200732469,375525150620604306053003374010760009632920829636687994297407⟩,⟨-415281066387888614318213609983132146991551612679202359806114,-415281066387888614318213609983131819980288897302054565477619⟩⟩,
  ⟨⟨-291268930075817916917525973157171041293261349414375659019999,-291268930075817916917525973157170029413044222719033698325645⟩,⟨472240204583844893938031745214101285971771755977840903836599,472240204583844893938031745214102297851988882674702396534948⟩⟩,
  ⟨⟨187762575310302153026501687005378357518829383983514747744779,187762575310302153026501687005381488608460087965113949785835⟩,⟨-357466701171119366105852128545455787690857955349332647975118,-357466701171119366105852128545452656601227251365552224847630⟩⟩,
  ⟨⟨-91456170927759873883136228063446566066244314844293260917129,-91456170927759873883136228063436877446870630662554812440516⟩,⟨251273764493802546582199074203776465269345082616415110556504,251273764493802546582199074203786153888718766801302550387410⟩⟩,
  ⟨⟨-14989884742938991971769901044,14989884742938991973489035649⟩,⟨-87266462599716478846184538424445625556886533421330329851216,-87266462599716478846184538424415645787400655432842170328534⟩⟩]
def cBox19 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-29998959670852502253334400260293903887583974252661922254902,-29998959670852502253334400260293903887583974252636024531917⟩,⟨5289625983156427915144478140897837194877087266713827602257,5289625983156427915144478140897837194877087266739574304582⟩⟩,
  ⟨⟨78086407022271780569795821758218198413269382170775846533150,78086407022271780569795821758218198413269382171284672081956⟩,⟨-78086407022271780569795821758218198413269382171286314132106,-78086407022271780569795821758218198413269382170777455029911⟩⟩,
  ⟨⟨-80720000810435206393835349879154567726463443619508748554834,-80720000810435206393835349879154567726463443613886575389358⟩,⟨189023499821901213903802269589175580750885147411238541307570,189023499821901213903802269589175580750885147416861274407702⟩⟩,
  ⟨⟨67507155055958924739506865476422524023515207615668978818468,67507155055958924739506865476422524023515207659481108692414⟩,⟨-357502382059455574647445980170955115113667522474281043405528,-357502382059455574647445980170955115113667522430466758593259⟩⟩,
  ⟨⟨101557059525424301156435943073245227416599589270826380034608,101557059525424301156435943073245227416599589535790935133826⟩,⟨558446214245317866030907332236726730461939952322224489699378,558446214245317866030907332236726730461939952587192296978519⟩⟩,
  ⟨⟨-316813851638276482210105745845552627547356702942999283715638,-316813851638276482210105745845552627547356701626316019986436⟩,⟨-601703324395952791558640268212132304843598359512603356451727,-601703324395952791558640268212132304843598358195924958390532⟩⟩,
  ⟨⟨506121083576086063020068714933506598554881096112685948901954,506121083576086063020068714933506598554881101710074924655714⟩,⟨618976975322717298666015133405325669399951741549123731773832,618976975322717298666015133405325669399951747146542073309327⟩⟩,
  ⟨⟨-690006283994083385615241844205971094361649671524974608116270,-690006283994083385615241844205971094361649650505595771635579⟩,⟨-482393741243518841048223492776900887676042270870130483109826,-482393741243518841048223492776900887676042249850833123838616⟩⟩,
  ⟨⟨668447966033740715972586642084335948860231481516704581744113,668447966033740715972586642084335948860231553168509489527479⟩,⟨385646512794520419157083715915497786976514590509616856569899,385646512794520419157083715915497786976514662161550135987056⟩⟩,
  ⟨⟨-715458638580059901986008458442524668361845996529158190953812,-715458638580059901986008458442524668361845769394408869721595⟩,⟨-403460210979846917994325574928498767314801919771670706277635,-403460210979846917994325574928498767314801692637274954608435⟩⟩,
  ⟨⟨718847743922454399947720228927531466340474793034918292267314,718847743922454399947720228927531466340475476907821448921677⟩,⟨451622723002544877139974661387162452885423166620231768972962,451622723002544877139974661387162452885423850494462646974757⟩⟩,
  ⟨⟨-939878367470178921963504273211870500198541921428454833740560,-939878367470178921963504273211870500198539930801844895202854⟩,⟨-634873636723393983507044971236595974941072115797798745401444,-634873636723393983507044971236595974941070125174487478715883⟩⟩,
  ⟨⟨1265078633113030273681581575773852304879836996777787625007695,1265078633113030273681581575773852304879842675095626537354899⟩,⟨527096354735120649335024318014269194272578787681612380576866,527096354735120649335024318014269194272584466004278832625825⟩⟩,
  ⟨⟨-1493605818398317590648981886871000986505573365232055247199583,-1493605818398317590648981886871000986505557343351298089895170⟩,⟨-391519817628296909079952779285602707159119367006676357123971,-391519817628296909079952779285602707159103345131783531010332⟩⟩,
  ⟨⟨1721671744626475063966632333378512160200365871519935349965516,1721671744626475063966632333378512160200410841135749272501570⟩,⟨-22484811085035126531,22484811085035039585⟩⟩,
  ⟨⟨-1493605818398317590648981886871000986505628320622913876371973,-1493605818398317590648981886871000986505502387960439460810458⟩,⟨391519817628296909079952779285602707159048389741459557904904,391519817628296909079952779285602707159174322397000330423569⟩⟩,
  ⟨⟨1265078633113030273681581575773852304879663659475134189248483,1265078633113030273681581575773852304880016012398279973277361⟩,⟨-527096354735120649335024318014269194272757803307337319285939,-527096354735120649335024318014269194272405450378553894163097⟩⟩,
  ⟨⟨-939878367470178921963504273211870500199033710661943906609705,-939878367470178921963504273211870500198048141568355822551594⟩,⟨634873636723393983507044971236595974940578335942815733199285,634873636723393983507044971236595974941563905029470491249177⟩⟩,
  ⟨⟨718847743922454399947720228927531466339096890029384454710045,718847743922454399947720228927531466341853379913355286722940⟩,⟨-451622723002544877139974661387162452886801753500218554752292,-451622723002544877139974661387162452884045263614475861630815⟩⟩,
  ⟨⟨-715458638580059901986008458442524668365700532469774018337051,-715458638580059901986008458442524668357991233453793042576007⟩,⟨403460210979846917994325574928498767310947156699936077046583,403460210979846917994325574928498767318656455709009584396123⟩⟩,
  ⟨⟨668447966033740715972586642084335948849450970970670302258425,668447966033740715972586642084335948871012063714543769209023⟩,⟨-385646512794520419157083715915497786987295172703408478747750,-385646512794520419157083715915497786965734079967758514491537⟩⟩,
  ⟨⟨-690006283994083385615241844205971094391800270516615102219731,-690006283994083385615241844205971094331499051513955277647968⟩,⟨482393741243518841048223492776900887645891650868348475027256,482393741243518841048223492776900887706192869852615132730453⟩⟩,
  ⟨⟨506121083576086063020068714933506598470557076027990091960802,506121083576086063020068714933506598639205121794770781594205⟩,⟨-618976975322717298666015133405325669484275767213720737773276,-618976975322717298666015133405325669315627721481945068234056⟩⟩,
  ⟨⟨-316813851638276482210105745845552627783190759517585899416406,-316813851638276482210105745845552627311522645051729404125838⟩,⟨601703324395952791558640268212132304607764301655842067120159,601703324395952791558640268212132305079432416052686248742816⟩⟩,
  ⟨⟨101557059525424301156435943073245226757028326534715813496313,101557059525424301156435943073245228076170852271901501321075⟩,⟨-558446214245317866030907332236726731121511215255824338607035,-558446214245317866030907332236726729802368689653592449155427⟩⟩,
  ⟨⟨67507155055958924739506865476422522178852669710710722084500,67507155055958924739506865476422525868177745564439365996386⟩,⟨357502382059455574647445980170955113269004984657688746425127,357502382059455574647445980170955116958330060247059056683781⟩⟩,
  ⟨⟨-80720000810435206393835349879154572885541878680084755910964,-80720000810435206393835349879154562567385008553310568840187⟩,⟨-189023499821901213903802269589175585909963582218599634068138,-189023499821901213903802269589175575591806712609500182732679⟩⟩,
  ⟨⟨78086407022271780569795821758218183984565078878919718290927,78086407022271780569795821758218212841973685463140801375051⟩,⟨78086407022271780569795821758218183984565079385810314559212,78086407022271780569795821758218212841973684956253455613337⟩⟩,
  ⟨⟨-29998959670852502253334400260293944241207299171120834931905,-29998959670852502253334400260293863533960649334177113145186⟩,⟨-5289625983156427915144478140897877548500411192552700777149,-5289625983156427915144478140897796841253763340900702008225⟩⟩,
  ⟨⟨-112859400346877519141247487,112859400346877519142760649⟩,⟨-112859400344933608154912740,112859400344933608155606681⟩⟩]
def dBox19 : Fin 31 → CI :=
  ![⟨⟨-42583077798,44302517076⟩,⟨87266462599716478846184538424430635672143594427042682259620,87266462599716478846184538424430635672143594427129817743561⟩⟩,
  ⟨⟨-181457271423278353442539591330307138269855717433356022029335,-181457271423278353442539591330307138269855717431661495719402⟩,⟨-259147840492017835097636591434791992491066951319352075211822,-259147840492017835097636591434791992491066951317657379576528⟩⟩,
  ⟨⟨463283353389689492913152625700529092592727468812342369416043,463283353389689492913152625700529092592727468831098942901547⟩,⟨239761622777744388978996186713944534605045962234127162870132,239761622777744388978996186713944534605045962252883356251452⟩⟩,
  ⟨⟨-715879142894163214074909965167889506994367295814875328814300,-715879142894163214074909965167889506994367295667760389729781⟩,⟨-186843456626211955596675440011241833636374199720804791858584,-186843456626211955596675440011241833636374199573692176309978⟩⟩,
  ⟨⟨1052605604807642356909770599267183736629640509771488434136173,1052605604807642356909770599267183736629640510669533929643382⟩,⟨-142411835615632875872479695126482728482201354555008845572373,-142411835615632875872479695126482728482201353656966440657340⟩⟩,
  ⟨⟨-812977363793342802495857965562931326390239989956313477922380,-812977363793342802495857965562931326390239985441158924785590⟩,⟨607100304604663942637492387094525792213327541170105197216736,607100304604663942637492387094525792213327545685274208056550⟩⟩,
  ⟨⟨473072243456819281193494896531721261739175618631327382456264,473072243456819281193494896531721261739175638087054928004015⟩,⟨-555655604929565712607196180868459947826557188629096385673297,-555655604929565712607196180868459947826557169173435639871565⟩⟩,
  ⟨⟨-164254048994606382087931692071709467202526473202483808889137,-164254048994606382087931692071709467202526399075258764761691⟩,⟨513574503728378073777157256851500952568070991964542419784128,513574503728378073777157256851500952568071066091970404268698⟩⟩,
  ⟨⟨-73979948119989317195749242042714556673615934468193110335190,-73979948119989317195749242042714556673615678098319371228723⟩,⟨41798032003651696182358695113588094931528895375612307123387,41798032003651696182358695113588094931529151745116787909188⟩⟩,
  ⟨⟨-476477632554014619234664538028970434614952517268193604596324,-476477632554014619234664538028970434614951693712348011581435⟩,⟨-368873804775857495635611946291443473217333740325247339358974,-368873804775857495635611946291443473217332916768399093134400⟩⟩,
  ⟨⟨876268059154901152680500126938744620329962096201600764848496,876268059154901152680500126938744620329964603589648311986013⟩,⟨274321263132523281150547859763576604296978576265731550490534,274321263132523281150547859763576604296981083650385078512737⟩⟩,
  ⟨⟨-1476351782220317664238898615498549808641422893342140070345224,-1476351782220317664238898615498549808641415533197243729743287⟩,⟨116612691931377481974974485439858545954561218550214706597736,116612691931377481974974485439858545954568578703584341729182⟩⟩,
  ⟨⟨1199865919846385717352609925952783968864379288314723116838990,1199865919846385717352609925952783968864400402736798595624681⟩,⟨-1054183988184891228483685874932210759927210994084364144085838,-1054183988184891228483685874932210759927189879676608142172871⟩⟩,
  ⟨⟨-524008195812816144593888790208054388364147579789167579969521,-524008195812816144593888790208054388364087801134272743537150⟩,⟨1051617433767373144881355401663515306385969753876802285604678,1051617433767373144881355401663515306386029532552970224401118⟩⟩,
  ⟨⟨-1274305368544844319877162087721548204034037842402078145887,-1274305368544844319877162087721548203865950903760215312707⟩,⟨-1025958610177857886849970202129735948881281829755629925325420,-1025958610177857886849970202129735948881113742843011174864403⟩⟩,
  ⟨⟨723129021051270681269578775215770990398059333624373763243050,723129021051270681269578775215770990398530442642206701094991⟩,⟨-235554523768393966555,235554523768394310280⟩⟩,
  ⟨⟨-1274305368544844319877162087721548204609297858345324896986,-1274305368544844319877162087721548203290690887816968684155⟩,⟨1025958610177857886849970202129735948880538482828009185056048,1025958610177857886849970202129735948881857089770631914464153⟩⟩,
  ⟨⟨-524008195812816144593888790208054388365962078542347073364442,-524008195812816144593888790208054388362273302381093249908488⟩,⟨-1051617433767373144881355401663515306387844031311615258076303,-1051617433767373144881355401663515306384155255118157251300493⟩⟩,
  ⟨⟨1199865919846385717352609925952783968859231137805321372349553,1199865919846385717352609925952783968869548553246200339784035⟩,⟨1054183988184891228483685874932210759922041729168663700993446,1054183988184891228483685874932210759932359144592308584697561⟩⟩,
  ⟨⟨-1476351782220317664238898615498549808655847180804897084663307,-1476351782220317664238898615498549808626991245734486715015697⟩,⟨-116612691931377481974974485439858545968992866178179440878699,-116612691931377481974974485439858545940136931075619606949883⟩⟩,
  ⟨⟨876268059154901152680500126938744620289611582777055085794183,876268059154901152680500126938744620370315117014193990562267⟩,⟨-274321263132523281150547859763576604337331597084118758321068,-274321263132523281150547859763576604256628062831997871102978⟩⟩,
  ⟨⟨-476477632554014619234664538028970434727806439181664033672643,-476477632554014619234664538028970434502097771798877581967996⟩,⟨368873804775857495635611946291443473104478994826037324126640,368873804775857495635611946291443473330187662267609108702891⟩⟩,
  ⟨⟨-73979948119989317195749242042714556989242362537191895726437,-73979948119989317195749242042714556357989250029320586423697⟩,⟨-41798032003651696182358695113588095247155579864526090745176,-41798032003651696182358695113588094615902467256203004526464⟩⟩,
  ⟨⟨-164254048994606382087931692071709468085258202230848564634619,-164254048994606382087931692071709466319794670046894008398097⟩,⟨-513574503728378073777157256851500953450802795221791310352994,-513574503728378073777157256851500951685339262834721513567140⟩⟩,
  ⟨⟨473072243456819281193494896531721259270386703532419843836687,473072243456819281193494896531721264207964553185962465995482⟩,⟨555655604929565712607196180868459945357768253877014965814812,555655604929565712607196180868459950295346103925517059713359⟩⟩,
  ⟨⟨-812977363793342802495857965562931333294850153667297664325809,-812977363793342802495857965562931319485629821730174737767245⟩,⟨-607100304604663942637492387094525799117937709783598768516423,-607100304604663942637492387094525785308717377071780636853541⟩⟩,
  ⟨⟨1052605604807642356909770599267183717319102847799473667510702,1052605604807642356909770599267183755940178172641548695690108⟩,⟨142411835615632875872479695126482709171663690926657822112488,142411835615632875872479695126482747792739017285317464323252⟩⟩,
  ⟨⟨-715879142894163214074909965167889561001306981065662840569987,-715879142894163214074909965167889452987427610416972877448614⟩,⟨186843456626211955596675440011241779629434512837834937830075,186843456626211955596675440011241887643313886456662030037232⟩⟩,
  ⟨⟨463283353389689492913152625700528941548277793773606174441511,463283353389689492913152625700529243637177143869835137416657⟩,⟨-239761622777744388978996186713944685649495640199818017024074,-239761622777744388978996186713944383560596284287192501711318⟩⟩,
  ⟨⟨-181457271423278353442539591330307560704933700533129825904107,-181457271423278353442539591330306715834777734331887691462133⟩,⟨259147840492017835097636591434791570055988962522712121732101,259147840492017835097636591434792414926144940114297332600038⟩⟩,
  ⟨⟨-1181449536837289227599044726,1181449536837289229318187288⟩,⟨-87266462599716478846184538424431817121680442869236817196463,-87266462599716478846184538424429454222606745984935682291851⟩⟩]
def cBox21 : Fin 31 → CI :=
  ![⟨⟨0,0⟩,⟨0,0⟩⟩,
  ⟨⟨-26380642397055816535097180326270597663156998636395478033762,-26380642397055816535097180326270597663156998636364942629027⟩,⟨15230870989335429967337177468944677677953239825973862604340,15230870989335429967337177468944677677953239826004339573799⟩⟩,
  ⟨⟨30461741978670859934674354937889355355906479651670098379681,30461741978670859934674354937889355355906479652282995651015⟩,⟨-113684768751453352939543070528319906038126956577023122919257,-113684768751453352939543070528319906038126956576409678405484⟩⟩,
  ⟨⟨87304126354397536404445890202049308374969957936872404506549,87304126354397536404445890202049308374969957943803418549328⟩,⟨212138666513571275911748963587695134398300673323976180034379,212138666513571275911748963587695134398300673330907843919176⟩⟩,
  ⟨⟨-280130822297018338949280501709181007402567910453984373837594,-280130822297018338949280501709181007402567910398404365830818⟩,⟨-257831279481577565813760495994529167432160392833196534627727,-257831279481577565813760495994529167432160392777616643197488⟩⟩,
  ⟨⟨621185128551378397767909713294140725516948779982022747080166,621185128551378397767909713294140725516948780330659109668665⟩,⟨135984311566894126075063076242971746008534474023176947637487,135984311566894126075063076242971746008534474371810241566312⟩⟩,
  ⟨⟨-795793381260173470576801493698239342266888696944796735028317,-795793381260173470576801493698239342266888695129218463051055⟩,⟨363353849069800831954149217299611558084788386443150825998307,363353849069800831954149217299611558084788388258723384347552⟩⟩,
  ⟨⟨560261644594036677898561003418362014805135816755076733125810,560261644594036677898561003418362014805135824949677540100926⟩,⟨-909478150011626823516344564226559248305015656711039243503645,-909478150011626823516344564226559248305015648516420360133426⟩⟩,
  ⟨⟨75060827609552406205714366367193035296721498300770189953784,75060827609552406205714366367193035296721531486332835559642⟩,⟨1356055025854210148475362497116601357072024500296630778284272,1356055025854210148475362497116601357072024533482157472068222⟩⟩,
  ⟨⟨-1110467045117477712860333524956928462718112629212057074373401,-1110467045117477712860333524956928462718112505049512113454899⟩,⟨-1196677644134750505633807894181447418000037902916017943214385,-1196677644134750505633807894181447418000037778753394234666298⟩⟩,
  ⟨⟨1802631901696793473434380430006643465839033161186825262226003,1802631901696793473434380430006643465839033601143301223879245⟩,⟨288293021460248425748434850932418522788066652479234314199099,288293021460248425748434850932418522788067092435521724437244⟩⟩,
  ⟨⟨-1871717584817365280102883489105659691936346055575725171141848,-1871717584817365280102883489105659691936344549424693227086919⟩,⟨1000863375947639403320367629040227314372734338493802314931264,1000863375947639403320367629040227314372735844645527623712077⟩⟩,
  ⟨⟨879016408032955963581670209288669892949106645291678576191403,879016408032955963581670209288669892949111700631805730554065⟩,⟨-2249208777539376798393398362896685574606044773109867675066683,-2249208777539376798393398362896685574606039717771600203727289⟩⟩,
  ⟨⟨743032096466061837506607133045698146940566300262971447282248,743032096466061837506607133045698146940583097265537570600442⟩,⟨2440141428574632044800598841747259222126971686881038015216650,2440141428574632044800598841747259222126988483886539263138552⟩⟩,
  ⟨⟨-2165985750766594305388529647306255023923849544875266398541216,-2165985750766594305388529647306255023923793992156719108400310⟩,⟨-1688947132945340120494837359478323559800934200945961187154186,-1688947132945340120494837359478323559800878648230729066810312⟩⟩,
  ⟨⟨2903042702743675543357925473083776361664895181102970879358692,2903042702743675543357925473083776361665078566340728256865948⟩,⟨-91692620716126603246,91692620716126668223⟩⟩,
  ⟨⟨-2165985750766594305388529647306255023924124250500843214021059,-2165985750766594305388529647306255023923519286531142293014327⟩,⟨1688947132945340120494837359478323559800603942605389549676469,1688947132945340120494837359478323559801208906571300704194271⟩⟩,
  ⟨⟨743032096466061837506607133045698146939577067479687142180325,743032096466061837506607133045698146941572330048821875846715⟩,⟨-2440141428574632044800598841747259222127977716670086037770084,-2440141428574632044800598841747259222125982454097491240578927⟩⟩,
  ⟨⟨879016408032955963581670209288669892945819040007234115803487,879016408032955963581670209288669892952399305916250190815798⟩,⟨2249208777539376798393398362896685574602752112487813935678036,2249208777539376798393398362896685574609332378393653943217273⟩⟩,
  ⟨⟨-1871717584817365280102883489105659691947195805736941506772471,-1871717584817365280102883489105659691925494799263476891415370⟩,⟨-1000863375947639403320367629040227314383585594807559131435967,-1000863375947639403320367629040227314361884588331770807383881⟩⟩,
  ⟨⟨1802631901696793473434380430006643465803249723615642007754697,1802631901696793473434380430006643465874817038714484478432286⟩,⟨-288293021460248425748434850932418522823850530006255546265665,-288293021460248425748434850932418522752283214908500492182306⟩⟩,
  ⟨⟨-1110467045117477712860333524956928462836122688559123324668875,-1110467045117477712860333524956928462600102445702445863354769⟩,⟨1196677644134750505633807894181447417882027719406195970599688,1196677644134750505633807894181447418118047962263216207162386⟩⟩,
  ⟨⟨75060827609552406205714366367193034907538633910247717466032,75060827609552406205714366367193035685904395876855308301347⟩,⟨-1356055025854210148475362497116601357461207397872640014130987,-1356055025854210148475362497116601356682841635906148236232532⟩⟩,
  ⟨⟨560261644594036677898561003418362013521658522977609678369889,560261644594036677898561003418362016088613118727144594629941⟩,⟨909478150011626823516344564226559247021538354738929443179764,909478150011626823516344564226559249588492950488530160621446⟩⟩,
  ⟨⟨-795793381260173470576801493698239346499639030529713918278368,-795793381260173470576801493698239338034138361544301279687919⟩,⟨-363353849069800831954149217299611562317538721843629310122411,-363353849069800831954149217299611553852038052858244900507325⟩⟩,
  ⟨⟨621185128551378397767909713294140711557858566261271439501020,621185128551378397767909713294140739476038994051410417307773⟩,⟨-135984311566894126075063076242971759967624688092565416369081,-135984311566894126075063076242971732049444260302421772507053⟩⟩,
  ⟨⟨-280130822297018338949280501709181053437931254645179106630229,-280130822297018338949280501709180961367204566207209633278953⟩,⟨257831279481577565813760495994529121396797048586422351018729,257831279481577565813760495994529213467523737024390826540231⟩⟩,
  ⟨⟨87304126354397536404445890202049156556001403701289343920384,87304126354397536404445890202049460193938512179386479505991⟩,⟨-212138666513571275911748963587695286217269227566491238860357,-212138666513571275911748963587694982579332119088392784982519⟩⟩,
  ⟨⟨30461741978670859934674354937888854675613363991869716804655,30461741978670859934674354937889856036199595312083376825565⟩,⟨113684768751453352939543070528319405357833840916609065562616,113684768751453352939543070528320406718420072236823735867133⟩⟩,
  ⟨⟨-26380642397055816535097180326272248845208237661284933745271,-26380642397055816535097180326268946481105759611475486608816⟩,⟨-15230870989335429967337177468946328860004478850893948034922,-15230870989335429967337177468943026495902000801084254458089⟩⟩,
  ⟨⟨-5445395402658874330671108695,5445395402658874330670999096⟩,⟨-5445395402658874330817171884,5445395402658874330817628439⟩⟩]
def dBox21 : Fin 31 → CI :=
  ![⟨⟨-59766454282,61485893561⟩,⟨87266462599716478846184538424430635672143594427025497960562,87266462599716478846184538424430635672143594427147002042267⟩⟩,
  ⟨⟨-238416409619234633062357726561276946695815781769353816009653,-238416409619234633062357726561276946695815781766947095224861⟩,⟨-238416409619234633062357726561276946695815781769348502303695,-238416409619234633062357726561276946695815781766941703596748⟩⟩,
  ⟨⟨575790770928143146708997935902992009224082658706306080633642,575790770928143146708997935902992009224082658733567307571768⟩,⟨43633231299858239423092269212215317836071797199905931980442,43633231299858239423092269212215317836071797227165735178653⟩⟩,
  ⟨⟨-715249228857703899187073179683830840087447345414406563501297,-715249228857703899187073179683830840087447345194469129676810⟩,⟨238416409619234633062357726561276946695815781658186309688711,238416409619234633062357726561276946695815781878122251233225⟩⟩,
  ⟨⟨825898669637335181509453606820276436080205940548874392649522,825898669637335181509453606820276436080205941940387900831653⟩,⟨-825898669637335181509453606820276436080205941940402412345543,-825898669637335181509453606820276436080205940548889189998016⟩⟩,
  ⟨⟨-3661288260996330,3661317930385404⟩,⟨1430498457715407798374146359367661680174894686947577405792627,1430498457715407798374146359367661680174894694270190702817772⟩⟩,
  ⟨⟨-901473643147094258617540200888699591592042051631690409369429,-901473643147094258617540200888699591592042018198663748900234⟩,⟨-956798363536909899778730414456922389588421349601761350369224,-956798363536909899778730414456922389588421316168751315637655⟩⟩,
  ⟨⟨1430498457715407798374146359367661680174894622122590108938247,1430498457715407798374146359367661680174894759095176516924212⟩,⟨302299894039036308432346376273692622047344306195796620180014,302299894039036308432346376273692622047344443168429772156317⟩⟩,
  ⟨⟨-1500647392255152208802734025503706561136739954129956463393579,-1500647392255152208802734025503706561136739436166463183885931⟩,⟨1128198563676371489941799983093969058127550056945074769801394,1128198563676371489941799983093969058127550574908468745498298⟩⟩,
  ⟨⟨40500506239886871893792761000400715030912665610050812131877,40500506239886871893792761000400715030914517191648974808234⟩,⟨-1930714255133791867975057701202230533887142181449206798164193,-1930714255133791867975057701202230533887140329867369035317395⟩⟩,
  ⟨⟨1180390559006215763573690688450377253318768218069304311264865,1180390559006215763573690688450377253318774598099064862114710⟩,⟨1608164107974812123595814944428337554324336895261252133143302,1608164107974812123595814944428337554324343275290198274929643⟩⟩,
  ⟨⟨-2454313030732090741052164931748814347920013574795232326020356,-2454313030732090741052164931748814347919992069646381410705601⟩,⟨-517333325478356138018508214122954608422555907512648146207158,-517333325478356138018508214122954608422534402361656776341194⟩⟩,
  ⟨⟨1954097233313706671451253589914245494207720443619317140013093,1954097233313706671451253589914245494207792070723468146801285⟩,⟨-1558265426555011149114123658792493030877987689987018924398753,-1558265426555011149114123658792493030877916062886667488298168⟩⟩,
  ⟨⟨-453449841058554462648519564410538933071135153033089707064645,-453449841058554462648519564410538933070897971013263741473922⟩,⟨1913596727073819799557460828913844779176724074757897824114755,1913596727073819799557460828913844779176961256783161707987198⟩⟩,
  ⟨⟨-831324708607349848188952534752654710630588724423214778697916,-831324708607349848188952534752654710629805336328453470189140⟩,⟨-1863698045654018825075769543278000255730846150975547704346222,-1863698045654018825075769543278000255730062762887723704651118⟩⟩,
  ⟨⟨2175396114872969236096014444187136686191981024472437880972001,2175396114872969236096014444187136686194565873631157920255994⟩,⟨-1292424583077888194849,1292424583077888292726⟩⟩,
  ⟨⟨-831324708607349848188952534752654710634459962789574441976460,-831324708607349848188952534752654710625934097962093807009701⟩,⟨1863698045654018825075769543278000255726191524521639263022248,1863698045654018825075769543278000255734717389341632145812503⟩⟩,
  ⟨⟨-453449841058554462648519564410538933085075809768578308664653,-453449841058554462648519564410538933056957314277775139706288⟩,⟨-1913596727073819799557460828913844779190901913519589308090563,-1913596727073819799557460828913844779162783418021470223920058⟩⟩,
  ⟨⟨1954097233313706671451253589914245494161390069451771881504425,1954097233313706671451253589914245494254122444891013405123054⟩,⟨1558265426555011149114123658792493030831585688720252229126955,1558265426555011149114123658792493030924318064153434183581357⟩⟩,
  ⟨⟨-2454313030732090741052164931748814348072913198265108501052589,-2454313030732090741052164931748814347767092446176505235520772⟩,⟨517333325478356138018508214122954608269634778890619161817070,517333325478356138018508214122954608575455530983685760631972⟩⟩,
  ⟨⟨1180390559006215763573690688450377252814491523242757780719687,1180390559006215763573690688450377253823051292925611392581324⟩,⟨-1608164107974812123595814944428337554828619970115751600025358,-1608164107974812123595814944428337553820060200435698807884878⟩⟩,
  ⟨⟨40500506239886871893792761000400713367860368834929242100754,40500506239886871893792761000400716693966813966770544826717⟩,⟨1930714255133791867975057701202230532224088033091734326085394,1930714255133791867975057701202230535550194478224841507222930⟩⟩,
  ⟨⟨-1500647392255152208802734025503706566621284848061178130654815,-1500647392255152208802734025503706555652194542235241516528743⟩,⟨-1128198563676371489941799983093969063612095468839526963202777,-1128198563676371489941799983093969052643005163014016551952441⟩⟩,
  ⟨⟨1430498457715407798374146359367661662087539024848815588009641,1430498457715407798374146359367661698262250356368951037701431⟩,⟨-302299894039036308432346376273692640134700040442257968285228,-302299894039036308432346376273692603959988708921968424124939⟩⟩,
  ⟨⟨-901473643147094258617540200888699651241917312558934380578712,-901473643147094258617540200888699531942166757271419777523772⟩,⟨956798363536909899778730414456922329938546055241536421357135,956798363536909899778730414456922449238296610528976244643058⟩⟩,
  ⟨⟨-196717955099245915430176123,196717955099245945099425105⟩,⟨-1430498457715407798374146359367661876892849789854830138551116,-1430498457715407798374146359367661483456939591362937969969386⟩⟩,
  ⟨⟨825898669637335181509453606820275787328575242979800167375297,825898669637335181509453606820277084831836639509462126184650⟩,⟨825898669637335181509453606820275787328575242979819370331614,825898669637335181509453606820277084831836639509472231868869⟩⟩,
  ⟨⟨-715249228857703899187073179683832979590565503399579747430081,-715249228857703899187073179683828700584329187209295945745598⟩,⟨-238416409619234633062357726561279086198933939863295654345936,-238416409619234633062357726561274807192697623673012906410297⟩⟩,
  ⟨⟨575790770928143146708997935902984953405837268852526573231673,575790770928143146708997935902999065042328048587346814890806⟩,⟨-43633231299858239423092269212222373654317187080944732301207,-43633231299858239423092269212208262017826407346126934997422⟩⟩,
  ⟨⟨-238416409619234633062357726561300215916921117469708674019543,-238416409619234633062357726561253677474710446066592237073261⟩,⟨238416409619234633062357726561253677474710446066587241783152,238416409619234633062357726561300215916921117469702964200159⟩⟩,
  ⟨⟨-76739030402714413924509991930,76739030402714413926229267919⟩,⟨-87266462599716478846184538424507374702546308841011450021670,-87266462599716478846184538424353896641740880013161049979486⟩⟩]
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

def damping (q : Fin 2) : ℝ := if q.val=0 then h else H
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2 = 3/4 := by
  unfold b
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith
lemma damping_pos (q : Fin 2) : 0 < damping q := by
  unfold damping h H
  split_ifs <;> norm_num

lemma waveDen_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < waveDen k t := by
  unfold waveDen
  positivity

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def bBox : RI :=
  ⟨866025403784438646763723170752936183471402626905190314027903,
   866025403784438646763723170752936183471402626905190314027904⟩

def dampingBox (q : Fin 2) : RI := (RI.point (if q.val=0 then 17 else 27)).divNat 50
def realFrequencyBox (j : Fin 31) : RI := (RI.point ((j.val:ℤ)-15)).divNat 18

def denBox (q : Fin 2) (j : Fin 31) : RI :=
  ((dampingBox q).pow 2).add ((realFrequencyBox j).pow 2)

def xwaveBox (q : Fin 2) (j : Fin 31) : RI :=
  ((RI.point 4).divNat 3).mul (denBox q j).invPos

def lambdaBox (q : Fin 2) (j : Fin 31) : CI :=
  ((CI.ofReal (dampingBox q)).add (CI.imag.mul (CI.ofReal (realFrequencyBox j)))).mul
    (CI.ofReal (bBox.mul (denBox q j)).invPos)

def zetaBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.ofReal ((realFrequencyBox j).mul (xwaveBox q j)).neg).add
    (CI.imag.mul (CI.ofReal (((dampingBox q).mul (xwaveBox q j)).sub (dampingBox v))))

def wavePhaseBox (q v : Fin 2) (j : Fin 31) : CI :=
  (CI.imag.mul (CI.ofReal piBox)).mul (zetaBox q v j)
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
def lambdaTable0 : Fin 31 → CI :=
  ![⟨⟨484662521595592790353888749132006423318792208626848524255707,484662521595592790353888749132006423318792208626848524255718⟩,⟨-1187898337244099976357570463558839272840176981928550304548321,-1187898337244099976357570463558839272840176981928550304548304⟩⟩,
  ⟨⟨544867911283138584822799053349139132217167968733227359708864,544867911283138584822799053349139132217167968733227359708877⟩,⟨-1246429862412408527372416135112409779581756791219801149660822,-1246429862412408527372416135112409779581756791219801149660802⟩⟩,
  ⟨⟨616125455828785186640031209410849401263812337445142139496261,616125455828785186640031209410849401263812337445142139496276⟩,⟨-1308763223165720167699412699728928466736856272350792126380972,-1308763223165720167699412699728928466736856272350792126380948⟩⟩,
  ⟨⟨701012548099458312593443087189901521419594222238944623687366,701012548099458312593443087189901521419594222238944623687384⟩,⟨-1374534408038153554104790367039022591018812200468518869975255,-1374534408038153554104790367039022591018812200468518869975228⟩⟩,
  ⟨⟨802766040626567318021182493639755454113483865641057322008204,802766040626567318021182493639755454113483865641057322008222⟩,⟨-1442880138381085048730883566999560456739921980727390611452680,-1442880138381085048730883566999560456739921980727390611452654⟩⟩,
  ⟨⟨925410982171966473511620285128677340472764915781774561777701,925410982171966473511620285128677340472764915781774561777726⟩,⟨-1512109447993409270443823995308296307962034176114010721859022,-1512109447993409270443823995308296307962034176114010721858987⟩⟩,
  ⟨⟨1073846233722498686723799701152437280744992316366756771588193,1073846233722498686723799701152437280744992316366756771588226⟩,⟨-1579185637827203951064411325224172471683812229951112899394440,-1579185637827203951064411325224172471683812229951112899394398⟩⟩,
  ⟨⟨1253783091791566934865867417482053677595842248732774067210649,1253783091791566934865867417482053677595842248732774067210686⟩,⟨-1638932146132767235118780937885037487053388560434998780667555,-1638932146132767235118780937885037487053388560434998780667512⟩⟩,
  ⟨⟨1471316801780572746287703798999140201404204040972285428207427,1471316801780572746287703798999140201404204040972285428207474⟩,⟨-1682878694847060330721229835456532910102847759282025816577167,-1682878694847060330721229835456532910102847759282025816577115⟩⟩,
  ⟨⟨1731711256342143539892173366336002562518781963229355264278468,1731711256342143539892173366336002562518781963229355264278521⟩,⟨-1697756133668768176364875849349022120116452905126818886547563,-1697756133668768176364875849349022120116452905126818886547510⟩⟩,
  ⟨⟨2036714968166507859120504869475829831497534486598772117327453,2036714968166507859120504869475829831497534486598772117327534⟩,⟨-1663982817129499884902373259375677966909750397548016435725101,-1663982817129499884902373259375677966909750397548016435725031⟩⟩,
  ⟨⟨2379632196935300900143966807600333492252828912864691275637083,2379632196935300900143966807600333492252828912864691275637190⟩,⟨-1555315161395621503362069808889106857681587524748164232442604,-1555315161395621503362069808889106857681587524748164232442527⟩⟩,
  ⟨⟨2738208034284337940790445239206431826227001486185040670515926,2738208034284337940790445239206431826227001486185040670516040⟩,⟨-1342258840335459774897277078042368542268137983424039544370603,-1342258840335459774897277078042368542268137983424039544370534⟩⟩,
  ⟨⟨3068475513042242764016742717786079804032373350955130295563686,3068475513042242764016742717786079804032373350955130295563827⟩,⟨-1002769775504000903273445332609830001317769068939585063909750,-1002769775504000903273445332609830001317769068939585063909684⟩⟩,
  ⟨⟨3307861033012044094737030335155177733322574733706269069974164,3307861033012044094737030335155177733322574733706269069974324⟩,⟨-540500168792817662538730446920780675379505675442200828427179,-540500168792817662538730446920780675379505675442200828427126⟩⟩,
  ⟨⟨3396178054056622144171463414717396797927069125118393388344594,3396178054056622144171463414717396797927069125118393388344762⟩,⟨0,31⟩⟩,
  ⟨⟨3307861033012044094737030335155177733322574733706269069974164,3307861033012044094737030335155177733322574733706269069974324⟩,⟨540500168792817662538730446920780675379505675442200828427147,540500168792817662538730446920780675379505675442200828427199⟩⟩,
  ⟨⟨3068475513042242764016742717786079804032373350955130295563686,3068475513042242764016742717786079804032373350955130295563827⟩,⟨1002769775504000903273445332609830001317769068939585063909703,1002769775504000903273445332609830001317769068939585063909769⟩⟩,
  ⟨⟨2738208034284337940790445239206431826227001486185040670515926,2738208034284337940790445239206431826227001486185040670516040⟩,⟨1342258840335459774897277078042368542268137983424039544370551,1342258840335459774897277078042368542268137983424039544370620⟩⟩,
  ⟨⟨2379632196935300900143966807600333492252828912864691275637083,2379632196935300900143966807600333492252828912864691275637190⟩,⟨1555315161395621503362069808889106857681587524748164232442542,1555315161395621503362069808889106857681587524748164232442619⟩⟩,
  ⟨⟨2036714968166507859120504869475829831497534486598772117327453,2036714968166507859120504869475829831497534486598772117327522⟩,⟨1663982817129499884902373259375677966909750397548016435725044,1663982817129499884902373259375677966909750397548016435725104⟩⟩,
  ⟨⟨1731711256342143539892173366336002562518781963229355264278468,1731711256342143539892173366336002562518781963229355264278521⟩,⟨1697756133668768176364875849349022120116452905126818886547521,1697756133668768176364875849349022120116452905126818886547574⟩⟩,
  ⟨⟨1471316801780572746287703798999140201404204040972285428207427,1471316801780572746287703798999140201404204040972285428207474⟩,⟨1682878694847060330721229835456532910102847759282025816577124,1682878694847060330721229835456532910102847759282025816577176⟩⟩,
  ⟨⟨1253783091791566934865867417482053677595842248732774067210649,1253783091791566934865867417482053677595842248732774067210686⟩,⟨1638932146132767235118780937885037487053388560434998780667520,1638932146132767235118780937885037487053388560434998780667564⟩⟩,
  ⟨⟨1073846233722498686723799701152437280744992316366756771588190,1073846233722498686723799701152437280744992316366756771588219⟩,⟨1579185637827203951064411325224172471683812229951112899394404,1579185637827203951064411325224172471683812229951112899394440⟩⟩,
  ⟨⟨925410982171966473511620285128677340472764915781774561777698,925410982171966473511620285128677340472764915781774561777724⟩,⟨1512109447993409270443823995308296307962034176114010721858989,1512109447993409270443823995308296307962034176114010721859024⟩⟩,
  ⟨⟨802766040626567318021182493639755454113483865641057322008202,802766040626567318021182493639755454113483865641057322008222⟩,⟨1442880138381085048730883566999560456739921980727390611452656,1442880138381085048730883566999560456739921980727390611452686⟩⟩,
  ⟨⟨701012548099458312593443087189901521419594222238944623687366,701012548099458312593443087189901521419594222238944623687382⟩,⟨1374534408038153554104790367039022591018812200468518869975233,1374534408038153554104790367039022591018812200468518869975256⟩⟩,
  ⟨⟨616125455828785186640031209410849401263812337445142139496261,616125455828785186640031209410849401263812337445142139496275⟩,⟨1308763223165720167699412699728928466736856272350792126380952,1308763223165720167699412699728928466736856272350792126380974⟩⟩,
  ⟨⟨544867911283138584822799053349139132217167968733227359708864,544867911283138584822799053349139132217167968733227359708876⟩,⟨1246429862412408527372416135112409779581756791219801149660804,1246429862412408527372416135112409779581756791219801149660824⟩⟩,
  ⟨⟨484662521595592790353888749132006423318792208626848524255706,484662521595592790353888749132006423318792208626848524255718⟩,⟨1187898337244099976357570463558839272840176981928550304548306,1187898337244099976357570463558839272840176981928550304548324⟩⟩]
def lambdaTable1 : Fin 31 → CI :=
  ![⟨⟨632363271491386733866957331929936273877072142606332060184437,632363271491386733866957331929936273877072142606332060184447⟩,⟨-975869246128683231276168722114099188081901454639401327445131,-975869246128683231276168722114099188081901454639401327445118⟩⟩,
  ⟨⟨695495452311889102656312280958738938524202848832969323903008,695495452311889102656312280958738938524202848832969323903020⟩,⟨-1001742421025354674607857194796537565775600811076293264880890,-1001742421025354674607857194796537565775600811076293264880875⟩⟩,
  ⟨⟨766766483305021768452523399539563595650378948727648249178784,766766483305021768452523399539563595650378948727648249178798⟩,⟨-1025510728700131994843909896503531557968613820314755888819378,-1025510728700131994843909896503531557968613820314755888819361⟩⟩,
  ⟨⟨847147608315192686285388283690451432415719011887209895975599,847147608315192686285388283690451432415719011887209895975615⟩,⟨-1045861244833571217636281831716606706686072854181740612315570,-1045861244833571217636281831716606706686072854181740612315553⟩⟩,
  ⟨⟨937571497629617852726961687451015753227278487330715266385992,937571497629617852726961687451015753227278487330715266386007⟩,⟨-1061037703078785635802117136004235934722228740806365013399800,-1061037703078785635802117136004235934722228740806365013399783⟩⟩,
  ⟨⟨1038811539969651372682217363333125698690491102376627926064938,1038811539969651372682217363333125698690491102376627926064958⟩,⟨-1068736152232151617985820332647248661204208953062374409531847,-1068736152232151617985820332647248661204208953062374409531826⟩⟩,
  ⟨⟨1151289310791720505298893432315572474334213241085186532681100,1151289310791720505298893432315572474334213241085186532681124⟩,⟨-1066008621103444912313790215107011550309456704708506048778814,-1066008621103444912313790215107011550309456704708506048778792⟩⟩,
  ⟨⟨1274788275215006256480639262342659648761022352601003016539963,1274788275215006256480639262342659648761022352601003016539987⟩,⟨-1049208456967083338667192808512477077169565722305352276987641,-1049208456967083338667192808512477077169565722305352276987619⟩⟩,
  ⟨⟨1408061465661966174121270806429713133685689307968605702715022,1408061465661966174121270806429713133685689307968605702715051⟩,⟨-1014036034941745187124371979939093820555537567467102872325651,-1014036034941745187124371979939093820555537567467102872325627⟩⟩,
  ⟨⟨1548351345470467506629766622469657451962997743721894171421681,1548351345470467506629766622469657451962997743721894171421714⟩,⟨-955772435475597226314670754610899661705554162791292698408464,-955772435475597226314670754610899661705554162791292698408439⟩⟩,
  ⟨⟨1690903177434865611834786382084501908966045785718948332555732,1690903177434865611834786382084501908966045785718948332555771⟩,⟨-869806161231926755059046492841821969632739601707277948845559,-869806161231926755059046492841821969632739601707277948845533⟩⟩,
  ⟨⟨1828650724438748637897012821268636700750633651505115900089306,1828650724438748637897012821268636700750633651505115900089350⟩,⟨-752531162320472690492597868834829918004375988273710246950350,-752531162320472690492597868834829918004375988273710246950325⟩⟩,
  ⟨⟨1952353401239619548785459973030554713642739014175352503096556,1952353401239619548785459973030554713642739014175352503096598⟩,⟨-602578210259141836044895053404492195568746609313380402190307,-602578210259141836044895053404492195568746609313380402190286⟩⟩,
  ⟨⟨2051479372073813623261967510370243148550431412415745955015790,2051479372073813623261967510370243148550431412415745955015835⟩,⟨-422115097134529552111515948635852499701734858521758426957993,-422115097134529552111515948635852499701734858521758426957973⟩⟩,
  ⟨⟨2115938329452879892384469589700340107083998106424519016410272,2115938329452879892384469589700340107083998106424519016410320⟩,⟨-217689128544534968352311686183162562457201451278242697161557,-217689128544534968352311686183162562457201451278242697161540⟩⟩,
  ⟨⟨2138334330331947275959810298155397983880006486185655096365160,2138334330331947275959810298155397983880006486185655096365208⟩,⟨0,13⟩⟩,
  ⟨⟨2115938329452879892384469589700340107083998106424519016410272,2115938329452879892384469589700340107083998106424519016410320⟩,⟨217689128544534968352311686183162562457201451278242697161548,217689128544534968352311686183162562457201451278242697161566⟩⟩,
  ⟨⟨2051479372073813623261967510370243148550431412415745955015790,2051479372073813623261967510370243148550431412415745955015835⟩,⟨422115097134529552111515948635852499701734858521758426957982,422115097134529552111515948635852499701734858521758426958002⟩⟩,
  ⟨⟨1952353401239619548785459973030554713642739014175352503096549,1952353401239619548785459973030554713642739014175352503096598⟩,⟨602578210259141836044895053404492195568746609313380402190291,602578210259141836044895053404492195568746609313380402190315⟩⟩,
  ⟨⟨1828650724438748637897012821268636700750633651505115900089306,1828650724438748637897012821268636700750633651505115900089350⟩,⟨752531162320472690492597868834829918004375988273710246950333,752531162320472690492597868834829918004375988273710246950358⟩⟩,
  ⟨⟨1690903177434865611834786382084501908966045785718948332555732,1690903177434865611834786382084501908966045785718948332555766⟩,⟨869806161231926755059046492841821969632739601707277948845541,869806161231926755059046492841821969632739601707277948845563⟩⟩,
  ⟨⟨1548351345470467506629766622469657451962997743721894171421681,1548351345470467506629766622469657451962997743721894171421714⟩,⟨955772435475597226314670754610899661705554162791292698408446,955772435475597226314670754610899661705554162791292698408471⟩⟩,
  ⟨⟨1408061465661966174121270806429713133685689307968605702715022,1408061465661966174121270806429713133685689307968605702715051⟩,⟨1014036034941745187124371979939093820555537567467102872325633,1014036034941745187124371979939093820555537567467102872325657⟩⟩,
  ⟨⟨1274788275215006256480639262342659648761022352601003016539963,1274788275215006256480639262342659648761022352601003016539987⟩,⟨1049208456967083338667192808512477077169565722305352276987625,1049208456967083338667192808512477077169565722305352276987647⟩⟩,
  ⟨⟨1151289310791720505298893432315572474334213241085186532681098,1151289310791720505298893432315572474334213241085186532681119⟩,⟨1066008621103444912313790215107011550309456704708506048778797,1066008621103444912313790215107011550309456704708506048778817⟩⟩,
  ⟨⟨1038811539969651372682217363333125698690491102376627926064936,1038811539969651372682217363333125698690491102376627926064956⟩,⟨1068736152232151617985820332647248661204208953062374409531829,1068736152232151617985820332647248661204208953062374409531850⟩⟩,
  ⟨⟨937571497629617852726961687451015753227278487330715266385990,937571497629617852726961687451015753227278487330715266386007⟩,⟨1061037703078785635802117136004235934722228740806365013399786,1061037703078785635802117136004235934722228740806365013399805⟩⟩,
  ⟨⟨847147608315192686285388283690451432415719011887209895975599,847147608315192686285388283690451432415719011887209895975615⟩,⟨1045861244833571217636281831716606706686072854181740612315557,1045861244833571217636281831716606706686072854181740612315574⟩⟩,
  ⟨⟨766766483305021768452523399539563595650378948727648249178784,766766483305021768452523399539563595650378948727648249178797⟩,⟨1025510728700131994843909896503531557968613820314755888819364,1025510728700131994843909896503531557968613820314755888819380⟩⟩,
  ⟨⟨695495452311889102656312280958738938524202848832969323903008,695495452311889102656312280958738938524202848832969323903019⟩,⟨1001742421025354674607857194796537565775600811076293264880878,1001742421025354674607857194796537565775600811076293264880892⟩⟩,
  ⟨⟨632363271491386733866957331929936273877072142606332060184436,632363271491386733866957331929936273877072142606332060184447⟩,⟨975869246128683231276168722114099188081901454639401327445121,975869246128683231276168722114099188081901454639401327445135⟩⟩]
def lambdaTable : Fin 2 → Fin 31 → CI := ![lambdaTable0,lambdaTable1]

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def columnTable : Fin 23 → Fin 31 → CI := ![cBox0,dBox0,cBox1,dBox1,cBox3,dBox3,cBox4,dBox4,cBox7,dBox7,cBox9,dBox9,cBox12,dBox12,cBox13,dBox13,cBox16,dBox16,cBox19,dBox19,cBox21,dBox21,coeffBox15]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def jetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t))*
    Real.sqrt (Xwave k t)/Q n*Real.exp (-Real.pi*(k*Xwave k t-v)*n)

def frequencyDecay (k v t : ℝ) : ℝ := Real.pi*(k*Xwave k t-v)

end AtomicTriangular.Construction
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
namespace AtomicTriangular.Construction
open Complex

def frequencyDistance (l : Fin 31) : ℕ := Int.natAbs ((l.val:ℤ)-15)
def fullTailW (i : Fin 15) (d : Fin 2) : ℝ :=
  if d.val=0 then Real.pi^2/18^2 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then
      ((frequencyDistance l:ℝ)-i.val-1/2)*‖fourierCoeff l‖ else 0
  else Real.pi/18 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then ‖fourierCoeff l‖ else 0

def normJetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+‖I*Real.pi*zeta k v t‖)*‖lambda k t‖*(Q n)⁻¹ *
    Real.exp (-frequencyDecay k v t*n)
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

def fullTailWBox (pn : Fin 31 → RI) (i : Fin 15) (d : Fin 2) : RI :=
  if d.val=0 then ((piBox.pow 2).divNat (18^2)).mul (RI.sum (fun l : Fin 31 =>
    if i.val < frequencyDistance l then
      (((RI.point ((frequencyDistance l:ℤ)-i.val)).sub ((RI.point 1).divNat 2)).mul (pn l)) else RI.point 0))
  else (piBox.divNat 18).mul (RI.sum (fun l : Fin 31 =>
    if i.val < frequencyDistance l then pn l else RI.point 0))

def decayBox (q v : Fin 2) (j : Fin 31) : RI := (wavePhaseBox q v j).re.neg

def decayExpBox (q v : Fin 2) (n : ℤ) (j : Fin 31) : RI :=
  (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).exp.re

def psiBox (_q _v : Fin 2) (_n : ℤ) (_j : Fin 31) (qb db lell dnorm ex : RI) : RI :=
  ((((RI.point 1).add db.abs).add dnorm).mul lell).mul qb.invPos |>.mul ex
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma norm_exp_phase (t : ℝ) (n : ℤ) : ‖exp (I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

lemma norm_exp_neg_phase (t : ℝ) (n : ℤ) : ‖exp (-I*Real.pi*(t:ℂ)*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_SpectralEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def spectralCVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    (-(Real.pi:ℂ)^2 • ∫ t in (0:ℝ)..frequency l,
      (frequency l-t) • (exp (-I*Real.pi*(t:ℂ)*n) • f t))
def spectralDVector (n : ℤ) (f : ℝ → E) : E :=
  ∑ l : Fin 31, (fourierCoeff l * exp (I*Real.pi*frequency l*n)) •
    ((I*Real.pi) • ∫ t in (0:ℝ)..frequency l,
      exp (-I*Real.pi*(t:ℂ)*n) • f t)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailJetVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev JetVector := PiLp 1 (fun _ : Fin 2 => ℂ)
def jetVector (k v : ℝ) (n : ℤ) (t : ℝ) : JetVector :=
  WithLp.toLp 1 (fun d => jetMultiplier k v n d t)
lemma continuous_jetMultiplier {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (d : Fin 2) :
    Continuous (jetMultiplier k v n d) := by
  have hl : Continuous (lambda k) := by
    unfold lambda
    apply Continuous.div
    · fun_prop
    · unfold waveDen; fun_prop
    · intro t; exact_mod_cast (mul_pos b_pos (waveDen_pos hk t)).ne'
  have hX : Continuous (Xwave k) := by
    unfold Xwave
    exact continuous_const.div (by unfold waveDen; fun_prop) (fun t => (waveDen_pos hk t).ne')
  have hz : Continuous (zeta k v) := by unfold zeta; fun_prop
  unfold jetMultiplier transformedWave
  split_ifs <;> fun_prop

def tailJetVector (k v : ℝ) (m n : ℤ) (c : Fin 2) : JetVector :=
  if c.val=0 then spectralCVector n (jetVector k v m) else spectralDVector n (jetVector k v m)
def tailJet (k v : ℝ) (m n : ℤ) (c d : Fin 2) : ℝ :=
  (tailJetVector k v m n c d).re
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_PeriodicJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma P_periodic : Function.Periodic P 36 := by
  intro s
  unfold P
  apply Finset.prod_congr rfl
  intro a _
  unfold sineFactor
  have hh : (kappa:ℂ)*(s+36-(residue a:ℂ)) = (kappa:ℂ)*(s-(residue a:ℂ))+(Real.pi:ℂ) := by
    unfold kappa
    push_cast
    ring
  rw [hh,Complex.sin_add_pi]
  ring
lemma waveDerivative_periodic (k : ℕ) : Function.Periodic (waveDerivative k) 36 := by
  have he : (fun s : ℂ => P (s+36)) = P := funext P_periodic
  have hh := iteratedDeriv_comp_add_const k P 36
  rw [he] at hh
  rw [waveDerivative_eq_iterated]
  intro s
  exact (congrFun hh s).symm
lemma waveDerivative_emod (k : ℕ) (n : ℤ) : waveDerivative k n = waveDerivative k ((n%36:ℤ):ℂ) := by
  have hh := (waveDerivative_periodic k).int_mul (n/36) ((n%36:ℤ):ℂ)
  have hn : (((n%36:ℤ):ℂ)+(n/36:ℤ)*36) = (n:ℂ) := by
    exact_mod_cast (by simpa [mul_comm] using Int.emod_add_mul_ediv n 36)
  rw [hn] at hh
  exact hh
lemma Q_emod (n : ℤ) : Q n = Q (n%36) := by simp only [Q,waveDerivative_emod 2 n]
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def columnNorm22 : Fin 31 → RI := ![⟨999999999999999999999999999999999999999999999999642331844289,1000000000000000000000000000000000000000000000000357668187168⟩,⟨1999999999999999999999999999999999999999999999991359427596864,2000000000000000000000000000000000000000000000008640669480563⟩,⟨999999999999999999999999999999999999999999999914749418893163,1000000000000000000000000000000000000000000000085239856765338⟩,⟨1999999999999999999999999999999999999999999999417509412670172,2000000000000000000000000000000000000000000000582492882524173⟩,⟨3464101615137754587054892683011744733885610504603359924369746,3464101615137754587054892683011744733885610510638192400956246⟩,⟨3464101615137754587054892683011744733885610498496628994962482,3464101615137754587054892683011744733885610516744944595527730⟩,⟨1732050807568877293527446341505872366942805211400557929894805,1732050807568877293527446341505872366942805296220253398619502⟩,⟨3464101615137754587054892683011744733885610418590275204646280,3464101615137754587054892683011744733885610596651299102579323⟩,⟨6244997998398398205846893120939794461072959707131949918511179,6244997998398398205846893120939794461072960248851440868612609⟩,⟨3999999999999999999999999999999999999999999362928123213716836,4000000000000000000000000000000000000000000637071939906768380⟩,⟨2645751311064590590501615753639260425710258075122571507953073,2645751311064590590501615753639260425710260291042390874813847⟩,⟨7211102550927978586238442534940991892502591117614493411337669,7211102550927978586238442534940991892502595177766602589220360⟩,⟨7211102550927978586238442534940991892502590543480579824190872,7211102550927978586238442534940991892502595751900542098193568⟩,⟨3464101615137754587054892683011744733885606747829845107873690,3464101615137754587054892683011744733885614267411830811703549⟩,⟨6244997998398398205846893120939794461072956067393381610442172,6244997998398398205846893120939794461072963888590039804580656⟩,⟨11999999999999999999999999999999999999999996594619670830608815,12000000000000000000000000000000000000000003405380459998996234⟩,⟨6244997998398398205846893120939794461072956067393379957766038,6244997998398398205846893120939794461072963888590041457345321⟩,⟨3464101615137754587054892683011744733885606747829841564093519,3464101615137754587054892683011744733885614267411834355530863⟩,⟨7211102550927978586238442534940991892502590543480575378413509,7211102550927978586238442534940991892502595751900546544059555⟩,⟨7211102550927978586238442534940991892502591117614487308261036,7211102550927978586238442534940991892502595177766608692359100⟩,⟨2645751311064590590501615753639260425710258075122565414629558,2645751311064590590501615753639260425710260291042396968100579⟩,⟨3999999999999999999999999999999999999999999362928116295429364,4000000000000000000000000000000000000000000637071946825119994⟩,⟨6244997998398398205846893120939794461072959707131943472246193,6244997998398398205846893120939794461072960248851447314843391⟩,⟨3464101615137754587054892683011744733885610418590269933644683,3464101615137754587054892683011744733885610596651304373515720⟩,⟨1732050807568877293527446341505872366942805211400550694668349,1732050807568877293527446341505872366942805296220260633810949⟩,⟨3464101615137754587054892683011744733885610498496623689643226,3464101615137754587054892683011744733885610516744949900782248⟩,⟨3464101615137754587054892683011744733885610504603352673726512,3464101615137754587054892683011744733885610510638199651565353⟩,⟨1999999999999999999999999999999999999999999999417502161236240,2000000000000000000000000000000000000000000000582500134016655⟩,⟨999999999999999999999999999999999999999999999914742167237916,1000000000000000000000000000000000000000000000085247108361504⟩,⟨1999999999999999999999999999999999999999999999991352175976525,2000000000000000000000000000000000000000000000008647921159874⟩,⟨999999999999999999999999999999999999999999999999637023266357,1000000000000000000000000000000000000000000000000362976765099⟩]
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
def fullWTable : Fin 15 → Fin 2 → RI := ![![⟨19073245724430726486023070892582989751120842549446228250198161,19073245724430726486023070892582989751120846523551196112944043⟩,⟨19249728390638505454504582078632221599256705750745315988124752,19249728390638505454504582078632221599256715849098698735746681⟩],![⟨15903767836802543226044380036212972789116925085277065157363521,15903767836802543226044380036212972789116927535134142565045892⟩,⟨17069812853588353102935126726852967505882490255852642380353737,17069812853588353102935126726852967505882497624093354982875564⟩],![⟨13030046036447111214550331117134458650984917833534636618104132,13030046036447111214550331117134458650984919226450666414184074⟩,⟨15860613277432207869205741221758197017693114069538764989523611,15860613277432207869205741221758197017693118812950192022322604⟩],![⟨10481509550968005797138021195410941791824314443843300236630317,10481509550968005797138021195410941791824315167535395978000575⟩,⟨13343463633179101715309512416153494468304966743868152208171531,13343463633179101715309512416153494468304969669198026311145946⟩],![⟨8372298556065107035608411825787254709301263035711786858687579,8372298556065107035608411825787254709301263372516802614802089⟩,⟨10826313988925995561413283610548791918916819217786996926946345,10826313988925995561413283610548791918916820725856412148271401⟩],![⟨6563344500227691305631924989067266258136580134496081994405971,6563344500227691305631924989067266258136580275594103775192955⟩,⟨9902772557585319823469686156588176228922781515298484702403490,9902772557585319823469686156588176228922782249865958694045525⟩],![⟨4956831606082338719005907828952618971435115639873305892143720,4956831606082338719005907828952618971435115691577753353539288⟩,⟨8506509155989856161930733541797286058168484226845144567700122,8506509155989856161930733541797286058168484516652516795531848⟩],![⟨3662399197536197554462841304575949539376559487735892502167196,3662399197536197554462841304575949539376559505361127584006986⟩,⟨6326593618939703810361278190018031964794267461444033220561366,6326593618939703810361278190018031964794267562155621473203518⟩],![⟨2663722876262807638404416717490782931189913770715747791188343,2663722876262807638404416717490782931189913776187541057816623⟩,⟨5117394042783558576631892684923261476604889993793044988951523,5117394042783558576631892684923261476604890032349604822851818⟩],![⟨1823330409371752621556575212363239908982210041509983689920908,1823330409371752621556575212363239908982210042836141174478472⟩,⟨4512794254705485959767199932375876232510201259232621338859313,4512794254705485959767199932375876232510201268181517593331124⟩],![⟨1141221796863032503919316789193320472753448302552686929459205,1141221796863032503919316789193320472753448302872841181065220⟩,⟨3303594678549340726037814427281105744320823763689053775149664,3303594678549340726037814427281105744320823766268080525266998⟩],![⟨670158323530758918562835808633565817829942552316579808787400,670158323530758918562835808633565817829942552370439544627993⟩,⟨2094395102393195492308428922186335256131446266013835325932495,2094395102393195492308428922186335256131446266486301765647680⟩],![⟨365540903744050319216092259254672264270877755820289807653388,365540903744050319216092259254672264270877755827175464770344⟩,⟨1396263401595463661538952614790890170754297510800475274873204,1396263401595463661538952614790890170754297510866281015522786⟩],![⟨152308709893354299673371774689446776779532398259591934333511,152308709893354299673371774689446776779532398260185397889004⟩,⟨1047197551196597746154214461093167628065723133121890162672419,1047197551196597746154214461093167628065723133128179871235269⟩],![⟨30461741978670859934674354937889355355906479651966659914084,30461741978670859934674354937889355355906479651988805939194⟩,⟨349065850398865915384738153697722542688574377708218668183875,349065850398865915384738153697722542688574377708471331827106⟩]]
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
def lambdaNorm0 : Fin 31 → RI := ![⟨1282965400728599511865999375488755701076065293567047386831048,1282965400728599511865999375488755701076065293567047386831069⟩,⟨1360319242920376331262611458027229948880866815779688666193907,1360319242920376331262611458027229948880866815779688666193932⟩,⟨1446537850051409120311705353011916165964611209200332016103362,1446537850051409120311705353011916165964611209200332016103391⟩,⟨1542972271777329303825828393833962971882592387610435544860345,1542972271777329303825828393833962971882592387610435544860379⟩,⟨1651162139136515772024631703194756862068460037694587721887345,1651162139136515772024631703194756862068460037694587721887378⟩,⟨1772811458851565677518643854752765858245957394634107123702825,1772811458851565677518643854752765858245957394634107123702869⟩,⟨1909704954279510749512587210958122436637386311452010522605726,1909704954279510749512587210958122436637386311452010522605781⟩,⟨2063509297505048571194200330483423691323470769502469155777055,2063509297505048571194200330483423691323470769502469155777113⟩,⟨2235364362418788852550773008744886685884462934188820320098040,2235364362418788852550773008744886685884462934188820320098112⟩,⟨2425118505300722290853409183605840623171423165210710387729416,2425118505300722290853409183605840623171423165210710387729492⟩,⟨2630027885262003410746848054634805264999665906883705775570270,2630027885262003410746848054634805264999665906883705775570379⟩,⟨2842825116667962544453462324798388729691436651496786619395853,2842825116667962544453462324798388729691436651496786619395986⟩,⟨3049498652808030233532934169595343599155257179109214835559555,3049498652808030233532934169595343599155257179109214835559689⟩,⟨3228171184557008481225230324691265650167650536014600585745627,3228171184557008481225230324691265650167650536014600585745783⟩,⟨3351728665358306096864226616764876644012340701676673346752577,3351728665358306096864226616764876644012340701676673346752744⟩,⟨3396178054056622144171463414717396797927069125118393388344593,3396178054056622144171463414717396797927069125118393388344763⟩,⟨3351728665358306096864226616764876644012340701676673346752580,3351728665358306096864226616764876644012340701676673346752747⟩,⟨3228171184557008481225230324691265650167650536014600585745633,3228171184557008481225230324691265650167650536014600585745788⟩,⟨3049498652808030233532934169595343599155257179109214835559563,3049498652808030233532934169595343599155257179109214835559697⟩,⟨2842825116667962544453462324798388729691436651496786619395861,2842825116667962544453462324798388729691436651496786619395994⟩,⟨2630027885262003410746848054634805264999665906883705775570279,2630027885262003410746848054634805264999665906883705775570371⟩,⟨2425118505300722290853409183605840623171423165210710387729423,2425118505300722290853409183605840623171423165210710387729500⟩,⟨2235364362418788852550773008744886685884462934188820320098047,2235364362418788852550773008744886685884462934188820320098118⟩,⟨2063509297505048571194200330483423691323470769502469155777061,2063509297505048571194200330483423691323470769502469155777120⟩,⟨1909704954279510749512587210958122436637386311452010522605730,1909704954279510749512587210958122436637386311452010522605778⟩,⟨1772811458851565677518643854752765858245957394634107123702825,1772811458851565677518643854752765858245957394634107123702870⟩,⟨1651162139136515772024631703194756862068460037694587721887346,1651162139136515772024631703194756862068460037694587721887384⟩,⟨1542972271777329303825828393833962971882592387610435544860350,1542972271777329303825828393833962971882592387610435544860379⟩,⟨1446537850051409120311705353011916165964611209200332016103365,1446537850051409120311705353011916165964611209200332016103393⟩,⟨1360319242920376331262611458027229948880866815779688666193908,1360319242920376331262611458027229948880866815779688666193933⟩,⟨1282965400728599511865999375488755701076065293567047386831049,1282965400728599511865999375488755701076065293567047386831072⟩]
def envelopePhase01 : Fin 31 → CI := ![⟨⟨-61701114137989816067161627646150052256513703401751035641411,-61701114137989816067161627646150052256513703401750839240628⟩,⟨4309218497736466090286737878963435317948493085941923625589786,4309218497736466090286737878963435317948493085941937342258338⟩⟩,
  ⟨⟨-280102109215477611457921804296902262032669433141113423472188,-280102109215477611457921804296902262032669433141112531879444⟩,⟨4521547384012340431893543993096351874671237373080282916064091,4521547384012340431893543993096351874671237373080297308596482⟩⟩,
  ⟨⟨-538595887203048139991821925797008402306147763163138462578881,-538595887203048139991821925797008402306147763163136748174876⟩,⟨4747667804222218031683242089212944358994125834106859432397622,4747667804222218031683242089212944358994125834106874544693681⟩⟩,
  ⟨⟨-846532195187524747993839147860504790348077200920737322482375,-846532195187524747993839147860504790348077200920734627886655⟩,⟨4986259270835319797575816813394973231008918973692722799777758,4986259270835319797575816813394973231008918973692738671534043⟩⟩,
  ⟨⟨-1215653035296087850221131865646334884051594550779219160898305,-1215653035296087850221131865646334884051594550779215291354456⟩,⟨5234190155323584671388979120717308963512863773016251994264551,5234190155323584671388979120717308963512863773016268655209353⟩⟩,
  ⟨⟨-1660559669299263450120517735760078753086557320652554243506541,-1660559669299263450120517735760078753086557320652548957780876⟩,⟨5485326310845999671389452880279428612014752935155396989838030,5485326310845999671389452880279428612014752935155414450174067⟩⟩,
  ⟨⟨-2199023199083866505633158533331880188073417640995126230926379,-2199023199083866505633158533331880188073417640995119231218049⟩,⟨5728651811797580668239685235739429037558660465673048869438298,5728651811797580668239685235739429037558660465673067104303473⟩⟩,
  ⟨⟨-2851761916619823867017689527799816518820808734759227696468997,-2851761916619823867017689527799816518820808734759218619028789⟩,⟨5945388169357270870310479679438886374231738837152643946442860,5945388169357270870310479679438886374231738837152662871201288⟩⟩,
  ⟨⟨-3640886926374962798486912081210183384409017121565761620098520,-3640886926374962798486912081210183384409017121565750030795365⟩,⟨6104808613593816671698885058377092253779153624280739904504491,6104808613593816671698885058377092253779153624280759336713976⟩⟩,
  ⟨⟨-4585493518642748865956493394328995793800167982017527249676601,-4585493518642748865956493394328995793800167982017512653597245⟩,⟨6158777991746310994829726295392085638496705350666732013330626,6158777991746310994829726295392085638496705350666751617329992⟩⟩,
  ⟨⟨-5691924595834966057411211221004125182024745178091478054526921,-5691924595834966057411211221004125182024745178091459936568015⟩,⟨6036261951612299351455096934620144395009163932805566941640516,6036261951612299351455096934620144395009163932805586155659237⟩⟩,
  ⟨⟨-6935890698886559371630982611792825656736292775366657218276596,-6935890698886559371630982611792825656736292775366635140650539⟩,⟨5642059301846436418562620940368468767452787092175940614804266,5642059301846436418562620940368468767452787092175958574036995⟩⟩,
  ⟨⟨-8236659950513430756102758595797490457044107530421173396032343,-8236659950513430756102758595797490457044107530421147177929158⟩,⟨4869176462476430933761071579788442163975774022590049597024074,4869176462476430933761071579788442163975774022590065096094284⟩⟩,
  ⟨⟨-9434737836510082390775143918316743179856472322347209329013198,-9434737836510082390775143918316743179856472322347179297309601⟩,⟨3637646362564892398544108282773749914157824770591416110231887,3637646362564892398544108282773749914157824770591427689220023⟩⟩,
  ⟨⟨-10303132444366289020410111933312765071030663868542945218457287,-10303132444366289020410111933312765071030663868542912422567756⟩,⟨1960717725049800223722212313771845854329597278464945493883594,1960717725049800223722212313771845854329597278464951735042057⟩⟩,
  ⟨⟨-10623511157609720429515048585889864066836153619926107266666728,-10623511157609720429515048585889864066836153619926073450980061⟩,⟨-45,8⟩⟩,
  ⟨⟨-10303132444366289020410111933312765071030663868542945218457287,-10303132444366289020410111933312765071030663868542912422567756⟩,⟨-1960717725049800223722212313771845854329597278464951735042057,-1960717725049800223722212313771845854329597278464945493883594⟩⟩,
  ⟨⟨-9434737836510082390775143918316743179856472322347209329013198,-9434737836510082390775143918316743179856472322347179297309601⟩,⟨-3637646362564892398544108282773749914157824770591427689220023,-3637646362564892398544108282773749914157824770591416110231887⟩⟩,
  ⟨⟨-8236659950513430756102758595797490457044107530421173396032343,-8236659950513430756102758595797490457044107530421147177929089⟩,⟨-4869176462476430933761071579788442163975774022590065096094284,-4869176462476430933761071579788442163975774022590049597024039⟩⟩,
  ⟨⟨-6935890698886559371630982611792825656736292775366657218276596,-6935890698886559371630982611792825656736292775366635140650539⟩,⟨-5642059301846436418562620940368468767452787092175958574036995,-5642059301846436418562620940368468767452787092175940614804266⟩⟩,
  ⟨⟨-5691924595834966057411211221004125182024745178091478054526883,-5691924595834966057411211221004125182024745178091459936568015⟩,⟨-6036261951612299351455096934620144395009163932805586155659205,-6036261951612299351455096934620144395009163932805566941640516⟩⟩,
  ⟨⟨-4585493518642748865956493394328995793800167982017527249676601,-4585493518642748865956493394328995793800167982017512653597245⟩,⟨-6158777991746310994829726295392085638496705350666751617329992,-6158777991746310994829726295392085638496705350666732013330626⟩⟩,
  ⟨⟨-3640886926374962798486912081210183384409017121565761620098520,-3640886926374962798486912081210183384409017121565750030795347⟩,⟨-6104808613593816671698885058377092253779153624280759336713976,-6104808613593816671698885058377092253779153624280739904504469⟩⟩,
  ⟨⟨-2851761916619823867017689527799816518820808734759227696468997,-2851761916619823867017689527799816518820808734759218619028789⟩,⟨-5945388169357270870310479679438886374231738837152662871201288,-5945388169357270870310479679438886374231738837152643946442860⟩⟩,
  ⟨⟨-2199023199083866505633158533331880188073417640995126230926357,-2199023199083866505633158533331880188073417640995119231218036⟩,⟨-5728651811797580668239685235739429037558660465673067104303454,-5728651811797580668239685235739429037558660465673048869438295⟩⟩,
  ⟨⟨-1660559669299263450120517735760078753086557320652554243506532,-1660559669299263450120517735760078753086557320652548957780867⟩,⟨-5485326310845999671389452880279428612014752935155414450174052,-5485326310845999671389452880279428612014752935155396989838017⟩⟩,
  ⟨⟨-1215653035296087850221131865646334884051594550779219160898305,-1215653035296087850221131865646334884051594550779215291354450⟩,⟨-5234190155323584671388979120717308963512863773016268655209353,-5234190155323584671388979120717308963512863773016251994264539⟩⟩,
  ⟨⟨-846532195187524747993839147860504790348077200920737322482369,-846532195187524747993839147860504790348077200920734627886649⟩,⟨-4986259270835319797575816813394973231008918973692738671534034,-4986259270835319797575816813394973231008918973692722799777749⟩⟩,
  ⟨⟨-538595887203048139991821925797008402306147763163138462578878,-538595887203048139991821925797008402306147763163136748174876⟩,⟨-4747667804222218031683242089212944358994125834106874544693672,-4747667804222218031683242089212944358994125834106859432397622⟩⟩,
  ⟨⟨-280102109215477611457921804296902262032669433141113423472185,-280102109215477611457921804296902262032669433141112531879440⟩,⟨-4521547384012340431893543993096351874671237373080297308596476,-4521547384012340431893543993096351874671237373080282916064085⟩⟩,
  ⟨⟨-61701114137989816067161627646150052256513703401751035641411,-61701114137989816067161627646150052256513703401750839240625⟩,⟨-4309218497736466090286737878963435317948493085941937342258338,-4309218497736466090286737878963435317948493085941923625589780⟩⟩]
def phaseNorm01 : Fin 31 → RI := ![⟨4309660205714598429477404277420998732962715372212178110772362,4309660205714598429477404277420998732962715372212191828846916⟩,⟨4530214999032142900284478381606384253712079367956827102731829,4530214999032142900284478381606384253712079367956841522854099⟩,⟨4778120457770006425834698383919577390838847222261187900254515,4778120457770006425834698383919577390838847222261203109484387⟩,⟨5057607959646554550941703895701703627763239715899998758483825,5057607959646554550941703895701703627763239715900014857350049⟩,⟨5373505269776044691608194626371341129847101941870707694733703,5373505269776044691608194626371341129847101941870724799132299⟩,⟨5731165950464413467593734949508440972014316684099196400174063,5731165950464413467593734949508440972014316684099214643041995⟩,⟨6136216636570187617508240480447207818462927641384645064745235,6136216636570187617508240480447207818462927641384664596929565⟩,⟨6593950751515859769147980270724695455120045646089208452475016,6593950751515859769147980270724695455120045646089229441672293⟩,⟨7108076098302365657562859254570225401679313987539884101007931,7108076098302365657562859254570225401679313987539906726717050⟩,⟨7678365526668640003568579499529822454833762365105567814526348,7678365526668640003568579499529822454833762365105592255523132⟩,⟨8296653780480017514892644379834106459477553465517506549735109,8296653780480017514892644379834106459477553465517532958804581⟩,⟨8940884349573759168480554426934021973185211341813996392978550,8940884349573759168480554426934021973185211341814024852697674⟩,⟨9568252011894670075143465218981282025405518237963752047549946,9568252011894670075143465218981282025405518237963782504242348⟩,⟨10111713460277468857435381336061605736687385991045863487844992,10111713460277468857435381336061605736687385991045895674428956⟩,⟨10488038527936371273024733224220062509630851563556440436927588,10488038527936371273024733224220062509630851563556473821391477⟩,⟨10623511157609720429515048585889864066836153619926073450980060,10623511157609720429515048585889864066836153619926107266666729⟩,⟨10488038527936371273024733224220062509630851563556440436927588,10488038527936371273024733224220062509630851563556473821391477⟩,⟨10111713460277468857435381336061605736687385991045863487844992,10111713460277468857435381336061605736687385991045895674428956⟩,⟨9568252011894670075143465218981282025405518237963752047549869,9568252011894670075143465218981282025405518237963782504242348⟩,⟨8940884349573759168480554426934021973185211341813996392978550,8940884349573759168480554426934021973185211341814024852697674⟩,⟨8296653780480017514892644379834106459477553465517506549735109,8296653780480017514892644379834106459477553465517532958804532⟩,⟨7678365526668640003568579499529822454833762365105567814526348,7678365526668640003568579499529822454833762365105592255523132⟩,⟨7108076098302365657562859254570225401679313987539884101007903,7108076098302365657562859254570225401679313987539906726717050⟩,⟨6593950751515859769147980270724695455120045646089208452475016,6593950751515859769147980270724695455120045646089229441672293⟩,⟨6136216636570187617508240480447207818462927641384645064745227,6136216636570187617508240480447207818462927641384664596929539⟩,⟨5731165950464413467593734949508440972014316684099196400174048,5731165950464413467593734949508440972014316684099214643041978⟩,⟨5373505269776044691608194626371341129847101941870707694733690,5373505269776044691608194626371341129847101941870724799132299⟩,⟨5057607959646554550941703895701703627763239715899998758483815,5057607959646554550941703895701703627763239715900014857350039⟩,⟨4778120457770006425834698383919577390838847222261187900254515,4778120457770006425834698383919577390838847222261203109484378⟩,⟨4530214999032142900284478381606384253712079367956827102731823,4530214999032142900284478381606384253712079367956841522854093⟩,⟨4309660205714598429477404277420998732962715372212178110772356,4309660205714598429477404277420998732962715372212191828846916⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopePsiB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
def envelopeExpB1 : Fin 31 → RI := ![⟨940163846483244417184606941581156992434378851333648275035807,940163846483244417184606941581156992434378851333648459828303⟩,⟨755706572910691539042303978749141248586157450777118634329767,755706572910691539042303978749141248586157450777119308571949⟩,⟨583567071375140899468048309010397782300196182671066899754901,583567071375140899468048309010397782300196182671067901350439⟩,⟨428899696455472795772624439880400222978969539349961726480100,428899696455472795772624439880400222978969539349962884156689⟩,⟨296516315434988089698047993174226897816590897560819476718773,296516315434988089698047993174226897816590897560820626866039⟩,⟨190032594924800012499975114596888048884308303178972961078394,190032594924800012499975114596888048884308303178973968824609⟩,⟨110911443867012821826721645882868547192098665145370022020939,110911443867012821826721645882868547192098665145370801723844⟩,⟨57742493736332758162040340679040057196236536824055952521931,57742493736332758162040340679040057196236536824056479610779⟩,⟨26229070391919064380411003155127795161953680043563575398645,26229070391919064380411003155127795161953680043563881547764⟩,⟨10198715289414200153834874804820132571970125212723056784719,10198715289414200153834874804820132571970125212723206986387⟩,⟨3373094873933466286741118593271994588029282509691612000491,3373094873933466286741118593271994588029282509691673797687⟩,⟨972256694977247423736489801601331497560640132656720761197,972256694977247423736489801601331497560640132656742519195⟩,⟨264767109483956331932502799847836939305318136829281421627,264767109483956331932502799847836939305318136829288475928⟩,⟨79899749808080537588923567653676641965412668300508798878,79899749808080537588923567653676641965412668300511243042⟩,⟨33527906221484148905641248163244200771522856302939261450,33527906221484148905641248163244200771522856302940383386⟩,⟨24337038313637822280874848261699808836734199813224924272,24337038313637822280874848261699808836734199813225764505⟩,⟨33527906221484148905641248163244200771522856302939261450,33527906221484148905641248163244200771522856302940383386⟩,⟨79899749808080537588923567653676641965412668300508798878,79899749808080537588923567653676641965412668300511243042⟩,⟨264767109483956331932502799847836939305318136829281421627,264767109483956331932502799847836939305318136829288475928⟩,⟨972256694977247423736489801601331497560640132656720761197,972256694977247423736489801601331497560640132656742519195⟩,⟨3373094873933466286741118593271994588029282509691612000491,3373094873933466286741118593271994588029282509691673797687⟩,⟨10198715289414200153834874804820132571970125212723056784719,10198715289414200153834874804820132571970125212723206986387⟩,⟨26229070391919064380411003155127795161953680043563575398645,26229070391919064380411003155127795161953680043563881547764⟩,⟨57742493736332758162040340679040057196236536824055952521931,57742493736332758162040340679040057196236536824056479610779⟩,⟨110911443867012821826721645882868547192098665145370022020939,110911443867012821826721645882868547192098665145370801723844⟩,⟨190032594924800012499975114596888048884308303178972961078394,190032594924800012499975114596888048884308303178973968824609⟩,⟨296516315434988089698047993174226897816590897560819476718773,296516315434988089698047993174226897816590897560820626866039⟩,⟨428899696455472795772624439880400222978969539349961726480100,428899696455472795772624439880400222978969539349962884156689⟩,⟨583567071375140899468048309010397782300196182671066899754901,583567071375140899468048309010397782300196182671067901350439⟩,⟨755706572910691539042303978749141248586157450777118634329767,755706572910691539042303978749141248586157450777119308571949⟩,⟨940163846483244417184606941581156992434378851333648275035807,940163846483244417184606941581156992434378851333648459828303⟩]
def psiB1 : Fin 31 → RI := ![⟨20946057871546415761270592744052569460596014194673686595886005,20946057871546415761270592744052569460596683976618312230176750⟩,⟨18549951312052779900924895662113910516427234472541396650497986,18549951312052779900924895662113910516427825489654014179481647⟩,⟨15876977624264297445933879387171137582971400515625338719808678,15876977624264297445933879387171137582971904463644603099065825⟩,⟨13016565351753387856520425215206088760107237610628953548321009,13016565351753387856520425215206088760107649150759389922971639⟩,⟨10106233523115600623582689007645433414385500726451212681705114,10106233523115600623582689007645433414385818959413983622603051⟩,⟨7325225662696594985702595439759298015416109887560199354053007,7325225662696594985702595439759298015416339590684534875675311⟩,⟨4869699105590342338540408851468034805874593883920166620801964,4869699105590342338540408851468034805874745938649949921606324⟩,⟨2907419108145168667594502119783248121060628353878731189093026,2907419108145168667594502119783248121060718747221080444406779⟩,⟨1523503777702176280489466761125174647102180619517387294805746,1523503777702176280489466761125174647102227783112915788335731⟩,⟨686116966002421091608369721719139245199095476413569435522198,686116966002421091608369721719139245199116627549040991682659⟩,⟨262992034772664998851994385005210887261892703234469212033250,262992034772664998851994385005210887261900778075715684067712⟩,⟨87422147118958484984145421226484866463052981317124837880543,87422147118958484984145421226484866463055655633761884798248⟩,⟨27097891023059242088303325275167737215167764492913106462679,27097891023059242088303325275167737215168590808201267789944⟩,⟨9088286837150332716841713612445064518206955863677881100212,9088286837150332716841713612445064518207232312894115952010⟩,⟨4089888506068033654288339475479829691786533028157708396000,4089888506068033654288339475479829691786657237912611274865⟩,⟨3042601455959027934532276456279777513274700711346669862450,3042601455959027934532276456279777513274793064473720788829⟩,⟨4089888506068033654288339475479829691786533028157708396000,4089888506068033654288339475479829691786657237912611274865⟩,⟨9088286837150332716841713612445064518206955863677881100212,9088286837150332716841713612445064518207232312894115952010⟩,⟨27097891023059242088303325275167737215167764492913106462679,27097891023059242088303325275167737215168590808201267789944⟩,⟨87422147118958484984145421226484866463052981317124837880543,87422147118958484984145421226484866463055655633761884798248⟩,⟨262992034772664998851994385005210887261892703234469212033251,262992034772664998851994385005210887261900778075715684067710⟩,⟨686116966002421091608369721719139245199095476413569435522200,686116966002421091608369721719139245199116627549040991682661⟩,⟨1523503777702176280489466761125174647102180619517387294805746,1523503777702176280489466761125174647102227783112915788335735⟩,⟨2907419108145168667594502119783248121060628353878731189093035,2907419108145168667594502119783248121060718747221080444406789⟩,⟨4869699105590342338540408851468034805874593883920166620801969,4869699105590342338540408851468034805874745938649949921606299⟩,⟨7325225662696594985702595439759298015416109887560199354052992,7325225662696594985702595439759298015416339590684534875675297⟩,⟨10106233523115600623582689007645433414385500726451212681705100,10106233523115600623582689007645433414385818959413983622603089⟩,⟨13016565351753387856520425215206088760107237610628953548321030,13016565351753387856520425215206088760107649150759389922971619⟩,⟨15876977624264297445933879387171137582971400515625338719808710,15876977624264297445933879387171137582971904463644603099065825⟩,⟨18549951312052779900924895662113910516427234472541396650497982,18549951312052779900924895662113910516427825489654014179481642⟩,⟨20946057871546415761270592744052569460596014194673686595886000,20946057871546415761270592744052569460596683976618312230176799⟩]
def envelopeExpB3 : Fin 31 → RI := ![⟨831018399966972471512410647393996693313308275999240686512625,831018399966972471512410647393996693313308275999241176428587⟩,⟨431578298813558971792544233034700799322422359640836718685424,431578298813558971792544233034700799322422359640837875010634⟩,⟨198734073576061844001456422476190720736184977950589905971855,198734073576061844001456422476190720736184977950590931358324⟩,⟨78898222053326816970522736413520668081843893011328061573579,78898222053326816970522736413520668081843893011328702550902⟩,⟨26070285341581984194683404395797834274938682324174509733553,26070285341581984194683404395797834274938682324174814540483⟩,⟨6862530635975071100635506243219849665693505616570336007054,6862530635975071100635506243219849665693505616570445892220⟩,⟨1364360310410754679718370755735771883862968763128579192191,1364360310410754679718370755735771883862968763128608214277⟩,⟨192524767560758877379855797298503128965534407626341149328,192524767560758877379855797298503128965534407626346480594⟩,⟨18044659687945943288483725096914541077272729345329906988,18044659687945943288483725096914541077272729345330547896⟩,⟨1060807066634567212776183468323924839053914177014350609,1060807066634567212776183468323924839053914177014398328⟩,⟨38378294387021963091056639278814505429738799941423350,38378294387021963091056639278814505429738799941425510⟩,⟨919057804081045294589126330541872799454387959525930,919057804081045294589126330541872799454387959525997⟩,⟨18560603897104994329360115622758291216344286652325,18560603897104994329360115622758291216344286652329⟩,⟨510077607331856943034638560341492633342127544278,510077607331856943034638560341492633342127544281⟩,⟨37689406558012280163084098596677601939322946805,37689406558012280163084098596677601939322946808⟩,⟨14414619319164273189590995879003500661462898249,14414619319164273189590995879003500661462898252⟩,⟨37689406558012280163084098596677601939322946805,37689406558012280163084098596677601939322946808⟩,⟨510077607331856943034638560341492633342127544278,510077607331856943034638560341492633342127544281⟩,⟨18560603897104994329360115622758291216344286652325,18560603897104994329360115622758291216344286652329⟩,⟨919057804081045294589126330541872799454387959525930,919057804081045294589126330541872799454387959525997⟩,⟨38378294387021963091056639278814505429738799941423350,38378294387021963091056639278814505429738799941425510⟩,⟨1060807066634567212776183468323924839053914177014350609,1060807066634567212776183468323924839053914177014398328⟩,⟨18044659687945943288483725096914541077272729345329906988,18044659687945943288483725096914541077272729345330547896⟩,⟨192524767560758877379855797298503128965534407626341149328,192524767560758877379855797298503128965534407626346480594⟩,⟨1364360310410754679718370755735771883862968763128579192191,1364360310410754679718370755735771883862968763128608214277⟩,⟨6862530635975071100635506243219849665693505616570336007054,6862530635975071100635506243219849665693505616570445892220⟩,⟨26070285341581984194683404395797834274938682324174509733553,26070285341581984194683404395797834274938682324174814540511⟩,⟨78898222053326816970522736413520668081843893011328061573579,78898222053326816970522736413520668081843893011328702550902⟩,⟨198734073576061844001456422476190720736184977950589905971855,198734073576061844001456422476190720736184977950590931358324⟩,⟨431578298813558971792544233034700799322422359640836718685424,431578298813558971792544233034700799322422359640837875010634⟩,⟨831018399966972471512410647393996693313308275999240686512625,831018399966972471512410647393996693313308275999241176428587⟩]
def envelopeExpB4 : Fin 31 → RI := ![⟨781293455411300114154957627451923243040778105164166482704485,781293455411300114154957627451923243040778105164167096883448⟩,⟨326146557139021022856967670775631924889847770171666373532876,326146557139021022856967670775631924889847770171667539280059⟩,⟨115974661299234185135061976316897028371414958173076229947716,115974661299234185135061976316897028371414958173077028624775⟩,⟨33839423489548361367422941604375640529233273670239064634413,33839423489548361367422941604375640529233273670239431792958⟩,⟨7730264951824669842413535568941081794641458088300035795808,7730264951824669842413535568941081794641458088300156588907⟩,⟨1304104504505280898519408226617123522031855865275908498146,1304104504505280898519408226617123522031855865275936430890⟩,⟨151323171982502606964177619129271640419567150988440363164,151323171982502606964177619129271640419567150988444673475⟩,⟨11116860184966039664313477395309637026666221239918278129,11116860184966039664313477395309637026666221239918690878⟩,⟨473294649153358444692363089131763369141771570511640934,473294649153358444692363089131763369141771570511663511⟩,⟨10818869249604588859027738500793289877196293210155129,10818869249604588859027738500793289877196293210155787⟩,⟨129453628067173305393749288139305549783525694238874,129453628067173305393749288139305549783525694238886⟩,⟨893560103088883677484597151552296469466320021645,893560103088883677484597151552296469466320021648⟩,⟨4914237444113144598541121311673455314444747092,4914237444113144598541121311673455314444747095⟩,⟨40755073208519716597173739301744114259161039,40755073208519716597173739301744114259161042⟩,⟨1263646888620425410413591971032324037497004,1263646888620425410413591971032324037497007⟩,⟨350809142647004857127966788581896455469112,350809142647004857127966788581896455469115⟩,⟨1263646888620425410413591971032324037497004,1263646888620425410413591971032324037497007⟩,⟨40755073208519716597173739301744114259161039,40755073208519716597173739301744114259161042⟩,⟨4914237444113144598541121311673455314444747092,4914237444113144598541121311673455314444747095⟩,⟨893560103088883677484597151552296469466320021645,893560103088883677484597151552296469466320021648⟩,⟨129453628067173305393749288139305549783525694238874,129453628067173305393749288139305549783525694238886⟩,⟨10818869249604588859027738500793289877196293210155129,10818869249604588859027738500793289877196293210155787⟩,⟨473294649153358444692363089131763369141771570511640934,473294649153358444692363089131763369141771570511663511⟩,⟨11116860184966039664313477395309637026666221239918278129,11116860184966039664313477395309637026666221239918690878⟩,⟨151323171982502606964177619129271640419567150988440363164,151323171982502606964177619129271640419567150988444673475⟩,⟨1304104504505280898519408226617123522031855865275908498146,1304104504505280898519408226617123522031855865275936430890⟩,⟨7730264951824669842413535568941081794641458088300035795808,7730264951824669842413535568941081794641458088300156588907⟩,⟨33839423489548361367422941604375640529233273670239064634413,33839423489548361367422941604375640529233273670239431792958⟩,⟨115974661299234185135061976316897028371414958173076229947716,115974661299234185135061976316897028371414958173077028624775⟩,⟨326146557139021022856967670775631924889847770171666373532876,326146557139021022856967670775631924889847770171667539280059⟩,⟨781293455411300114154957627451923243040778105164166482704485,781293455411300114154957627451923243040778105164167096883448⟩]
def envelopeExpB7 : Fin 31 → RI := ![⟨649269237220565770929106403476934137364815566205458828751547,649269237220565770929106403476934137364815566205459722204273⟩,⟨140757776293957900110529425081907301594945256271018679265943,140757776293957900110529425081907301594945256271019561143839⟩,⟨23048116871600858638208110241012487102843924705771413942733,23048116871600858638208110241012487102843924705771692586272⟩,⟨2669870348634950037718312088069581146513423014858464024805,2669870348634950037718312088069581146513423014858514970901⟩,⟨201530213060099653417515402759258841088955995197795160793,201530213060099653417515402759258841088955995197800711115⟩,⟨8949457114680580299921450853183574913221930412244047880,8949457114680580299921450853183574913221930412244386618⟩,⟨206459329898387272455094328687913507717487891297620688,206459329898387272455094328687913507717487891297631116⟩,⟨2140270923116041726595082924805897285678344998099196,2140270923116041726595082924805897285678344998099340⟩,⟨8540440876098125704443182154668420418084317488561,8540440876098125704443182154668420418084317488565⟩,⟨11476732952975965272793046403822409447967378720,11476732952975965272793046403822409447967378723⟩,⟨4968209447430026127170016771434735476260096,4968209447430026127170016771434735476260099⟩,⟨821233386159301891228366772355220760257,821233386159301891228366772355220760260⟩,⟨91211214656505718409367865026968803,91211214656505718409367865026968806⟩,⟨20788250228836403062336815673994,20788250228836403062336815673997⟩,⟨47626101330982474825864847323,47626101330982474825864847326⟩,⟨5056780244938971547843931071,5056780244938971547843931074⟩,⟨47626101330982474825864847323,47626101330982474825864847326⟩,⟨20788250228836403062336815673994,20788250228836403062336815673997⟩,⟨91211214656505718409367865026968803,91211214656505718409367865026968806⟩,⟨821233386159301891228366772355220760257,821233386159301891228366772355220760260⟩,⟨4968209447430026127170016771434735476260096,4968209447430026127170016771434735476260099⟩,⟨11476732952975965272793046403822409447967378720,11476732952975965272793046403822409447967378723⟩,⟨8540440876098125704443182154668420418084317488561,8540440876098125704443182154668420418084317488565⟩,⟨2140270923116041726595082924805897285678344998099196,2140270923116041726595082924805897285678344998099340⟩,⟨206459329898387272455094328687913507717487891297620688,206459329898387272455094328687913507717487891297631116⟩,⟨8949457114680580299921450853183574913221930412244047880,8949457114680580299921450853183574913221930412244386618⟩,⟨201530213060099653417515402759258841088955995197795160793,201530213060099653417515402759258841088955995197800711115⟩,⟨2669870348634950037718312088069581146513423014858464024805,2669870348634950037718312088069581146513423014858514970901⟩,⟨23048116871600858638208110241012487102843924705771413942733,23048116871600858638208110241012487102843924705771692586272⟩,⟨140757776293957900110529425081907301594945256271018679265943,140757776293957900110529425081907301594945256271019561143839⟩,⟨649269237220565770929106403476934137364815566205458828751547,649269237220565770929106403476934137364815566205459722204273⟩]
def envelopeExpB9 : Fin 31 → RI := ![⟨573894310742810710148689975858067893338037425691259309244613,573894310742810710148689975858067893338037425691260324835507⟩,⟨80385699708483246302061475099667486062926632189861722091874,80385699708483246302061475099667486062926632189862370327292⟩,⟨7849048342218573052789217215698237318739521506995107710292,7849048342218573052789217215698237318739521506995229971225⟩,⟨491135865473997320575951950907058652113586784213613062804,491135865473997320575951950907058652113586784213625152141⟩,⟨17718924342220727699638225385653737034136779988956359805,17718924342220727699638225385653737034136779988956990216⟩,⟨323186259963161321120199534475607398252689665792766764,323186259963161321120199534475607398252689665792782597⟩,⟨2539728143518817973445508253672745987486162799872109,2539728143518817973445508253672745987486162799872278⟩,⟨7136081858042324748740804493961005126965107581726,7136081858042324748740804493961005126965107581729⟩,⟨5875517008093937563142486565976249999759421001,5875517008093937563142486565976249999759421004⟩,⟨1193738532051324670299043647440623155199422,1193738532051324670299043647440623155199425⟩,⟨56527139578349796817534002111004500337,56527139578349796817534002111004500340⟩,⟨776298025429664819186353682423087,776298025429664819186353682423090⟩,⟨6394054116135615763367969298,6394054116135615763367969301⟩,⟨132711566216549269359629,132711566216549269359632⟩,⟨53537476631519601172,53537476631519601175⟩,⟨2995087622088307760,2995087622088307763⟩,⟨53537476631519601172,53537476631519601175⟩,⟨132711566216549269359629,132711566216549269359632⟩,⟨6394054116135615763367969298,6394054116135615763367969301⟩,⟨776298025429664819186353682423087,776298025429664819186353682423090⟩,⟨56527139578349796817534002111004500337,56527139578349796817534002111004500340⟩,⟨1193738532051324670299043647440623155199422,1193738532051324670299043647440623155199425⟩,⟨5875517008093937563142486565976249999759421001,5875517008093937563142486565976249999759421004⟩,⟨7136081858042324748740804493961005126965107581726,7136081858042324748740804493961005126965107581729⟩,⟨2539728143518817973445508253672745987486162799872109,2539728143518817973445508253672745987486162799872278⟩,⟨323186259963161321120199534475607398252689665792766764,323186259963161321120199534475607398252689665792782597⟩,⟨17718924342220727699638225385653737034136779988956359805,17718924342220727699638225385653737034136779988956990216⟩,⟨491135865473997320575951950907058652113586784213613062804,491135865473997320575951950907058652113586784213625152142⟩,⟨7849048342218573052789217215698237318739521506995107710292,7849048342218573052789217215698237318739521506995229971225⟩,⟨80385699708483246302061475099667486062926632189861722091874,80385699708483246302061475099667486062926632189862370327292⟩,⟨573894310742810710148689975858067893338037425691259309244613,573894310742810710148689975858067893338037425691260324835507⟩]
def envelopeExpB12 : Fin 31 → RI := ![⟨476916731863639057153704468866118902653292210566893142463789,476916731863639057153704468866118902653292210566894268149700⟩,⟨34692723529124802802216337869546188929598180030782749996544,34692723529124802802216337869546188929598180030783123626948⟩,⟨1559873350744532140703850922018210699642286229984251654558,1559873350744532140703850922018210699642286229984284153453⟩,⟨38749746572520288231997756893491666244144252221134876212,38749746572520288231997756893491666244144252221136154307⟩,⟨461937413547597238648194579439513013520884987299907991,461937413547597238648194579439513013520884987299930064⟩,⟨2217875610123398119846994377443182983839996704470148,2217875610123398119846994377443182983839996704470297⟩,⟨3465104278250264201246489842053568805715337263982,3465104278250264201246489842053568805715337263985⟩,⟨1373872501014146899996226436939647001610470771,1373872501014146899996226436939647001610470774⟩,⟨106021704901793433734910681319519689903672,106021704901793433734910681319519689903675⟩,⟨1266326270514020017980687685265417089,1266326270514020017980687685265417092⟩,⟨2169415203594189064638686311033,2169415203594189064638686311036⟩,⟨713462758563839207337370,713462758563839207337373⟩,⟨118677505746246938,118677505746246941⟩,⟨67693198160,67693198163⟩,⟨2017794,2017797⟩,⟨43172,43175⟩,⟨2017794,2017797⟩,⟨67693198160,67693198163⟩,⟨118677505746246938,118677505746246941⟩,⟨713462758563839207337370,713462758563839207337373⟩,⟨2169415203594189064638686311033,2169415203594189064638686311036⟩,⟨1266326270514020017980687685265417089,1266326270514020017980687685265417092⟩,⟨106021704901793433734910681319519689903672,106021704901793433734910681319519689903675⟩,⟨1373872501014146899996226436939647001610470771,1373872501014146899996226436939647001610470774⟩,⟨3465104278250264201246489842053568805715337263982,3465104278250264201246489842053568805715337263985⟩,⟨2217875610123398119846994377443182983839996704470148,2217875610123398119846994377443182983839996704470297⟩,⟨461937413547597238648194579439513013520884987299907991,461937413547597238648194579439513013520884987299930064⟩,⟨38749746572520288231997756893491666244144252221134876212,38749746572520288231997756893491666244144252221136154307⟩,⟨1559873350744532140703850922018210699642286229984251654558,1559873350744532140703850922018210699642286229984284153453⟩,⟨34692723529124802802216337869546188929598180030782749996544,34692723529124802802216337869546188929598180030783123626948⟩,⟨476916731863639057153704468866118902653292210566893142463789,476916731863639057153704468866118902653292210566894268149700⟩]
def envelopeExpB13 : Fin 31 → RI := ![⟨448379869081136991664472325527456331060096209027074031608687,448379869081136991664472325527456331060096209027075178265273⟩,⟨26217519203133016670146720919736371215474205808209465984260,26217519203133016670146720919736371215474205808209772035807⟩,⟨910290723010114582470448351667215137268506881284349462191,910290723010114582470448351667215137268506881284370029537⟩,⟨16619754542680448983402702520635052830847089271294746127,16619754542680448983402702520635052830847089271295340967⟩,⟨136971979826701883387264755978627452532842223907501843,136971979826701883387264755978627452532842223907508952⟩,⟨421468657412173396774755739697309963091699444227446,421468657412173396774755739697309963091699444227479⟩,⟨384319718650500155901097808255861995995429323400,384319718650500155901097808255861995995429323403⟩,⟨79330824284329198308731157066671280471564333,79330824284329198308731157066671280471564336⟩,⟨2780850760940410488100251292717762605847,2780850760940410488100251292717762605850⟩,⟨12914901096478198382283744780477090,12914901096478198382283744780477093⟩,⟨7317643302676886261024213853,7317643302676886261024213856⟩,⟨693668943630628138410,693668943630628138413⟩,⟨31421900157198,31421900157201⟩,⟨5408668,5408671⟩,⟨66,69⟩,⟨0,3⟩,⟨66,69⟩,⟨5408668,5408671⟩,⟨31421900157198,31421900157201⟩,⟨693668943630628138410,693668943630628138413⟩,⟨7317643302676886261024213853,7317643302676886261024213856⟩,⟨12914901096478198382283744780477090,12914901096478198382283744780477093⟩,⟨2780850760940410488100251292717762605847,2780850760940410488100251292717762605850⟩,⟨79330824284329198308731157066671280471564333,79330824284329198308731157066671280471564336⟩,⟨384319718650500155901097808255861995995429323400,384319718650500155901097808255861995995429323403⟩,⟨421468657412173396774755739697309963091699444227446,421468657412173396774755739697309963091699444227479⟩,⟨136971979826701883387264755978627452532842223907501843,136971979826701883387264755978627452532842223907508952⟩,⟨16619754542680448983402702520635052830847089271294746127,16619754542680448983402702520635052830847089271295340967⟩,⟨910290723010114582470448351667215137268506881284349462191,910290723010114582470448351667215137268506881284370029537⟩,⟨26217519203133016670146720919736371215474205808209465984260,26217519203133016670146720919736371215474205808209772035807⟩,⟨448379869081136991664472325527456331060096209027074031608687,448379869081136991664472325527456331060096209027075178265742⟩]
def envelopeExpB16 : Fin 31 → RI := ![⟨372611921381207054094484292453235685467023869608889140627029,372611921381207054094484292453235685467023869608890313832703⟩,⟨11314912336799961567959729892030827154772765078878993649445,11314912336799961567959729892030827154772765078879156482577⟩,⟨180905783522298643645672207961038390334881054951937219625,180905783522298643645672207961038390334881054951942266207⟩,⟨1311269084380189147544714845891597073376432389784399320,1311269084380189147544714845891597073376432389784457372⟩,⟨3570898597883529358221734402271672999613544870771802,3570898597883529358221734402271672999613544870772034⟩,⟨2892341573594321664965028488805696941426706749679,2892341573594321664965028488805696941426706749682⟩,⟨524350570634970297304010686470012839670736821,524350570634970297304010686470012839670736824⟩,⟨15273148505743884622984303530686996176217,15273148505743884622984303530686996176220⟩,⟨50179505624135226457441038889297858,50179505624135226457441038889297861⟩,⟨13700218348030593350948611771,13700218348030593350948611774⟩,⟨280838668889353204131,280838668889353204134⟩,⟨637521856091,637521856094⟩,⟨582,585⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨582,585⟩,⟨637521856091,637521856094⟩,⟨280838668889353204131,280838668889353204134⟩,⟨13700218348030593350948611771,13700218348030593350948611774⟩,⟨50179505624135226457441038889297858,50179505624135226457441038889297861⟩,⟨15273148505743884622984303530686996176217,15273148505743884622984303530686996176220⟩,⟨524350570634970297304010686470012839670736821,524350570634970297304010686470012839670736824⟩,⟨2892341573594321664965028488805696941426706749679,2892341573594321664965028488805696941426706749682⟩,⟨3570898597883529358221734402271672999613544870771802,3570898597883529358221734402271672999613544870772034⟩,⟨1311269084380189147544714845891597073376432389784399320,1311269084380189147544714845891597073376432389784457372⟩,⟨180905783522298643645672207961038390334881054951937219625,180905783522298643645672207961038390334881054951942266207⟩,⟨11314912336799961567959729892030827154772765078878993649445,11314912336799961567959729892030827154772765078879156482577⟩,⟨372611921381207054094484292453235685467023869608889140627029,372611921381207054094484292453235685467023869608890313832703⟩]
def envelopeExpB19 : Fin 31 → RI := ![⟨309647362714830025314078565367175150593498371932099896950646,309647362714830025314078565367175150593498371932101055121668⟩,⟨4883270617540678626615222245235252285045771376316717769436,4883270617540678626615222245235252285045771376316801358258⟩,⟨35952143292855615020463653737419768034205365946855380529,35952143292855615020463653737419768034205365946856575272⟩,⟨103456799391090702226820947501277777669701488819930057,103456799391090702226820947501277777669701488819935526⟩,⟨93094345372678635597776563953300534026000874541600,93094345372678635597776563953300534026000874541611⟩,⟨19848782658495378169445161515231647308639253850,19848782658495378169445161515231647308639253853⟩,⟨715403107315584422371804350776709847608276,715403107315584422371804350776709847608279⟩,⟨2940459365989293158851698675612822713,2940459365989293158851698675612822716⟩,⟨905472102296889661657784190117,905472102296889661657784190120⟩,⟨14533288438027409982392,14533288438027409982395⟩,⟨10778109109893,10778109109896⟩,⟨584,587⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨584,587⟩,⟨10778109109893,10778109109896⟩,⟨14533288438027409982392,14533288438027409982395⟩,⟨905472102296889661657784190117,905472102296889661657784190120⟩,⟨2940459365989293158851698675612822713,2940459365989293158851698675612822716⟩,⟨715403107315584422371804350776709847608276,715403107315584422371804350776709847608279⟩,⟨19848782658495378169445161515231647308639253850,19848782658495378169445161515231647308639253853⟩,⟨93094345372678635597776563953300534026000874541600,93094345372678635597776563953300534026000874541611⟩,⟨103456799391090702226820947501277777669701488819930057,103456799391090702226820947501277777669701488819935526⟩,⟨35952143292855615020463653737419768034205365946855380529,35952143292855615020463653737419768034205365946856575272⟩,⟨4883270617540678626615222245235252285045771376316717769436,4883270617540678626615222245235252285045771376316801358258⟩,⟨309647362714830025314078565367175150593498371932099896950646,309647362714830025314078565367175150593498371932101055121668⟩]
def envelopeExpB21 : Fin 31 → RI := ![⟨273699799114597007071697878679024715889885301461725116293863,273699799114597007071697878679024715889885301461726248039570⟩,⟨2788798855681657520467570141720148190286233385371231805096,2788798855681657520467570141720148190286233385371284624707⟩,⟨12243521337732300744794049557504421728573857719351543076,12243521337732300744794049557504421728573857719351993723⟩,⟨19031390319792813039243333413136386702230156208528950,19031390319792813039243333413136386702230156208530068⟩,⟨8185034081491003670164670857358114770075542839966,8185034081491003670164670857358114770075542839970⟩,⟨716786923499295569447704487222279901138425674,716786923499295569447704487222279901138425677⟩,⟨8800422855699657168510288547229477643180,8800422855699657168510288547229477643183⟩,⟨9804066629750289102817336179963042,9804066629750289102817336179963045⟩,⟨622932330377603710210874968,622932330377603710210874971⟩,⟨1511662463261434919,1511662463261434922⟩,⟨122630835,122630838⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨-1,2⟩,⟨122630835,122630838⟩,⟨1511662463261434919,1511662463261434922⟩,⟨622932330377603710210874968,622932330377603710210874971⟩,⟨9804066629750289102817336179963042,9804066629750289102817336179963045⟩,⟨8800422855699657168510288547229477643180,8800422855699657168510288547229477643183⟩,⟨716786923499295569447704487222279901138425674,716786923499295569447704487222279901138425677⟩,⟨8185034081491003670164670857358114770075542839966,8185034081491003670164670857358114770075542839970⟩,⟨19031390319792813039243333413136386702230156208528950,19031390319792813039243333413136386702230156208530068⟩,⟨12243521337732300744794049557504421728573857719351543076,12243521337732300744794049557504421728573857719351993723⟩,⟨2788798855681657520467570141720148190286233385371231805096,2788798855681657520467570141720148190286233385371284624707⟩,⟨273699799114597007071697878679024715889885301461725116293863,273699799114597007071697878679024715889885301461726248039570⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def finiteEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  ∑ n : Fin 10, normJetEnvelope (damping q) (damping v) (finiteNode n) (frequency j)

def finiteTailEnvelope (d : Fin 2) : ℝ :=
  ∑ i : Fin 15, finiteEnvelopeSum 0 1 ⟨i.val+16,by omega⟩ * fullTailW i d
end AtomicTriangular.Construction
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
def envelopeSumBoxB : Fin 31 → RI := ![⟨106347376951456338225032043942064733748296283269995867913956226,106347376951456338225032043942064733748301424186069970119430680⟩,⟨58487042695827358134825117562935735521301834079234237122443803,58487042695827358134825117562935735521304749053863564411008639⟩,⟨33970633629183266609636215761619989484513494296837195435710356,33970633629183266609636215761619989484515088780385976998045760⟩,⟨20292169844773681939764565684539370344435941569226406962962515,20292169844773681939764565684539370344436799435084985306881940⟩,⟨12586568179256571993816573081650023302543625259724153413250160,12586568179256571993816573081650023302544097549244970261171271⟩,⟨8012010921028981986723998805567334090822937740097979488608896,8012010921028981986723998805567334090823210497173924675652861⟩,⟨5016499901071824707078210431562593085065983669330583021435276,5016499901071824707078210431562593085066144981186553614552874⟩,⟨2930200705720548573728234458506443690721806972236622490565837,2930200705720548573728234458506443690721898805111524701172149⟩,⟨1525900231866898777450384023265758787941538790843934488080876,1525900231866898777450384023265758787941586105621459449229705⟩,⟨686277457783415438908814219964027090185374671247312237869604,686277457783415438908814219964027090185395832463053825798771⟩,⟨262998698385186006650602092030146487116338919353906897321633,262998698385186006650602092030146487116346994611215648454473⟩,⟨87422330007979130953696547583095618143256842048779704655753,87422330007979130953696547583095618143259516376764572750522⟩,⟨27097895208622630192368585930603612045359115587875087530702,27097895208622630192368585930603612045359941903421464016566⟩,⟨9088286964583683036884937176604500996233572014947869529779,9088286964583683036884937176604500996233848464171929903969⟩,⟨4089888516146006890195905924404023946250489000103955758448,4089888516146006890195905924404023946250613209859475674545⟩,⟨3042601459906638278065935485475747235564841468005612772945,3042601459906638278065935485475747235564933821132905148737⟩,⟨4089888516146006890195905924404023946250489000103955758448,4089888516146006890195905924404023946250613209859475674545⟩,⟨9088286964583683036884937176604500996233572014947869529779,9088286964583683036884937176604500996233848464171929903969⟩,⟨27097895208622630192368585930603612045359115587875087530702,27097895208622630192368585930603612045359941903421464016566⟩,⟨87422330007979130953696547583095618143256842048779704655753,87422330007979130953696547583095618143259516376764572750522⟩,⟨262998698385186006650602092030146487116338919353906897321634,262998698385186006650602092030146487116346994611215648454471⟩,⟨686277457783415438908814219964027090185374671247312237869606,686277457783415438908814219964027090185395832463053825798773⟩,⟨1525900231866898777450384023265758787941538790843934488080876,1525900231866898777450384023265758787941586105621459449229709⟩,⟨2930200705720548573728234458506443690721806972236622490565846,2930200705720548573728234458506443690721898805111524701172159⟩,⟨5016499901071824707078210431562593085065983669330583021435281,5016499901071824707078210431562593085066144981186553614552848⟩,⟨8012010921028981986723998805567334090822937740097979488608879,8012010921028981986723998805567334090823210497173924675652846⟩,⟨12586568179256571993816573081650023302543625259724153413250144,12586568179256571993816573081650023302544097549244970261173505⟩,⟨20292169844773681939764565684539370344435941569226406962962550,20292169844773681939764565684539370344436799435084985306881914⟩,⟨33970633629183266609636215761619989484513494296837195435710424,33970633629183266609636215761619989484515088780385976998045761⟩,⟨58487042695827358134825117562935735521301834079234237122443795,58487042695827358134825117562935735521304749053863564411008626⟩,⟨106347376951456338225032043942064733748296283269995867913956215,106347376951456338225032043942064733748301424186069970119434023⟩]
def boundB : Fin 2 → RI := ![⟨106992734143269554352850967031322302145957125684055638576194107,106992734143269554352850967031322302145961173439079333035328504⟩,⟨334702182249134137883567462407238680064117422331211329138320346,334702182249134137883567462407238680064131247872720098964606091⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
def Bkernel (i : Fin 20) (p : TailNode × Fin 2) : ℝ :=
  tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩
end AtomicTriangular.Construction
end

end OAI
end


