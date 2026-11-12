-- Prove2me | Definitions.Def_OAIQ262T000
-- name    : OAIQ262T000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T16:40:20.059735+00:00
-- url     : https://prove2.me/theorems/8d05157d-b131-460a-bfa5-8f3de208bdc1
-- title:
--   Definitions bundle OAIQ262T000 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 180 declarations of OpenAI's Lean: 103 definitions, 2 inductive types or structures, 2 instances and 73 theorems. The definitions and types are `OAI.AtomicTriangular.Analysis.dampedEntireSchwartz`, `OAI.AtomicTriangular.Analysis.gaussianSchwartz`, `OAI.AtomicTriangular.Bernstein.bernsteinBasis`, `OAI.AtomicTriangular.Bernstein.bernsteinCoefficient`, `OAI.AtomicTriangular.Constants.arctanPoly`, `OAI.AtomicTriangular.Constants.bStar`, `OAI.AtomicTriangular.Constants.eps`, `OAI.AtomicTriangular.Constants.pStar`, `OAI.AtomicTriangular.Construction.AallKernel`, `OAI.AtomicTriangular.Construction.AallOperator`, `OAI.AtomicTriangular.Construction.CallKernel`, `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients`, `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.enumerateTail`, `OAI.AtomicTriangular.Construction.frequencyDecay`, `OAI.AtomicTriangular.Construction.normJetEnvelope`, `OAI.AtomicTriangular.Construction.repetitionEntry`, `OAI.AtomicTriangular.Construction.repetitionEnvelope`, `OAI.AtomicTriangular.Construction.repetitionKernel`, `OAI.AtomicTriangular.Construction.repetitionNorm`, `OAI.AtomicTriangular.Construction.repetitionRatio`, `OAI.AtomicTriangular.Construction.tailBase`, `OAI.AtomicTriangular.Construction.tailEnumeration`, `OAI.AtomicTriangular.Construction.tailEnvelopeSum`, `OAI.AtomicTriangular.FiniteCertificate.QBox0`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox0`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox10`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox11`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox12`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox13`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox14`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox15`, `OAI.AtomicTriangular.FiniteCertificate.coeffBox9`, `OAI.AtomicTriangular.FiniteCertificate.coeffStep`, `OAI.AtomicTriangular.FiniteCertificate.frequencyBox`, `OAI.AtomicTriangular.FiniteCertificate.jetBox2_0`, `OAI.AtomicTriangular.FiniteCertificate.partialPolynomial`, `OAI.AtomicTriangular.FiniteCertificate.phaseBox0`, `OAI.AtomicTriangular.FiniteCertificate.phaseBox1` and 65 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_Bernstein`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_L1Kernel`, `Triangular_Construction_PeriodicJets`, `Triangular_Construction_Repetition`, `Triangular_Construction_RepetitionOperators`, `Triangular_Construction_TailEnumeration`, `Triangular_Envelope_Analytic`, `Triangular_Envelope_EnvelopeBoxes`, `Triangular_Envelope_EnvelopeSumsBase`, `Triangular_Envelope_KernelBounds`, `Triangular_Schwartz_Gaussian`.
--
--   **Imports.** It imports the published bundle `Def_TriangularGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ262T005`, `OAIQ262T006`, `OAIQ262T007`, `OAIQ262T008`, `OAIQ262T009`, `OAIQ262T010`, `OAIQ262T011`, `OAIQ262T012`, `OAIQ262T013`, `OAIQ262T014`, `OAIQ262T015`, `OAIQ262T016`, `OAIQ262T017`, `OAIQ262T018`, `OAIQ262T019`, `OAIQ262T020`, `OAIQ262T021`, `OAIQ262T022`, `OAIQ262T023`, `OAIQ262T024`, `OAIQ262T025`, `OAIQ262T026`, `OAIQ262T027`, `OAIQ262T028`, `OAIQ262T029`, `OAIQ262T030`, `OAIQ262T031`, `OAIQ262T032`, `OAIQ262T033`, `OAIQ262T034`, `OAIQ262T035`, `OAIQ262T036`, `OAIQ262T037`, `OAIQ262T038`, `OAIQ262T039`, `OAIQ262T040`, `OAIQ262T041`, `OAIQ262T042`, `OAIQ262T043`, `OAIQ262T044`, `OAIQ262T045`, `OAIQ262T046`, `OAIQ262T047`, `OAIQ262T048`, `OAIQ262T049`, `OAIQ262T050`, `OAIQ262T051`, `OAIQ262T052`, `OAIQ262T053`, `OAIQ262T054`, `OAIQ262T055`, `OAIQ262T056`, `OAIQ262T057`, `OAIQ262T058`, `OAIQ262T059`, `OAIQ262T060`, `OAIQ262T061`, `OAIQ262T062`, `OAIQ262T063`, `OAIQ262T064`, `OAIQ262T065`, `OAIQ262T066`, `OAIQ262T067`, `OAIQ262T068`, `OAIQ262T069`, `OAIQ262T070`, `OAIQ262T071`, `OAIQ262T072`, `OAIQ262T073`, `OAIQ262T074`, `OAIQ262T075`, `OAIQ262T076`, `OAIQ262T077`, `OAIQ262T078`, `OAIQ262T079`, `OAIQ262T080`, `OAIQ262T081`, `OAIQ262T082`, `OAIQ262T083` and `OAIQ262T084`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_TriangularGaussian

section
-- module Solutions.OAIQ262_TG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Auxiliary_Bernstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset
noncomputable section
namespace AtomicTriangular.Bernstein

def bernsteinBasis (n d : ℕ) (x : ℝ) : ℝ :=
  (n.choose d : ℝ) * x^d * (1-x)^(n-d)

lemma bernsteinBasis_sum (n : ℕ) (x : ℝ) :
    ∑ d ∈ range (n+1), bernsteinBasis n d x = 1 := by
  calc
    _ = (x+(1-x))^n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [bernsteinBasis]
      ring
    _ = 1 := by simp

lemma bernsteinBasis_nonneg (n d : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ bernsteinBasis n d x := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (by linarith [hx.2]) _)

lemma choose_ratio (n r d : ℕ) (hr : r ≤ n) (hd : r ≤ d) :
    (d.choose r : ℝ)/(n.choose r : ℝ)*(n.choose d : ℝ) =
      ((n-r).choose (d-r) : ℝ) := by
  have h : (n.choose d : ℝ)*(d.choose r : ℝ) =
      (n.choose r : ℝ)*((n-r).choose (d-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n:=n) hd
  have hn : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hn).mpr
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma bernstein_monomial (n r : ℕ) (hr : r ≤ n) (x : ℝ) :
    ∑ d ∈ range (n+1), ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x = x^r := by
  let f : ℕ → ℝ := fun d => ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x
  have hlo : ∑ d ∈ range r, f d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hd)]
  have heq : ∀ d, r ≤ d →
      f d = x^r * ((n-r).choose (d-r) : ℝ)*x^(d-r)*(1-x)^((n-r)-(d-r)) := by
    intro d hd
    dsimp [f,bernsteinBasis]
    rw [show n-d = (n-r)-(d-r) by omega]
    rw [show d = r+(d-r) by omega, pow_add]
    have hratio := choose_ratio n r d hr hd
    rw [show r+(d-r)=d by omega]
    calc
      _ = (((d.choose r : ℝ)/(n.choose r : ℝ))*(n.choose d : ℝ))*
        x^r*x^(d-r)*(1-x)^((n-r)-(d-r)) := by ring
      _ = _ := by rw [hratio]; ring
  change (∑ d ∈ range (n+1), f d) = _
  rw [← Finset.sum_range_add_sum_Ico f (show r ≤ n+1 by omega), hlo, zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  have he : n+1-r = n-r+1 := by omega
  rw [he]
  calc
    _ = x^r * ∑ j ∈ range (n-r+1), bernsteinBasis (n-r) j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [heq _ (by omega)]
      simp only [Nat.add_sub_cancel_left, bernsteinBasis]
      ring
    _ = x^r := by rw [bernsteinBasis_sum, mul_one]

def bernsteinCoefficient (n : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ range (n+1), (d.choose r : ℝ)/(n.choose r : ℝ)*c r

lemma bernstein_polynomial (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    (∑ d ∈ range (n+1), bernsteinCoefficient n c d * bernsteinBasis n d x) =
      ∑ r ∈ range (n+1), c r * x^r := by
  unfold bernsteinCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = c r * ∑ d ∈ range (n+1),
        ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [bernstein_monomial n r (by simpa using Nat.le_of_lt_succ (mem_range.mp hr))]

lemma bernstein_polynomial_lower (n : ℕ) (c : ℕ → ℝ) (m : ℝ)
    (hc : ∀ d < n+1, m ≤ bernsteinCoefficient n c d)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    m ≤ ∑ r ∈ range (n+1), c r*x^r := by
  rw [← bernstein_polynomial]
  calc
    m = ∑ d ∈ range (n+1), m*bernsteinBasis n d x := by
      rw [← Finset.mul_sum, bernsteinBasis_sum, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (hc d (mem_range.mp hd)) (bernsteinBasis_nonneg n d hx)

lemma strict_bernstein_bound (n : ℕ) (c : ℕ → ℝ) (m : ℝ)
    (hc : ∀ d < n+1, m < bernsteinCoefficient n c d)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    m < ∑ r ∈ range (n+1), c r*x^r := by
  let b := (range (n+1)).inf' (by simp) (bernsteinCoefficient n c)
  have hb : m < b := by
    dsimp [b]
    exact (Finset.lt_inf'_iff _).mpr (fun d hd => hc d (mem_range.mp hd))
  exact hb.trans_le (bernstein_polynomial_lower n c b (by
    intro d hd
    exact Finset.inf'_le _ (mem_range.mpr hd)) hx)

end AtomicTriangular.Bernstein
end

end OAI
end

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

theorem node_residue (n : Node) : ∃ a : Fin 15, n.val % 36 = residue a := by
  have hn := n.property.2
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | exact ⟨0,h⟩ | exact ⟨1,h⟩ | exact ⟨2,h⟩ | exact ⟨3,h⟩
    | exact ⟨4,h⟩ | exact ⟨5,h⟩ | exact ⟨6,h⟩ | exact ⟨7,h⟩
    | exact ⟨8,h⟩ | exact ⟨9,h⟩ | exact ⟨10,h⟩ | exact ⟨11,h⟩
    | exact ⟨12,h⟩ | exact ⟨13,h⟩ | exact ⟨14,h⟩

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

structure RI where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

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

def RI.pow (a : RI) : ℕ → RI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

structure CI where
  re : RI
  im : RI
  deriving DecidableEq, Repr

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

def CI.pow (a : CI) : ℕ → CI
  | 0 => .point 1
  | n+1 => (a.pow n).mul a

end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Interval

def RI.sum {ι : Type*} [Fintype ι] (v : ι → RI) : RI :=
  ⟨∑ i, (v i).lo, ∑ i, (v i).hi⟩

def CI.sum {ι : Type*} [Fintype ι] (v : ι → CI) : CI :=
  ⟨RI.sum (fun i => (v i).re), RI.sum (fun i => (v i).im)⟩

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

lemma bStar_bracket : bStar < Real.sqrt 3 / 2 ∧ Real.sqrt 3 / 2 < bStar + eps := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hp : 0 < bStar := by norm_num [bStar]
  have he : 0 < eps := by norm_num [eps]
  have h₁ : bStar^2 < (3:ℝ)/4 := by norm_num [bStar]
  have h₂ : (3:ℝ)/4 < (bStar+eps)^2 := by norm_num [bStar, eps]
  constructor <;> nlinarith

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

def partialPolynomial (n : ℕ) : Polynomial ℂ :=
  ∏ a ∈ Finset.univ.filter (fun a : Fin 15 => a.val < n), atomFactor a

def coeffStep (e : CI) (v : Fin 31 → CI) (j : Fin 31) : CI :=
  ((e.neg.mul (v j)).add (if h : j.val=0 then CI.point 0
    else (CI.point 2).mul (v ⟨j.val-1,by omega⟩))).sub
      (if h : j.val<2 then CI.point 0 else e.conj.mul (v ⟨j.val-2,by omega⟩))

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial
def phaseBox0 : CI := ⟨⟨999999999999999999999999999999999999999999999999999999935489,1000000000000000000000000000000000000000000000000000000066558⟩,⟨-63486,68606⟩⟩
def phaseBox1 : CI := ⟨⟨984807753012208059366743024589523013670643251719842378260439,984807753012208059366743024589523013670643251719842475161964⟩,⟨173648177666930348851716626769314796000375677184069063062132,173648177666930348851716626769314796000375677184069621580864⟩⟩
def phaseBox2 : CI := ⟨⟨939692620785908384054109277324731469936208134264464471960044,939692620785908384054109277324731469936208134264464856618258⟩,⟨342020143325668733044099614682259580763083367514159975976700,342020143325668733044099614682259580763083367514161109522372⟩⟩
def phaseBox3 : CI := ⟨⟨866025403784438646763723170752936183471402626905189954512964,866025403784438646763723170752936183471402626905190810370953⟩,⟨499999999999999999999999999999999999999999999999999011153642,500000000000000000000000000000000000000000000000000751856976⟩⟩
def phaseBox4 : CI := ⟨⟨766044443118978035202392650555416673935832457080394614080696,766044443118978035202392650555416673935832457080396112163801⟩,⟨642787609686539326322643409907263432907559884205680453940922,642787609686539326322643409907263432907559884205682847200174⟩⟩
def phaseBox5 : CI := ⟨⟨642787609686539326322643409907263432907559884205680817903044,642787609686539326322643409907263432907559884205683112135181⟩,⟨766044443118978035202392650555416673935832457080393548649076,766044443118978035202392650555416673935832457080396649890976⟩⟩
def phaseBox6 : CI := ⟨⟨499999999999999999999999999999999999999999999999998625582869,500000000000000000000000000000000000000000000000001848404295⟩,⟨866025403784438646763723170752936183471402626905188241914124,866025403784438646763723170752936183471402626905192112487718⟩⟩
def phaseBox7 : CI := ⟨⟨342020143325668733044099614682259580763083367514158799320630,342020143325668733044099614682259580763083367514163057632021⟩,⟨939692620785908384054109277324731469936208134264462172730300,939692620785908384054109277324731469936208134264466875061792⟩⟩
def phaseBox8 : CI := ⟨⟨173648177666930348851716626769314796000375677184067060768548,173648177666930348851716626769314796000375677184072432368187⟩,⟨984807753012208059366743024589523013670643251719839559295028,984807753012208059366743024589523013670643251719845151568286⟩⟩
def phaseBox9 : CI := ⟨⟨-2854777273,3675745116⟩,⟨999999999999999999999999999999999999999999999999996734740088,1000000000000000000000000000000000000000000000000003265262478⟩⟩
def phaseBox10 : CI := ⟨⟨-173648177666930348851716626769314796000375677184072788297342,-173648177666930348851716626769314796000375677184065087845911⟩,⟨984807753012208059366743024589523013670643251719838747234178,984807753012208059366743024589523013670643251719846248746530⟩⟩
def phaseBox11 : CI := ⟨⟨-342020143325668733044099614682259580763083367514164579490877,-342020143325668733044099614682259580763083367514155734542861⟩,⟨939692620785908384054109277324731469936208134264460562604050,939692620785908384054109277324731469936208134264469046765440⟩⟩
def phaseBox12 : CI := ⟨⟨-500000000000000000000000000000000000000000000000004489253604,-499999999999999999999999999999999999999999999999994562770708⟩,⟨866025403784438646763723170752936183471402626905185861538948,866025403784438646763723170752936183471402626905195313833830⟩⟩
def phaseBox13 : CI := ⟨⟨-642787609686539326322643409907263432907559884205686789753345,-642787609686539326322643409907263432907559884205675882485247⟩,⟨766044443118978035202392650555416673935832457080390439298182,766044443118978035202392650555416673935832457080400814661650⟩⟩
def phaseBox14 : CI := ⟨⟨-766044443118978035202392650555416673935832457080400710407312,-766044443118978035202392650555416673935832457080388960420236⟩,⟨642787609686539326322643409907263432907559884205676669856626,642787609686539326322643409907263432907559884205687889085620⟩⟩
def phaseBox15 : CI := ⟨⟨-866025403784438646763723170752936183471402626905196181323615,-866025403784438646763723170752936183471402626905183762590658⟩,⟨499999999999999999999999999999999999999999999999994618824454,500000000000000000000000000000000000000000000000006566147044⟩⟩
def phaseBox16 : CI := ⟨⟨-939692620785908384054109277324731469936208134264470823413628,-939692620785908384054109277324731469936208134264457943587609⟩,⟨342020143325668733044099614682259580763083367514155053298568,342020143325668733044099614682259580763083367514167575120924⟩⟩
def phaseBox17 : CI := ⟨⟨-984807753012208059366743024589523013670643251719848835505828,-984807753012208059366743024589523013670643251719835732797643⟩,⟨173648177666930348851716626769314796000375677184063698304240,173648177666930348851716626769314796000375677184076603333880⟩⟩
def phaseBox18 : CI := ⟨⟨-1000000000000000000000000000000000000000000000000006530375474,-999999999999999999999999999999999999999999999999993469625023⟩,⟨-5709403374,7351347078⟩⟩
def phaseBox19 : CI := ⟨⟨-984807753012208059366743024589523013670643251719850175773758,-984807753012208059366743024589523013670643251719834962769522⟩,⟨-173648177666930348851716626769314796000375677184076234168892,-173648177666930348851716626769314796000375677184060833470644⟩⟩
def phaseBox20 : CI := ⟨⟨-939692620785908384054109277324731469936208134264473669623711,-939692620785908384054109277324731469936208134264456220534602⟩,⟨-342020143325668733044099614682259580763083367514168657202328,-342020143325668733044099614682259580763083367514150885369606⟩⟩
def phaseBox21 : CI := ⟨⟨-866025403784438646763723170752936183471402626905200655848102,-866025403784438646763723170752936183471402626905180930009073⟩,⟨-500000000000000000000000000000000000000000000000009235181440,-499999999999999999999999999999999999999999999999989105858860⟩⟩
def phaseBox22 : CI := ⟨⟨-766044443118978035202392650555416673935832457080406888294869,-766044443118978035202392650555416673935832457080384893374795⟩,⟨-642787609686539326322643409907263432907559884205692234760934,-642787609686539326322643409907263432907559884205669808574574⟩⟩
def phaseBox23 : CI := ⟨⟨-642787609686539326322643409907263432907559884205694695891306,-642787609686539326322643409907263432907559884205670491952222⟩,⟨-766044443118978035202392650555416673935832457080406878657306,-766044443118978035202392650555416673935832457080382264458734⟩⟩
def phaseBox24 : CI := ⟨⟨-500000000000000000000000000000000000000000000000014096951365,-499999999999999999999999999999999999999999999999987799006330⟩,⟨-866025403784438646763723170752936183471402626905203089251490,-866025403784438646763723170752936183471402626905176444175326⟩⟩
def phaseBox25 : CI := ⟨⟨-342020143325668733044099614682259580763083367514175810431770,-342020143325668733044099614682259580763083367514147589449286⟩,⟨-939692620785908384054109277324731469936208134264478478914456,-939692620785908384054109277324731469936208134264450007296924⟩⟩
def phaseBox26 : CI := ⟨⟨-173648177666930348851716626769314796000375677184085513919999,-173648177666930348851716626769314796000375677184055596221926⟩,⟨-984807753012208059366743024589523013670643251719857237281372,-984807753012208059366743024589523013670643251719827188460900⟩⟩
def phaseBox27 : CI := ⟨⟨-16899068771,14436150239⟩,⟨-1000000000000000000000000000000000000000000000000015667611120,-999999999999999999999999999999999999999999999999984332392110⟩⟩
def phaseBox28 : CI := ⟨⟨173648177666930348851716626769314796000375677184051917148030,173648177666930348851716626769314796000375677184084341989196⟩,⟨-984807753012208059366743024589523013670643251719858787552808,-984807753012208059366743024589523013670643251719826493551508⟩⟩
def phaseBox29 : CI := ⟨⟨342020143325668733044099614682259580763083367514142813650362,342020143325668733044099614682259580763083367514175957454200⟩,⟨-939692620785908384054109277324731469936208134264481532580062,-939692620785908384054109277324731469936208134264448638369502⟩⟩
def phaseBox30 : CI := ⟨⟨499999999999999999999999999999999999999999999999982086571115,500000000000000000000000000000000000000000000000015543483824⟩,⟨-866025403784438646763723170752936183471402626905207554081534,-866025403784438646763723170752936183471402626905174442267480⟩⟩
def phaseBox31 : CI := ⟨⟨642787609686539326322643409907263432907559884205664038197821,642787609686539326322643409907263432907559884205697376234924⟩,⟨-766044443118978035202392650555416673935832457080412620035652,-766044443118978035202392650555416673935832457080379689347294⟩⟩
def phaseBox32 : CI := ⟨⟨766044443118978035202392650555416673935832457080377922011624,766044443118978035202392650555416673935832457080410693391161⟩,⟨-642787609686539326322643409907263432907559884205699080092946,-642787609686539326322643409907263432907559884205666736654508⟩⟩
def phaseBox33 : CI := ⟨⟨866025403784438646763723170752936183471402626905173685228535,866025403784438646763723170752936183471402626905205437711262⟩,⟨-500000000000000000000000000000000000000000000000016979488526,-499999999999999999999999999999999999999999999999985627454324⟩⟩
def phaseBox34 : CI := ⟨⟨939692620785908384054109277324731469936208134264448958204507,939692620785908384054109277324731469936208134264479247218206⟩,⟨-342020143325668733044099614682259580763083367514177069829976,-342020143325668733044099614682259580763083367514147101516694⟩⟩
def phaseBox35 : CI := ⟨⟨984807753012208059366743024589523013670643251719827941038041,984807753012208059366743024589523013670643251719856342140171⟩,⟨-173648177666930348851716626769314796000375677184085066392648,-173648177666930348851716626769314796000375677184056852251010⟩⟩
def coeffBox0 (j : Fin 31) : CI := if j.val=0 then CI.point 1 else CI.point 0
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
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def phaseTable : Fin 36 → CI := ![phaseBox0, phaseBox1, phaseBox2, phaseBox3, phaseBox4, phaseBox5, phaseBox6, phaseBox7, phaseBox8, phaseBox9, phaseBox10, phaseBox11, phaseBox12, phaseBox13, phaseBox14, phaseBox15, phaseBox16, phaseBox17, phaseBox18, phaseBox19, phaseBox20, phaseBox21, phaseBox22, phaseBox23, phaseBox24, phaseBox25, phaseBox26, phaseBox27, phaseBox28, phaseBox29, phaseBox30, phaseBox31, phaseBox32, phaseBox33, phaseBox34, phaseBox35]
def phaseModBox (n : ℤ) : CI := phaseTable ⟨(n%36).toNat, by omega⟩

def frequencyBox (j : Fin 31) : CI :=
  ((CI.imag.mul (CI.ofReal piBox)).mul (CI.point ((j.val:ℤ)-15))).divNat 18

def waveDerivativeBox (k : ℕ) (n : ℤ) : CI := CI.sum (fun j : Fin 31 =>
  ((coeffBox15 j).mul ((frequencyBox j).pow k)).mul (phaseModBox (((j.val:ℤ)-15)*n)))

def jetBox2_0 : CI := ⟨⟨2193245422464301915296553555528033585625259535611342042812338,2193245422464301915296553555528033585625273534273468147240545⟩,⟨-6999331474201310627,6999331474198725149⟩⟩
lemma jetBox2_0_calc : waveDerivativeBox 2 0 = jetBox2_0 := by decide +kernel
def QBox0 : RI := ⟨1096622711232150957648276777764016792812629767805671021406169,1096622711232150957648276777764016792812636767136734073620273⟩
lemma QBox0_calc : jetBox2_0.re.divNat 2 = QBox0 := by decide +kernel
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

def damping (q : Fin 2) : ℝ := if q.val=0 then h else H

end AtomicTriangular.Construction

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
-- module Solutions.OAIQ262_TG.Triangular_Construction_L1Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology lp
namespace AtomicTriangular.L1Kernel
variable {α β : Type*}

lemma l1_norm (a : ℓ¹(α,ℝ)) : ‖a‖ = ∑' i, |a i| := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs] using
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ENNReal).toReal) a
lemma l1_summable (a : ℓ¹(α,ℝ)) : Summable (fun i => |a i|) := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using
    a.property.summable (by norm_num : 0 < (1:ENNReal).toReal)

def column (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) : ℓ¹(β,ℝ) :=
  ⟨fun i => K i j, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using hK j⟩
lemma column_norm (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) :
    ‖column K hK j‖ = ∑' i, |K i j| := l1_norm _

variable (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|))
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ j, ∑' i, |K i j| ≤ C)
include C hB
lemma summable_columns (a : ℓ¹(α,ℝ)) :
    Summable (fun j => a j • column K hK j) := by
  apply Summable.of_norm_bounded ((l1_summable a).mul_right C)
  intro j
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _)

omit C hB in
def applyKernel (a : ℓ¹(α,ℝ)) : ℓ¹(β,ℝ) := ∑' j, a j • column K hK j
lemma applyKernel_norm (a : ℓ¹(α,ℝ)) : ‖applyKernel K hK a‖ ≤ C*‖a‖ := by
  have hs : Summable (fun j => ‖a j • column K hK j‖) :=
    ((l1_summable a).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
  calc
    _ ≤ ∑' j, ‖a j • column K hK j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j, |a j| * C := hs.tsum_le_tsum (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
      ((l1_summable a).mul_right C)
    _ = C*‖a‖ := by rw [tsum_mul_right,l1_norm,mul_comm]

lemma applyKernel_add (a b : ℓ¹(α,ℝ)) :
    applyKernel K hK (a+b) = applyKernel K hK a + applyKernel K hK b := by
  simp only [applyKernel,lp.coeFn_add,Pi.add_apply,add_smul]
  exact (summable_columns K hK C hB a).tsum_add (summable_columns K hK C hB b)
lemma applyKernel_smul (r : ℝ) (a : ℓ¹(α,ℝ)) :
    applyKernel K hK (r • a) = r • applyKernel K hK a := by
  simp only [applyKernel,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
  exact (summable_columns K hK C hB a).tsum_const_smul r

def operator : ℓ¹(α,ℝ) →L[ℝ] ℓ¹(β,ℝ) :=
  LinearMap.mkContinuous
    { toFun := applyKernel K hK
      map_add' := applyKernel_add K hK C hB
      map_smul' := fun r a => applyKernel_smul K hK C hB r a }
    C (applyKernel_norm K hK C hB)
include hC in
lemma operator_norm : ‖operator K hK C hB‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (applyKernel_norm K hK C hB)
end AtomicTriangular.L1Kernel
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def frequencyDecay (k v t : ℝ) : ℝ := Real.pi*(k*Xwave k t-v)

end AtomicTriangular.Construction
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
namespace AtomicTriangular.Construction
open Complex

def tailBase (a : Fin 15) : ℤ := residue a + if residue a < 25 then 36 else 0
lemma tailBase_mod (a : Fin 15) : tailBase a % 36 = residue a := by
  fin_cases a <;> (first | (simp [tailBase,residue]; all_goals first | (norm_num [tailBase,residue]; done) | rfl | decide) | (norm_num [tailBase,residue]; done) | norm_num [tailBase,residue])
lemma tailBase_pos (a : Fin 15) : 25 ≤ tailBase a := by
  fin_cases a <;> (first | (simp [tailBase,residue]; all_goals first | (norm_num [tailBase,residue]; done) | rfl | decide) | (norm_num [tailBase,residue]; done) | norm_num [tailBase,residue])

def normJetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+‖I*Real.pi*zeta k v t‖)*‖lambda k t‖*(Q n)⁻¹ *
    Real.exp (-frequencyDecay k v t*n)
end AtomicTriangular.Construction
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

def tailEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  (∑ a : Fin 15, normJetEnvelope (damping q) (damping v) (tailBase a) (frequency j)) *
    (1-Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*36))⁻¹

end AtomicTriangular.Construction
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
lemma residue_injective : Function.Injective residue := by decide +kernel
lemma residue_mod (a : Fin 15) : residue a % 36 = residue a := by revert a; decide +kernel
lemma residue_mem (a : Fin 15) : residue a ∈ residues := by revert a; decide +kernel
lemma finiteNode_lt25 {n : ℤ} (hn : n ∈ FiniteNodes) : n<25 := by
  simp only [FiniteNodes,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h|h|h|h|h|h|h <;> omega
lemma tailBase_node (a : Fin 15) (l : ℕ) :
    0 < tailBase a+36*l ∧ (tailBase a+36*l)%36 ∈ residues := by
  constructor
  · have hh := tailBase_pos a
    omega
  · simpa [Int.add_emod,Int.mul_emod,tailBase_mod,residue_mod] using residue_mem a

def enumerateTail (p : Fin 15 × ℕ) : TailNode :=
  ⟨⟨tailBase p.1+36*p.2,tailBase_node p.1 p.2⟩,by
    intro hh
    have hlt := finiteNode_lt25 hh
    change tailBase p.1+36*(p.2:ℤ)<25 at hlt
    have hge := tailBase_pos p.1
    omega⟩
lemma tailBase_le (n : TailNode) (a : Fin 15) (ha : n.val.val%36=residue a) :
    tailBase a ≤ n.val.val := by
  have hn := n.val.property.1
  have hf := n.property
  have hdiv := Int.emod_add_mul_ediv n.val.val 36
  have hq : 0≤n.val.val/36 := Int.ediv_nonneg hn.le (by norm_num)
  rw [ha] at hdiv
  fin_cases a <;> norm_num [tailBase,residue] at *
  all_goals by_contra hlt
  all_goals have hn' : n.val.val = (n.val.val%36) := by omega
  all_goals simp only [FiniteNodes,Finset.mem_insert,Finset.mem_singleton] at hf
  all_goals omega
lemma enumerateTail_injective : Function.Injective enumerateTail := by
  intro p q hpq
  have hh := congrArg (fun n : TailNode => n.val.val) hpq
  change tailBase p.1+36*p.2=tailBase q.1+36*q.2 at hh
  have hm := congrArg (fun n : ℤ => n%36) hh
  simp only [Int.add_emod,Int.mul_emod,Int.emod_self,zero_mul,Int.zero_emod,
    add_zero,tailBase_mod,residue_mod] at hm
  have ha := residue_injective hm
  apply Prod.ext ha
  rw [ha] at hh
  omega
lemma enumerateTail_surjective : Function.Surjective enumerateTail := by
  intro n
  obtain ⟨a,ha⟩ := node_residue n.val
  have hle := tailBase_le n a ha
  have hm : (n.val.val-tailBase a)%36=0 := by
    rw [Int.sub_emod,ha,tailBase_mod]
    simp
  have hd := Int.emod_add_mul_ediv (n.val.val-tailBase a) 36
  rw [hm,zero_add] at hd
  have hq : 0 ≤ (n.val.val-tailBase a)/36 := Int.ediv_nonneg (sub_nonneg.mpr hle) (by norm_num)
  refine ⟨(a,((n.val.val-tailBase a)/36).toNat),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change tailBase a+36*(((n.val.val-tailBase a)/36).toNat:ℤ)=n.val.val
  rw [Int.toNat_of_nonneg hq]
  omega

def tailEnumeration : (Fin 15 × ℕ) ≃ TailNode :=
  Equiv.ofBijective enumerateTail ⟨enumerateTail_injective,enumerateTail_surjective⟩
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
lemma paired_summable_bound {α : Type*} (K : α → Fin 2 → ℝ) (G : α → ℝ)
    (hG : Summable G) (hdom : ∀ a, (∑ d : Fin 2, |K a d|) ≤ G a) :
    Summable (fun p : α × Fin 2 => |K p.1 p.2|) ∧
      (∑' p : α × Fin 2, |K p.1 p.2|)  ≤  ∑' a, G a := by
  have hs : Summable (fun a => ∑ d : Fin 2, |K a d|) :=
    hG.of_nonneg_of_le (fun a => Finset.sum_nonneg (fun d _ => abs_nonneg _)) hdom
  have hp : Summable (fun p : α × Fin 2 => |K p.1 p.2|) := by
    apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    exact ⟨fun a => (hasSum_fintype _).summable,by simpa only [tsum_fintype] using hs⟩
  refine ⟨hp,?_⟩
  rw [hp.tsum_prod]
  simp only [tsum_fintype]
  exact hs.tsum_le_tsum hdom hG
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_BlockOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel
abbrev TailCoefficients := ℓ¹(TailNode × Fin 2,ℝ)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_Repetition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma pi_eta_pos : 0<Real.pi*eta := mul_pos Real.pi_pos (by norm_num [eta])
def repetitionRatio : ℝ := Real.exp (-36*Real.pi*eta)
def repetitionNorm : ℝ := (1+Real.pi*eta)*repetitionRatio/(1-repetitionRatio)
lemma repetitionRatio_pos : 0 < repetitionRatio := Real.exp_pos _
lemma repetitionRatio_lt : repetitionRatio<1 := by
  rw [repetitionRatio,Real.exp_lt_one_iff]
  nlinarith [pi_eta_pos]

def repetitionEnvelope (a : Fin 11) (n : TailNode) : ℝ :=
  if n.val.val%36=residue ⟨a.val,by omega⟩ then
    (1+Real.pi*eta)*Real.exp (-Real.pi*eta*n.val.val) else 0
lemma repetitionEnvelope_nonneg (a : Fin 11) (n : TailNode) : 0 ≤ repetitionEnvelope a n := by
  unfold repetitionEnvelope
  split_ifs
  · exact mul_nonneg (by linarith [pi_eta_pos]) (Real.exp_pos _).le
  · rfl
lemma repetitionEnvelope_enumerate (a : Fin 11) (r : Fin 15) (l : ℕ) :
    repetitionEnvelope a (enumerateTail (r,l)) =
      if r=⟨a.val,by omega⟩ then
        (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase r)*repetitionRatio^l else 0 := by
  have hm : (enumerateTail (r,l)).val.val%36=residue r := by
    change (tailBase r+36*(l:ℤ))%36=residue r
    simp [Int.add_emod,tailBase_mod,residue_mod]
  unfold repetitionEnvelope
  simp only [hm,residue_injective.eq_iff]
  split_ifs
  · change _ * Real.exp (-Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ)) = _
    rw [show -Real.pi*eta*((tailBase r+36*(l:ℤ):ℤ):ℝ) =
      -Real.pi*eta*(tailBase r:ℝ)+(l:ℝ)*(-36*Real.pi*eta) by push_cast; ring,
      Real.exp_add,Real.exp_nat_mul]
    simp only [repetitionRatio] <;> ring
  · rfl
lemma summable_repetitionEnvelope (a : Fin 11) : Summable (repetitionEnvelope a) := by
  apply tailEnumeration.summable_iff.mp
  apply (summable_prod_of_nonneg (fun p => repetitionEnvelope_nonneg a _)).mpr
  refine ⟨fun r => ?_,(hasSum_fintype _).summable⟩
  change Summable (fun l : ℕ => repetitionEnvelope a (enumerateTail (r,l)))
  simp_rw [repetitionEnvelope_enumerate]
  split_ifs
  · exact (summable_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt).mul_left _
  · exact summable_zero
lemma tsum_repetitionEnvelope (a : Fin 11) :
    (∑' n, repetitionEnvelope a n) =
      (1+Real.pi*eta)*Real.exp (-Real.pi*eta*tailBase ⟨a.val,by omega⟩)/(1-repetitionRatio) := by
  rw [← tailEnumeration.tsum_eq]
  have hs := tailEnumeration.summable_iff.mpr (summable_repetitionEnvelope a)
  change Summable (fun p : Fin 15 × ℕ => repetitionEnvelope a (enumerateTail p)) at hs
  change (∑' p : Fin 15 × ℕ, repetitionEnvelope a (enumerateTail p)) = _
  rw [hs.tsum_prod,tsum_fintype]
  simp_rw [repetitionEnvelope_enumerate]
  have hi (P : Prop) [Decidable P] (f : ℕ → ℝ) :
      (∑' l, if P then f l else 0) = if P then ∑' l, f l else 0 := by
    by_cases hh : P <;> simp [hh]
  simp_rw [hi]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte,tsum_mul_left,
    tsum_geometric_of_lt_one repetitionRatio_pos.le repetitionRatio_lt,div_eq_mul_inv]
lemma repetitionEnvelope_bound (a : Fin 11) : (∑' n, repetitionEnvelope a n) ≤ repetitionNorm := by
  rw [tsum_repetitionEnvelope]
  have ht : 36 ≤ tailBase ⟨a.val,by omega⟩ := by revert a; decide +kernel
  have he : Real.exp (-Real.pi*eta*(tailBase ⟨a.val,by omega⟩:ℝ)) ≤ repetitionRatio := by
    unfold repetitionRatio
    apply Real.exp_le_exp.mpr
    have ht' : (36:ℝ) ≤ (tailBase ⟨a.val,by omega⟩:ℝ) := by exact_mod_cast ht
    nlinarith [pi_eta_pos]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr repetitionRatio_lt).le
  exact mul_le_mul_of_nonneg_left he (by linarith [pi_eta_pos])

def repetitionEntry (c d : Fin 2) : ℝ :=
  if c.val=0 then if d.val=0 then 1 else -Real.pi*eta
  else if d.val=0 then 0 else 1
lemma repetitionEntry_bound (c : Fin 2) : (∑ d : Fin 2, |repetitionEntry c d|) ≤ 1+Real.pi*eta := by
  fin_cases c <;> norm_num [Fin.sum_univ_succ,repetitionEntry,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num [eta] : 0<eta)]
  exact pi_eta_pos.le
def repetitionKernel (p : TailNode × Fin 2) (a : Fin 11) (c : Fin 2) : ℝ :=
  if p.1.val.val%36=residue ⟨a.val,by omega⟩ then
    Real.exp (-Real.pi*eta*p.1.val.val)*repetitionEntry c p.2 else 0
lemma repetitionKernel_pair (a : Fin 11) (c : Fin 2) (n : TailNode) :
    (∑ d : Fin 2, |repetitionKernel (n,d) a c|) ≤ repetitionEnvelope a n := by
  unfold repetitionKernel repetitionEnvelope
  split_ifs with hh
  · simp only [abs_mul,abs_of_pos (Real.exp_pos _),←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (repetitionEntry_bound c) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · simp
lemma repetitionKernel_bounds (a : Fin 11) (c : Fin 2) :
    Summable (fun p => |repetitionKernel p a c|) ∧
      (∑' p, |repetitionKernel p a c|) ≤ repetitionNorm := by
  obtain ⟨hs,hb⟩ := paired_summable_bound (fun n d => repetitionKernel (n,d) a c)
    (repetitionEnvelope a) (summable_repetitionEnvelope a) (repetitionKernel_pair a c)
  exact ⟨hs,hb.trans (repetitionEnvelope_bound a)⟩
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Construction_RepetitionOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma repetitionNorm_nonneg : 0 ≤ repetitionNorm := by
  unfold repetitionNorm
  exact div_nonneg (mul_nonneg (by linarith [pi_eta_pos]) repetitionRatio_pos.le)
    (sub_pos.mpr repetitionRatio_lt).le
abbrev TrigonometricCoefficients := ℓ¹(Fin 22,ℝ)
def AallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  repetitionKernel p ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩
def AallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator AallKernel (fun _ => (repetitionKernel_bounds _ _).1) repetitionNorm
    (fun _ => (repetitionKernel_bounds _ _).2)
lemma AallOperator_norm : ‖AallOperator‖ ≤ repetitionNorm :=
  operator_norm _ _ _ repetitionNorm_nonneg _
def CallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val,by omega⟩)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Schwartz_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

lemma polynomial_gaussian_bound {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → (1+r)^m * Real.exp (-c*r^2) ≤ C := by
  let B : ℝ := 2+c⁻¹
  refine ⟨B^m*(m.factorial:ℝ)*Real.exp 1, by positivity, ?_⟩
  intro r hr
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have h : 1+r ≤ B*(1+c*r^2) := by
    dsimp [B]
    have hsq := sq_nonneg (r-1)
    have hmul : c⁻¹*c=1 := inv_mul_cancel₀ hc.ne'
    nlinarith [sq_nonneg r, mul_nonneg hc.le (sq_nonneg r)]
  have hp : (1+c*r^2)^m ≤ (m.factorial:ℝ)*Real.exp (1+c*r^2) := by
    have hh := Real.pow_div_factorial_le_exp (1+c*r^2) (by positivity : 0 ≤ 1+c*r^2) m
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (m.factorial : ℝ))).mp hh |>.trans_eq (mul_comm _ _)
  calc
    (1+r)^m * Real.exp (-c*r^2) ≤ (B*(1+c*r^2))^m * Real.exp (-c*r^2) := by gcongr
    _ = B^m * ((1+c*r^2)^m * Real.exp (-c*r^2)) := by rw [mul_pow]; ring
    _ ≤ B^m * (((m.factorial:ℝ)*Real.exp (1+c*r^2))*Real.exp (-c*r^2)) := by gcongr
    _ = B^m*(m.factorial:ℝ)*Real.exp 1 := by
      rw [mul_assoc (m.factorial:ℝ), ← Real.exp_add]
      rw [show 1+c*r^2 + -c*r^2 = 1 by ring]
      ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gaussian_schwartz_decay {c : ℝ} (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖^k * ‖iteratedFDeriv ℝ n (fun y : E => Real.exp (-c*‖y‖^2)) x‖ ≤ C := by
  have ht : (fun x : E => -c*‖x‖^2).HasTemperateGrowth := by fun_prop
  obtain ⟨l,B,hB,hder⟩ := ht.norm_iteratedFDeriv_le_uniform n
  obtain ⟨C,hC,hCbound⟩ := polynomial_gaussian_bound hc (k+l*n)
  refine ⟨(n.factorial:ℝ)*(B+1)^n*C, fun x => ?_⟩
  have hw : 1 ≤ (B+1)*(1+‖x‖)^l := by
    have hh : 1 ≤ (1+‖x‖)^l := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith
  have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun x : E => -c*‖x‖^2) x‖ ≤ ((B+1)*(1+‖x‖)^l)^i := by
    calc
      _ ≤ B*(1+‖x‖)^l := hder i hin x
      _ ≤ (B+1)*(1+‖x‖)^l := by gcongr; linarith
      _ ≤ ((B+1)*(1+‖x‖)^l)^i := le_self_pow₀ hw (by omega)
  have hexp (i : ℕ) (_hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i Real.exp (-c*‖x‖^2)‖ ≤ Real.exp (-c*‖x‖^2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp]
    exact le_of_eq (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hd := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp ht.1 (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) x hexp hD
  calc
    _ ≤ ‖x‖^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (1+‖x‖)^k * ((n.factorial:ℝ)*Real.exp (-c*‖x‖^2)*((B+1)*(1+‖x‖)^l)^n) := by gcongr; linarith
    _ = (n.factorial:ℝ)*(B+1)^n*((1+‖x‖)^(k+l*n)*Real.exp (-c*‖x‖^2)) := by
      rw [mul_pow,pow_add,pow_mul]
      ring
    _ ≤ (n.factorial:ℝ)*(B+1)^n*C := by gcongr; exact hCbound ‖x‖ (norm_nonneg _)

def gaussianSchwartz (c : ℝ) (hc : 0 < c) : 𝓢(E,ℝ) where
  toFun x := Real.exp (-c*‖x‖^2)
  smooth' := Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
  decay' := gaussian_schwartz_decay hc

@[simp] lemma gaussianSchwartz_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gaussianSchwartz c hc x = Real.exp (-c*‖x‖^2) := rfl

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

def dampedEntireSchwartz (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (_hf : Differentiable ℂ f) (_hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) : 𝓢(E,ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : E => (f (b*‖x‖^2)).re) (gaussianSchwartz c hc)

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end AtomicTriangular.Analysis
end

end OAI
end


