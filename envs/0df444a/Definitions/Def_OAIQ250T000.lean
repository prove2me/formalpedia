-- Prove2me | Definitions.Def_OAIQ250T000
-- name    : OAIQ250T000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:07:04.206193+00:00
-- url     : https://prove2.me/theorems/8516402b-d8ac-4833-9c19-464e0bf738b8
-- title:
--   Definitions bundle OAIQ250T000 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 481 declarations of OpenAI's Lean: 161 definitions, 2 inductive types or structures, 1 instance and 317 theorems. The definitions and types are `OAI.AtomicTriangular.Analysis.dampedEntireSchwartz`, `OAI.AtomicTriangular.Analysis.gaussianSchwartz`, `OAI.AtomicTriangular.Bernstein.bernsteinBasis`, `OAI.AtomicTriangular.Bernstein.bernsteinCoefficient`, `OAI.AtomicTriangular.Constants.arctanPoly`, `OAI.AtomicTriangular.Constants.bStar`, `OAI.AtomicTriangular.Constants.eps`, `OAI.AtomicTriangular.Constants.pStar`, `OAI.AtomicTriangular.Construction.AallKernel`, `OAI.AtomicTriangular.Construction.AallOperator`, `OAI.AtomicTriangular.Construction.CallKernel`, `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients`, `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.enumerateTail`, `OAI.AtomicTriangular.Construction.frequencyDecay`, `OAI.AtomicTriangular.Construction.normJetEnvelope`, `OAI.AtomicTriangular.Construction.repetitionEntry`, `OAI.AtomicTriangular.Construction.repetitionEnvelope`, `OAI.AtomicTriangular.Construction.repetitionKernel`, `OAI.AtomicTriangular.Construction.repetitionNorm`, `OAI.AtomicTriangular.Construction.repetitionRatio`, `OAI.AtomicTriangular.Construction.tailBase`, `OAI.AtomicTriangular.Construction.tailEnumeration`, `OAI.AtomicTriangular.Construction.tailEnvelopeSum`, `OAI.AtomicTriangular.Construction.tailFiniteEnvelope`, `OAI.AtomicTriangular.FiniteCertificate.QBox0`, `OAI.AtomicTriangular.FiniteCertificate.QBox1`, `OAI.AtomicTriangular.FiniteCertificate.QBox12`, `OAI.AtomicTriangular.FiniteCertificate.QBox13`, `OAI.AtomicTriangular.FiniteCertificate.QBox16`, `OAI.AtomicTriangular.FiniteCertificate.QBox19`, `OAI.AtomicTriangular.FiniteCertificate.QBox21`, `OAI.AtomicTriangular.FiniteCertificate.QBox25`, `OAI.AtomicTriangular.FiniteCertificate.QBox27`, `OAI.AtomicTriangular.FiniteCertificate.QBox28`, `OAI.AtomicTriangular.FiniteCertificate.QBox3`, `OAI.AtomicTriangular.FiniteCertificate.QBox31`, `OAI.AtomicTriangular.FiniteCertificate.QBox4`, `OAI.AtomicTriangular.FiniteCertificate.QBox7` and 123 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Triangular_Auxiliary_Bernstein`, `Triangular_Certificate_TargetInterval`, `Triangular_Certificate_WaveIntervals`, `Triangular_Construction_BlockOperators`, `Triangular_Construction_L1Kernel`, `Triangular_Construction_PeriodicJets`, `Triangular_Construction_Repetition`, `Triangular_Construction_RepetitionOperators`, `Triangular_Construction_TailEnumeration`, `Triangular_Envelope_Analytic`, `Triangular_Envelope_EnvelopeBoxes`, `Triangular_Envelope_EnvelopeNorm0`, `Triangular_Envelope_EnvelopeNorm1`, `Triangular_Envelope_EnvelopeNorm2`, `Triangular_Envelope_EnvelopeSums`, `Triangular_Envelope_EnvelopeSumsBase`, `Triangular_Envelope_JetEnvelopeAnalytic`, `Triangular_Envelope_KernelBounds`, `Triangular_Envelope_TailEnvelopeSeries`, `Triangular_Schwartz_Gaussian`, `Triangular_Schwartz_SpectralCLM`.
--
--   **Imports.** It imports the published bundle `Def_AtomicGaussian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ250T003`, `OAIQ250T004`, `OAIQ250T005`, `OAIQ250T006`, `OAIQ250T007`, `OAIQ250T008`, `OAIQ250T009`, `OAIQ250T010`, `OAIQ250T011`, `OAIQ250T012`, `OAIQ250T013`, `OAIQ250T014`, `OAIQ250T015`, `OAIQ250T016`, `OAIQ250T017`, `OAIQ250T018`, `OAIQ250T019`, `OAIQ250T020`, `OAIQ250T021`, `OAIQ250T022`, `OAIQ250T023`, `OAIQ250T024`, `OAIQ250T025`, `OAIQ250T026`, `OAIQ250T027`, `OAIQ250T028`, `OAIQ250T029`, `OAIQ250T030`, `OAIQ250T031`, `OAIQ250T032`, `OAIQ250T033`, `OAIQ250T034`, `OAIQ250T035`, `OAIQ250T036`, `OAIQ250T037`, `OAIQ250T038`, `OAIQ250T039`, `OAIQ250T040`, `OAIQ250T041`, `OAIQ250T042`, `OAIQ250T043`, `OAIQ250T044`, `OAIQ250T045` and `OAIQ250T046`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_AtomicGaussian

section
-- module Solutions.OAIQ250_TR.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Auxiliary_Bernstein
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_L1Kernel
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

def restPolynomial (a : Fin 15) : Polynomial ℂ :=
  ∏ r ∈ Finset.univ.erase a, atomFactor r

end AtomicTriangular.FiniteCertificate

noncomputable section
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Polynomial Complex
def kappaBox : CI := (CI.ofReal piBox).divNat 36
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

def damping (q : Fin 2) : ℝ := if q.val=0 then h else H
lemma damping_pos (q : Fin 2) : 0 < damping q := by
  unfold damping h H
  split_ifs <;> norm_num

lemma waveDen_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < waveDen k t := by
  unfold waveDen
  positivity

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

lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]

def frequencyDecay (k v t : ℝ) : ℝ := Real.pi*(k*Xwave k t-v)

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_JetEnvelopeAnalytic
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

lemma frequency_mem (l : Fin 31) : frequency l ∈ Set.Icc (-(5/6):ℝ) (5/6) := by
  unfold frequency
  have hn : (l.val:ℝ) ≤ 30 := by exact_mod_cast (show l.val ≤ 30 by omega)
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) l.val]

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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm0
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm1
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
def columnNorm13 : Fin 31 → RI := ![⟨87266462599716478846184538424430635672143594427026719566427,87266462599716478846184538424430635672143594427145780436766⟩,⟨174532925199432957692369076848861271344287188852978558297337,174532925199432957692369076848861271344287188855365162313097⟩,⟨230885357835168934485899363490153922498509522292574296940320,230885357835168934485899363490153922498509522327159545890907⟩,⟨174532925199432957692369076848861271344287188744343821854373,174532925199432957692369076848861271344287188963999663950379⟩,⟨0,1414213562373095048801688724210⟩,⟨0,1414213562373095048801688724210⟩,⟨151149947019518154216173188136846311023672164513026125869383,151149947019518154216173188136846311023672210169097428062132⟩,⟨302299894039036308432346376273692622047344306213072256927691,302299894039036308432346376273692622047344443151174454817808⟩,⟨151149947019518154216173188136846311023671928416162477585031,151149947019518154216173188136846311023672446265956304480935⟩,⟨174532925199432957692369076848861271344285924456530104199805,174532925199432957692369076848861271344288453251815718259547⟩,⟨380385691632435860067260086363184803408494087704397494847973,380385691632435860067260086363184803408503011600639873023456⟩,⟨174532925199432957692369076848861271344272503349991987155413,174532925199432957692369076848861271344301874358348317435985⟩,⟨174532925199432957692369076848861271344251382031166780598903,174532925199432957692369076848861271344322995677180525843985⟩,⟨302299894039036308432346376273692622047182406647582592869491,302299894039036308432346376273692622047506342716664002963577⟩,⟨544978884262538087892363837944813523343079994361431449402637,544978884262538087892363837944813523344028435613062704136014⟩,⟨302299894039036308432346376273692622046052191356680549619521,302299894039036308432346376273692622048636558007558337978788⟩,⟨544978884262538087892363837944813523338393118620393501810697,544978884262538087892363837944813523348715311354100651686964⟩,⟨302299894039036308432346376273692622028142669294568605949327,302299894039036308432346376273692622066546080069677989887093⟩,⟨174532925199432957692369076848861271297929654165010479167314,174532925199432957692369076848861271390644723543336827242483⟩,⟨174532925199432957692369076848861271135446712381203468448080,174532925199432957692369076848861271553127665327136836105299⟩,⟨380385691632435860067260086363184802703145358738520849106200,380385691632435860067260086363184804113851740566516518767617⟩,⟨174532925199432957692369076848861269072938203717982501013505,174532925199432957692369076848861273615636173990363321456439⟩,⟨151149947019518154216173188136846305540150575821861605064925,151149947019518154216173188136846316507193798860257176971349⟩,⟨302299894039036308432346376273692603963364222640912838206723,302299894039036308432346376273692640131324526723333873511377⟩,⟨151149947019518154216173188136846229555633860217376108217405,151149947019518154216173188136846392491710514464747445741358⟩,⟨0,1414213562373095048801688724210⟩,⟨0,1414213562373095048801688724210⟩,⟨174532925199432957692369076848859132240449182016123234944909,174532925199432957692369076848863410448125195692220250889703⟩,⟨230885357835168934485899363490144947493544076251031452819880,230885357835168934485899363490162897503474968368702390017701⟩,⟨174532925199432957692369076848838006465750014813292203511686,174532925199432957692369076848884536222824362895051517076869⟩,⟨87266462599716478846184538424353910962996786061774588876937,87266462599716478846184538424507360381290402792397911096365⟩]
def columnNorm14 : Fin 31 → RI := ![⟨0,1414213562373095048801688724210⟩,⟨30461741978670859934674354937889355355906479651955782912206,30461741978670859934674354937889355355906479651999682941166⟩,⟨69888549636684381842593080915506036251148515862805061470874,69888549636684381842593080915506036251148515863698056910564⟩,⟨98514840691397729107567818413642907001502071614187395360483,98514840691397729107567818413642907001502071622956494066527⟩,⟨109714457820694066552354641345627755790800223114832012988128,109714457820694066552354641345627755790800223174407984591619⟩,⟨91047325504087586891830866890603602017492643345971266381836,91047325504087586891830866890603602017492643823440270880869⟩,⟨132642816899682796868632841511304299366114918196558908244523,132642816899682796868632841511304299366114920163742554463971⟩,⟨139958158981533001999311756673922706708176654596765654341026,139958158981533001999311756673922706708176667106198114547921⟩,⟨115091701996640668486247594326219733605709440762344381554351,115091701996640668486247594326219733605709492245746428105691⟩,⟨75288504364019780311185132435958781212353232239939850151045,75288504364019780311185132435958781212353425583637088403194⟩,⟨93529642382435028475622107508596000286211732570082246538723,93529642382435028475622107508596000286212279262102862474680⟩,⟨199943506105011662034385329904920055459486255546284140206249,199943506105011662034385329904920055459488690958433279250706⟩,⟨122536253588045453021064722706002204514928761301237364373756,122536253588045453021064722706002204514937397531918357225316⟩,⟨201764191783732811109075479503783892905317191251126785137440,201764191783732811109075479503783892905344794710159563267386⟩,⟨204378985572639053835977128596719525065310468451675698615362,204378985572639053835977128596719525065402734987924657466258⟩,⟨361977890262483171833229981609085417805657015812970977097238,361977890262483171833229981609085417805899608767183252625571⟩,⟨204378985572639053835977128596719525064822395184344947834999,204378985572639053835977128596719525065890808255255408204599⟩,⟨201764191783732811109075479503783892903477843815991595428971,201764191783732811109075479503783892907184142145294752935675⟩,⟨122536253588045453021064722706002204508184514320835690623839,122536253588045453021064722706002204521681644512320030983328⟩,⟨199943506105011662034385329904920055437141779525287827972587,199943506105011662034385329904920055481833166979429591429016⟩,⟨93529642382435028475622107508596000226269764937597592817345,93529642382435028475622107508596000346154246894587516124316⟩,⟨75288504364019780311185132435958780950907097437003827731577,75288504364019780311185132435958781473799560386573110723604⟩,⟨115091701996640668486247594326219732702207309673566458992571,115091701996640668486247594326219734509211623334524350669474⟩,⟨139958158981533001999311756673922703635095818405185127960933,139958158981533001999311756673922709781257503297778640833350⟩,⟨132642816899682796868632841511304291850680362157253939188289,132642816899682796868632841511304306881549476203047523418257⟩,⟨91047325504087586891830866890603569374627016658146409543878,91047325504087586891830866890603634660358270511265127584079⟩,⟨109714457820694066552354641345627668176135538776378471146619,109714457820694066552354641345627843405464907512861526319364⟩,⟨98514840691397729107567818413642552758125998716706942123606,98514840691397729107567818413643261244878144520436947152391⟩,⟨69888549636684381842593080915504637473454599413157633326911,69888549636684381842593080915507435028842432313345484899731⟩,⟨30461741978670859934674354937884615907135912224374479867521,30461741978670859934674354937894094804677047079580985918701⟩,⟨0,1414213562373095048801688724210⟩]
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
def columnNorm16 : Fin 31 → RI := ![⟨0,1414213562373095048801688724210⟩,⟨30461741978670859934674354937889355355906479651959487677337,30461741978670859934674354937889355355906479651995978175986⟩,⟨93340192681939659953812544564663728666758123701663536299013,93340192681939659953812544564663728666758123702232168215415⟩,⟨155081640769000344479309199852116367956661071278869038038094,155081640769000344479309199852116367956661071285548564447059⟩,⟨262008186045164535796354191411546328142616276041760154708411,262008186045164535796354191411546328142616276096211589369281⟩,⟨296609937675440629276389446590607762803870626780568793470555,296609937675440629276389446590607762803870627124833503123640⟩,⟨356606773056001870513426986053960204279573353752931927081307,356606773056001870513426986053960204279573355931294038060905⟩,⟨444635109378071297956976477548108704914038393719630132718418,444635109378071297956976477548108704914038403661993804162845⟩,⟨611622293554807824704755128638466195546677156670503407160883,611622293554807824704755128638466195546677191756793949977106⟩,⟨804450329813742288237570478876009483007164456491919332016474,804450329813742288237570478876009483007164571562137079877323⟩,⟨897022583737670694832519360546670034193440768493918047841184,897022583737670694832519360546670034193441134643125691421078⟩,⟨969241755484870500377835554632446386891487459785452158636872,969241755484870500377835554632446386891488825597904804619719⟩,⟨946040908846589944965973824606364188146936387473699437279545,946040908846589944965973824606364188146941280311813986719524⟩,⟨1124920954993481040239322356409313499982332761784983528204941,1124920954993481040239322356409313499982347634113004608359165⟩,⟨1198828082154592168512249196410530205253283184155255100553960,1198828082154592168512249196410530205253323126091148361792976⟩,⟨1369448924088595957991831509245547466286884315921547727343605,1369448924088595957991831509245547466286988887405638699606789⟩,⟨1198828082154592168512249196410530205253111517729614782610607,1198828082154592168512249196410530205253494792516788679786797⟩,⟨1124920954993481040239322356409313499981653784282945771647924,1124920954993481040239322356409313499983026611615042365033357⟩,⟨946040908846589944965973824606364188144752439421592498314177,946040908846589944965973824606364188149125228363920925865179⟩,⟨969241755484870500377835554632446386885499012263999038491999,969241755484870500377835554632446386897477273119357925025169⟩,⟨897022583737670694832519360546670034177291053375594156016968,897022583737670694832519360546670034209590849761449583543639⟩,⟨804450329813742288237570478876009482953986104255728120020452,804450329813742288237570478876009483060342923798328292217777⟩,⟨611622293554807824704755128638466195366008305485129701644703,611622293554807824704755128638466195727346042942167655837788⟩,⟨444635109378071297956976477548108704292219229618878264797638,444635109378071297956976477548108705535857567762745672516749⟩,⟨356606773056001870513426986053960202423385845173851443983568,356606773056001870513426986053960206135760864510374521625089⟩,⟨296609937675440629276389446590607758167157801274154361145370,296609937675440629276389446590607767440583452631247935997705⟩,⟨262008186045164535796354191411546314117750263324647719362412,262008186045164535796354191411546342167482288813324025152504⟩,⟨155081640769000344479309199852116325742900782055088996625603,155081640769000344479309199852116410170421360509328606115763⟩,⟨93340192681939659953812544564663603907264493499834654159017,93340192681939659953812544564663853426251753904061050384676⟩,⟨30461741978670859934674354937888860554748467701312498632542,30461741978670859934674354937889850157064491602642966655120⟩,⟨0,1414213562373095048801688724210⟩]
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

def tailEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  (∑ a : Fin 15, normJetEnvelope (damping q) (damping v) (tailBase a) (frequency j)) *
    (1-Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*36))⁻¹

def tailFiniteEnvelope (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, tailEnvelopeSum 1 0 j * ‖finiteColumn ⟨c.val,by omega⟩ j‖
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
def boundC : Fin 22 → RI := ![⟨6983430325648370090762786336118446593363754,6983430325648370090762786446578740417141912⟩,⟨6856113601763651669234484249463260417292237909,6856113601763651669234484249463263003483720803⟩,⟨6980275474701897361264833427827823165781882,6980275474701897361264833538288127294569656⟩,⟨6849926501624327130340125007838659162779128828,6849926501624327130340125007838751568239066090⟩,⟨6973598786895930262447651247794129162920230,6973598786895930262447651358254938264699275⟩,⟨6836835820083327838570406946101411437962929601,6836835820083327838570406946107411399810476915⟩,⟨6970127717751114871303779034145933886275183,6970127717751114871303779144607310934352254⟩,⟨6830032419816511259075261648126221145691191044,6830032419816511259075261648139565050473184385⟩,⟨6966603083247449730494732527001762407925335,6966603083247449730494732637462168998477775⟩,⟨6823126181462009803004838304747855282887858411,6823126181462009803004838304749027480297356046⟩,⟨6973598786155837885597122670431812071336839,6973598786155837885597122780892105895067075⟩,⟨6836835803450007218291346535708063526022658801,6836835803450007218291346535708066111748162278⟩,⟨6983430319365317341592722342903761446494632,6983430319365317341592722453364570599057920⟩,⟨6856113562673563870668110733543919108677854686,6856113562673563870668110733549917183576988372⟩,⟨6986430469537304015669954082576071774519466,6986430469537304015669954193037449039042045⟩,⟨6861998095658831191648932715642117935687677355,6861998095658831191648932715655459086026521348⟩,⟨6994280707523134943003159481072253806359477,6994280707523134943003159591532660388642822⟩,⟨6877399299610182510026301010869972298375284114,6877399299610182510026301010871144536623494991⟩,⟨7000003726719105447955797071924050152776533,7000003726719105447955797182384354282597204⟩,⟨6888630442760375097555168696099136027582442669,6888630442760375097555168696099228441876634200⟩,⟨7002436798840667900299665935692288640605379,7002436798840667900299666046153097865828986⟩,⟨6893406056783168904034913493915297148668338947,6893406056783168904034913493921298545869113913⟩]
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_TailEnumeration
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_TailEnvelopeSeries
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
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

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetEnvt48 : RI := ⟨35940479,35940482⟩
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
open AtomicTriangular.L1Kernel
abbrev TailCoefficients := ℓ¹(TailNode × Fin 2,ℝ)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Repetition
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
-- module Solutions.OAIQ250_TR.Triangular_Construction_RepetitionOperators
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
-- module Solutions.OAIQ250_TR.Triangular_Schwartz_Gaussian
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


