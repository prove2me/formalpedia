-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogTwo_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogTwo_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:19:00.45998+00:00
-- url     : https://prove2.me/theorems/dbcd410a-1707-405e-83f7-d70e8253d98a
-- title:
--   FLT.Assumptions.MazurProof.N13LocalDlogTwo source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LocalDlogTwo

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LocalDlogTwo
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_RamifiedDlog_p0

set_option autoImplicit false




/-!
# The first ramified local character for N13 at two

Let `π = 1 - i`.  The first ramified quotient of the unramified cubic
extension of `ℚ₂(i)` is the dual-number ring

`𝔽₈[ε] / (ε²)`, where `𝔽₈ = 𝔽₂[α] / (α³ + α + 1)`.

This file formalizes the finite algebra in that quotient.  The logarithm
`a + εb ↦ b / a`, including its descent through squares and scalar units,
is supplied by `RamifiedDlog`.  Here we calculate the four N13 generator
jets and prove structurally that vanishing of the resulting `𝔽₈` character
leaves exactly the two candidates `(0, 0, s, s)`.
-/

open Polynomial
open scoped CharTwo

namespace MazurProof.N13LocalDlogTwo

noncomputable section

/-! ## The residue field -/

/-- The residue polynomial of the N13 cubic at the prime above two. -/
def residueCubic : (ZMod 2)[X] :=
  X ^ 3 + X + 1

theorem residueCubic_monic : residueCubic.Monic := by
  unfold residueCubic
  monicity!

theorem residueCubic_natDegree : residueCubic.natDegree = 3 := by
  unfold residueCubic
  compute_degree!

theorem residueCubic_irreducible : Irreducible residueCubic := by
  have eval_zero : residueCubic.eval (0 : ZMod 2) = 1 := by
    simp only [residueCubic, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  have eval_one : residueCubic.eval (1 : ZMod 2) = 1 := by
    simp only [residueCubic, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    simp only [one_pow, CharTwo.add_self_eq_zero, zero_add]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, residueCubic_natDegree]
    omega
  · intro x
    change residueCubic.eval x ≠ 0
    fin_cases x
    · exact fun h => one_ne_zero (eval_zero.symm.trans h)
    · exact fun h => one_ne_zero (eval_one.symm.trans h)

instance residueCubicIrreducibleFact :
    Fact (Irreducible residueCubic) :=
  ⟨residueCubic_irreducible⟩

/-- The degree-three residue field at two. -/
abbrev F8 : Type :=
  AdjoinRoot residueCubic

instance instCharPF8OfNatNat : CharP F8 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

/-- The residue of the cubic generator. -/
def alpha : F8 :=
  AdjoinRoot.root residueCubic

theorem alpha_relation :
    alpha ^ 3 + alpha + 1 = 0 := by
  change AdjoinRoot.mk residueCubic (X ^ 3 + X + 1) = 0
  rw [← residueCubic, AdjoinRoot.mk_self]

theorem charTwo : (2 : F8) = 0 :=
  CharP.cast_eq_zero F8 2

@[simp] theorem alpha_cubed :
    alpha ^ 3 = alpha + 1 := by
  have h : alpha ^ 3 + (alpha + 1) = 0 := by
    simpa only [add_assoc] using alpha_relation
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h

@[simp] theorem alpha_pow_four :
    alpha ^ 4 = alpha ^ 2 + alpha := by
  calc
    alpha ^ 4 = alpha * alpha ^ 3 := by ring
    _ = alpha * (alpha + 1) := by rw [alpha_cubed]
    _ = alpha ^ 2 + alpha := by ring

theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  have hm : alpha ^ 3 + alpha = 0 := by rw [h]; norm_num
  have hone : (1 : F8) = 0 := by
    linear_combination alpha_relation - hm
  exact one_ne_zero hone

theorem alpha_ne_one : alpha ≠ 1 := by
  intro h
  have hr := alpha_relation
  rw [h] at hr
  have hone : (1 : F8) = 0 := by
    linear_combination hr - charTwo
  exact one_ne_zero hone

theorem alpha_sq_add_one_ne_zero : alpha ^ 2 + 1 ≠ 0 := by
  intro h
  have hm : alpha ^ 3 + alpha = 0 := by
    calc
      alpha ^ 3 + alpha = alpha * (alpha ^ 2 + 1) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hone : (1 : F8) = 0 := by
    linear_combination alpha_relation - hm
  exact one_ne_zero hone

theorem alpha_sq_add_alpha_add_one_ne_zero :
    alpha ^ 2 + alpha + 1 ≠ 0 := by
  intro h
  have hfac : alpha ^ 2 * (alpha - 1) = 0 := by
    linear_combination alpha_relation - h
  rcases mul_eq_zero.mp hfac with ha | ha
  · exact (pow_ne_zero 2 alpha_ne_zero) ha
  · exact alpha_ne_one (sub_eq_zero.mp ha)

/-! ## The four generator jets -/

abbrev JetUnit : Type :=
  (DualNumber F8)ˣ

/--
The first-order reduction of `ζ = i`, under `i ↦ 1 + ε`.
-/
def zetaJet : JetUnit :=
  RamifiedDlog.unitOf 1 1 one_ne_zero

/--
The first-order reduction of
`e₁ = 1 - θ² + (i - 1)θ`.
-/
def e1Jet : JetUnit :=
  RamifiedDlog.unitOf (alpha ^ 2 + 1) alpha
    alpha_sq_add_one_ne_zero

/--
The first-order reduction of
`e₂ = 1 + iθ² + (1 + 2i)θ`.
-/
def e2Jet : JetUnit :=
  RamifiedDlog.unitOf
    (alpha ^ 2 + alpha + 1) (alpha ^ 2)
    alpha_sq_add_alpha_add_one_ne_zero

/--
The first-order reduction of
`a = 1 - iθ² - (1 + i)θ`.
-/
def aJet : JetUnit :=
  RamifiedDlog.unitOf
    (alpha ^ 2 + 1) (alpha ^ 2 + alpha)
    alpha_sq_add_one_ne_zero

/--
The first-order reduction of the rational Gaussian factor `q = 2 - 3i`.
-/
def qJet : JetUnit :=
  RamifiedDlog.unitOf 1 1 one_ne_zero

theorem dlog_zeta :
    RamifiedDlog.dlog zetaJet = 1 := by
  simp [zetaJet]

theorem dlog_e1 :
    RamifiedDlog.dlog e1Jet = alpha ^ 2 := by
  rw [e1Jet, RamifiedDlog.dlog_unitOf,
    div_eq_iff alpha_sq_add_one_ne_zero]
  calc
    alpha = (alpha ^ 2 + alpha) + alpha ^ 2 := by
      rw [add_comm (alpha ^ 2) alpha]
      exact (CharTwo.add_cancel_right alpha (alpha ^ 2)).symm
    _ = alpha ^ 4 + alpha ^ 2 := by rw [alpha_pow_four]
    _ = alpha ^ 2 * (alpha ^ 2 + 1) := by ring

theorem dlog_e2 :
    RamifiedDlog.dlog e2Jet = alpha + alpha ^ 2 := by
  rw [e2Jet, RamifiedDlog.dlog_unitOf,
    div_eq_iff alpha_sq_add_alpha_add_one_ne_zero]
  calc
    alpha ^ 2 = (alpha ^ 2 + alpha) + alpha := by
      exact (CharTwo.add_cancel_right (alpha ^ 2) alpha).symm
    _ = alpha ^ 4 + alpha := by rw [alpha_pow_four]
    _ = alpha ^ 4 + 2 * alpha ^ 3 + 2 * alpha ^ 2 + alpha := by
      rw [charTwo]
      ring
    _ = (alpha + alpha ^ 2) * (alpha ^ 2 + alpha + 1) := by
      ring

theorem dlog_a :
    RamifiedDlog.dlog aJet = 1 + alpha + alpha ^ 2 := by
  rw [aJet, RamifiedDlog.dlog_unitOf,
    div_eq_iff alpha_sq_add_one_ne_zero]
  calc
    alpha ^ 2 + alpha =
        (alpha ^ 2 + alpha) + ((alpha + 1) + (alpha + 1)) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
    _ = (alpha ^ 2 + alpha) + (alpha + 1) + alpha + 1 := by
      ac_rfl
    _ = alpha ^ 4 + alpha ^ 3 + alpha + 1 := by
      rw [alpha_pow_four, alpha_cubed]
    _ = alpha ^ 4 + alpha ^ 3 + 2 * alpha ^ 2 + alpha + 1 := by
      rw [charTwo]
      ring
    _ = (1 + alpha + alpha ^ 2) * (alpha ^ 2 + 1) := by
      ring

theorem dlog_q :
    RamifiedDlog.dlog qJet = 1 := by
  simp [qJet]

theorem dlog_aq :
    RamifiedDlog.dlog (aJet * qJet) = alpha + alpha ^ 2 := by
  rw [RamifiedDlog.dlog_mul, dlog_a, dlog_q]
  have htwo := charTwo
  linear_combination htwo

/-! ## Structural collapse of the candidate space -/

/--
The logarithm of the candidate
`ζⁱ e₁ʲ e₂ᵏ (aq)ˢ`, collected in the basis `1, α, α²`.
-/
def candidateDlog (i j k s : ZMod 2) : F8 :=
  (i : F8) + ((k + s : ZMod 2) : F8) * alpha +
    ((j + k + s : ZMod 2) : F8) * alpha ^ 2

/--
The collected formula is precisely the linear combination of the four
calculated generator logarithms.
-/
theorem candidateDlog_eq_generator_sum
    (i j k s : ZMod 2) :
    candidateDlog i j k s =
      (i : F8) * RamifiedDlog.dlog zetaJet +
      (j : F8) * RamifiedDlog.dlog e1Jet +
      (k : F8) * RamifiedDlog.dlog e2Jet +
      (s : F8) * RamifiedDlog.dlog (aJet * qJet) := by
  rw [dlog_zeta, dlog_e1, dlog_e2, dlog_aq]
  unfold candidateDlog
  simp only [map_add]
  ring

/--
No nonzero polynomial of degree at most two can vanish at `α`, whose
minimal polynomial has degree three.
-/
private theorem coeffs_zero_of_power_sum_zero
    (c0 c1 c2 : ZMod 2)
    (h :
      (c0 : F8) + (c1 : F8) * alpha +
          (c2 : F8) * alpha ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let p : (ZMod 2)[X] :=
    C c0 + C c1 * X + C c2 * X ^ 2
  have hm : AdjoinRoot.mk residueCubic p = 0 := by
    simpa [p, alpha, map_add, map_mul, map_pow] using h
  have hdvd : residueCubic ∣ p :=
    AdjoinRoot.mk_eq_zero.mp hm
  have hpdeg : p.natDegree ≤ 2 := by
    dsimp [p]
    compute_degree
  have hdeg : p.natDegree < residueCubic.natDegree := by
    rw [residueCubic_natDegree]
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have h0 := congrArg (fun q : (ZMod 2)[X] => q.coeff 0) hpzero
  have h1 := congrArg (fun q : (ZMod 2)[X] => q.coeff 1) hpzero
  have h2 := congrArg (fun q : (ZMod 2)[X] => q.coeff 2) hpzero
  simp [p, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/--
The first ramified character kills exactly two of the sixteen binary
candidates: the identity and `e₂(aq)`.
-/
theorem candidateDlog_eq_zero_iff
    (i j k s : ZMod 2) :
    candidateDlog i j k s = 0 ↔
      i = 0 ∧ j = 0 ∧ k = s := by
  constructor
  · intro h
    obtain ⟨hi, hks, hjks⟩ :=
      coeffs_zero_of_power_sum_zero i (k + s) (j + k + s)
        (by simpa only [candidateDlog] using h)
    have hkeqs : k = s :=
      CharTwo.add_eq_zero.mp hks
    have hj : j = 0 := by
      rw [hkeqs] at hjks
      exact (CharTwo.add_cancel_right j s).symm.trans hjks
    exact ⟨hi, hj, hkeqs⟩
  · rintro ⟨rfl, rfl, hks⟩
    rw [hks]
    simp [candidateDlog]

end

end MazurProof.N13LocalDlogTwo


