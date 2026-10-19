-- Prove2me | Definitions.Def_copenhagen_states
-- name    : copenhagen_states
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-18T21:23:59.97267+00:00
-- url     : https://prove2.me/theorems/7161ec06-0a00-4c95-8840-1d01552de486
-- title:
--   Qubit states, the inner product, and the Born probability
-- statement:
--   State space of the mission's fragment of quantum mechanics. A qubit state is a complex amplitude for each of the two outcomes of a two-outcome measurement; `br` is the inner product ⟨φ|ψ⟩; `ket b` is the computational basis vector |b⟩; `cat` is the Schrödinger cat state (|dead⟩ + |alive⟩)/√2, written (|false⟩ + |true⟩)/√2; `prob ψ b` is the Born probability of the outcome b upon measuring ψ in the computational basis — the squared magnitude of the amplitude ⟨b|ψ⟩ — and `had` is the Hadamard operation, the algebra of a balanced beam splitter, which splits the incoming amplitude into an equal sum and an equal difference.
--
--   The file also fixes the numeric constant c = 1/√2 and proves its basic facts (c * c = 1/2, conj c = c, c ≠ 0, |c| = 1/√2, |c|² = 1/2), together with the evaluation of the basis vectors on concrete outcomes. These are the definitions on which all of the mission's theorems are stated; they follow the source's ket notation, with `false` playing the first basis vector (the article's |dead⟩, or the first slit) and `true` the second. The source fixes no formalism beyond this notation; the two-outcome fragment is the smallest arena in which every number the article quotes is exactly representable.
-- source:
--   "Copenhagen interpretation", Wikipedia, retrieved 2026-10-18, oldid 1380019891, sections "Principles", "Nature of the wave function" and "Consequences"

import Mathlib

open ComplexConjugate

namespace Copenhagen

/-- One over the square root of two: the amplitude normalization of an
equal superposition, as a complex number. -/
noncomputable def c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma sq_c : c * c = 1 / 2 := by
  have hx : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    push_cast
    exact_mod_cast Real.mul_self_sqrt (by norm_num)
  simp only [c]
  rw [← mul_inv, hx]
  norm_num

lemma conj_c : conj c = c := by
  simp only [c, Complex.conj_inv, Complex.conj_ofReal]

/-- A qubit state: a complex amplitude for each of the two outcomes of a
two-outcome measurement. The outcome `false` is the first outcome of the
computational basis and `true` the second. -/
def Qubit := Bool → ℂ

/-- The inner product of two qubit states, `⟨φ | ψ⟩`. -/
def br (φ ψ : Qubit) : ℂ := conj (φ false) * ψ false + conj (φ true) * ψ true

/-- The computational basis state `|b⟩`. -/
def ket (b : Bool) : Qubit := fun b' => if b' = b then 1 else 0

@[simp] lemma ket_false_false : ket false false = 1 := rfl
@[simp] lemma ket_false_true : ket false true = 0 := rfl
@[simp] lemma ket_true_false : ket true false = 0 := rfl
@[simp] lemma ket_true_true : ket true true = 1 := rfl

/-- The Schrödinger cat state, `(|false⟩ + |true⟩)/√2`: the state the
source writes `(|dead⟩ + |alive⟩)/√2`. -/
noncomputable def cat : Qubit := fun _ => c

/-- Born-rule probability of the outcome `b` upon measuring `ψ` in the
computational basis: the squared magnitude of the amplitude `⟨b|ψ⟩`. -/
def prob (ψ : Qubit) (b : Bool) : ℝ := Complex.normSq (br (ket b) ψ)

lemma normSq_c : Complex.normSq c = 1 / 2 := by
  simp only [c]
  rw [Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma normSq_neg_c : Complex.normSq (-c) = 1 / 2 := by
  rw [Complex.normSq_neg, normSq_c]

lemma c_ne_zero : c ≠ 0 := by
  have h : (0:ℝ) < Complex.normSq c := by rw [normSq_c]; norm_num
  exact Complex.normSq_pos.mp h

/-- The Hadamard operation, the algebra of a balanced beam splitter: the
incoming amplitude is split into an equal sum and an equal difference,
phase-locked by `c`. -/
noncomputable def had (ψ : Qubit) : Qubit :=
  fun b => if b then c * (ψ false - ψ true) else c * (ψ false + ψ true)

lemma norm_c : ‖c‖ = (Real.sqrt 2 : ℝ)⁻¹ := by
  have h1 : c = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := rfl
  rw [h1, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

end Copenhagen


