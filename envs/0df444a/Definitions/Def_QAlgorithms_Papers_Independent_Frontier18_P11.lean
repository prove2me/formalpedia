-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11
-- name    : QAlgorithms_Papers_Independent_Frontier18_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:32:58.356634+00:00
-- url     : https://prove2.me/theorems/6d2de350-c5b7-4f47-b3d6-50ce01cfc1ce
-- title:
--   Definitions for On the Choi-Jamiolkowski Correspondence in Infinite Dimensions
-- statement:
--   The objects the formalized statements of *On the Choi-Jamiolkowski Correspondence in Infinite Dimensions* (arXiv:1004.0196) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `JointHilbert`: Completed Hilbert tensor product, output factor first (PDF pp.2,6). The algebraic tensor product has the product inner product before completion.
--   - `positiveOperator`: Positivity of a bounded operator, including reality of every quadratic matrix element (PDF p.6, Definition 2). Inner products conjugate the first slot.
--   - `densityOperator`: A density operator in an arbitrary countable Hilbert basis (PDF pp.2,6). For a positive bounded operator, finite diagonal sum is precisely the trace-class condition; its sum here is one. `HasSum` forbids default `tsum` values on divergent series. No finite-rank or finite-spectrum restriction.
--   - `inputMarginal`: Full partial-trace identity Tr_B O = I_A (PDF p.3, (3); p.4, (5)). This is imposed on all input vectors, including off-diagonal matrix elements.
--   - `finiteSeparableCJ`: Finite sums rho_alpha tensor M_alpha in Definition 2 (PDF p.6). The M_alpha form a finite positive resolution of the input identity. The displayed equality specifies the operator on a total set of product vectors; its action on entangled vectors is thereby fixed as well.
--   - `weakOperatorClosure`: Weak-operator closure via its defining finite matrix-element neighborhoods (PDF p.6). The approximating operators need not have finite rank.
--   - `separableCJ`: Definition 2 (PDF p.6): the normalized positive bounded CJ operators in the weak-operator closure of finite separable sums. The marginal is explicitly retained: an unrestricted weak limit can lose normalization.
--   - `complexMatrix`: Entrywise complexification, used only for Lemma 3's positivity hypothesis (PDF p.14). This source uses hbar=1 and the factor i/2.
--   - `normalCovariance`: Covariance normal form (30), PDF pp.14–15: q quantum pairs, c classical positive-variance coordinates, then the zero block. Quantified dimension identities in Lemma 3 specify the exact ranks without truncated subtraction.
--   - `normalCommutator`: Skew normal form (31), PDF p.14. Each quantum pair has the source's block [[0,-1],[1,0]]; all classical and noiseless coordinates have zero defect.
-- source:
--   On the Choi-Jamiolkowski Correspondence in Infinite Dimensions, arXiv:1004.0196v3, https://arxiv.org/abs/1004.0196v3

import Mathlib

/-!
# Holevo: On the Choi-Jamiolkowski Correspondence in Infinite Dimensions

Source: arXiv:1004.0196v3. This draft states Lemma 2, its sequential consequence,
and Lemma 3. All other planned results are individually recorded in HARD.md.
The joint Hilbert space is the completion of the algebraic tensor product,
with the output factor first. Definition 2 is implemented using bounded
operators, its full input marginal, and actual weak-operator neighborhoods.
No finite-dimensional cutoff of a Hilbert space is used.
-/

noncomputable section

open scoped TensorProduct ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P11

section Operators

variable {A B : Type*}
variable [NormedAddCommGroup A] [InnerProductSpace ℂ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Completed Hilbert tensor product, output factor first (PDF pp.2,6).
The algebraic tensor product has the product inner product before completion. -/
abbrev JointHilbert (A B : Type*) [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] :=
  UniformSpace.Completion (TensorProduct ℂ B A)

/-- Positivity of a bounded operator, including reality of every quadratic
matrix element (PDF p.6, Definition 2). Inner products conjugate the first slot. -/
def positiveOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Prop :=
  ∀ x : H, (inner ℂ x (T x)).im = 0 ∧ 0 ≤ (inner ℂ x (T x)).re

/-- A density operator in an arbitrary countable Hilbert basis (PDF pp.2,6).
For a positive bounded operator, finite diagonal sum is precisely the
trace-class condition; its sum here is one. `HasSum` forbids default `tsum`
values on divergent series. No finite-rank or finite-spectrum restriction. -/
def densityOperator {I : Type*} (e : HilbertBasis I ℂ B)
    (rho : B →L[ℂ] B) : Prop :=
  positiveOperator rho ∧ HasSum (fun i : I => (inner ℂ (e i) (rho (e i))).re) 1

/-- Full partial-trace identity Tr_B O = I_A (PDF p.3, (3); p.4, (5)).
This is imposed on all input vectors, including off-diagonal matrix elements. -/
def inputMarginal {I : Type*} (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) : Prop :=
  ∀ a a' : A, HasSum
    (fun k : I => inner ℂ (↑((e k) ⊗ₜ[ℂ] a) : JointHilbert A B)
      (O (↑((e k) ⊗ₜ[ℂ] a') : JointHilbert A B)))
    (inner ℂ a a')

/-- Finite sums rho_alpha tensor M_alpha in Definition 2 (PDF p.6).
The M_alpha form a finite positive resolution of the input identity.
The displayed equality specifies the operator on a total set of product
vectors; its action on entangled vectors is thereby fixed as well. -/
def finiteSeparableCJ {I : Type*} (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) : Prop :=
  ∃ (n : ℕ) (rho : Fin n → B →L[ℂ] B) (M : Fin n → A →L[ℂ] A),
    (∀ i, densityOperator e (rho i)) ∧
    (∀ i, positiveOperator (M i)) ∧
    (∑ i, M i) = ContinuousLinearMap.id ℂ A ∧
    ∀ (b b' : B) (a a' : A),
      inner ℂ (↑(b ⊗ₜ[ℂ] a) : JointHilbert A B)
        (O (↑(b' ⊗ₜ[ℂ] a') : JointHilbert A B)) =
        ∑ i, inner ℂ b (rho i b') * inner ℂ a (M i a')

/-- Weak-operator closure via its defining finite matrix-element neighborhoods
(PDF p.6). The approximating operators need not have finite rank. -/
def weakOperatorClosure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set (H →L[ℂ] H)) (O : H →L[ℂ] H) : Prop :=
  ∀ (tests : Finset (H × H)) (epsilon : ℝ), 0 < epsilon →
    ∃ F ∈ S, ∀ p ∈ tests,
      ‖inner ℂ p.1 (F p.2) - inner ℂ p.1 (O p.2)‖ < epsilon

/-- Definition 2 (PDF p.6): the normalized positive bounded CJ operators in
the weak-operator closure of finite separable sums. The marginal is explicitly
retained: an unrestricted weak limit can lose normalization. -/
def separableCJ {I : Type*} (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) : Prop :=
  positiveOperator O ∧ inputMarginal e O ∧
    weakOperatorClosure {F | finiteSeparableCJ e F} O

/-! Definitional sanity checks (not proofs of source results). -/

example (a : A) : (↑((0 : B) ⊗ₜ[ℂ] a) : JointHilbert A B) = 0 := by
  simp

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    positiveOperator (0 : H →L[ℂ] H) := by
  intro x
  simp

example {I : Type*} (e : HilbertBasis I ℂ B) :
    ¬ densityOperator e (0 : B →L[ℂ] B) := by
  intro h
  have hz : HasSum (fun _ : I => (0 : ℝ)) 0 := hasSum_zero
  have he : (0 : ℝ) = 1 := hz.unique (by simpa using h.2)
  norm_num at he

example {I : Type*} (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) (h : separableCJ e O) :
    inputMarginal e O := h.2.1

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) : weakOperatorClosure {O} O := by
  intro tests epsilon hepsilon
  refine ⟨O, by simp, ?_⟩
  intro p hp
  simpa using hepsilon

example {I : Type*} (e : HilbertBasis I ℂ B)
    (O : JointHilbert A B →L[ℂ] JointHilbert A B) (hO : finiteSeparableCJ e O) :
    ∃ (n : ℕ) (M : Fin n → A →L[ℂ] A),
      (∀ i, positiveOperator (M i)) ∧ (∑ i, M i) = ContinuousLinearMap.id ℂ A := by
  obtain ⟨n, rho, M, hrho, hM, hsum, helements⟩ := hO
  exact ⟨n, M, hM, hsum⟩

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (O : H →L[ℂ] H) : ¬ weakOperatorClosure ∅ O := by
  intro h
  obtain ⟨F, hF, _⟩ := h ∅ 1 zero_lt_one
  exact hF

end Operators

/-- Entrywise complexification, used only for Lemma 3's positivity hypothesis
(PDF p.14). This source uses hbar=1 and the factor i/2. -/
def complexMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => (M i j : ℂ)

/-- Covariance normal form (30), PDF pp.14–15: q quantum pairs, c classical
positive-variance coordinates, then the zero block. Quantified dimension
identities in Lemma 3 specify the exact ranks without truncated subtraction. -/
def normalCovariance (N q c : ℕ) (nu : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i =>
    if i.val < 2 * q then nu (i.val / 2)
    else if i.val < 2 * q + c then (1 / 2 : ℝ) else 0

/-- Skew normal form (31), PDF p.14. Each quantum pair has the source's
block [[0,-1],[1,0]]; all classical and noiseless coordinates have zero defect. -/
def normalCommutator (N q : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i.val < 2 * q ∧ j.val < 2 * q ∧ i.val / 2 = j.val / 2 then
      if i.val % 2 = 0 ∧ j.val % 2 = 1 then -1
      else if i.val % 2 = 1 ∧ j.val % 2 = 0 then 1 else 0
    else 0

example {m n : ℕ} : complexMatrix (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  ext i j
  simp [complexMatrix]

example (nu : ℕ → ℝ) : normalCovariance 2 1 0 nu 0 0 = nu 0 := by
  simp [normalCovariance]

example (nu : ℕ → ℝ) : normalCovariance 2 0 1 nu 0 0 = (1 / 2 : ℝ) := by
  simp [normalCovariance]

example (nu : ℕ → ℝ) : normalCovariance 2 0 1 nu 1 1 = 0 := by
  simp [normalCovariance]

example : normalCommutator 2 1 0 1 = -1 := by
  norm_num [normalCommutator]

example : normalCommutator 2 1 1 0 = 1 := by
  norm_num [normalCommutator]

example (N : ℕ) : normalCommutator N 0 = 0 := by
  ext i j
  simp [normalCommutator]

end QAlgorithms.Papers.Independent.Frontier18.P11


