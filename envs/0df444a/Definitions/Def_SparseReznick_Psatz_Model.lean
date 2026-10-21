-- Prove2me | Definitions.Def_SparseReznick_Psatz_Model
-- name    : SparseReznick_Psatz_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:07.571922+00:00
-- url     : https://prove2.me/theorems/6d06bd52-a4b3-4296-a24d-d8a0ad9dd063
-- title:
--   Assumption 1.1(i), p. 3; Φl and Hl, p. 6 — sparse form model
-- statement:
--   Let $I_1,\ldots,I_p$ be nonempty variable blocks covering all coordinates. The running intersection property assigns to each later block an earlier parent containing its overlap with preceding blocks. The model defines the squared coordinate norm, these overlaps, the denominator factors $\Phi_l$ and $H_l$, supported sums of squares, and continuous rational forms on blocks.
--
--   $$H_l=\|x(I_l)\|_2^2\Phi_l,\qquad \Sigma[x(T)]_t=\{\text{finite sums of squares in }x(T)\text{ of degree at most }2t\}. $$
--
--   These definitions give every target the same representation of the paper’s sparsity and degree conventions. **Formalization Note** Block indices start at zero; the first block has index zero in Lean.
-- source:
--   Mai, Magron & Lasserre, A sparse version of Reznick’s Positivstellensatz, arXiv:2002.05101v2, pp. 3, 6, 8–9, Assumption 1.1(i), definitions of Φl and Hl, and §3

import Mathlib

namespace SparseReznick.Psatz

open MvPolynomial

noncomputable def sqNorm {n : ℕ} (T : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ T, X i ^ 2

def Ihat {n p : ℕ} (I : Fin p → Finset (Fin n)) (l : Fin p) : Finset (Fin n) :=
  I l ∩ (Finset.univ.filter (fun j : Fin p => j < l)).biUnion I

def RIP {n p : ℕ} (I : Fin p → Finset (Fin n)) (s : Fin p → Fin p) : Prop :=
  2 ≤ p ∧ (∀ l, (I l).Nonempty) ∧ Finset.univ.biUnion I = Finset.univ ∧
    ∀ l, l.val ≠ 0 → s l < l ∧ Ihat I l ⊆ I (s l)

noncomputable def Phi {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (l : Fin p) : MvPolynomial (Fin n) ℝ :=
  (if l.val = 0 then 1 else sqNorm (Ihat I l)) *
    ∏ j ∈ Finset.univ.filter (fun j : Fin p => l < j ∧ s j = l), sqNorm (Ihat I j)

def degPhi {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (l : Fin p) : ℕ :=
  (if l.val = 0 then 0 else 2) +
    2 * (Finset.univ.filter (fun j : Fin p => l < j ∧ s j = l)).card

noncomputable def H {n p : ℕ} (I : Fin p → Finset (Fin n))
    (s : Fin p → Fin p) (l : Fin p) : MvPolynomial (Fin n) ℝ :=
  sqNorm (I l) * Phi I s l

def IsSOSIn {n : ℕ} (T : Finset (Fin n)) (t : ℕ)
    (sig : MvPolynomial (Fin n) ℝ) : Prop :=
  (∃ (m : ℕ) (g : Fin m → MvPolynomial (Fin n) ℝ),
      (∀ i, g i ∈ MvPolynomial.supported ℝ (↑T : Set (Fin n))) ∧
      sig = ∑ i, g i ^ 2) ∧ sig.totalDegree ≤ 2 * t

def IsPDForm {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (m : ℕ) : Prop :=
  f.IsHomogeneous m ∧ ∀ x : Fin n → ℝ, x ≠ 0 → 0 < MvPolynomial.eval x f

def DependsOn {n : ℕ} (I : Finset (Fin n)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ I, x i = y i) → f x = f y

def IsContRatForm {n : ℕ} (I : Finset (Fin n)) (m : ℕ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  DependsOn I f ∧ Continuous f ∧
    (∀ (t : ℝ) x, f (t • x) = t ^ m * f x) ∧
    ∃ P Q : MvPolynomial (Fin n) ℝ,
      P ∈ MvPolynomial.supported ℝ (↑I : Set (Fin n)) ∧
      Q ∈ MvPolynomial.supported ℝ (↑I : Set (Fin n)) ∧ Q ≠ 0 ∧
      ∀ x, MvPolynomial.eval x Q ≠ 0 →
        f x = MvPolynomial.eval x P / MvPolynomial.eval x Q

def IsPDOn {n : ℕ} (I : Finset (Fin n)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, (∃ i ∈ I, x i ≠ 0) → 0 < f x

noncomputable def ratForm {n : ℕ} (J : Finset (Fin n))
    (q : MvPolynomial (Fin n) ℝ) (k : ℕ) : (Fin n → ℝ) → ℝ :=
  fun x => MvPolynomial.eval x q / MvPolynomial.eval x (sqNorm J) ^ k

end SparseReznick.Psatz


