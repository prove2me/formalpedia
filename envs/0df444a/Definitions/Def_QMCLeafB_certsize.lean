-- Prove2me | Definitions.Def_QMCLeafB_certsize
-- name    : QMCLeafB_certsize
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:24:20.596768+00:00
-- url     : https://prove2.me/theorems/d35592d7-8229-4839-8731-d6633d1e1729
-- title:
--   QMCLeafB certsize
-- statement:
--   The Check_certsize module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

/-!
# Certificate size accounting for the leaf-B rational endgame

The leaf-B engine must return, in polynomial time, the rational data of the
`QMCLeafB.IntegrationProbe` premise: a symmetric unit-diagonal `X`, a vector `y`, and the rational
gap ledger
`(∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000`.
For `Turing.TM2ComputableInPolyTime` the *encoded length* of that output has to be bounded by a
polynomial in the encoded length of the input (this is what `LeafB.Tm2Size`'s size profiles
consume).  This file supplies that bound: given the input height budget `B` (every input rational
of the instance is `HasHeight B`) and the dimension `n`, every quantity the engine must emit or
check has height at most `ledgerHeight n B = 3 n^2 B + n B + 2 n^2 + 3 n + 15`, and its
`Ratio.encode` length is at most `16 * (n+1)^2 * (B+1) + 80` — that is, linear in the input length
`n^2 * B`.

The height calculus itself (`OAI.MetricKMedian.Binary.HasHeight` with its `add`/`mul`/`sub`/`div`/
`sum` closure lemmas and `Ratio.encode_length`) is already in the substrate; what was missing is the
linear-algebra layer (`mulVec`, matrix product, `qf`, `trace`, double sums) and the closure of the
endgame ledger.  Nothing here is a new analytic fact: it is the arithmetic accounting that turns the
`Tm2` size obligation of `d9f601e5` into concrete inequalities.
-/

open Matrix
open OAI.MetricKMedian.Binary
open scoped BigOperators

namespace QMCLeafB.CertSize

variable {n : ℕ}

/-! ## 1. Reading a height bound off `HasHeight` -/

/-- The numerator of a rational of height `L` has at most `2 ^ L`. -/
theorem num_natAbs_le_of_hasHeight {q : ℚ} {L : ℕ} (h : HasHeight q L) : q.num.natAbs ≤ 2 ^ L := by
  have h' : |q.num| ≤ (2 : ℤ) ^ L := h.1
  have h2 : (q.num.natAbs : ℤ) = |q.num| := Int.natCast_natAbs q.num
  have := h2 ▸ h'
  exact_mod_cast this

/-- The denominator of a rational of height `L` is at most `2 ^ L`. -/
theorem den_le_of_hasHeight {q : ℚ} {L : ℕ} (h : HasHeight q L) : q.den ≤ 2 ^ L := by
  have h' : (q.den : ℤ) ≤ (2 : ℤ) ^ L := h.2
  exact_mod_cast h'

/-- A rational of height `L` has encoded length at most `3 * L + 10`. -/
theorem encode_length_le_of_hasHeight {q : ℚ} {L : ℕ} (h : HasHeight q L) :
    (Ratio.encode q).length ≤ 3 * L + 10 := by
  rw [Ratio.encode_length]
  have hnum : q.num.natAbs.bits.length ≤ L + 1 :=
    NatBinary.length_le_height (num_natAbs_le_of_hasHeight h)
  have hden : q.den.bits.length ≤ L + 1 := NatBinary.length_le_height (den_le_of_hasHeight h)
  omega

/-! ## 2. The linear-algebra layer -/

/-- Entries of a matrix–vector product. -/
theorem hasHeight_mulVec (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) {B C : ℕ}
    (hM : ∀ i j, HasHeight (M i j) B) (hx : ∀ i, HasHeight (x i) C) :
    ∀ i, HasHeight ((M *ᵥ x) i) (n * (B + C + 1)) := by
  intro i
  rw [Matrix.mulVec, dotProduct]
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasHeight (M i j * x j) (B + C) := by
    intro j _
    exact (hM i j).mul (hx j)
  have h2 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun j => M i j * x j) h1
  simpa [Finset.card_univ] using h2

/-- Entries of a matrix product. -/
theorem hasHeight_mul (A X : Matrix (Fin n) (Fin n) ℚ) {B C : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) C) :
    ∀ i j, HasHeight ((A * X) i j) (n * (B + C + 1)) := by
  intro i j
  rw [Matrix.mul_apply]
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin n)), HasHeight (A i k * X k j) (B + C) := by
    intro k _
    exact (hA i k).mul (hX k j)
  have h2 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun k => A i k * X k j) h1
  simpa [Finset.card_univ] using h2

/-- Entries of the Gram product `M Mᵀ` — the matrix the engine checks a factorization against. -/
theorem hasHeight_gram (M : Matrix (Fin n) (Fin n) ℚ) {C : ℕ}
    (hM : ∀ i j, HasHeight (M i j) C) :
    ∀ i j, HasHeight ((M * Mᵀ) i j) (n * (C + C + 1)) := by
  intro i j
  refine (hasHeight_mul M Mᵀ hM ?_) i j
  intro k l
  simpa using hM l k

/-- The quadratic form `x ⬝ᵥ (M *ᵥ x)` at a rational test vector. -/
theorem hasHeight_qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) {B C : ℕ}
    (hM : ∀ i j, HasHeight (M i j) B) (hx : ∀ i, HasHeight (x i) C) :
    HasHeight (x ⬝ᵥ (M *ᵥ x)) (n * (C + n * (B + C + 1) + 1)) := by
  have h1 := hasHeight_mulVec M x hM hx
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasHeight (x i * (M *ᵥ x) i) (C + n * (B + C + 1)) := by
    intro i _
    exact (hx i).mul (h1 i)
  have h3 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun i => x i * (M *ᵥ x) i) h2
  simpa [dotProduct, Finset.card_univ] using h3

/-- The trace of a matrix product — the duality-gap quantity `tr(A X)`. -/
theorem hasHeight_trace_mul (A X : Matrix (Fin n) (Fin n) ℚ) {B C : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) C) :
    HasHeight (A * X).trace (n * (n * (B + C + 1) + 1)) := by
  rw [Matrix.trace]
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasHeight ((A * X) i i) (n * (B + C + 1)) := by
    intro i _
    exact hasHeight_mul A X hA hX i i
  have h2 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun i => (A * X) i i) h1
  simpa [Finset.card_univ] using h2

/-- The double sum `∑ i, ∑ j, A i j` — the normalizer `V` of the instance. -/
theorem hasHeight_sum_sum (A : Matrix (Fin n) (Fin n) ℚ) {B : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) :
    HasHeight (∑ i, ∑ j, A i j) (n * (n * (B + 1) + 1)) := by
  have h1 : ∀ i, HasHeight (∑ j, A i j) (n * (B + 1)) := by
    intro i
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasHeight (A i j) B := by
      intro j _
      exact hA i j
    have h3 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun j => A i j) h2
    simpa [Finset.card_univ] using h3
  have h4 : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasHeight (∑ j, A i j) (n * (B + 1)) := by
    intro i _
    exact h1 i
  have h5 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun i => ∑ j, A i j) h4
  simpa [Finset.card_univ] using h5

/-! ## 3. The endgame ledger

`IntegrationProbe`'s gap hypothesis is the rational inequality
`(∑ i, y i) + (A * X).trace ≤ (∑ i, ∑ j, A i j) / 5000`.
The left-hand difference is the single rational the engine has to emit for that check. -/

/-- The height budget of every rational in the endgame ledger, in terms of the dimension `n` and
the input height `B`. -/
def ledgerHeight (n B : ℕ) : ℕ :=
  n * (B + 1) + (n * (n * (B + (B + 1)) + 1) + (n * (n * (B + 1) + 1) + 15))

/-- The closed polynomial form of the ledger height: `3 n² B + n B + 2 n² + 3 n + 15`. -/
theorem ledgerHeight_eq (n B : ℕ) :
    ledgerHeight n B = 3 * (n * n) * B + n * B + 2 * n * n + 3 * n + 15 := by
  simp only [ledgerHeight]
  ring

/-- The trace part of the ledger: `tr(A X)` and the normalizing double sum over `5000`. -/
theorem hasHeight_ledger_gap (A X : Matrix (Fin n) (Fin n) ℚ) {B : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B) :
    HasHeight ((A * X).trace - (∑ i, ∑ j, A i j) / 5000)
      (n * (n * (B + B + 1) + 1) + (n * (n * (B + 1) + 1) + 13) + 1) := by
  have h3 : HasHeight (∑ i, ∑ j, A i j) (n * (n * (B + 1) + 1)) := hasHeight_sum_sum A hA
  have h4 : HasHeight ((5000 : ℚ)) 13 := by
    constructor <;> norm_num
  have h5 : HasHeight ((∑ i, ∑ j, A i j) / 5000) (n * (n * (B + 1) + 1) + 13) := h3.div h4
  exact (hasHeight_trace_mul A X hA hX).sub h5

/-- Every rational appearing in the endgame ledger has height at most `ledgerHeight n B`. -/
theorem hasHeight_ledger (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) {B : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) :
    HasHeight ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000) (ledgerHeight n B) := by
  have h1 : HasHeight (∑ i, y i) (n * (B + 1)) := by
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasHeight (y i) B := by
      intro i _
      exact hy i
    have h3 := HasHeight.sum (Finset.univ : Finset (Fin n)) (fun i => y i) h2
    simpa [Finset.card_univ] using h3
  have h2 := hasHeight_ledger_gap A X hA hX
  simpa [sub_eq_add_neg, add_assoc, ledgerHeight] using h1.add h2

/-! ## 4. Encoded length of the ledger: linear in the input length -/

/-- The ledger's encoded length is at most `3 * ledgerHeight n B + 10`. -/
theorem ledger_encode_length_le (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) {B : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) :
    (Ratio.encode ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000)).length
      ≤ 3 * ledgerHeight n B + 10 :=
  encode_length_le_of_hasHeight (hasHeight_ledger A X y hA hX hy)

/-- The ledger's encoded length is at most `16 (n+1)² (B+1) + 80`, i.e. at most a constant times
the input length `n² (B+1)`.  With `N` the encoded length of the instance this is `O(N)`. -/
theorem ledger_encode_length_poly (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) {B : ℕ}
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) :
    (Ratio.encode ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000)).length
      ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80 := by
  refine (ledger_encode_length_le A X y hA hX hy).trans ?_
  rw [ledgerHeight_eq]
  nlinarith

/-- The quadratic form the engine certifies at a rational test vector has encoded length
`≤ 16 (n+1)² (B+1) + 40` when both the matrix and the vector have height `B`. -/
theorem qf_encode_length_poly (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) {B : ℕ}
    (hM : ∀ i j, HasHeight (M i j) B) (hx : ∀ i, HasHeight (x i) B) :
    (Ratio.encode (x ⬝ᵥ (M *ᵥ x))).length ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 40 := by
  have h := encode_length_le_of_hasHeight (hasHeight_qf M x hM hx)
  refine h.trans ?_
  nlinarith

/-- The entry of the Gram product `M Mᵀ` the engine compares against `X`. -/
theorem gram_encode_length_poly (M : Matrix (Fin n) (Fin n) ℚ) {B : ℕ}
    (hM : ∀ i j, HasHeight (M i j) B) (i j : Fin n) :
    (Ratio.encode ((M * Mᵀ) i j)).length ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 40 := by
  have h := encode_length_le_of_hasHeight (hasHeight_gram M hM i j)
  refine h.trans ?_
  nlinarith

/-! ## 5. The assembled certificate

Every rational the engine emits for the `IntegrationProbe` premise — the primal matrix `X`, the
dual vector `y`, a matrix–vector product entry, the quadratic form at a rational test vector, and
the gap ledger — fits in the same height budget, and therefore in the same encoded-length budget
`16 (n+1)² (B+1) + 80`, linear in the input length. -/

theorem cert_heights (A X : Matrix (Fin n) (Fin n) ℚ) (y x : Fin n → ℚ) {B : ℕ} (hn : 1 ≤ n)
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) (hx : ∀ i, HasHeight (x i) B) :
    (∀ i j, HasHeight (X i j) (ledgerHeight n B)) ∧
    (∀ i, HasHeight (y i) (ledgerHeight n B)) ∧
    HasHeight (x ⬝ᵥ (X *ᵥ x)) (ledgerHeight n B) ∧
    HasHeight ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000) (ledgerHeight n B) := by
  have hledger := hasHeight_ledger A X y hA hX hy
  have hb : B ≤ ledgerHeight n B := by
    rw [ledgerHeight_eq]
    nlinarith
  have hb' : n * (B + n * (B + B + 1) + 1) ≤ ledgerHeight n B := by
    rw [ledgerHeight_eq]
    nlinarith
  refine ⟨fun i j => (hX i j).mono hb, fun i => (hy i).mono hb, ?_, hledger⟩
  exact (hasHeight_qf X x hX hx).mono hb'

/-- **The certificate size bound.** Every rational the engine emits for the premise package has
encoded length at most `16 (n+1)² (B+1) + 80`, when every input rational has height `B`. -/
theorem cert_encode_lengths (A X : Matrix (Fin n) (Fin n) ℚ) (y x : Fin n → ℚ) {B : ℕ}
    (hn : 1 ≤ n) (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) (hx : ∀ i, HasHeight (x i) B) :
    (∀ i j, (Ratio.encode (X i j)).length ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80) ∧
    (∀ i, (Ratio.encode (y i)).length ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80) ∧
    (Ratio.encode (x ⬝ᵥ (X *ᵥ x))).length ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80 ∧
    (Ratio.encode ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000)).length
      ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80 := by
  obtain ⟨hX', hy', hqf, hled⟩ := cert_heights A X y x hn hA hX hy hx
  have harith : 3 * ledgerHeight n B + 10 ≤ 16 * (n + 1) * (n + 1) * (B + 1) + 80 := by
    rw [ledgerHeight_eq]
    nlinarith
  refine ⟨fun i j => ?_, fun i => ?_, ?_, ?_⟩
  · exact (encode_length_le_of_hasHeight (hX' i j)).trans harith
  · exact (encode_length_le_of_hasHeight (hy' i)).trans harith
  · exact (encode_length_le_of_hasHeight hqf).trans harith
  · exact (encode_length_le_of_hasHeight hled).trans harith

/-! ## 6. Linear in the input length

If `N` is the encoded length of the instance — at least `n² (B+1)` bits for an `n`-vertex instance
whose weights all have height `B` — then the ledger occupies at most `144 * N` bits.  This is a
`SizeProfile` with the monomial `144 * X`, the shape `LeafB.Tm2Size` consumes. -/

theorem ledger_encode_length_linear (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    {B N : ℕ} (hn : 1 ≤ n) (hN : n * n * (B + 1) ≤ N)
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) :
    (Ratio.encode ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000)).length ≤ 144 * N := by
  have h1 := ledger_encode_length_poly A X y hA hX hy
  have hsq : (n + 1) * (n + 1) ≤ 4 * (n * n) := by nlinarith
  have hpos : 1 ≤ N := by nlinarith
  nlinarith

/-- The same bound read as a `SizeProfile` monomial: `144 * X` evaluated at the input length. -/
theorem ledger_encode_length_monomial (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    {B N : ℕ} (hn : 1 ≤ n) (hN : n * n * (B + 1) ≤ N)
    (hA : ∀ i j, HasHeight (A i j) B) (hX : ∀ i j, HasHeight (X i j) B)
    (hy : ∀ i, HasHeight (y i) B) :
    (Ratio.encode ((∑ i, y i) + (A * X).trace - (∑ i, ∑ j, A i j) / 5000)).length
      ≤ (Polynomial.C 144 * Polynomial.X).eval N := by
  simpa using ledger_encode_length_linear A X y hn hN hA hX hy

end QMCLeafB.CertSize


