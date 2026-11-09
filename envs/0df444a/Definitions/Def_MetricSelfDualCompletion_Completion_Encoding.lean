-- Prove2me | Definitions.Def_MetricSelfDualCompletion_Completion_Encoding
-- name    : MetricSelfDualCompletion_Completion_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T06:45:59.700783+00:00
-- url     : https://prove2.me/theorems/d3b8e35b-d47f-4c3f-8188-b0e0b8767870
-- title:
--   Bit-string encodings of sizes (unary), vectors and $\mathbb F_2$ matrices
-- statement:
--   The algorithmic clauses of the mission speak about one fixed deterministic machine computing a function on binary strings, in polynomial time in the input length (`PvsNP.PolyTimeComputable`). This file fixes how the mathematical inputs and outputs are written as binary strings.
--
--   1. A natural number $n$ (a length or a dimension) is written in **unary** as $1^n0$.
--   2. A vector $v\in\mathbb F_2^n$ is written as its $n$ bits $v_1\cdots v_n$.
--   3. An $r\times c$ matrix over $\mathbb F_2$ is written as $1^r0\,1^c0$ followed by its $rc$ entries in row-major order. A generator matrix of a $k$-dimensional code of length $n$ is the $k\times n$ matrix whose rows are the basis vectors (§2.1: "Generator matrices have basis rows"); the matrix of a linear map $\mathbb F_2^m\to\mathbb F_2^N$ is $N\times m$ ("vectors are columns").
--
--   Each encoding is prefix-free, so the encoding of a tuple of such objects determines the objects, including their dimensions; the file proves these injectivity facts.
--
--   Sizes are written in unary because the paper measures running times in the code length ($\mathrm{poly}(N)$, $\mathrm{poly}(n_j)$, $\mathrm{poly}(n)$) while the machine model measures them in the input length; with unary sizes the two are polynomially related, and a binary-size input could be expanded to unary within the same polynomial bound.
-- source:
--   Rafail Ostrovsky, STOC 2027 submission #5 (October 2026), §2.1, printed p. 5 (PDF p. 7). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/5.pdf

import Mathlib

/-!
# Metric self-dual completion: binary-string encodings of sizes, vectors and matrices

Rafail Ostrovsky, *Metric Self-Dual Completion and Optimal Additive Hardness for Quantum and
Graph-State Distance*, STOC 2027 submission #5 (October 2026), §2.1 (printed p. 5, PDF p. 7):
"Codes are specified by bases. Generator matrices have basis rows. Vectors are columns. Matrices
also represent linear maps. All our algorithms are deterministic."

The algorithmic clauses of the mission are stated with `PvsNP.PolyTimeComputable` on `List Bool`.
This file fixes how their inputs and outputs are written as bit strings:

* a size parameter `n` is written in **unary**, `1ⁿ0` (so that the input length of an algorithm
  is polynomially related to the code length the paper measures its running time in);
* a vector of `F₂ⁿ` is its `n` bits, `1 ↦ true`, `0 ↦ false`;
* an `r × c` matrix over `F₂` is `1ʳ0 1ᶜ0` followed by its `r·c` entries in row-major order.

Each encoding is prefix-free, hence injective even when followed by further data
(`encNat_append_inj`, `encVec_append_inj`, `encMatrix_append_inj`).
-/

namespace MetricSelfDualCompletion.Completion

/-- The bit of an element of `F₂ = ZMod 2`: `1 ↦ true`, `0 ↦ false`. -/
def bitOf (a : ZMod 2) : Bool := decide (a = 1)

/-- Unary encoding `1ⁿ0` of a natural number. -/
def encNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A vector of `F₂ⁿ` as its `n` bits, in coordinate order. -/
def encVec {n : ℕ} (v : Fin n → ZMod 2) : List Bool := List.ofFn fun i => bitOf (v i)

/-- The `r · c` entries of an `r × c` matrix over `F₂` (rows `Fin r`), row-major. -/
def encBits {r c : ℕ} (M : Fin r → Fin c → ZMod 2) : List Bool :=
  List.ofFn fun k : Fin (r * c) => bitOf (M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- An `r × c` matrix over `F₂` with its dimensions: `1ʳ0 1ᶜ0` then the entries row-major. A
generator matrix of a code of dimension `r` and length `c` has the `r` basis vectors as rows; a
matrix of a linear map `F₂ᵐ → F₂ᴺ` (vectors are columns) is an `N × m` matrix. -/
def encMatrix {r c : ℕ} (M : Fin r → Fin c → ZMod 2) : List Bool :=
  encNat r ++ encNat c ++ encBits M

lemma bitOf_injective : Function.Injective bitOf := by
  unfold Function.Injective
  decide

lemma encNat_append_inj {a b : ℕ} {l l' : List Bool} (h : encNat a ++ l = encNat b ++ l') :
    a = b ∧ l = l' := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [encNat] using h
    | succ b => simp [encNat, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [encNat, List.replicate_succ] at h
    | succ b =>
      simp only [encNat, List.replicate_succ, List.cons_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      have := ih (b := b) (by simpa [encNat, List.append_assoc] using h)
      exact ⟨by omega, this.2⟩

lemma encVec_append_inj {n : ℕ} {v v' : Fin n → ZMod 2} {l l' : List Bool}
    (h : encVec v ++ l = encVec v' ++ l') : v = v' ∧ l = l' := by
  have h2 := List.append_inj h (by simp [encVec])
  refine ⟨?_, h2.2⟩
  funext i
  have := congrFun (List.ofFn_injective h2.1) i
  exact bitOf_injective this

lemma encBits_append_inj {r c : ℕ} {M M' : Fin r → Fin c → ZMod 2} {l l' : List Bool}
    (h : encBits M ++ l = encBits M' ++ l') : M = M' ∧ l = l' := by
  have h2 := List.append_inj h (by simp [encBits])
  refine ⟨?_, h2.2⟩
  funext i j
  have := congrFun (List.ofFn_injective h2.1) (finProdFinEquiv (i, j))
  simpa using bitOf_injective this

/-- The matrix encoding is prefix-free, hence injective (dimensions included). -/
lemma encMatrix_append_inj {r c r' c' : ℕ} {M : Fin r → Fin c → ZMod 2}
    {M' : Fin r' → Fin c' → ZMod 2} {l l' : List Bool}
    (h : encMatrix M ++ l = encMatrix M' ++ l') : r = r' ∧ c = c' ∧ HEq M M' ∧ l = l' := by
  simp only [encMatrix, List.append_assoc] at h
  obtain ⟨rfl, h⟩ := encNat_append_inj h
  obtain ⟨rfl, h⟩ := encNat_append_inj h
  obtain ⟨rfl, rfl⟩ := encBits_append_inj h
  exact ⟨rfl, rfl, HEq.rfl, rfl⟩

/-! ### Sanity checks -/

example : encNat 2 = [true, true, false] := rfl

example : encMatrix (fun (_ : Fin 1) (j : Fin 2) => if j = 0 then (1 : ZMod 2) else 0) =
    [true, false, true, true, false, true, false] := by decide

end MetricSelfDualCompletion.Completion


