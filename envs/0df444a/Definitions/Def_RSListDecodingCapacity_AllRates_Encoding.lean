-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
-- name    : RSListDecodingCapacity_AllRates_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:56.540696+00:00
-- url     : https://prove2.me/theorems/9e0b53b0-02aa-4565-b967-7b7271593e32
-- title:
--   Binary encodings of list-decoding and root-finding inputs and outputs
-- statement:
--   Inputs and outputs of the algorithms of the mission are binary strings.
--
--   1. A natural number is written in binary (least significant bit first, no leading zeros), each bit $b$ as the block $0b$, followed by the end marker $10$; a list is written as its length followed by its entries; an element of $\mathbb F_q$ is written as its residue in $\{0,\dots,q-1\}$.
--   2. The **input of the list-decoding problem** is $n,k,q$, an integer agreement threshold $A$, the evaluation points $\alpha_1,\dots,\alpha_n$ and the received word $y_1,\dots,y_n$.
--   3. A polynomial of degree less than $k$ is written as its $k$ coefficients $a_0,\dots,a_{k-1}$ (trailing zeros included); a **decoder output** is a list of such polynomials.
--   4. A **term listing** of $Q\in\mathbb F_q[X,Y_0,\dots,Y_d]$ is a list of pairs (exponent vector, coefficient) with distinct exponent vectors and nonzero coefficients whose terms sum to $Q$; each term is written as its exponent list $[a,b_0,\dots,b_d]$ and its coefficient. The **input of the root finder** of Theorem 2.1 is $q,k,d$ and a term listing of $Q$.
--
--   The encodings are injective and of length polynomial in the size of the data, so they neither pad the input nor carry precomputed answers. They let the time bounds of Theorems 2.1 and 4.1 and Corollary 5.1 be stated as step counts of a Turing machine.
--
--   **Formalization Note** The source fixes no input format. Any listing of the terms of $Q$ is accepted; they differ only in order.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), list-decoding problem, p.3; Algorithm 1 (input line), p.26; Theorem 2.1, p.13; Corollary 5.1, p.28

import Mathlib

namespace RSListDecodingCapacity.AllRates

open Polynomial

/-- A list of bits written as the two-bit blocks `0b`, followed by the end marker `10`
(self-delimiting). -/
def encBits (L : List Bool) : List Bool :=
  L.flatMap (fun b => [false, b]) ++ [true, false]

/-- A natural number in binary (`Nat.digits 2`, least significant digit first, no leading zeros),
made self-delimiting by `encBits`. -/
def encNat (k : ℕ) : List Bool :=
  encBits ((Nat.digits 2 k).map fun d => decide (d = 1))

/-- A list, written as its length followed by the codes of its entries. -/
def encList {β : Type*} (f : β → List Bool) (l : List β) : List Bool :=
  encNat l.length ++ l.flatMap f

/-- An element of `𝔽_q = ZMod q`, written as its residue `0, …, q−1` in binary. -/
def encZMod {q : ℕ} (x : ZMod q) : List Bool :=
  encNat x.val

/-- A vector `(v₁, …, vₙ) ∈ 𝔽_qⁿ`, as the list of its entries. -/
def encVec {q n : ℕ} (v : Fin n → ZMod q) : List Bool :=
  encList encZMod (List.ofFn v)

/-- **Input of the list-decoding problem** (p.3, the list-decoding problem; Algorithm 1, p.26;
Corollary 5.1, p.28): `n`, `k`, `q`, the integer agreement threshold `A`, the evaluation points
`α₁, …, αₙ` and the received word `y₁, …, yₙ`, every number in binary. -/
def encDecodingInput {q n : ℕ} (k A : ℕ) (α y : Fin n → ZMod q) : List Bool :=
  encNat n ++ encNat k ++ encNat q ++ encNat A ++ encVec α ++ encVec y

/-- A polynomial of degree less than `k`, written as its `k` coefficients `a₀, …, a_{k−1}`
(trailing zeros included). -/
noncomputable def encPoly {q : ℕ} (k : ℕ) (P : (ZMod q)[X]) : List Bool :=
  encList encZMod ((List.range k).map P.coeff)

/-- **Output of a list decoder**: a list of polynomials of degree less than `k`, each written by
`encPoly k`. -/
noncomputable def encPolyList {q : ℕ} (k : ℕ) (L : List (ZMod q)[X]) : List Bool :=
  encList (encPoly k) L

/-- `l` lists the terms of `Q`: distinct exponent vectors, nonzero coefficients, and the sum of
the listed terms is `Q`. Every polynomial has such listings, which differ only in their order. -/
def IsTermListing {σ R : Type*} [CommSemiring R] (Q : MvPolynomial σ R)
    (l : List ((σ →₀ ℕ) × R)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ t ∈ l, t.2 ≠ 0) ∧
    (l.map fun t => MvPolynomial.monomial t.1 t.2).sum = Q

/-- A term `c · X^a Y₀^{b₀} ⋯ Y_d^{b_d}` of a polynomial in `𝔽_q[X, Y₀, …, Y_d]`: its exponent list
`[a, b₀, …, b_d]` followed by its coefficient. -/
def encTerm {q d : ℕ} (t : (Option (Fin (d + 1)) →₀ ℕ) × ZMod q) : List Bool :=
  encList encNat (t.1 none :: List.ofFn fun j : Fin (d + 1) => t.1 (some j)) ++ encZMod t.2

/-- **Input of the root finder of Theorem 2.1** (p.13): `q`, `k`, `d` and the polynomial
`Q ∈ 𝔽_q[X, Y₀, …, Y_d]`, given as a list of its terms. -/
def encRootFindingInput {q d : ℕ} (k : ℕ) (l : List ((Option (Fin (d + 1)) →₀ ℕ) × ZMod q)) :
    List Bool :=
  encNat q ++ encNat k ++ encNat d ++ encList encTerm l

end RSListDecodingCapacity.AllRates


