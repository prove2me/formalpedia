-- Prove2me | Definitions.Def_SpaceReset_Hardness_Coding
-- name    : SpaceReset_Hardness_Coding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:30.019203+00:00
-- url     : https://prove2.me/theorems/d6050d73-d0ed-46e4-8541-ead002e2055a
-- title:
--   Binary codes of numbers, matrices, orders and graphs
-- statement:
--   Every finite object used in a polynomial-time or NP-hardness clause of this mission is written as a binary string in a fixed way. A natural number $a$ is written as the two-bit blocks $0b$, one for each binary digit $b$ of $a$ (least significant first, no leading zeros), followed by the terminator $10$; its code has $2(\lfloor\log_2 a\rfloor+2)$ bits ($2$ bits for $a=0$). A finite list of natural numbers is written as the concatenation of the codes of its entries, which can be decoded uniquely from left to right.
--
--   Objects are listed as natural numbers in a fixed layout:
--
--   1. a binary matrix $G\in\mathbb F_2^{k\times n}$ as $k,n$ followed by its entries row by row;
--   2. a coordinate permutation $\pi$ of $\{0,\dots,n-1\}$ as $n,\pi(0),\dots,\pi(n-1)$;
--   3. a simple graph on $\{0,\dots,s-1\}$ as $s$ followed by its adjacency matrix row by row;
--   4. a rational number as its sign bit, the absolute value of its reduced numerator, and its denominator;
--   5. a labelling $\{0,\dots,k-1\}\to\{0,\dots,q-1\}$ as $k,q$ followed by the labels.
--
--   All codes have length polynomial in the bit size of the object, so they are a standard explicit input representation for Cook-style polynomial-time computation.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), §1.5.3, p. 7; §3.2–3.3, pp. 26–28; App. D, pp. 41–44 (explicit input representations)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness

/-!
Rinka Miura, *The Complexity of Space–Reset Tradeoffs in Online Quantum Computation*, STOC 2027
submission #1715 (October 2026): the binary codings used to state the polynomial-time and
NP-hardness clauses (§1.5.3, p. 7; §3.2–3.3, pp. 26–28; App. D, pp. 41–44).

Every finite object (a binary matrix, an order, a graph, a budget, a circuit, …) is first listed
as a finite list of natural numbers in a fixed layout, and the list is written as a binary string.
A natural number `a` is written as the two-bit blocks `0b` for the binary digits `b` of `a`
(least significant first, no leading zeros) followed by the terminator `10`; its code has
`2(⌊log₂ a⌋ + 2)` bits (two bits for `a = 0`), so every code is polynomial in the bit size of
the object and the concatenation of codes is uniquely decodable from left to right.
-/

/-- Binary code of one natural number: blocks `0b` per binary digit, then the terminator `10`. -/
def encNat (a : ℕ) : List Bool :=
  (Nat.bits a).flatMap (fun b => [false, b]) ++ [true, false]

/-- Binary code of a list of natural numbers: the concatenation of the codes of its entries. -/
def encNats (l : List ℕ) : List Bool :=
  l.flatMap encNat

/-- A binary matrix `G ∈ 𝔽₂^{k×n}` as a list: `k`, `n`, then the entries row by row (`0`/`1`). -/
def specNats {k n : ℕ} (G : Matrix (Fin k) (Fin n) (ZMod 2)) : List ℕ :=
  [k, n] ++ (List.finRange k).flatMap (fun i => (List.finRange n).map (fun j => (G i j).val))

/-- A coordinate permutation `π` of `{0,…,n−1}` as a list: `n`, then `π(0), …, π(n−1)`. -/
def permNats {n : ℕ} (π : Equiv.Perm (Fin n)) : List ℕ :=
  [n] ++ (List.finRange n).map (fun j => (π j).val)

/-- A simple graph on `{0,…,s−1}` as a list: `s`, then its adjacency matrix row by row
(`1` for an edge, `0` otherwise). -/
def graphNats {s : ℕ} (X : SimpleGraph (Fin s)) : List ℕ := by
  classical
  exact [s] ++ (List.finRange s).flatMap
    (fun u => (List.finRange s).map (fun v => if X.Adj u v then 1 else 0))

/-- A rational number as a list: sign bit (`1` for negative), `|numerator|`, denominator of
its reduced form. -/
def ratNats (x : ℚ) : List ℕ :=
  [if x < 0 then 1 else 0, x.num.natAbs, x.den]

/-- A vertex labelling `Fin k → Fin q` as a list: `k`, `q`, then the labels. -/
def labelNats {k q : ℕ} (col : Fin k → Fin q) : List ℕ :=
  [k, q] ++ (List.finRange k).map (fun i => (col i).val)

end SpaceReset.Hardness


