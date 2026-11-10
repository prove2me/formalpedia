-- Prove2me | Definitions.Def_OptStochMatch_Tight_Machine
-- name    : OptStochMatch_Tight_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:39.318688+00:00
-- url     : https://prove2.me/theorems/584e19a7-e0bd-4b7a-9880-8a3e386ae3a4
-- title:
--   Explicit binary input and per-arrival polynomial-time randomized Turing machines
-- statement:
--   The explicit input lists the types with positive rate, each once in any order, with its rational rate in binary ($\lambda=n\mu$ for an i.i.d. instance). At each arrival a deterministic multi-stack Turing machine (Mathlib's `Turing.TM2ComputableInPolyTime`: running time bounded by a polynomial in the input length) reads the encoded instance, the unmatched set and the arriving type (as $m$-bit strings) and $B=p(|\text{input}|+m)$ fresh fair random bits, and outputs the index of the vertex to match (empty output, an index $\ge m$, or a vertex that is not an unmatched neighbour means rejection). The induced routing probability of vertex $i$ is the fraction of the $2^B$ random strings on which the output is $i$.
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §6, p. 26 (PDF 27); Theorem 6.5, p. 30 (PDF 31)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §6, p. 26 (PDF 27) and §6.3, Theorem 6.5, p. 30 (PDF 31).

The computational model of Section 6: "We assume that the neighborhoods with positive rates or
probabilities are listed explicitly, with rational values encoded in binary. In the i.i.d.
model, we use `λ_S = nµ_S`. Computational complexity is measured in the length of this explicit
input and in `m`."

* The explicit input is a list `L` of pairs `(S, λ_S)`, one for each type with `λ_S > 0`, in
  any order, with `λ_S ∈ ℚ` (`IsListing`).
* Binary encodings: a type `S ⊆ [m]` is its `m`-bit indicator string; a rational is its
  numerator and denominator in binary (`Nat.bits`, least significant bit first). Variable-length
  fields are made self-delimiting by doubling each bit (`b ↦ true, b`) and appending
  `false, false`.
* Per arrival, a deterministic Turing machine (Mathlib's `Turing.TM2ComputableInPolyTime`, a
  multi-stack machine whose running time is bounded by a polynomial in the input length) reads
  the encoded instance, the current set of unmatched vertices, the arriving type and a block of
  `B` fresh fair random bits, `B` a fixed polynomial in the instance length plus `m`. Its output
  bit string is read as a vertex index (`[]` = reject; an index `≥ m`, or a vertex that is not
  an unmatched neighbour, is a rejection).

The machine sees only the explicit input, the unmatched set, the arriving type and random bits:
no arrival times, no further memory. The paper's algorithm is of this form ("Its decisions
depend only on the set of unmatched vertices and the known neighborhood distribution", p. 26).
Per-arrival recomputation from the explicit input subsumes polynomial preprocessing.
-/

namespace OptStochMatch.Tight

open scoped NNReal BigOperators

/-- Self-delimiting encoding of a bit string: each bit `b` becomes `true, b`; then
`false, false` ends the field. -/
def selfDelim (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false, false]

/-- A set `A ⊆ [m]` as its `m`-bit indicator string. -/
def encSet (m : ℕ) (A : Finset (Fin m)) : List Bool := List.ofFn fun i : Fin m => decide (i ∈ A)

/-- A rational number in binary: numerator (absolute value) and denominator. Only positive
rationals occur. -/
def encRat (q : ℚ) : List Bool := selfDelim (Nat.bits q.num.natAbs) ++ selfDelim (Nat.bits q.den)

/-- One entry `(S, λ_S)` of the explicit input. -/
def encEntry {m : ℕ} (e : Ty m × ℚ) : List Bool := selfDelim (encSet m e.1) ++ encRat e.2

/-- The explicit input: each entry is preceded by `true`; the list ends with `false`. -/
def encInstance {m : ℕ} (L : List (Ty m × ℚ)) : List Bool :=
  L.flatMap (fun e => true :: encEntry e) ++ [false]

/-- `L` lists exactly the types with positive rate, each once, with its (rational) rate. -/
def IsListing {m : ℕ} (lam : Ty m → ℝ≥0) (L : List (Ty m × ℚ)) : Prop :=
  (L.map Prod.fst).Nodup ∧ (∀ e ∈ L, 0 < e.2 ∧ ((lam e.1 : ℝ) = (e.2 : ℝ))) ∧
    ∀ S : Ty m, 0 < lam S → ∃ q : ℚ, (S, q) ∈ L

/-- The machine input at an arrival: instance, unmatched set, arriving type, random bits. -/
def machineInput {m : ℕ} (L : List (Ty m × ℚ)) (A S : Finset (Fin m)) (r : List Bool) :
    List Bool :=
  encInstance L ++ selfDelim (encSet m A) ++ selfDelim (encSet m S) ++ r

/-- Binary string (least significant bit first) to natural number. -/
def bitsToNat (l : List Bool) : ℕ := l.foldr (fun b k => Nat.bit b k) 0

/-- Output decoding: `[]` is a rejection; otherwise the encoded index, if it is `< m`. -/
def decodeVertex (m : ℕ) (out : List Bool) : Option (Fin m) :=
  if out = [] then none else
    if h : bitsToNat out < m then some ⟨bitsToNat out, h⟩ else none

/-- Number of fair random bits supplied per arrival: `p(|enc(L)| + m)`. -/
def randomBits {m : ℕ} (p : Polynomial ℕ) (L : List (Ty m × ℚ)) : ℕ :=
  p.eval ((encInstance L).length + m)

/-- The routing rule implemented by the machine `f` with random-bit budget `p` on the explicit
input `L`: the probability of routing to `i` is the fraction of the `2^B` random strings on
which `f` outputs `i`. -/
noncomputable def machineRule {m : ℕ} (f : List Bool → List Bool) (p : Polynomial ℕ)
    (L : List (Ty m × ℚ)) : RoutingRule m where
  prob := fun _ h S i =>
    ((Finset.univ.filter fun r : Fin (randomBits p L) → Bool =>
        decodeVertex m (f (machineInput L (unmatchedSet h) S (List.ofFn r))) = some i).card : ℝ) /
      (2 : ℝ) ^ (randomBits p L)

/-- `f` is computed by a deterministic multi-stack Turing machine in time polynomial in the
length of its input (Mathlib's `Turing.TM2ComputableInPolyTime`, identity encodings over
`Bool`). -/
def PolyTimeBits (f : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (id : List Bool → List Bool) f)

end OptStochMatch.Tight


