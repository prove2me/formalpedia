-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Supplement_Common
-- name    : TwoMasterRoommates_Capped_Supplement_Common
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:32:06.482379+00:00
-- url     : https://prove2.me/theorems/5cf11ea4-7669-48e1-a9ac-711ecfe91976
-- title:
--   Binary codes of numbers, lists, pair functions and matchings; total edge reward
-- statement:
--   All algorithmic statements of this supplement read their input as a binary string. A natural number $k$ is written with a self-delimiting code: each bit of its binary expansion becomes the pair `1 b`, and a final `0` ends the code. An integer is a sign bit followed by the code of its absolute value, and a rational number in lowest terms is the code of its numerator followed by the code of its denominator. A list is the code of its length followed by the codes of its entries. A function $w$ on unordered pairs of $\{0,\dots,n-1\}$ is written as the codes of its values on the pairs $\{i,j\}$ with $i<j$, in lexicographic order. A matching $M$ is written as the list $M(0),\dots,M(n-1)$.
--
--   For a function $w$ on unordered pairs and a perfect matching $M$, the total reward (or weight) is
--
--   $$w(M)=\sum_{v\,:\,v<M(v)} w(\{v,M(v)\}),$$
--
--   each edge counted once.
--
--   All codes are prefix-free and decodable in time polynomial in their length, so concatenations of codes can be parsed uniquely.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 18 (PDF p. 19), Theorem C.1 ('L is the binary input length'); p. 23 (PDF p. 24), Theorem D.1 ('total reward'); encoding convention for the algorithmic claims of Appendices C and D

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Self-delimiting binary code of a natural number: each bit `b` of the little-endian binary
expansion is written as `true, b`, and the code ends with `false`. -/
def encNat (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- Self-delimiting binary code of an integer: a sign bit, then the absolute value. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- Self-delimiting binary code of a rational number in lowest terms: numerator, denominator. -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- Code of a list: its length, then the codes of its entries. -/
def encList {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ l.flatMap f

/-- The unordered pairs `{i, j}` with `i < j`, in lexicographic order. -/
def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => decide (i < j)).map fun j => (i, j)

/-- Code of a pair function: the codes of its values on the pairs `{i, j}`, `i < j`. -/
def encWeights {n : ℕ} {β : Type} (e : β → List Bool) (w : Sym2 (Fin n) → β) : List Bool :=
  (pairs n).flatMap fun p => e (w s(p.1, p.2))

/-- Total reward (weight) of a matching `M`: each edge `{v, M v}` with `v < M v` counted once. -/
def edgeSum {n : ℕ} {β : Type} [AddCommMonoid β] (w : Sym2 (Fin n) → β)
    (M : Fin n → Fin n) : β :=
  ∑ v ∈ Finset.univ.filter (fun v => v < M v), w s(v, M v)

/-- Code of a matching on `Fin n`: the list `M 0, …, M (n-1)` of partner indices. -/
def encM {n : ℕ} (M : Fin n → Fin n) : List Bool :=
  encList (fun v : Fin n => encNat (M v).val) (List.finRange n)

end TwoMasterRoommates.Capped.Supplement


