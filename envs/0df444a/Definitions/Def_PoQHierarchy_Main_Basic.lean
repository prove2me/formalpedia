-- Prove2me | Definitions.Def_PoQHierarchy_Main_Basic
-- name    : PoQHierarchy_Main_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:40:37.348797+00:00
-- url     : https://prove2.me/theorems/52a502f0-7f0e-461b-920f-1880b86a960a
-- title:
--   Strings, polynomial bounds, weighted lists, schedules $B(n,k)$ and fixed-length codes
-- statement:
--   This file fixes the elementary vocabulary of the mission.
--
--   1. **Strings.** $\{0,1\}^*$ is the published type `QAlgorithms.Complexity.Str` of finite lists of bits. The security parameter is given in unary, $1^\lambda$.
--   2. **Polynomial bounds.** A function $f:\mathbb N\to\mathbb N$ is *polynomially bounded* if $f(m)\le p(m)$ for all $m$ and some polynomial $p$ with natural coefficients.
--   3. **Codes.** A list of strings is coded injectively as one string (each bit $b$ becomes $1b$ and every item is closed by $0$); natural numbers are written in binary.
--   4. **Finite distributions.** A *weighted list* is a finite list of pairs (weight, value); it represents the finitely supported distribution in which a value has the sum of its weights as probability. Sequential sampling multiplies weights, and expectations and probabilities are finite sums. The random coins of an algorithm are the uniform distribution on $\{0,1\}^c$.
--   5. **Schedules.** For integers $0\le k\le n$,
--   $$B(n,k)=\{b\in\{0,1\}^n : \mathrm{wt}(b)=k\}$$
--   is the set of bit strings of length $n$ and Hamming weight exactly $k$. A schedule $b\in B(n,k)$ marks with $b_i=1$ the rounds in which a prover invokes its quantum device, and $I_b=\{i: b_i=1\}$. The schedule $1^n\in B(n,n)$ invokes the device in every round.
--   6. **Fixed-length codes.** An element $j$ of a finite set $\{0,\dots,m-1\}$ is coded by the one-hot string of length $m$; all elements of the set have codes of the same length, and decoding returns the element whose code a string is, if any.
--
--   These conventions are shared by every statement of the mission: all probabilities are finite sums over weighted lists, and all questions and answers of a compiled game are sent as fixed-length codes, so that two questions of the same player are messages of equal length.
--
--   **Formalization Note** Rounds and players are indexed by `Fin n`, i.e. $0,\dots,n-1$ for the paper's $1,\dots,n$.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.18 (B(n,k), negligible functions, [n]), p.26 (schedules); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_QAlgorithms_ClassicalStringComputability

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, *A Hierarchy of Proofs of Quantumness*, STOC 2027 submission
#1666 (October 2026), §3 (p.18) and §4.2 (pp.25–26): the elementary vocabulary.

* strings `Str = {0,1}*` (the published `QAlgorithms.Complexity.Str`);
* polynomially bounded functions;
* the unary security parameter `1^λ`;
* a self-delimiting encoding of lists of strings, and binary numerals;
* finite weighted lists, used for every probability distribution of the mission;
* the schedule sets `B(n,k)` of p.18;
* fixed-length binary codes of the finite question and answer sets.
-/

/-- `f : ℕ → ℕ` is bounded by a polynomial. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ m, f m ≤ p.eval m

/-- The security parameter in unary, `1^λ`. -/
def unary (lam : ℕ) : Str := List.replicate lam true

/-- Self-delimiting code of one string: each bit `b` becomes `1b`, and a final `0` closes it. -/
def packOne (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- The injective code of a list of strings as one string. -/
def pack (l : List Str) : Str := l.flatMap packOne

/-- Parser for `pack`; `cur` is the reversed current item. A truncated last item is dropped. -/
def unpackAux : Str → Str → List Str
  | [], _ => []
  | false :: rest, cur => cur.reverse :: unpackAux rest []
  | true :: b :: rest, cur => unpackAux rest (b :: cur)
  | [true], _ => []

/-- The inverse of `pack`, total on all strings. -/
def unpack (s : Str) : List Str := unpackAux s []

/-- Binary numeral of a natural number, least significant bit first. -/
def natCode (m : ℕ) : Str := Nat.bits m

/-- The number written by a string, least significant bit first. -/
def bitsVal (s : Str) : ℕ := s.foldr (fun b acc => 2 * acc + b.toNat) 0

/-- All bit strings of length `c`. -/
def allStrings : ℕ → List Str
  | 0 => [[]]
  | c + 1 => (allStrings c).flatMap (fun s => [false :: s, true :: s])

/-! ### Finite weighted lists -/

/-- A finite weighted list: a finitely supported (sub-)distribution, written as a list of
weight–value pairs. A value may occur several times; its probability is the sum of its weights. -/
abbrev WList (α : Type) := List (ℝ × α)

/-- The point mass. -/
def WList.pure {α : Type} (a : α) : WList α := [(1, a)]

/-- Sequential composition: sample `a` from `d`, then from `f a`; weights multiply. -/
def WList.bind {α β : Type} (d : WList α) (f : α → WList β) : WList β :=
  d.flatMap (fun p => (f p.2).map (fun q => (p.1 * q.1, q.2)))

/-- The expectation of `f` under `d`. -/
def WList.expect {α : Type} (d : WList α) (f : α → ℝ) : ℝ :=
  (d.map (fun p => p.1 * f p.2)).sum

/-- The probability of the Boolean event `e` under `d`. -/
def WList.prob {α : Type} (d : WList α) (e : α → Bool) : ℝ :=
  d.expect (fun a => if e a then 1 else 0)

/-- `a` lies in the support of `d`: its total weight is positive. -/
def WList.InSupport {α : Type} [DecidableEq α] (d : WList α) (a : α) : Prop :=
  0 < d.prob (fun b => decide (b = a))

/-- Independent product of a list of weighted lists. -/
def WList.seq {α : Type} : List (WList α) → WList (List α)
  | [] => WList.pure []
  | d :: ds => d.bind (fun a => (WList.seq ds).bind (fun as => WList.pure (a :: as)))

/-- The uniform distribution on bit strings of length `c` (the random coins). -/
noncomputable def coinDist (c : ℕ) : WList Str :=
  (allStrings c).map (fun s => ((2 : ℝ)⁻¹ ^ c, s))

/-! ### Schedules (p.18, p.26) -/

/-- `B(n,k)`: bit strings of length `n` and Hamming weight exactly `k` (p.18). A schedule
`b ∈ B(n,k)` marks with `b i = true` the rounds in which a prover invokes its device (p.26).
Rounds are indexed by `Fin n`, i.e. `0, …, n-1` for the paper's `1, …, n`. -/
def Schedule (n k : ℕ) : Type :=
  {b : Fin n → Bool // (Finset.univ.filter (fun i => b i = true)).card = k}

/-- The set `I_b = {i ∈ [n] : b_i = 1}` of positions at which a schedule equals `1`. -/
def Schedule.ones {n k : ℕ} (b : Schedule n k) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b.val i = true)

/-- The schedule `1^n ∈ B(n,n)`: one invocation in every round. -/
def Schedule.allOnes (n : ℕ) : Schedule n n :=
  ⟨fun _ => true, by simp⟩

/-! ### Fixed-length codes of finite sets -/

/-- The code of `j ∈ Fin m`: the one-hot string of length `m`. All codes of `Fin m` have the
same length `m`. -/
def codeFin (m : ℕ) (j : Fin m) : Str := List.ofFn (fun t : Fin m => decide (t = j))

/-- Decoding: the element whose code is `s`, if there is one. -/
def decodeFin (m : ℕ) (s : Str) : Option (Fin m) :=
  (List.finRange m).find? (fun j => decide (codeFin m j = s))

end PoQHierarchy.Main


