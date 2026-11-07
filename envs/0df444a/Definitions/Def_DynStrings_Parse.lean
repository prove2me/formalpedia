-- Prove2me | Definitions.Def_DynStrings_Parse
-- name    : DynStrings_Parse
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:45.581934+00:00
-- url     : https://prove2.me/theorems/1b4c0e3b-9ca2-4e97-9922-8f5166c33cb0
-- title:
--   Restricted block compression: run and block rounds, level words $S_k$, boundaries $B_k$, phrases, the grammar and its size, and the random orders
-- statement:
--   Restricted block compression of a string $S$, for a choice of the orders.
--
--   A choice of the orders is, for every even $k\ge2$, a strict total order $\prec_k$ on structural symbols in which paused symbols precede active ones. Starting from $S_0=S$, round $k$ produces $S_k$ from $S_{k-1}$:
--
--   1. for odd $k$ (run round), every maximal run $A^r$ with $r\ge2$ and $A$ active in round $k$ is replaced by the symbol $(A,r)$;
--   2. for even $k$ (block round), $S_{k-1}$ is cut into blocks, with a boundary at both ends and between positions $i$ and $i+1$ ($1\le i<|S_{k-1}|$) whenever $S_{k-1}[i]$ or $S_{k-1}[i+1]$ is paused, or $i>1$ and $S_{k-1}[i-1]\succ_k S_{k-1}[i]\prec_k S_{k-1}[i+1]$; every block of length $s\ge2$ is replaced by its tuple.
--
--   With $b_k(j)=|\mathrm{val}(S_k[1..j])|$, the level-$k$ boundaries are $B_k=\{b_k(j):0\le j\le|S_k|\}$, and $S_k[j]$ represents the level-$k$ phrase $S(b_k(j-1)..b_k(j)]$. The grammar of $S$ is the set of symbols labelling the nodes of the parse tree, the unfolding of the root reached after $\kappa(|S|)$ rounds, and its size is its run-length straight-line program size. The margin of eq. (1) is $\mu_k=2\lfloor 8\ell_k\rfloor$.
--
--   The random orders of the paper are random orders $\prec_k$ such that every realization is a choice of the orders, the restriction of $\prec_k$ to every fixed finite set of active symbols is a uniformly random ordering, and the orders of different rounds are independent.
--
--   **Formalization Note** Level words are lists with 0-based indices; the boundary rule is the source's with $i=c$ for the cut $c$ between the 0-based symbols $c-1$ and $c$. A phrase is recorded by its two end cuts and its symbol. The grammar is the unfolding of the symbols of $S_{\kappa(|S|)}$, which by Fact 4.4 is the single root of a non-empty string. `IsRandomOrders` requires measurability of each order for the product σ-algebra on relations, uniformity as "each listing of $n$ distinct well-formed active symbols is increasing with probability $1/n!$", and independence of the rounds $k$ even, $k\ge2$.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), §4.2, p.15 (random orders); Definition 4.2, pp.15–16; §4.3, pp.16–17 (phrases, boundaries, κ, Definition 4.5, grammar); p.13 (size); eq. (1), p.18 (μ_k)

import Mathlib
import Definitions.Def_DynStrings_Strings
import Definitions.Def_DynStrings_StrSym

namespace DynStrings

/-!
# Restricted block compression: the parse, phrases, the grammar and the random orders

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), §4.2, p.15 (random orders), Definition 4.2, pp.15–16 (restricted block
compression), §4.3, pp.16–17 (level words, boundaries, phrases, parse tree, grammar), p.13
(RLSLP size), and eq. (1), p.18 (`μ_k`).

**Formalization Note.**
* A *choice of the orders* is a family `lt : ℕ → StrSym α → StrSym α → Prop`; for every even
  `k ≥ 2`, `lt k` is a strict total order (`A ≺_k B`) in which paused symbols precede active ones
  (`IsOrderFamily`). The relations at odd `k` and at `k = 0` are never read by the parse.
* Level words are `List (StrSym α)` with 0-based indices. The block round places a boundary at cut
  `c` (between the symbols `w[c-1]` and `w[c]`, 0-based) when `c = 0`, `c = |w|`, or `0 < c < |w|`
  and `w[c-1]` or `w[c]` is paused, or `1 < c` and `w[c-1]` is a local minimum
  (`w[c-2] ≻_k w[c-1] ≺_k w[c]`). This is Definition 4.2(ii) with the paper's 1-based `i = c`.
* `bnd lt S k j = b_k(j) = |val(S_k[1..j])|`, `boundaries lt S k = B_k`, and
  `IsPhrase lt S k x y A` says that the 0-based symbol `S_k[j]` (the paper's `S_k[j+1]`) is `A`
  and represents the fragment `S(x..y]`.
* `grammar lt S` is the set of symbols labelling the nodes of the parse tree: the union of the
  unfoldings of the symbols of `S_{κ(|S|)}`. By Fact 4.4 this level word is the single root
  symbol for non-empty `S`, so this is the unfolding of the root (Definition 4.5); for the empty
  string it is empty.
* `IsRandomOrders μ ord` is the paper's assumption on the random orders (§4.2): every realization
  is a choice of the orders, each `ord k` (even `k ≥ 2`) is a random variable for the product
  σ-algebra on relations, its restriction to every finite set of distinct well-formed symbols
  active in round `k` is a uniformly random ordering (each listing is increasing with probability
  `1/n!`), and the orders of different rounds are independent.
-/

open MeasureTheory ProbabilityTheory

variable {α : Type}

/-- A choice of the orders (§4.2): for every even `k ≥ 2`, `≺_k = lt k` is a strict total order
on structural symbols in which paused symbols precede active symbols with respect to round `k`. -/
structure IsOrderFamily (lt : ℕ → StrSym α → StrSym α → Prop) : Prop where
  strictTotal : ∀ k, Even k → 2 ≤ k → IsStrictTotalOrder (StrSym α) (lt k)
  pausedFirst : ∀ k, Even k → 2 ≤ k → ∀ A B : StrSym α, ¬ Active k A → Active k B → lt k A B

variable [DecidableEq α]

open Classical in
/-- Run round `k` (Definition 4.2(i)): every maximal run `A^r` with `r ≥ 2` and `A ∈ 𝒜_k` is
replaced by the single symbol `(A, r)`. -/
noncomputable def runRound (k : ℕ) (w : List (StrSym α)) : List (StrSym α) :=
  (w.splitBy (fun a b => decide (a = b))).flatMap fun g =>
    match g with
    | [] => []
    | A :: _ => if 2 ≤ g.length ∧ Active k A then [StrSym.run A g.length] else g

/-- Block boundary at cut `c` of `w` in block round `k` (Definition 4.2(ii)), 0-based: the two
ends, or `0 < c < |w|` and one of `w[c-1]`, `w[c]` is paused, or `1 < c` and `w[c-1]` is a local
minimum `w[c-2] ≻_k w[c-1] ≺_k w[c]`. -/
def IsCut (lt : ℕ → StrSym α → StrSym α → Prop) (k : ℕ) (w : List (StrSym α)) (c : ℕ) : Prop :=
  c = 0 ∨ c = w.length ∨
    (0 < c ∧ c < w.length ∧
      ((∃ A, w[c - 1]? = some A ∧ ¬ Active k A) ∨ (∃ A, w[c]? = some A ∧ ¬ Active k A) ∨
        (1 < c ∧ ∃ A B C, w[c - 2]? = some A ∧ w[c - 1]? = some B ∧ w[c]? = some C ∧
          lt k B A ∧ lt k B C)))

open Classical in
/-- The block boundaries of round `k`, as an increasing list of cuts of `w`. -/
noncomputable def cuts (lt : ℕ → StrSym α → StrSym α → Prop) (k : ℕ) (w : List (StrSym α)) :
    List ℕ :=
  (List.range (w.length + 1)).filter (fun c => decide (IsCut lt k w c))

/-- The blocks formed in round `k`, as index intervals `[a, b)` of `w` (0-based), from left to
right. -/
noncomputable def blockIntervals (lt : ℕ → StrSym α → StrSym α → Prop) (k : ℕ)
    (w : List (StrSym α)) : List (ℕ × ℕ) :=
  (cuts lt k w).zip (cuts lt k w).tail

/-- Block round `k` (Definition 4.2(ii)): every block `A₁ ⋯ A_s` with `s ≥ 2` is replaced by the
single symbol `(A₁, …, A_s)`; blocks of length one are left unchanged. -/
noncomputable def blockRound (lt : ℕ → StrSym α → StrSym α → Prop) (k : ℕ)
    (w : List (StrSym α)) : List (StrSym α) :=
  (blockIntervals lt k w).flatMap fun p =>
    if 2 ≤ p.2 - p.1 then [StrSym.tuple (frag w p.1 p.2)] else frag w p.1 p.2

/-- Round `k`: a run round for odd `k`, a block round for even `k`. -/
noncomputable def round (lt : ℕ → StrSym α → StrSym α → Prop) (k : ℕ) (w : List (StrSym α)) :
    List (StrSym α) :=
  if k % 2 = 1 then runRound k w else blockRound lt k w

/-- The level-`k` word `S_k` of `S` (Definition 4.2): `S_0 = S` (as terminals) and `S_k` is
round `k` applied to `S_{k-1}`. -/
noncomputable def level (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) : ℕ → List (StrSym α)
  | 0 => S.map StrSym.term
  | k + 1 => round lt (k + 1) (level lt S k)

/-- `b_k(j) = |val(S_k[1..j])|` (§4.3, p.16). -/
noncomputable def bnd (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) (k j : ℕ) : ℕ :=
  (StrSym.valL ((level lt S k).take j)).length

/-- The set `B_k = {b_k(j) : 0 ≤ j ≤ |S_k|}` of level-`k` boundaries (§4.3, p.16). -/
noncomputable def boundaries (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) (k : ℕ) :
    Finset ℕ :=
  (Finset.range ((level lt S k).length + 1)).image (bnd lt S k)

/-- `S(x..y]` is a level-`k` phrase represented by the symbol `A` (§4.3, p.16): some symbol
`S_k[j]` (0-based) equals `A` and `b_k(j) = x`, `b_k(j+1) = y`. -/
def IsPhrase (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) (k x y : ℕ) (A : StrSym α) :
    Prop :=
  ∃ j, (level lt S k)[j]? = some A ∧ bnd lt S k j = x ∧ bnd lt S k (j + 1) = y

/-- The grammar of `S` (§4.3, p.17): the set of symbols labelling the nodes of the parse tree
`T(S)`, obtained by unfolding the symbols of `S_{κ(|S|)}` (the root, for non-empty `S`). -/
noncomputable def grammar (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) :
    Finset (StrSym α) :=
  StrSym.symsL (level lt S (kappa S.length))

/-- The size of restricted block compression of `S`: the RLSLP size of its grammar, one unit per
terminal, one per run and `s` per tuple of arity `s` (p.13). -/
noncomputable def size (lt : ℕ → StrSym α → StrSym α → Prop) (S : List α) : ℕ :=
  ∑ A ∈ grammar lt S, StrSym.weight A

/-- The margin `μ_k = 2⌊8ℓ_k⌋` (eq. (1), p.18). -/
noncomputable def muk (k : ℕ) : ℕ := 2 * ⌊8 * ell k⌋₊

/-- The random orders of §4.2: a family `ord k ω` of relations on structural symbols such that
1. every realization `fun k => ord k ω` is a choice of the orders;
2. for even `k ≥ 2`, `ord k` is measurable for the product σ-algebra on relations;
3. for even `k ≥ 2` and every list `L` of distinct well-formed symbols active in round `k`, the
   probability that `L` is increasing in `≺_k` is `1/|L|!` (the restriction of `≺_k` to a finite
   set of active symbols is a uniformly random ordering);
4. the orders of the different rounds `k` (even, `k ≥ 2`) are independent. -/
structure IsRandomOrders {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (ord : ℕ → Ω → StrSym α → StrSym α → Prop) : Prop where
  family : ∀ ω, IsOrderFamily (fun k => ord k ω)
  measurable : ∀ k, Even k → 2 ≤ k → Measurable (ord k)
  uniform : ∀ k, Even k → 2 ≤ k → ∀ L : List (StrSym α), L.Nodup →
    (∀ A ∈ L, StrSym.WF A ∧ Active k A) →
    μ {ω | L.IsChain (ord k ω)} = 1 / (L.length.factorial : ENNReal)
  indep : iIndepFun (fun (k : {k : ℕ // Even k ∧ 2 ≤ k}) ω => ord k.1 ω) μ

end DynStrings


