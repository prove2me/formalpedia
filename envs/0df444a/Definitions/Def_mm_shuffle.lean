-- Prove2me | Definitions.Def_mm_shuffle
-- name    : mm_shuffle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T20:43:46.089218+00:00
-- url     : https://prove2.me/theorems/443eee0c-f4d6-4b4f-a25b-f2ea4e11c94f
-- title:
--   The four card shuffles: transpositions, riffle, adjacent transpositions, reversals
-- statement:
--   This file defines the card-shuffling chains of Chapters 8 and 16 of Levin–Peres–Wilmer. All of them are random walks on the symmetric group: a deck of $n$ cards is a permutation of $\{0,\dots,n-1\}$, an increment measure $\mu$ assigns probabilities to shuffling moves, and the walk steps from $a$ to $\sigma a$ with probability $\mu(\sigma)$ — equivalently, its transition matrix is $P(a,b)=\mu(ba^{-1})$.
--
--   **Random transpositions.** Choose two cards independently and uniformly and swap them (doing nothing if the same card is chosen twice). The increment measure gives the identity mass $1/n$, each transposition mass $2/n^2$, and every other permutation mass $0$.
--
--   **Random adjacent transpositions (lazy).** With probability $\tfrac12$ do nothing; otherwise swap a uniformly chosen pair of neighbouring positions: mass $1/2$ on the identity and $1/\bigl(2(n-1)\bigr)$ on each adjacent transposition $(i,\,i+1)$, $0\le i\le n-2$.
--
--   **The riffle shuffle.** The **inverse riffle** is performed by labels: each card receives an independent uniform bit, and the cards labeled $0$ are pulled to the top, both blocks preserving their relative order. Formally, a bit assignment $b$ determines the permutation $\sigma_b$ that stably sorts the bit string of the deck $x$, and
--   $$Q(x,y)=\frac{\#\{b\in\{0,1\}^n:\ y=x\circ\sigma_b\}}{2^n}.$$
--   The forward **riffle shuffle** (the Gilbert–Shannon–Reeds cut-and-interleave shuffle) is its time reversal, obtained by transposing $Q$ — legitimate because the stationary distribution is uniform.
--
--   **The $L$-reversal chain (Chapter 16).** States are circular arrangements, i.e. permutations of $\mathbb Z_n$. A move picks a starting position $i\in\mathbb Z_n$ and a length $k\in\{0,\dots,L-1\}$ uniformly and reverses the circular arc from $i$ to $i+k$, fixing everything else; the reversal with parameters $(i,k)$ is the permutation sending each $j$ on the arc to its mirror image $2i+k-j$. The increment measure counts parameter pairs,
--   $$\mu(g)=\frac{\#\{(i,k):\ g\ \text{is the}\ (i,k)\text{-reversal}\}}{nL},$$
--   so, for example, the identity — the $(i,0)$-reversal for every $i$ — receives mass $1/L$.
--
--   **Conventions.** Division is total ($r/0=0$), covering the degenerate deck sizes $n\le1$; that each measure is a probability distribution and each walk a stochastic matrix is proved in the theorems.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 8, Sections 8.1-8.3 and Ch. 16, Sections 16.1-16.2, pp. 99-109 and 217-223

import Definitions.Def_mm_mixing
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.ZMod.Basic

/-!
Card-shuffling chains, following Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, Chapter 8 (random transpositions, riffle shuffles) and
Chapter 16 (random adjacent transpositions and the `L`-reversal chain).

All of these are random walks on a symmetric group; decks are encoded as in
`topToRandom` (`x p` is the card at position `p`).
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

/-- The increment distribution of the **random transpositions** shuffle:
choose two cards independently and uniformly and exchange them, so the
identity has probability `1/n` and each transposition probability `2/n²`
(LPW §8.1). -/
def transpositionDist (n : ℕ) : Equiv.Perm (Fin n) → ℝ :=
  fun g =>
    if g = 1 then 1 / n
    else if ∃ i j : Fin n, i ≠ j ∧ g = Equiv.swap i j then 2 / (n : ℝ) ^ 2
    else 0

/-- The **random transpositions** chain on `n` cards (LPW §8.1–8.2). -/
def randomTranspositions (n : ℕ) :
    Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ :=
  groupWalk (transpositionDist n)

/-- The increment distribution of the lazy **random adjacent
transpositions** shuffle: probability `1/2` for the identity and
`1/(2(n-1))` for each adjacent transposition `(i, i+1)` (LPW §16.1). -/
def adjacentTranspositionDist (n : ℕ) : Equiv.Perm (Fin n) → ℝ :=
  fun g =>
    if g = 1 then 1 / 2
    else if ∃ i : Fin n, i.val + 1 < n ∧
        g = Equiv.swap i ⟨(i.val + 1) % n, Nat.mod_lt _ i.pos⟩ then
      1 / (2 * ((n : ℝ) - 1))
    else 0

/-- One **inverse riffle shuffle** (LPW §8.3.1): assign to each card an
independent uniform bit, then move the cards labeled `0` to the top of the
deck, preserving the relative order within each class.  For decks `x`, `y`,
the entry is the fraction of the `2^n` bit assignments that turn `x` into
`y`; the stable sorting of positions by bit is `Tuple.sort`. -/
def inverseRiffle (n : ℕ) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ :=
  fun x y =>
    ((Finset.univ.filter fun b : Fin n → Bool =>
        ∀ q : Fin n, y q = x (Tuple.sort (fun p : Fin n => b (x p)) q)).card : ℝ) /
      2 ^ n

/-- The (GSR) **riffle shuffle** (LPW §8.3): the time reversal of the inverse
riffle shuffle — since the stationary distribution is uniform,
`P_riffle(x,y) = P_inverse(y,x)`. -/
def riffleShuffle (n : ℕ) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ :=
  fun x y => inverseRiffle n y x

/-- `g` is the reversal `ρ_{i,i+k}` of the circular segment
`[i, i+k]` (positions mod `n`): it maps `j` in the segment to
`i + (i+k) − j` and fixes everything else (LPW §16.2). -/
def IsCircularReversal (n : ℕ) [NeZero n] (i : ZMod n) (k : ℕ)
    (g : Equiv.Perm (ZMod n)) : Prop :=
  ∀ j : ZMod n, g j = if (j - i).val ≤ k then i + i + (k : ZMod n) - j else j

instance (n : ℕ) [NeZero n] (i : ZMod n) (k : ℕ) (g : Equiv.Perm (ZMod n)) :
    Decidable (IsCircularReversal n i k g) :=
  inferInstanceAs (Decidable (∀ j : ZMod n,
    g j = if (j - i).val ≤ k then i + i + (k : ZMod n) - j else j))

/-- The increment distribution of the **`L`-reversal chain** (LPW §16.2):
choose a circular position `i` and a length `k < L` uniformly, and reverse
the segment `[i, i+k]`. -/
def lReversalDist (n L : ℕ) [NeZero n] : Equiv.Perm (ZMod n) → ℝ :=
  fun g =>
    (((Finset.univ ×ˢ Finset.range L).filter fun p : ZMod n × ℕ =>
        IsCircularReversal n p.1 p.2 g).card : ℝ) / ((n : ℝ) * L)

end

end MarkovMixing


