-- Prove2me | Definitions.Def_Chou_Growth
-- name    : Chou_Growth
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-19T11:41:07.883661+00:00
-- url     : https://prove2.me/theorems/4befe0e8-8d72-4232-8678-0a86ee173de6
-- title:
--   Growth of finitely generated groups: balls, exponential growth, exponentially bounded, free subsemigroups
-- statement:
--   The growth notions of §3, after Milnor and Wolf.
--
--   - `wordBall S n`: the elements of $G$ that are products of at most $n$ factors, each in $S$ or
--     with inverse in $S$.
--   - `HasExponentialGrowth G`: for some finite generating set $S$ of $G$ there is $c > 1$ with
--     $|\text{wordBall}(S, n)| \ge c^n$ for every $n$.
--   - `IsExponentiallyBounded G`: for some finite generating set $S$ and every $c > 1$,
--     $|\text{wordBall}(S, n)| \le c^n$ for all large $n$.
--   - `HasFreeSubsemigroupOfRankTwo G`: there are $a, b \in G$ such that distinct words in $a, b$
--     (including the empty word, which is $1$) give distinct elements of $G$: the homomorphism from
--     the free monoid on two letters is injective. This is the same as $a, b$ generating a free
--     subsemigroup, since a nonempty word $w$ equal to $1$ would give $u w = u$ for every word $u$.
--
--   Chou's $|F^n|$ counts products of exactly $n$ elements of a finite generating set $F$; for $F$
--   symmetric and containing $1$ the two notions coincide. "Almost nilpotent" is Mathlib's
--   `Group.IsVirtuallyNilpotent`. No theorem is stated here.
-- source:
--   Chou, C., Elementary amenable groups, Illinois Journal of Mathematics 24 (1980) 396–407, https://doi.org/10.1215/ijm/1256047608, §3 p. 399 (growth, Milnor–Wolf), p. 401 (free subsemigroup on two generators)

import Mathlib

/-!
# Growth of finitely generated groups (Chou §3, p. 399)

Chou, *Elementary amenable groups*, Illinois J. Math. 24 (1980) 396–407, following Milnor and
Wolf.  For a finite generating set `S` of `G`, the ball `wordBall S n` consists of the products
of at most `n` factors, each an element of `S` or the inverse of one; `G` has *exponential
growth* if the size of these balls is bounded below by `c ^ n` for some `c > 1`, and is
*exponentially bounded* if it is eventually below `c ^ n` for every `c > 1`.  Chou's `Fⁿ` is
the set of products of exactly `n` elements of `F`; for a finite generating set containing
`1` and closed under inverses the two agree, and the growth type does not depend on the
generating set (Wolf).  A finitely generated group is *almost nilpotent* if it has a nilpotent
subgroup of finite index; that is Mathlib's `Group.IsVirtuallyNilpotent`.
-/

namespace Chou

/-- `wordBall S n`: the elements of `G` that are products of at most `n` factors, each lying
in `S` or having its inverse in `S`. -/
def wordBall {G : Type*} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g | ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) ∧ l.prod = g}

/-- `G` has **exponential growth**: for some finite generating set `S` and some `c > 1`, the
ball of radius `n` has at least `c ^ n` elements for every `n`. -/
def HasExponentialGrowth (G : Type*) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ c : ℝ, 1 < c ∧ ∀ n : ℕ, c ^ n ≤ (Nat.card (wordBall (S : Set G) n) : ℝ)

/-- `G` is **exponentially bounded**: for some finite generating set `S` and every `c > 1`,
the ball of radius `n` has at most `c ^ n` elements for all large `n`. -/
def IsExponentiallyBounded (G : Type*) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∀ c : ℝ, 1 < c → ∃ N : ℕ, ∀ n ≥ N, (Nat.card (wordBall (S : Set G) n) : ℝ) ≤ c ^ n

/-- `G` contains a **free subsemigroup on two generators** (p. 401): there are `a b : G` such
that distinct words in `a`, `b` give distinct elements of `G`, the empty word counting as `1`
(the homomorphism from the free monoid on two letters is injective; a free subsemigroup gives
this, since a nonempty word equal to `1` would make `u w = u` for every word `u`). -/
def HasFreeSubsemigroupOfRankTwo (G : Type*) [Group G] : Prop :=
  ∃ a b : G, Function.Injective (FreeMonoid.lift ![a, b])

end Chou


