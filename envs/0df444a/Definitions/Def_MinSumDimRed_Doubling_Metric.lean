-- Prove2me | Definitions.Def_MinSumDimRed_Doubling_Metric
-- name    : MinSumDimRed_Doubling_Metric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:33:33.616191+00:00
-- url     : https://prove2.me/theorems/7545ae33-0b84-49ad-99c8-a0b7695f68c5
-- title:
--   Doubling dimension (floor $D \ge 1$), $r$-packings, $r$-coverings and $r$-nets (p. 3; §2.1, Definition 2.1)
-- statement:
--   Let $(\alpha, \mathrm{dist})$ be a metric space and $S \subseteq \alpha$. Balls of $S$ are closed and centred in $S$: $B_S(x, r) = \{y \in S : \mathrm{dist}(x, y) \le r\}$ for $x \in S$, $r > 0$ (p. 9).
--
--   1. **Doubling condition** `IsDoublingWith S D`: $D \ge 1$ and every ball $B_S(x, r)$ ($x \in S$, $r > 0$) is covered by at most $2^D$ balls $B_S(y, r/2)$ with centres $y \in S$ ($D$ real).
--   2. **Doubling dimension at most $D$** `HasDoublingDimAtMost S D`: some admissible exponent $D' \le D$ exists. Never true of a set that is not doubling.
--   3. **Doubling dimension** `ddim S` $= \inf\{D : \texttt{IsDoublingWith}\ S\ D\}$, "the smallest $D \ge 1$ such that every metric ball can be covered by at most $2^D$ balls of half the radius" (p. 3). For a doubling set (every finite set is one) the admissible set is a closed up-ray $[D_0, \infty)$ with $D_0 \ge 1$, so the infimum is attained and `HasDoublingDimAtMost S D` $\iff$ `ddim S` $\le D$. For a non-doubling set the infimum of the empty set is the junk value $0$; statements use `ddim` only on sets assumed (or known) to be doubling.
--   4. **Definition 2.1** (p. 9), for $r > 0$: $N \subseteq S$ is an **$r$-packing** if $\mathrm{dist}(u, v) > r$ for all distinct $u, v \in N$; an **$r$-covering** of $S$ if every $x \in S$ has some $u \in N$ with $\mathrm{dist}(u, x) \le r$; an **$r$-net** if both.
--
--   **Formalization Note** The floor $D \ge 1$ is part of the definition, as on p. 3; the published `DoublingMST_ddimOn` (floor $0$, distance tables on `Fin n`) is deliberately not reused.
-- source:
--   Asaf Dallal, Robert Krauthgamer, Dimension Reduction and Coresets for Min-Sum k-Clustering, arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 3 (doubling dimension), p. 9 (PDF 9), §2.1 and Definition 2.1

import Mathlib

namespace MinSumDimRed.Doubling

/-!
# Doubling dimension, packings, coverings and nets

Dallal, Krauthgamer, *Dimension Reduction and Coresets for Min-Sum k-Clustering*,
arXiv:2610.38920 (version of November 2, 2026, SHA-256 13a9281e…), p. 3 (doubling dimension:
"the smallest D ≥ 1 such that every metric ball can be covered by at most 2^D balls of half the
radius") and p. 9 (§2.1: closed balls `B_X(x, r) = {y ∈ X : dist(x, y) ≤ r}` for `r > 0`;
Definition 2.1, r-packing, r-covering, r-net).

**Formalization Note.** A point set is a subset `S` of a metric space `α`; its balls are
`S ∩ closedBall x r` with centre `x ∈ S`, and the covering balls are centred at points of `S`.
The doubling dimension is a real number `D ≥ 1` (not necessarily an integer). -/

variable {α : Type*} [MetricSpace α]

/-- `S` satisfies the doubling condition with exponent `D`: `D ≥ 1`, and every ball
`B_S(x, r) = S ∩ closedBall x r` (`x ∈ S`, `r > 0`) is covered by at most `2^D` balls
`B_S(y, r/2)` with centres `y ∈ S`. -/
def IsDoublingWith (S : Set α) (D : ℝ) : Prop :=
  1 ≤ D ∧
    ∀ x ∈ S, ∀ r : ℝ, 0 < r →
      ∃ T : Finset α, (↑T : Set α) ⊆ S ∧ (T.card : ℝ) ≤ (2 : ℝ) ^ D ∧
        S ∩ Metric.closedBall x r ⊆ ⋃ y ∈ T, Metric.closedBall y (r / 2)

/-- "`S` has doubling dimension at most `D`": some admissible exponent `D' ≤ D` exists. (The set
of admissible exponents is a closed up-ray when nonempty, so this says `ddim S ≤ D` and never
holds for a set that is not doubling.) -/
def HasDoublingDimAtMost (S : Set α) (D : ℝ) : Prop :=
  ∃ D' : ℝ, D' ≤ D ∧ IsDoublingWith S D'

/-- The doubling dimension `ddim(S)`: the least admissible exponent `D ≥ 1`. It is used only on
sets that are doubling (every finite set is), where the infimum is attained. -/
noncomputable def ddim (S : Set α) : ℝ :=
  sInf {D : ℝ | IsDoublingWith S D}

/-- Definition 2.1: `N ⊆ S` is an `r`-packing of `S` (`r > 0`): distinct points of `N` are at
distance `> r`. -/
def IsPacking (S N : Set α) (r : ℝ) : Prop :=
  0 < r ∧ N ⊆ S ∧ ∀ u ∈ N, ∀ v ∈ N, u ≠ v → r < dist u v

/-- Definition 2.1: `N ⊆ S` is an `r`-covering of `S` (`r > 0`): every `x ∈ S` lies in
`B_S(u, r)` for some `u ∈ N`. -/
def IsCovering (S N : Set α) (r : ℝ) : Prop :=
  0 < r ∧ N ⊆ S ∧ ∀ x ∈ S, ∃ u ∈ N, dist u x ≤ r

/-- Definition 2.1: an `r`-net of `S` is both an `r`-packing and an `r`-covering of `S`. -/
def IsNet (S N : Set α) (r : ℝ) : Prop :=
  IsPacking S N r ∧ IsCovering S N r

end MinSumDimRed.Doubling


