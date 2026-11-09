-- Prove2me | Definitions.Def_SkipListConc_levelSteps
-- name    : SkipListConc_levelSteps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:57.092205+00:00
-- url     : https://prove2.me/theorems/785fd52e-17f6-4b86-82f4-eadec01a9838
-- title:
--   Steps of a skip-list search along one level
-- statement:
--   A **skip list** over a finite ordered key set $S$ with heights $h:S\to\{1,2,\dots\}$ stores item $y$ on levels $1,\dots,h(y)$, with a head $-\infty$ on every level. A search for $x\in S$ starts on the highest level in use, advances along the current level while the next key does not exceed $x$, and descends otherwise; it reaches $x$ on level $h(x)$.
--
--   For a level $\ell\ge h(x)$, the number of **steps along level $\ell$** is
--   $$
--   \#\{\,y\in S:\ y\le x,\ h(y)\ge \ell,\ \text{and no } w\in S \text{ with } y\le w\le x \text{ has } h(w)\ge \ell+1\,\},
--   $$
--   the nodes of level $\ell$ between the last node $\le x$ of height $\ge\ell+1$ (or the head) and the last node $\le x$ of height $\ge \ell$. On the target's own level the step onto $x$ counts; above the maximum height the count is $0$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.4–5, Figure 1

import Mathlib

namespace SkipListConc

/-- The number of steps a skip-list search for `x` takes along level `ℓ` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §1.1, pp.4–5, Figure 1).

The key set is a finite ordered set `S` with heights `h`; item `y` occupies levels `1, …, h y`,
and the head `−∞` is on every level. The search advances along a level while the next key does
not exceed `x`, and descends otherwise. On level `ℓ ≥ h x` it enters at the last node `≤ x` of
height `≥ ℓ + 1` (or the head) and stops at the last node `≤ x` of height `≥ ℓ`, so its steps on
level `ℓ` are the nodes `y ≤ x` with `h y ≥ ℓ` such that no node `w` with `y ≤ w ≤ x` has height
`≥ ℓ + 1`.

**Formalization Note** On the target's own level `ℓ = h x` the step onto `x` is counted. Above
the maximum height the count is `0`. -/
def levelSteps {α : Type*} [LinearOrder α] (S : Finset α) (h : α → ℕ) (x : α) (ℓ : ℕ) : ℕ :=
  (S.filter fun y => y ≤ x ∧ ℓ ≤ h y ∧ ∀ w ∈ S, y ≤ w → w ≤ x → h w ≤ ℓ).card

end SkipListConc


