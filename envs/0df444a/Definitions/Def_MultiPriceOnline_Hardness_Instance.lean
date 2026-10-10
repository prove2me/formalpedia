-- Prove2me | Definitions.Def_MultiPriceOnline_Hardness_Instance
-- name    : MultiPriceOnline_Hardness_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:30.367454+00:00
-- url     : https://prove2.me/theorems/273f1f20-597e-43ea-b175-3713b460c77f
-- title:
--   §5, p. 23 — the random-permutation instance with m phases
-- statement:
--   The counterexample of §5 is built from a number $n$ of items, inventory $k$, a price set with $m$ prices, numbers $1 = B_1 > B_2 > \dots > B_m > 0$ (with $B_{m+1} = 0$), and a permutation $\pi$ of the $n$ items.
--
--   There are $T = nk$ customers, split into $n$ **groups** of $k$ consecutive customers. All $k$ customers of group $g$ would buy any of the items $\pi_g, \pi_{g+1}, \dots, \pi_n$, and no other item. The groups are split into $m$ **phases**: phase $j$ consists of the groups $(1 - B_j) n + 1, \dots, (1 - B_{j+1}) n$. The customers of phase $j$ are willing to pay $r^{(j)}$, that is, they buy at any price $r^{(1)}, \dots, r^{(j)}$. The arrival sequence lies in the deterministic case. In §5 the permutation $\pi$ is drawn uniformly at random from all $n!$ permutations.
--
--   **Formalization Note** The paper writes $\tau n$ for an integer and ignores rounding (p. 23). Here the rounding is explicit: with 0-based groups $g = 0, \dots, n-1$, group $g$ is in phase $j$ iff $\lfloor (1 - B_j) n \rfloor \le g < \lfloor (1 - B_{j+1}) n \rfloor$. The phase is computed as $1 + \#\{j \in \{2, \dots, m\} : \lfloor (1 - B_j) n \rfloor \le g\}$. This equals that $j$ when the $B_j$ decrease, and it always lies in $\{1, \dots, m\}$ when $m \ge 1$. Customer $t$ (0-based) is in group $\lfloor t/k \rfloor$. Group $g$'s interest set $\{\pi_g, \dots, \pi_n\}$ is the set of items $i$ with $\pi^{-1}(i) \ge g$, with 0-based positions.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 23, §5 (randomized arrival sequence, phases)

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_Model

namespace MultiPriceOnline.Hardness

open Finset

/-- The phase of group `g` (0-based, `g < n`) in the instance of §5 (p. 23), with the rounding made
explicit. The paper puts groups `(β₁ + … + β_{j−1})n + 1, …, (β₁ + … + β_j)n` (1-based) in phase `j`;
since `β₁ + … + β_{j−1} = 1 − B_j`, the 0-based group `g` is in phase `j` iff
`⌊(1 − B_j) n⌋ ≤ g < ⌊(1 − B_{j+1}) n⌋`, with `B_{m+1} = 0`. Here the phase is
`1 + #{j ∈ {2, …, m} : ⌊(1 − B_j) n⌋ ≤ g}`, which is that `j` when `B_1 = 1 > B_2 > … > B_m > 0`. -/
noncomputable def phaseOf (n m : ℕ) (B : ℕ → ℝ) (g : ℕ) : ℕ :=
  1 + ((Icc 2 m).filter (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g)).card

open Classical in
/-- The deterministic arrival sequence of §5 (p. 23) for the permutation `π` of the `n` items:
`T = n k` customers, customer `t` (0-based) belongs to group `g = ⌊t / k⌋`; the `k` customers of group
`g` buy any item in `{π g, π (g+1), …, π (n−1)}` (i.e. items `i` with `π⁻¹ i ≥ g`), at any price
`r⁽ʲ⁾` with `1 ≤ j ≤ phaseOf n m B g` ("willing to pay `r⁽ʲ⁾`" for phase `j`). -/
noncomputable def hardInstance (n k m : ℕ) (B : ℕ → ℝ) (π : Equiv.Perm (Fin n)) : Arrival n where
  T := n * k
  p := fun t i j =>
    if (t : ℕ) / k ≤ ((π.symm i : Fin n) : ℕ) ∧ 1 ≤ j ∧ j ≤ phaseOf n m B ((t : ℕ) / k)
    then 1 else 0

end MultiPriceOnline.Hardness


