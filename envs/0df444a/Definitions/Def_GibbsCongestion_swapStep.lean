-- Prove2me | Definitions.Def_GibbsCongestion_swapStep
-- name    : GibbsCongestion_swapStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:21.477419+00:00
-- url     : https://prove2.me/theorems/19ec20c0-28c0-4927-b0cb-6b35eaaa712c
-- title:
--   Swap step: two random players exchange strategies
-- statement:
--   The **swap step** of the relaxed logit dynamics selects two players $i,j$ uniformly at random and exchanges their strategies: $s'_j=s_i$, $s'_i=s_j$ and $s'_k=s_k$ otherwise. As a matrix, for $n\ge2$,
--   $$\mathrm{Swap}(s,s')=\frac{1}{n(n-1)}\sum_{i\ne j}[\,s'=s\circ(i\ j)\,],$$
--   the sum running over ordered pairs of distinct players. For $n=1$ the step leaves the profile unchanged. The swap step preserves the strategy load profile and lets the chain move inside a load class.
--
--   **Formalization Note** "Two players" is read as two distinct players, uniform among the $n(n-1)$ ordered pairs; this is the reading of App. B.3, p.30, where $P_\alpha(s,s')=1/(n(n-1))$. For $n=1$ there is no such pair and the identity is used.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.16; App. B.3, p.30

import Mathlib

namespace GibbsCongestion

/-- The **swap step** of the relaxed logit dynamics (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §4.2, p.16): select two players
`i, j` uniformly at random and exchange their strategies (`s'_j = s_i`, `s'_i = s_j`).

**Formalization Note** The two players are read as distinct: an ordered pair `(i, j)` with
`i ≠ j`, uniform among the `n(n-1)` such pairs, which is the reading of App. B.3, p.30
(`P_α(s, s') = 1/(n(n-1))`). The new profile is `s ∘ swap i j`. For `n < 2` there is no pair of
distinct players and the step is the identity. -/
noncomputable def swapStep {E : Type*} [DecidableEq E] (P : Finset (Finset E)) (n : ℕ) :
    Matrix (Fin n → P) (Fin n → P) ℝ :=
  fun s s' =>
    if 2 ≤ n then
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (if s' = s ∘ Equiv.swap i j then (1 : ℝ) else 0)
    else if s' = s then 1 else 0

end GibbsCongestion


