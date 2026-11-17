-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_RemovalRule
-- name    : IntroDelayAMDP_Supplement_RemovalRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:46:33.185433+00:00
-- url     : https://prove2.me/theorems/33961930-1b9e-473a-88e7-43d16129a7e1
-- title:
--   The removal choice of Algorithm 2
-- statement:
--   Line 5 of **Algorithm 2** removes "one such $i$" among the indices $i\in R_j$ with $\|\phi_i\|^2_{\Lambda_j^{-1}}>2d\log(1+1/\lambda)$, without saying which. A removal rule chooses one element of every nonempty set $V$ of violating indices, as a function of the features, the current $R_j$ and $V$. Theorems 4.1 and 5.2 are stated for every removal rule.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, line 5, p.17

import Mathlib

namespace IntroDelayAMDP.Supplement

/-- **The removal choice of Algorithm 2** (line 5, printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "while some `i ∈ R_j` has
`‖ϕ_i‖²_{Λ_j^{-1}} > 2d log(1 + 1/λ)` do Remove one such `i` from `R_j`"). The page does not fix which violating
index is removed. A rule `choose ϕ R V` picks, from the features `ϕ`, the current set `R = R_j` and the
nonempty set `V` of violating indices, one element of `V`. The theorems hold for every rule. -/
structure RemovalRule (d : ℕ) where
  /-- the removed index -/
  choose : (ℕ → Fin d → ℝ) → Finset ℕ → Finset ℕ → ℕ
  choose_mem : ∀ ϕ R V, V.Nonempty → choose ϕ R V ∈ V

end IntroDelayAMDP.Supplement


