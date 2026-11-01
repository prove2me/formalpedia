-- Prove2me | Definitions.Def_RobustMultiStop_IsSnell
-- name    : RobustMultiStop_IsSnell
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:22.156356+00:00
-- url     : https://prove2.me/theorems/60e8be81-fca3-46ef-aeb3-5066c343789f
-- title:
--   Upper Snell envelopes $Y^{*,l}_t=\operatorname{ess\,sup}\rho_t(\sum_k H_{\tau_k})$
-- statement:
--   Let $\rho$ be a DMU and $H$ an adapted reward process. A family $Y=(Y^{*,l}_r)_{l,r}$ is the family of **upper Snell envelopes** of $H$ if $Y^{*,0}\equiv0$ and, for every number of rights $l\ge1$ and every date $r$ with $r+l\le N+1$,
--
--   $$Y^{*,l}_r=\operatorname*{ess\,sup}_{r\le\tau_1<\tau_2<\dots<\tau_l\le N}\rho_r\Big(\sum_{k=1}^{l}H_{\tau_k}\Big), \tag{2.2}$$
--
--   the essential supremum running over the almost surely ordered stopping vectors. $Y^{*,l}_r$ is the value at time $r$, for a decision maker who evaluates cash flows with $\rho$, of $l$ exercise rights on the reward $H$ to be used at distinct dates.
--
--   **Formalization Note** `Y l r` is $Y^{*,l}_r$. The essential supremum is the least upper bound (`IsLUB`) in the lattice of a.e.-classes. The condition $r+l\le N+1$ says that $l$ distinct dates fit into $\{r,\dots,N\}$.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (2.2), p.5, and "setting Y^{*,0} ≡ 0", p.6

import Mathlib
import Definitions.Def_RobustMultiStop_IsSampled
import Definitions.Def_RobustMultiStop_IsStopVec

open MeasureTheory

namespace RobustMultiStop

/-- The upper Snell envelopes `Y^{*,l}`, Laeven, Schoenmakers, Schweizer & Stadje, *Robust Multiple
Stopping — A Pathwise Duality Approach*, arXiv:2006.01802v2, (2.2), p.5,
`Y_t^{*,L} := ess sup_{t ≤ τ_1 < τ_2 < ⋯ < τ_L} ρ_t(Σ_{l=1}^L H_{τ_l})`, and "setting `Y^{*,0} ≡ 0`",
p.6.

`IsSnell F N ρ H Y` says: `Y 0 r = 0` for every `r`, and for every `l ≥ 1` and every date `r` with
`r + l ≤ N + 1`, `Y l r` is the least upper bound, in the lattice of a.e.-classes, of the family
`{ρ_r(H_{τ_1} + ⋯ + H_{τ_l}) : r ≤ τ_1 < ⋯ < τ_l ≤ N a.s.}`.

**Formalization Note** `Y l r` is the paper's `Y_r^{*,l}`. The essential supremum is `IsLUB` in
`Ω →ₘ[P] ℝ`, whose order is a.s. comparison. The condition `r + l ≤ N + 1` says that `l` distinct
dates fit into `{r, …, N}`; `N` is the exercise horizon (the paper's `T`, or `T + L` after the
paper's extension, p.6). `H_{τ_k}` is a class `Z k` with `IsSampled N H (τ k) (Z k)`. -/
def IsSnell {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (F : Filtration ℕ m0) (N : ℕ) (ρ : ℕ → (Ω →ₘ[P] ℝ) → (Ω →ₘ[P] ℝ))
    (H : ℕ → Ω →ₘ[P] ℝ) (Y : ℕ → ℕ → Ω →ₘ[P] ℝ) : Prop :=
  (∀ r, Y 0 r = 0) ∧
    ∀ l r, 1 ≤ l → r + l ≤ N + 1 →
      IsLUB {W | ∃ τ : Fin l → Ω → ℕ, IsStopVec P F N r l τ ∧
        ∃ Z : Fin l → Ω →ₘ[P] ℝ, (∀ k, IsSampled N H (τ k) (Z k)) ∧ W = ρ r (∑ k, Z k)} (Y l r)

end RobustMultiStop


