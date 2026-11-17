-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_jointFilter
-- name    : EffHorizonProphet_Supplement_jointFilter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:54:31.005299+00:00
-- url     : https://prove2.me/theorems/8d52522a-b25e-44a9-87eb-28043f1c91dc
-- title:
--   The joint limit $\tilde\gamma\uparrow1$, $S\to\infty$, $\tilde\gamma^S\to0$
-- statement:
--   The **worst-case boundary regime** of Theorem 8 is the joint limit in which the common decay factor $\tilde\gamma$ increases to $1$, the number of phases $S$ tends to infinity, and $\tilde\gamma^S\to0$. It is the filter on pairs $(\tilde\gamma,S)\in\mathbb R\times\mathbb N$
--   $$\big(\mathcal N_{<}(1)\times\mathrm{atTop}\big)\ \sqcap\ \mathrm{comap}\big((\tilde\gamma,S)\mapsto\tilde\gamma^S\big)\,\mathcal N(0).$$
--   A property holds eventually in this regime when there are $\delta>0$, $S_0$ and $\varepsilon>0$ such that it holds for all $(\tilde\gamma,S)$ with $1-\delta<\tilde\gamma<1$, $S\ge S_0$ and $|\tilde\gamma^S|<\varepsilon$.
--
--   The limit is joint, not iterated. It is not empty: $\tilde\gamma=e^{-1/\sqrt S}$ tends to it.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 6, Theorem 8, p.11; Corollary 2

import Mathlib

open Filter Topology

namespace EffHorizonProphet.Supplement

/-- The **worst-case boundary regime** of Theorem 8 (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.11; Corollary 2): the joint limit
`γ̃ ↑ 1, S → ∞, γ̃^S → 0`, as a filter on pairs `(γ̃, S) : ℝ × ℕ`.

**Formalization Note** It is the meet of `𝓝[<] 1 ×ˢ atTop` (γ̃ tends to `1` from below and `S` to
infinity, jointly, not as iterated limits) with the preimage of `𝓝 0` under `(γ̃, S) ↦ γ̃^S`. A
property holds eventually in this filter when it holds for all `(γ̃, S)` with `γ̃` in some interval
`(1 − δ, 1)`, `S` above some threshold and `γ̃^S` below some `ε`. The filter is not trivial
(`γ̃ = 1 − 1/√S` tends to it; see the sanity file). -/
noncomputable def jointFilter : Filter (ℝ × ℕ) :=
  (𝓝[<] (1 : ℝ) ×ˢ atTop) ⊓ comap (fun p : ℝ × ℕ => p.1 ^ p.2) (𝓝 0)

end EffHorizonProphet.Supplement


