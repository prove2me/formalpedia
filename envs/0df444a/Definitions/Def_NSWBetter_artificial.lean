-- Prove2me | Definitions.Def_NSWBetter_artificial
-- name    : NSWBetter_artificial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:27.452203+00:00
-- url     : https://prove2.me/theorems/c5162ef3-90a1-44ba-b3ca-2d0ecb0d4c34
-- title:
--   Artificial instance $I_{i,x}(\Delta)$ (value multiset)
-- statement:
--   The **artificial instance** $I_{i,x}(\Delta)$: $\Delta$ agents, all with valuation $v_i$, and $\Delta x_{ig}$ copies of each good $g$. `artificial v x i Δ` is the multiset of the values of its goods.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4.1, p.17 (artificial instance)

import Mathlib

namespace NSWBetter

/-- **The artificial instance of agent i.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4.1, p.17: "For each bucket b ∈ Bi, we construct a set of goods Gb that contains ∆bg copies of each good g … Essentially, for each g ∈ G, the set of goods G′ has ∆xig copies of g. All agents in this instance have the valuation function vi. We refer to this instance as the artificial instance for agent i with ∆ agents, denoted Ii,x(∆)."

`artificial v x i Δ` is the multiset of values of `I_(i,x)(Δ)`: `Δ x_ig` copies of `v_i(g)` for each good `g`; the instance has `Δ` agents with valuation `v_i`.

**Formalization Note.** It is used only when every `Δ x_ig` is a natural number, where `⌊Δ x_ig⌋ = Δ x_ig`. -/
noncomputable def artificial {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n)
    (Δ : ℕ) : Multiset ℝ :=
  ∑ g, Multiset.replicate ⌊(Δ : ℝ) * x i g⌋₊ (v i g)

end NSWBetter


