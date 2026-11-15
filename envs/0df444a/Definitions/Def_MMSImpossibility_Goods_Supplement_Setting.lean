-- Prove2me | Definitions.Def_MMSImpossibility_Goods_Supplement_Setting
-- name    : MMSImpossibility_Goods_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:01:45.738183+00:00
-- url     : https://prove2.me/theorems/fd0fdca9-4eaf-480c-8fcc-4019fb9259d2
-- title:
--   §1.1 — chores maximin share, $\beta_n^{\mathrm{MMS}}$, $\beta^{\mathrm{MMS}}$ and $\alpha^{\mathrm{MMS}}$
-- statement:
--   In the **chores** setting there are $n$ agents and a finite set $M$ of $m$ indivisible chores; agent $i$ has a nonnegative additive cost function $c_i$, $c_i(S) = \sum_{g\in S} c_i(\{g\})$. An allocation $(B_1,\dots,B_n)$ is an ordered partition of $M$ into possibly empty bundles; every chore must be allocated.
--
--   The **chores maximin share** of agent $i$ is the smallest cost she can guarantee by partitioning the chores into $n$ bundles and receiving a costliest one:
--
--   $$\mathrm{MMS}^{\mathrm{ch}}_i = \min_{(B_1,\dots,B_n)} \; \max_{t\in[n]} c_i(B_t).$$
--
--   The **worst-case MMS approximation factor for chores** is
--
--   $$\beta_n^{\mathrm{MMS}} = \sup_I \; \min_{(B_1,\dots,B_n)} \; \max_{i\in[n]} \frac{c_i(B_i)}{\mathrm{MMS}^{\mathrm{ch}}_i},$$
--
--   the supremum over all additive chores instances $I$ with $n$ agents, any finite number of chores and $\mathrm{MMS}^{\mathrm{ch}}_i > 0$ for every agent, and $\beta^{\mathrm{MMS}} = \sup_{n\ge 1}\beta_n^{\mathrm{MMS}}$. For goods, $\alpha^{\mathrm{MMS}} = \inf_{n \ge 1} \alpha_n^{\mathrm{MMS}}$, with $\alpha_n^{\mathrm{MMS}}$ the worst-case MMS approximation ratio of the base mission.
--
--   These are the quantities bounded by Theorems 2–4 of the paper.
--
--   **Formalization Note** Chores are `Fin m` and the supremum ranges over every $m \in \mathbb N$. Allocations are maps `Fin m → Fin n` (the published `bundle`). Cost profiles use the published predicate `IsAdditive` (additive over singletons, nonnegative). $\beta_n^{\mathrm{MMS}}$ and $\beta^{\mathrm{MMS}}$ are suprema in `EReal`, so no boundedness is presupposed. $\alpha^{\mathrm{MMS}}$ is a real infimum over $n \ge 1$ only; its set is nonempty and bounded below by $0$. `mmsCh` is used only with $n \ge 1$.
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §1.1 Model (Chores; MMS approximation for chores; definition of α^MMS), PDF pp. 4–5 (printed pp. 3–4)

import Mathlib
import Definitions.Def_MMSImpossibility_Goods_Setting

namespace MMSImpossibility.Goods.Supplement

open LittleCharity.MMS MMSImpossibility.Goods

/-- §1.1 (PDF p. 4): the maximin share for chores of a cost function `c` on the chores
`Fin m` with `n` agents, `MMS^ch = min_{(B_1,…,B_n) ∈ A_n(M)} max_{t ∈ [n]} c(B_t)`:
the minimum over allocations `A : Fin m → Fin n` (every chore allocated) of the largest bundle
cost. Both extrema range over finite types; the outer one is nonempty for `n ≥ 1`, and every
statement using this definition has `n ≥ 1`. -/
noncomputable def mmsCh {m : ℕ} (c : Finset (Fin m) → ℝ) (n : ℕ) : ℝ :=
  ⨅ A : Fin m → Fin n, ⨆ t : Fin n, c (bundle A t)

/-- §1.1 (PDF p. 5): the best worst-case chores MMS factor of one instance,
`min_{(B_1,…,B_n) ∈ A_n(M)} max_{i ∈ [n]} c_i(B_i) / MMS^ch_i`. -/
noncomputable def bestRatioCh {n m : ℕ} (c : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  ⨅ A : Fin m → Fin n, ⨆ i : Fin n, c i (bundle A i) / mmsCh (c i) n

/-- §1.1 (PDF pp. 4–5): the instances in the range of the supremum defining `β_n^MMS`:
nonnegative additive chores instances with `n` agents, the chores `Fin m`, and
`MMS^ch_i > 0` for every agent. Cost profiles satisfy the same two conditions as valuations
(additivity over singletons and nonnegativity), so `IsAdditive` is reused. -/
def IsAdmissibleChoresInstance {n m : ℕ} (c : Fin n → Finset (Fin m) → ℝ) : Prop :=
  IsAdditive c ∧ ∀ i : Fin n, 0 < mmsCh (c i) n

/-- §1.1 (PDF p. 5): the worst-case MMS approximation factor for chores,
`β_n^MMS = sup_I min_B max_i c_i(B_i) / MMS^ch_i`, over all additive chores instances with `n`
agents, any finite number `m` of chores (the chore set `Fin m`), and positive chores maximin
shares. The supremum is taken in `EReal`, so no boundedness is presupposed. -/
noncomputable def betaMMS (n : ℕ) : EReal :=
  ⨆ (m : ℕ) (c : Fin n → Finset (Fin m) → ℝ) (_ : IsAdmissibleChoresInstance c),
    ((bestRatioCh c : ℝ) : EReal)

/-- §1.1 (PDF p. 5): `β^MMS = sup_{n ≥ 1} β_n^MMS`, in `EReal`. -/
noncomputable def betaMMSAll : EReal :=
  ⨆ (n : ℕ) (_ : 1 ≤ n), betaMMS n

/-- §1.1 (PDF p. 4): `α^MMS = inf_{n ≥ 1} α_n^MMS`, with `α_n^MMS` the published
`MMSImpossibility.Goods.alphaMMS`. Every `α_n^MMS` with `n ≥ 1` is the infimum of a nonempty set
of nonnegative ratios, so this set is nonempty and bounded below by `0`. -/
noncomputable def alphaMMSAll : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = alphaMMS n}

end MMSImpossibility.Goods.Supplement


