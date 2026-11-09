-- Prove2me | Definitions.Def_MMSImpossibility_Goods_Setting
-- name    : MMSImpossibility_Goods_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:03.763794+00:00
-- url     : https://prove2.me/theorems/43df8303-b752-47b2-a771-0867771b36f3
-- title:
--   §1.1 — allocations, best MMS ratio of an instance, and $\alpha_n^{\mathrm{MMS}}$
-- statement:
--   There are $n$ agents $[n]$ and a finite set $M$ of $m$ indivisible goods; each agent has a nonnegative additive valuation $v_i$. An **allocation** is an ordered partition $(B_1,\dots,B_n)$ of $M$ into possibly empty bundles; every item is allocated. Here an allocation is a map $A: M \to [n]$ and $B_i = A^{-1}(i)$.
--
--   The **maximin share** is $\mathrm{MMS}_i = \max_{(B_1,\dots,B_n)} \min_t v_i(B_t)$ (the published definition `LittleCharity.MMS.mms`). For one instance the best worst-case ratio is
--
--   $$\max_{(B_1,\dots,B_n)} \; \min_{i\in[n]} \frac{v_i(B_i)}{\mathrm{MMS}_i},$$
--
--   and the **worst-case MMS approximation ratio** is
--
--   $$\alpha_n^{\mathrm{MMS}} = \inf_I \; \max_{(B_1,\dots,B_n)} \; \min_{i\in[n]} \frac{v_i(B_i)}{\mathrm{MMS}_i},$$
--
--   the infimum over all additive goods instances $I$ with $n$ agents, any finite number of items, and $\mathrm{MMS}_i > 0$ for every agent. Equivalently, $\alpha_n^{\mathrm{MMS}}$ is the largest $\alpha$ such that every such instance admits an allocation giving every agent at least $\alpha\,\mathrm{MMS}_i$.
--
--   **Formalization Note** Items are `Fin m`, and the infimum ranges over every $m\in\mathbb N$ (every finite item set is in bijection with some `Fin m`). $\alpha_n^{\mathrm{MMS}}$ is a real `sInf`; for $n \ge 1$ its set is nonempty and bounded below by $0$, so it is the genuine infimum.
-- source:
--   Ezra and Garbuz, Improved Impossibility Bounds for Maximin Share Allocations, 2026 preprint, STOC 2027 submission #115, SHA-256 8e8d63bbe3b0c850c561528c6e8d5bdb6da3bc426e5f64316cc948d5a31d64a6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/115.pdf, §1.1 Model, PDF pp. 3–4 (printed pp. 2–3)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace MMSImpossibility.Goods

open LittleCharity.MMS

/-- §1.1 (PDF p. 3): an allocation of the items `Fin m` to the agents `Fin n` is a map
`A : Fin m → Fin n` (every item is allocated, bundles may be empty); agent `i`'s bundle is
`A⁻¹(i)`. -/
def bundle {n m : ℕ} (A : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun g => A g = i)

/-- §1.1 (PDF p. 4): the best worst-case MMS ratio of one instance,
`max_{(B_1,…,B_n) ∈ A_n(M)} min_{i ∈ [n]} v_i(B_i) / MMS_i`, with `MMS_i` the published
maximin share `mms (v i) n univ` (PDF p. 3). Both the maximum and the minimum range over
finite types. -/
noncomputable def bestRatio {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : ℝ :=
  ⨆ A : Fin m → Fin n, ⨅ i : Fin n, v i (bundle A i) / mms (v i) n Finset.univ

/-- §1.1 (PDF p. 4): the instances in the range of the infimum defining `α_n^MMS`: additive
goods instances with `n` agents, some finite number `m` of items (the item set `Fin m`), and
`MMS_i > 0` for every agent. -/
def IsAdmissibleInstance {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  IsAdditive v ∧ ∀ i : Fin n, 0 < mms (v i) n Finset.univ

/-- §1.1 (PDF p. 4): the worst-case MMS approximation ratio
`α_n^MMS = inf_I max_B min_i v_i(B_i)/MMS_i`, the infimum over all additive goods instances
with `n` agents, any finite number of items and positive maximin shares. Every finite item set
is in bijection with some `Fin m`, so quantifying over `m : ℕ` covers every instance. For
`n ≥ 1` the set is nonempty and bounded below by `0`. -/
noncomputable def alphaMMS (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
    IsAdmissibleInstance v ∧ r = bestRatio v}

end MMSImpossibility.Goods


