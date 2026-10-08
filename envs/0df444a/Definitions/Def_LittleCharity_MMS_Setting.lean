-- Prove2me | Definitions.Def_LittleCharity_MMS_Setting
-- name    : LittleCharity_MMS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:28.646976+00:00
-- url     : https://prove2.me/theorems/6f681468-f377-4d5b-8d67-3096def4c846
-- title:
--   Additive valuations and maximin share over an arbitrary set of goods
-- statement:
--   This file adds the **additive valuation** and **maximin share** notions of §§1.1.1 and 1.1.3 to the finite allocation model in `LittleCharity.EFX.Setting`.
--
--   For $n$ agents and $m$ goods, agent $i$ has a value $v_i(S)$ for every bundle $S$. A valuation profile is **additive** when each bundle has the sum of its singleton-good values and every value is nonnegative:
--
--   $$
--   v_i(S)=\sum_{g\in S}v_i(\{g\}),\qquad v_i(S)\ge 0.
--   $$
--
--   The second condition records the paper's codomain $\mathbb R_{\ge0}$. Additivity makes the empty bundle worth zero and valuations monotone.
--
--   Given a valuation $w$, a set $S$ of goods and an integer $k\ge1$, its **maximin share** is
--
--   $$
--   \operatorname{MMS}_w(k,S)=\max_{(S_1,\ldots,S_k)}\min_{1\le j\le k}w(S_j),
--   $$
--
--   where the maximum ranges over all partitions of $S$ into $k$ labelled, possibly empty, bundles. The paper's $\operatorname{MMS}_i(n,M)$ is this quantity for $w=v_i$ and the full good set $M$.
--
--   This benchmark measures what an agent can guarantee by partitioning the goods before receiving a worst-valued part. The same definition also applies to the smaller agent and good sets in Proposition 13 and Theorems 14 and 16.
--
--   **Formalization Note** Agents and goods are `Fin n` and `Fin m`, indexed from zero. A labelling of all goods by `Fin k`, restricted to $S$, represents a partition of $S$; labels outside $S$ have no effect. Every theorem using the maximin share requires $k\ge1$ or derives it from group membership, avoiding the empty-index value at $k=0$. The file imports the partial allocation, pool, envy graph and EFX definitions from `LittleCharity.EFX.Setting`; its EFX name is an alias of that shared predicate.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 3 (§1.1.1, additive valuations and property 1), p. 4 (§1.1.3, definition of MMS_i(n, M))

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace LittleCharity.MMS

/-- Additive valuations (p. 3): `v_i(S) = ∑_{g ∈ S} v_i({g})`, with values in `ℝ≥0`
(p. 3, `v_i : 2^M → ℝ≥0`). Agent `i` values bundle `S` at `v i S`. -/
def IsAdditive {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ i S, v i S = ∑ g ∈ S, v i {g}) ∧ ∀ i S, 0 ≤ v i S

/-- Envy-free up to any good (p. 3, property 1): for any two agents `i, j`,
`v_i(X_i) ≥ v_i(X_j \ {g})` for every `g ∈ X_j`. -/
def IsEFX {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (X : Fin n → Finset (Fin m)) : Prop :=
  LittleCharity.EFX.IsEFX v X

open Classical in

/-- The maximin share of a finite set `S` partitioned into `k` labelled bundles (p. 4).
Statements using this definition require `0 < k`. -/
noncomputable def mms {m : ℕ} (w : Finset (Fin m) → ℝ) (k : ℕ)
    (S : Finset (Fin m)) : ℝ :=
  ⨆ f : Fin m → Fin k, ⨅ j : Fin k, w (S.filter (fun g => f g = j))

end LittleCharity.MMS


