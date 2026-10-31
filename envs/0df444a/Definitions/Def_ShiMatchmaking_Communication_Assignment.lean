-- Prove2me | Definitions.Def_ShiMatchmaking_Communication_Assignment
-- name    : ShiMatchmaking_Communication_Assignment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:46:45.089993+00:00
-- url     : https://prove2.me/theorems/7cb9882d-fda4-4501-87b5-3f3db2293113
-- title:
--   Assignment games, transaction outcomes, and approximate stability
-- statement:
--   An assignment game consists of two distinct populations $I,J$ and real matrices $b,c$ of customer benefits and provider costs. The bounded-support predicate requires every entry to lie in $[0,1]$.
--
--   A transaction outcome is a binary matching $x$ with at most one partner for each agent, together with arbitrary real customer prices $p_i$, zero for unmatched customers. A matched customer has surplus $b_{ij}-p_i$ and the matched provider has surplus $p_i-c_{ij}$; unmatched agents have zero surplus. The predicate of $\epsilon$-stability requires individual rationality for every agent and
--   $$u_i+v_j+2\epsilon\ge b_{ij}-c_{ij}\quad\text{for all }i,j.$$
--   Feasibility is part of the transaction type; neither individual rationality nor stability is assumed of arbitrary outcomes. The general definition uses arbitrary finite populations when taking surplus sums. The subsequent binary market supplies bounded preferences and equal population sizes. The empty matching with zero prices gives a default outcome only for totalizing operations outside their intended domain.
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; §§2.1–2.3, PDF/printed pp. 7–9, equations (1)–(7).

import Mathlib

namespace ShiMatchmaking.Communication

/-- Assignment preferences; the two types label distinct populations. -/
structure AssignmentGame (I J : Type) where
  benefit : I → J → ℝ
  cost : I → J → ℝ

/-- The bounded-support convention of §2.3. -/
def AssignmentGame.Bounded {I J : Type} (g : AssignmentGame I J) : Prop :=
  ∀ i j, g.benefit i j ∈ Set.Icc 0 1 ∧ g.cost i j ∈ Set.Icc 0 1

/-- A transaction outcome has a partial one-to-one matching and real transfers. -/
structure Transaction (I J : Type) where
  matched : I → J → Bool
  row_unique : ∀ i j k, matched i j = true → matched i k = true → j = k
  col_unique : ∀ i k j, matched i j = true → matched k j = true → i = k
  price : I → ℝ
  unmatched_price : ∀ i, (∀ j, matched i j = false) → price i = 0

instance {I J : Type} : Inhabited (Transaction I J) :=
  ⟨{ matched := fun _ _ => false
     row_unique := by simp
     col_unique := by simp
     price := fun _ => 0
     unmatched_price := by simp }⟩

noncomputable def customerSurplus {I J : Type} [Fintype J]
    (g : AssignmentGame I J) (o : Transaction I J) (i : I) : ℝ :=
  ∑ j, if o.matched i j then g.benefit i j - o.price i else 0

noncomputable def providerSurplus {I J : Type} [Fintype I]
    (g : AssignmentGame I J) (o : Transaction I J) (j : J) : ℝ :=
  ∑ i, if o.matched i j then o.price i - g.cost i j else 0

/-- Equations (5)--(6), including every unmatched pair and zero unmatched surplus. -/
def Stable {I J : Type} [Fintype I] [Fintype J]
    (g : AssignmentGame I J) (ε : ℝ) (o : Transaction I J) : Prop :=
  (∀ i, 0 ≤ customerSurplus g o i) ∧
  (∀ j, 0 ≤ providerSurplus g o j) ∧
  ∀ i j, g.benefit i j - g.cost i j ≤
    customerSurplus g o i + providerSurplus g o j + 2 * ε

end ShiMatchmaking.Communication


