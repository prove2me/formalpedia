-- Prove2me | Definitions.Def_ForestRoundingNSW_Rounding_Allocation
-- name    : ForestRoundingNSW_Rounding_Allocation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:49:32.045429+00:00
-- url     : https://prove2.me/theorems/a36bb9d5-b910-490f-997d-186c5a1dbfe3
-- title:
--   The assignment polytope P, support graphs and forests, B_i, N₊ and the remaining items (§2.2–2.3, §3)
-- statement:
--   There are $n$ agents and $m$ items. A **fractional allocation** is a point of the assignment polytope
--   $$P=\Big\{x\in\mathbb R_{\ge0}^{N\times M}:\ \sum_{i\in N}x_{ij}\le 1\text{ for every }j\in M\Big\},$$
--   and $x_i=(x_{ij})_{j\in M}$ is the marginal vector of agent $i$. The **support graph** of $x$ is the bipartite graph on agents and items with an edge $(i,j)$ whenever $x_{ij}>0$; `IsForest x` says it is acyclic.
--
--   For valuations $v_i$ and a set $G\subseteq M$ of residual items, $B_i=\max_{j\in G}v_i(\{j\})$, with $B_i=0$ when $G=\emptyset$, and $N_+=\{i: B_i>0\}$. For bundles $E_i\subseteq G$, the **remaining items** are $G\setminus\bigcup_i E_i$. `SupportedOn x A R` says $x_{ij}\neq 0$ only for $i\in A$ and $j\in R$.
--
--   **Formalization Note.** Agents are `Fin n`, items `Fin m`, and an allocation is `Fin n → Fin m → ℝ`. The support graph is a `SimpleGraph (Fin n ⊕ Fin m)`. In Proposition 3.4 the family $(E_i)_{i\in N_+}$ is extended by $E_i=\emptyset$ for $i\notin N_+$, so `remaining G E` is the paper's $G\setminus\bigcup_{i\in N_+}E_i$.
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 14, §2.2; p. 15, §2.3(ii); p. 19, §3; p. 24, Proposition 3.4

import Mathlib

/-!
# The assignment polytope, support graphs, the residual items, `B_i` and `N₊`

Feng, Hu, Li, Zhang, *Correlated Forest Rounding for Unweighted Nash Social Welfare*, STOC 2027
submission (manuscript sha256 0c7af642…): §2.2 (p. 14, the assignment polytope `P`), §2.3 (p. 15,
`G`, `B_i`, `N₊`), §3 (p. 19, the support graph), Proposition 3.4 (p. 24, the remaining items).

Conventions.
* Agents are `Fin n`, items are `Fin m`. A fractional allocation is `x : Fin n → Fin m → ℝ`,
  and `x i` is agent `i`'s marginal vector `x_i`.
* `InP x`: `x ≥ 0` and `∑_i x_ij ≤ 1` for every item `j`.
* `supportGraph x` is the simple graph on `Fin n ⊕ Fin m` with an edge between agent `i` and item
  `j` iff `x_ij > 0` (no agent–agent or item–item edges). `IsForest x` is `IsAcyclic`.
* `B v G i = max_{j ∈ G} v_i({j})`, and `0` when `G = ∅`. `Nplus v G = {i : B_i > 0}`.
* `remaining G E = G \ ⋃_i E_i`. In Proposition 3.4 the bundles `E_i` are given for `i ∈ N₊`
  and are `∅` for the other agents, so this is the paper's `G \ ⋃_{i ∈ N₊} E_i`.
* `SupportedOn x A R`: `x_ij ≠ 0` only for `i ∈ A` and `j ∈ R`.
-/

namespace ForestRoundingNSW.Rounding

variable {n m : ℕ}

/-- `x ∈ P`: nonnegative, and every item is allocated at most once in total. -/
def InP (x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ j, ∑ i, x i j ≤ 1

/-- The support graph of `x`: agent `i` and item `j` are adjacent iff `x_ij > 0`. -/
def supportGraph (x : Fin n → Fin m → ℝ) : SimpleGraph (Fin n ⊕ Fin m) :=
  SimpleGraph.fromRel fun u v =>
    match u, v with
    | Sum.inl i, Sum.inr j => 0 < x i j
    | _, _ => False

/-- The support graph of `x` is a forest. -/
def IsForest (x : Fin n → Fin m → ℝ) : Prop :=
  (supportGraph x).IsAcyclic

/-- `B_i = max_{j ∈ G} v_i({j})`, with `B_i = 0` when `G = ∅`. -/
noncomputable def B (v : Fin n → Finset (Fin m) → ℝ) (G : Finset (Fin m)) (i : Fin n) : ℝ :=
  if h : G.Nonempty then G.sup' h (fun j => v i {j}) else 0

/-- `N₊ = {i : B_i > 0}`. -/
noncomputable def Nplus (v : Fin n → Finset (Fin m) → ℝ) (G : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < B v G i

/-- The remaining items `G \ ⋃_i E_i`. -/
def remaining (G : Finset (Fin m)) (E : Fin n → Finset (Fin m)) : Finset (Fin m) :=
  G \ Finset.univ.biUnion E

/-- `x` is supported on agents in `A` and items in `R`. -/
def SupportedOn (x : Fin n → Fin m → ℝ) (A : Finset (Fin n)) (R : Finset (Fin m)) : Prop :=
  ∀ i j, x i j ≠ 0 → i ∈ A ∧ j ∈ R

end ForestRoundingNSW.Rounding


