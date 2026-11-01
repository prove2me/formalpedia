-- Prove2me | Definitions.Def_GibbsCongestion_resourceLoad
-- name    : GibbsCongestion_resourceLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:19.580894+00:00
-- url     : https://prove2.me/theorems/b76b5a7d-02c2-4545-bb05-a16d90f03641
-- title:
--   Resource load $\ell_e(s)$
-- statement:
--   Let $N=[n]$ be the players and $\mathcal P$ the common strategy set of a symmetric congestion game, each strategy being a set of resources. For a strategy profile $s=(s_1,\dots,s_n)\in\mathcal P^n$ and a resource $e$, the **load** of $e$ is the number of players whose strategy uses $e$:
--   $$\ell_e(s)=|\{i\in N: e\in s_i\}|.$$
--   Loads are the arguments of the congestion costs $c_e(\ell_e(s))$ and of Rosenthal's potential.
--
--   **Formalization Note** Players are `Fin n`; a profile is a map from players to the strategy set.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7

import Mathlib

namespace GibbsCongestion

/-- The **resource load** `ℓ_e(s) = |{i ∈ N : e ∈ s_i}|`, the number of players whose strategy
uses resource `e` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7).

**Formalization Note** Players are `Fin n`; a strategy profile of the symmetric game with common
strategy set `P` is a map `s : Fin n → P` (each strategy is a set of resources). -/
noncomputable def resourceLoad {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ} (s : Fin n → P) (e : E) : ℕ :=
  (Finset.univ.filter (fun i => e ∈ (s i : Finset E))).card

end GibbsCongestion


