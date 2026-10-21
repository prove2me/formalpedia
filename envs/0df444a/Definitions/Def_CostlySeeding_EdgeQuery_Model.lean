-- Prove2me | Definitions.Def_CostlySeeding_EdgeQuery_Model
-- name    : CostlySeeding_EdgeQuery_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:31.961484+00:00
-- url     : https://prove2.me/theorems/63aee3b4-e192-4a6d-a8f9-1d65059e380d
-- title:
--   Finite independent cascade spread and the size-k optimum
-- statement:
--   Let $G=(V,E)$ be a finite undirected simple graph with $V=\{0,\ldots,n-1\}$ and let each edge independently be retained with probability $p$. For a retained edge set $A\subseteq E$, its probability is
--
--   $$
--   w_p(A)=p^{|A|}(1-p)^{|E|-|A|}.
--   $$
--
--   The adoption probability $\phi(v,S)$ is the sum of these weights over retained subgraphs in which $v$ is connected to at least one seed in $S$. The expected spread is $\Gamma(S)=\sum_{v\in V}\phi(v,S)$. The size-$k$ optimum is the maximum of $\Gamma(S)$ over $|S|=k$. These objects give the meaning of every spread and optimum appearing in the mission.
--
--   **Formalization Note** If $k>n$, the feasible family is empty and the auxiliary maximum returns zero; all theorem uses of the optimum have a feasible size.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, pp. 3, 8, §1.1, §2, Definitions 1–2

import Definitions.Def_CostlySeeding_EdgeQuery_SetFunction

namespace CostlySeeding.EdgeQuery

noncomputable def percW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (A : Finset (Sym2 (Fin n))) : ℝ :=
  if A ⊆ G.edgeFinset then p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) else 0

noncomputable def phi {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (v : Fin n) (S : Finset (Fin n)) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset, percW G p A *
    if ∃ s ∈ S, (SimpleGraph.fromEdgeSet (A : Set (Sym2 (Fin n)))).Reachable s v then 1 else 0

noncomputable def Gam {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ v : Fin n, phi G p v S

noncomputable def OPT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (k : ℕ) : ℝ := OPTof (Gam G p) k

end CostlySeeding.EdgeQuery


