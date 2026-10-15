-- Prove2me | Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
-- name    : StrictCompatLB_RegularDegree_GraphConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:21.435525+00:00
-- url     : https://prove2.me/theorems/a97c69ca-6e1a-4eef-bcf3-fec3bd7509bf
-- title:
--   Condition (A.19) — the uniform-weight subcriticality condition for bipartite graph sequences
-- statement:
--   Consider a sequence of bipartite **compatibility graphs** $G_N=(V_N,W_N,E_N)$, $N\ge 1$, between a set $V_N$ of $N$ servers and a set $W_N$ of $M(N)$ dispatchers, with $E_N\subseteq V_N\times W_N$. For a dispatcher $w\in W_N$ write $\mathcal N_w=\{v\in V_N:(v,w)\in E_N\}$ for its neighbourhood (the servers that can process task type $w$).
--
--   The sequence satisfies **condition (A.19)** if
--   $$\limsup_{N\to\infty}\max_{v\in V_N}\frac{N}{M(N)}\sum_{w\in W_N}\frac{\mathbb 1\{(v,w)\in E_N\}}{|\mathcal N_w|}\;\le\;1 ,$$
--   where "$\limsup\le 1$" means: for every $\varepsilon>0$, for all sufficiently large $N$, every server's value is at most $1+\varepsilon$.
--
--   The quantity on the left is the load a server receives, relative to the per-server arrival rate, when every dispatcher routes each task to a uniformly chosen compatible server. Condition (A.19) is the subcriticality condition of Definition 3.3 with uniform weights $\gamma^U_w(v)=1/\min(d,|\mathcal N_w|)$ on the sampled set $U$; the paper's random-graph results (Lemma A.5, Lemma B.2) verify it in place of (3.2).
--
--   **Formalization Note** $V_N$ is `Fin N`, $W_N$ is `Fin (M N)`, $E_N$ is a `Finset (Fin N × Fin (M N))`, and $\mathcal N_w$ is `StrictCompatLB.MeanField.nbrW`, defined together with proportional sparsity and the subcriticality condition in the module `Def_StrictCompatLB_MeanField_GraphConditions`. The indicator forces $(v,w)\in E_N$, so every term that enters has $|\mathcal N_w|\ge1$ and no division by zero occurs. If $M(N)=0$, Lean evaluates $N/M(N)$ to $0$; theorems using this definition assume $M(N)\ge1$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 34, display (A.19); p. 8, §2 (model, N_w); p. 11, Definition 3.3

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions

open Finset Filter

namespace StrictCompatLB.RegularDegree

/-! Condition (A.19) of Rutten & Mukherjee, arXiv:2008.07562v2 (p. 34), for sequences of bipartite
compatibility graphs `G_N = (V_N, W_N, E_N)` with `V_N = Fin N` (servers) and `W_N = Fin (M N)`
(dispatchers). The neighbourhoods and the conditions of Defs. 3.1 and 3.3 are in
`StrictCompatLB.MeanField` (module `Def_StrictCompatLB_MeanField_GraphConditions`). -/

/-- Condition (A.19): `limsup_N max_v (N/M(N)) Σ_w 𝟙{(v,w) ∈ E_N}/|𝒩_w| ≤ 1`, written as
"for every `ε > 0`, eventually every server's value is at most `1 + ε`". -/
def SatisfiesA19 (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v : Fin N,
    (N : ℝ) / (M N : ℝ) *
      ∑ w : Fin (M N), (if (v, w) ∈ G N then ((StrictCompatLB.MeanField.nbrW M G N w).card : ℝ)⁻¹ else 0)
      ≤ 1 + ε

end StrictCompatLB.RegularDegree


