-- Prove2me | Definitions.Def_SpectralSparsify_Decomp_cond
-- name    : SpectralSparsify_Decomp_cond
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:39.419347+00:00
-- url     : https://prove2.me/theorems/ac33985a-febd-45cb-943f-3035f7f20220
-- title:
--   Conductance Φ^G_B(S) of a set inside B and Φ^G_B = min_{S⊂B} Φ^G_B(S), volumes from G (§7, pp. 16–17)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $B\subseteq V$. For $S\subseteq B$ the **conductance of $S$ in the subgraph induced by $B$** is
--   $$\Phi^G_B(S)=\frac{|E(S,B-S)|}{\min\big(\operatorname{Vol}(S),\operatorname{Vol}(B-S)\big)},$$
--   where the volumes are measured with the degrees of $G$ (not of the induced subgraph $G(B)$), with the convention $\Phi^G_B(\emptyset)=1$. The **conductance of $B$** is
--   $$\Phi^G_B=\min_{S\subset B}\Phi^G_B(S),$$
--   the minimum over the proper subsets $S\subsetneq B$, with the convention $\Phi^G_B=1$ when $|B|=1$.
--
--   Because volumes are taken in $G$, $\Phi^G_B\le\Phi_{G(B)}$, so lower bounds on $\Phi^G_B$ give lower bounds on the conductance of the induced subgraph. A $\varphi$-decomposition of $G$ is a partition whose parts $A_i$ all satisfy $\Phi^G_{A_i}\ge\varphi$.
--
--   **Formalization Note** `condRel G B S` is $\Phi^G_B(S)$ and `cond G B` is $\Phi^G_B$, real-valued. The minimum ranges over the proper subsets of $B$ (the subset $S=B$ would give $0/0$); the empty set is included and contributes the value $1$. The quotient uses Lean's division, so it is $0$ whenever the denominator is $0$; every statement of the mission therefore assumes that $G$ has no isolated vertices, under which every nonempty set has positive volume and $\Phi^G_B(S)$ is the paper's quotient for every nonempty proper $S\subsetneq B$. The empty $B$, for which the paper defines nothing, also gets the value $1$.
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, pp. 16–17, Section 7 (definitions of Φ^G_B(S) and Φ^G_B, conventions Φ^G_B(∅) = 1 and Φ^G_B = 1 for |B| = 1)

import Mathlib
import Definitions.Def_SpectralSparsify_Decomp_vol
import Definitions.Def_SpectralSparsify_Decomp_cutEdges

namespace SpectralSparsify.Decomp

/-- The conductance `Φ^G_B(S)` of a vertex set `S` in the subgraph induced by `B`
(arXiv:0808.4134v3, §7, p. 16, with the convention `Φ^G_B(∅) = 1` of p. 17):
`Φ^G_B(S) = |E(S, B - S)| / min(Vol(S), Vol(B - S))`, volumes measured with the degrees of `G`. -/
noncomputable def condRel {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B S : Finset V) : ℝ :=
  if S = ∅ then 1
  else (cutEdges G S (B \ S) : ℝ) / min (vol G S) (vol G (B \ S))

/-- The conductance `Φ^G_B = min_{S ⊂ B} Φ^G_B(S)` of the subgraph induced by `B`
(arXiv:0808.4134v3, §7, pp. 16–17), the minimum over the proper subsets `S ⊊ B`, with the
convention `Φ^G_B = 1` when `|B| = 1` (p. 17). The empty `B` also gets the value `1`. -/
noncomputable def cond {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset V) : ℝ :=
  if h : B.card ≤ 1 then 1
  else
    (B.powerset.filter (· ⊂ B)).inf'
      ⟨∅, by
        rw [Finset.mem_filter]
        exact ⟨Finset.empty_mem_powerset B,
          Finset.empty_ssubset.mpr (Finset.card_pos.mp (by omega))⟩⟩
      (condRel G B)

end SpectralSparsify.Decomp


