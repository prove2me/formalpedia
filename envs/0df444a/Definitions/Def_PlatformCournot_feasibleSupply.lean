-- Prove2me | Definitions.Def_PlatformCournot_feasibleSupply
-- name    : PlatformCournot_feasibleSupply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:24.608274+00:00
-- url     : https://prove2.me/theorems/b2dd9d19-a104-43cc-8a2d-8790183cda8f
-- title:
--   Feasible supply profiles $Q_i(\mathcal E)$ of firm $i$
-- statement:
--   Let $\mathcal E\subseteq F\times M$ be an edge set: $(i,j)\in\mathcal E$ when firm $i$ has access to market $j$. The **feasible supply profiles** of firm $i$ are the nonnegative vectors that supply nothing to the markets firm $i$ cannot access:
--
--   $$Q_i(\mathcal E)=\{x\in\mathbb R^m_+ : x_j=0 \text{ for all } (i,j)\notin\mathcal E\}.$$
--
--   Open access is $\mathcal E=F\times M$; a single market $j$ is $\mathcal E=F\times\{j\}$.
--
--   **Formalization Note** The edge set is `E : Set (Fin n × Fin m)`; $F\times M$ is `Set.univ` and $F\times\{j\}$ is `Set.univ ×ˢ {j}`.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.3, p.11 (and §2.1, p.8 for F × M)

import Mathlib

namespace PlatformCournot

/-- **Feasible supply profiles of firm `i` under the edge set `ℰ`.**
Pang et al., arXiv:1903.04574v3, §2.3, p.11: "Qi(ℰ) := { x ∈ ℝ^m_+ | xj = 0, ∀(i,j) ∉ ℰ }."

`feasibleSupply E i` is the set of nonnegative vectors `x ∈ ℝ^m` that vanish on every market `j`
with `(i, j) ∉ ℰ`.

**Formalization Note** The edge set is `E : Set (Fin n × Fin m)`; open access is `E = Set.univ`
(the paper's `F × M`), and a single market `j` is `Set.univ ×ˢ {j}` (the paper's `F × {j}`). -/
def feasibleSupply {n m : ℕ} (E : Set (Fin n × Fin m)) (i : Fin n) : Set (Fin m → ℝ) :=
  {x | ∀ j, 0 ≤ x j ∧ ((i, j) ∉ E → x j = 0)}

end PlatformCournot


