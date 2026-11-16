-- Prove2me | Definitions.Def_TFNPRom_Supplement_sinkDagSol
-- name    : TFNPRom_Supplement_sinkDagSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:26:16.496491+00:00
-- url     : https://prove2.me/theorems/8c2744c6-1cdc-442e-9a71-13b14c47c515
-- title:
--   Solutions of Sink of Dag (canonical PLS-complete problem)
-- statement:
--   Let $K\ge 2$. An instance of **Sink of Dag** on the $K\times K$ grid assigns to every node $(i,j)$ a successor $\mathrm{Succ}_{ij}\in[K]\cup\{\bot\}$; for $i<K$ a value $k\neq\bot$ names the node $(i+1,k)$. A node is active iff $\mathrm{Succ}_{ij}\neq\bot$. The solutions are
--
--   1. $(1,1)$, if it is inactive (no canonical source);
--   2. $(K,j)$, if it is active (sink);
--   3. $(i,j)$ with $i<K$, if it is active but $(i+1,\mathrm{Succ}_{ij})$ is inactive (predecessor of a proper sink).
--
--   This is the canonical complete problem of PLS used as the target of the reductions in Theorems 36 and 39. An instance has $K^2$ cells.
--
--   **Formalization Note** 0-based `Fin K`: $(1,1)$ is $(0,0)$ and row $K$ is index $K-1$; $\bot$ is `none`.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), App. A, p.41

import Mathlib

namespace TFNPRom.Supplement

/-- The solutions of the canonical PLS-complete problem Sink of Dag on the `K × K` grid
(Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), App. A, p.41). Every node `(i, j)` has `Succ_ij ∈ [K] ∪ {⊥}`; for `i < K` a value
`k ≠ ⊥` names the node `(i + 1, k)`. A node is active iff `Succ_ij ≠ ⊥`. The solutions are
1. `(1, 1)` if it is inactive (no canonical source);
2. `(K, j)` if it is active (sink);
3. `(i, j)` with `i < K` if it is active but `(i + 1, Succ_ij)` is inactive (predecessor of a
   proper sink).

**Formalization Note** 0-based `Fin K`: `(1, 1)` is `(0, 0)`, row `K` is index `K − 1`; `⊥` is
`none`. The instance has `K²` cells (the pointers `Succ_ij`). -/
def sinkDagSol (K : ℕ) (succ : Fin K → Fin K → Option (Fin K)) (v : Fin K × Fin K) : Prop :=
  (v.1.val = 0 ∧ v.2.val = 0 ∧ succ v.1 v.2 = none) ∨
  (v.1.val + 1 = K ∧ succ v.1 v.2 ≠ none) ∨
  (∃ h : v.1.val + 1 < K, ∃ k, succ v.1 v.2 = some k ∧ succ ⟨v.1.val + 1, h⟩ k = none)

end TFNPRom.Supplement


