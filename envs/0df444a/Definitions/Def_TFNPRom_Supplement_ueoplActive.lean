-- Prove2me | Definitions.Def_TFNPRom_Supplement_ueoplActive
-- name    : TFNPRom_Supplement_ueoplActive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:24:51.522523+00:00
-- url     : https://prove2.me/theorems/71836f18-0029-4668-aedb-fcadb3215630
-- title:
--   Active nodes of a UEoPL instance
-- statement:
--   Let $N\ge 2$. A **UEoPL instance** on the grid $[N]\times[N]$ (row $i$, column $j$) consists of a successor $\mathrm{Succ}_v\in[N]\cup\{\bot\}$ for every node $v$ and a predecessor $\mathrm{Pred}_v\in[N]\cup\{\bot\}$ for every node $v$ in rows $2,\dots,N$.
--
--   A node $(i,j)$ with $i<N$ is **active** if $\mathrm{Succ}_{ij}=k\neq\bot$ and $\mathrm{Pred}_{i+1,k}=j$; a node $(N,j)$ of the last row is active if $\mathrm{Succ}_{Nj}\neq\bot$. Otherwise the node is inactive.
--
--   Activity is the notion on which all solution types of UEoPL (Definition 3) are built.
--
--   **Formalization Note** Rows and columns are `Fin N`, 0-based: row $i$ is index $i-1$ and the last row is index $N-1$; $\bot$ is `none`. The predecessor function is given on every node, but its values on the first row are never read.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, pp.19–20; App. A, p.42

import Mathlib

namespace TFNPRom.Supplement

/-- Activity of a node of a UEoPL instance (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, p.19; App. A, p.42). The grid is
`[N] × [N]` (row `i`, column `j`); the instance gives `Succ_v ∈ [N] ∪ {⊥}` for every node and
`Pred_v ∈ [N] ∪ {⊥}` for every node of rows `2, …, N`. A node `(i, j)` with `i < N` is active iff
`Succ_ij = k ≠ ⊥` and `Pred_{i+1,k} = j`; a node `(N, j)` of the last row is active iff
`Succ_Nj ≠ ⊥`.

**Formalization Note** `[N]` is `Fin N` (0-based): row `i` of the paper is index `i − 1`, the last
row is index `N − 1`. `⊥` is `none`. `pred` is given on every node; its values on the first row
(index `0`) are never read, since a predecessor is only looked up at row `i + 1`. -/
def ueoplActive (N : ℕ) (succ pred : Fin N → Fin N → Option (Fin N)) (v : Fin N × Fin N) : Prop :=
  ∃ k, succ v.1 v.2 = some k ∧ ∀ h : v.1.val + 1 < N, pred ⟨v.1.val + 1, h⟩ k = some v.2

end TFNPRom.Supplement


