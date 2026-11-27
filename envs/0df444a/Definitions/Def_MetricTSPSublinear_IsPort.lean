-- Prove2me | Definitions.Def_MetricTSPSublinear_IsPort
-- name    : MetricTSPSublinear_IsPort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:51:48.544067+00:00
-- url     : https://prove2.me/theorems/296ee1a7-1a8d-50b7-836c-4b57e09eac8a
-- title:
--   Port of a cell of a core decomposition
-- statement:
--   Let the core be represented by a finite tree on nodes $\{0,\dots,m-1\}$ (a subdivision of the computed core $C$) and let the cells be node sets $P_\iota$, $\iota\in I$. A node $p$ is a **port** of the cell $P$ if $p\in P$ and $p$ also belongs to some other cell $R\neq P$. Ports are the points through which local solutions of neighbouring cells are glued together.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §6, p.21 (PDF p.23): 'Let ∂P denote its ports, which are the points shared with other cells.'

import Mathlib

namespace MetricTSPSublinear

/-- **A port of a cell.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*,
arXiv:2611.04283, §6, p.21 (PDF p.23): "Let ∂P denote its ports, which are the points shared with other cells."
For cells given as node sets `cellNodes : ι → Finset (Fin m)` of a (subdivided) core tree, `IsPort cellNodes P p`
says that `p` is a node of `P` that also lies in some other cell. -/
def IsPort {m : ℕ} {ι : Type*} (cellNodes : ι → Finset (Fin m)) (P : ι) (p : Fin m) : Prop :=
  p ∈ cellNodes P ∧ ∃ R, R ≠ P ∧ p ∈ cellNodes R

end MetricTSPSublinear


