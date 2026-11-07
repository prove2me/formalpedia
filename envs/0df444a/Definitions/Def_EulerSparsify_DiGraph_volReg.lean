-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_volReg
-- name    : EulerSparsify_DiGraph_volReg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:25.515295+00:00
-- url     : https://prove2.me/theorems/a27d5e36-d8e2-4d52-b396-28673c86c358
-- title:
--   Degrees, volumes and regularized volumes $\mathrm{vol}_\beta$
-- statement:
--   For a weighted graph $G$, the **weighted degree** is $\deg_G(v)=\sum_{e\ni v}w_e$ and the **volume** of $S\subseteq V$ is $\mathrm{vol}_G(S)=\sum_{v\in S}\deg_G(v)$. For a regularization parameter $\beta>0$ the **regularized volume** is
--
--   $$\mathrm{vol}_\beta(S)=\sum_{v\in S}\bigl(\deg_G(v)+\beta\bigr)=\mathrm{vol}_G(S)+\beta|S| ,$$
--
--   the volume after adding a self-loop of weight $\beta$ at every vertex. Volumes are always measured in the input graph $G$, also when an algorithm works on a subgraph.
--
--   **Formalization Note** A self-loop at $v$ counts once in $\deg_G(v)$ (the paper's $e\ni v$).
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Regularized degrees and volumes, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

namespace EulerSparsify

/-- The weighted degree `deg_G(v) = Σ_{e ∋ v} w_e` (§3, p.9, PDF p.11). A self-loop at `v` is
counted once. -/
noncomputable def DiGraph.deg {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E)
    (v : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.head e = v ∨ G.tail e = v), G.w e

/-- The volume `vol_G(S) = Σ_{v ∈ S} deg_G(v)` (§3, p.9). -/
noncomputable def DiGraph.vol {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E)
    (S : Finset V) : ℝ :=
  ∑ v ∈ S, G.deg v

/-- **Regularized volume** `vol_β(S) = vol_G(S) + β|S|` (§3, "Regularized degrees and volumes",
p.9, PDF p.11).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), p.9: "For a regularization parameter β > 0, we define the β-regularized degrees and volumes
deg_β(v) := deg_G(v) + β, vol_β(S) := Σ_{v∈S} deg_β(v) = Σ_{v∈S} deg_G(v) + β|S|. Both are always
measured in the input graph G, also when an algorithm works on a subgraph of G."

**Formalization Note.** A self-loop counts once in `deg` (the paper's `e ∋ v`); the graphs of
the statements that use volumes may contain loops, and a loop never changes a cut. -/
noncomputable def DiGraph.volReg {V E : Type} [Fintype E] [DecidableEq V] (G : DiGraph V E)
    (β : ℝ) (S : Finset V) : ℝ :=
  G.vol S + β * S.card

end EulerSparsify


