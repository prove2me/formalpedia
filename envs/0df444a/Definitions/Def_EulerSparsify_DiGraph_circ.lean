-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_circ
-- name    : EulerSparsify_DiGraph_circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:04.942031+00:00
-- url     : https://prove2.me/theorems/2d7adef0-8490-415e-840b-c371e402c767
-- title:
--   Circulation subspace $C(F)$
-- statement:
--   For a set of edges $F\subseteq E$, the **circulation subspace** is
--
--   $$C(F)=\{x\in\mathbb R^E:\ \mathrm{supp}(x)\subseteq F,\ B^\top x=0\},$$
--
--   the circulations of the graph that use only edges of $F$. Here $B$ is the incidence matrix of the whole graph.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §5.1.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_incMat

namespace EulerSparsify

/-- **Circulation subspace** `C(F)` (§5.1.1, p.16, PDF p.18).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §5.1.1: "Given a subset of edges F ⊆ E, we define the circulation subspace by
C(F) := {x ∈ ℝ^E : supp(x) ⊆ F, Bᵀx = 0}."

**Formalization Note.** A subspace of `EuclideanSpace ℝ E` (so that its orthogonal projection
`P_{C(F)}` is taken in the standard inner product), cut out by `Bᵀx = 0` and `x_e = 0` for every
`e ∉ F`. `B` is the incidence matrix of the whole graph. -/
noncomputable def DiGraph.circ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : DiGraph V E) (F : Finset E) : Submodule ℝ (EuclideanSpace ℝ E) :=
  LinearMap.ker (Matrix.toEuclideanLin G.incMat.transpose) ⊓
    ⨅ (e : E) (_ : e ∉ F), LinearMap.ker ((EuclideanSpace.proj e : StrongDual ℝ (EuclideanSpace ℝ E)) : EuclideanSpace ℝ E →ₗ[ℝ] ℝ)

end EulerSparsify


