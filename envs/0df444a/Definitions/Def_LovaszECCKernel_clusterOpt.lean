-- Prove2me | Definitions.Def_LovaszECCKernel_clusterOpt
-- name    : LovaszECCKernel_clusterOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:55:47.489872+00:00
-- url     : https://prove2.me/theorems/e6f63475-71e0-4e87-9659-0597a10efd8a
-- title:
--   The Cluster Editing optimum $\mathrm{opt}(G)$
-- statement:
--   In **Cluster Editing**, given a graph $G$, one seeks a minimum-size set of adjacency modifications $M\subseteq\binom{V(G)}{2}$ such that $G\triangle M$ is a cluster graph. The optimum
--   $$\mathrm{opt}(G)=\min\{|M| : M\subseteq\tbinom{V(G)}{2},\ G\triangle M\text{ is a cluster graph}\}$$
--   exists on a finite vertex set ($M=E(G)$ leaves the edgeless graph). A $C$-approximation outputs a valid $M$ with $|M|\le C\cdot\mathrm{opt}(G)$.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §2.1, p.17 (= PDF p.17)

import Mathlib
import Definitions.Def_LovaszECCKernel_flip
import Definitions.Def_LovaszECCKernel_IsClusterGraph

set_option autoImplicit false

namespace LovaszECCKernel

/-- The optimum of **Cluster Editing** (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability
Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC
2027 submission (manuscript sha256 a9d53ab8…), §2.1, p.17 (= PDF p.17)): "we are given a graph G
with n vertices and m edges, and the task is to find a minimum-size set of adjacency modifications
M ⊆ (V(G) choose 2) such that G△M is a cluster graph".

**Formalization Note** The least `|M|` over sets `M` of pairs of distinct vertices with `G△M` a
cluster graph. On a finite vertex set the set is nonempty (`M = E(G)` leaves the edgeless graph). -/
noncomputable def clusterOpt {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {q : ℕ | ∃ M : Finset (Sym2 V), IsPairSet M ∧ IsClusterGraph (flip G M) ∧ M.card = q}

end LovaszECCKernel


