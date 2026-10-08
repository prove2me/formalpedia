-- Prove2me | Definitions.Def_LeightonRao_Uniform_Network
-- name    : LeightonRao_Uniform_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:29.914422+00:00
-- url     : https://prove2.me/theorems/2a23b363-7da6-40d1-80af-c16610630be1
-- title:
--   §1.1–1.2, §1.5, §2.2, pp. 788–795 — capacitated undirected network, cut capacity, connectivity, ratio cost, uniform min-cut 𝒮
-- statement:
--   A **network** on a finite vertex set $V$ (with $n=|V|$) assigns to every pair of nodes a capacity $C(u,v)\ge 0$, symmetric in $u$ and $v$ and zero on the diagonal. The pair $\{u,v\}$ is an edge of the underlying graph $G$ exactly when $C(u,v)>0$; parallel edges are merged into one capacity.
--
--   For $U\subseteq V$ with complement $\bar U$, the **cut capacity** is the total capacity of the edges linking $U$ to $\bar U$,
--   $$C(U,\bar U)=\sum_{u\in U}\sum_{v\in\bar U}C(u,v).$$
--   The network is **connected** if $C(U,\bar U)>0$ for every nonempty proper $U$ (the paper's standing assumption, p. 789). The **ratio cost** of the cut $\langle U,\bar U\rangle$ is $C(U,\bar U)/(|U|\,|\bar U|)$, and the **min-cut** (sparsest cut) of the uniform multicommodity flow problem on the network is Eq. (1),
--   $$\mathcal S=\min_{\emptyset\ne U\subsetneq V}\frac{C(U,\bar U)}{|U|\,|\bar U|}.$$
--
--   These are the cut-side objects of Theorem 2 and Lemmas 3–6.
--
--   **Formalization Note** The minimum ranges over nonempty proper subsets only: for $U=\emptyset$ or $U=V$ the ratio is $0/0$, which Lean would evaluate to $0$. The index type is nonempty exactly when $n\ge 2$, which every theorem using $\mathcal S$ assumes. The graph is `SimpleGraph.fromRel (0 < C u v)`.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 788–789 (§1.1–1.2, connectivity assumption p. 789), p. 792 (§1.5, Eq. (1)), p. 795 (§2.2, ratio cost)

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- An undirected capacitated network. A pair is an edge precisely when its capacity is
strictly positive. Parallel edges are represented by their summed capacity. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The capacity of the edges crossing a cut, each undirected edge counted once. -/
noncomputable def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The standing connectedness convention of p. 789. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

/-- The graph supported by positive-capacity pairs. -/
noncomputable def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

/-- The ratio cost of a cut. Used only for nonempty proper cuts, so the denominator is
positive. -/
noncomputable def ratioCost (N : Network V) (U : Finset V) : ℝ :=
  cutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- The uniform sparsest cut. With at least two vertices, the index of proper cuts is
nonempty and finite; improper cuts would give a spurious `0 / 0` in Lean. -/
noncomputable def minCut (N : Network V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, ratioCost N U.1

end LeightonRao.Uniform


