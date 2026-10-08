-- Prove2me | Definitions.Def_LeightonRao_ShortPaths_Network
-- name    : LeightonRao_ShortPaths_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:19.835321+00:00
-- url     : https://prove2.me/theorems/7b9e1a60-5883-4791-8ccd-4861b253f385
-- title:
--   §1.1–1.2 — undirected capacitated network, proper cut, and uniform demand
-- statement:
--   A **network** has a finite vertex set $V$ and a symmetric, nonnegative capacity $C(u,v)$ for each pair of vertices, with $C(u,u)=0$. A pair is an edge exactly when its capacity is positive. For a vertex set $U$, the capacity of its cut is
--
--   $$C(U,\bar U)=\sum_{u\in U}\sum_{v\notin U}C(u,v).$$
--
--   The network is **connected** when every nonempty proper cut has positive capacity. Its uniform **sparsest cut value** is
--
--   $$\mathcal S=\min_{\varnothing\ne U\subsetneq V}\frac{C(U,\bar U)}{|U|\,|\bar U|}.$$
--
--   The ordered-pair representation of a uniform multicommodity problem gives demand $1/2$ to each pair $(s,t)$ with $s\ne t$ and zero demand on the diagonal. This makes the total demand across a cut equal to $|U|\,|\bar U|$.
--
--   **Formalization Note** Parallel edges are merged into their total capacity. The minimum is encoded as an infimum over proper cuts and is used only for networks with at least two vertices. The ordered-pair normalization is footnote 2 on p. 791.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 788–792, §1.1–1.2, §1.5, Eq. (1) and footnote 2

import Mathlib

namespace LeightonRao.ShortPaths

/-- A finite undirected capacitated network. A pair is an edge exactly when its capacity is positive. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The paper's standing connectivity assumption, stated in cut form. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

noncomputable def ratioCost (N : Network V) (U : Finset V) : ℝ :=
  cutCap N U / ((U.card : ℝ) * (Uᶜ.card : ℝ))

/-- The infimum is over nonempty proper cuts. It is a genuine minimum when `2 ≤ card V`. -/
noncomputable def minCut (N : Network V) : ℝ :=
  ⨅ U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty}, ratioCost N U.1

noncomputable def uniformDemand (s t : V) : ℝ := if s = t then 0 else 1 / 2

end LeightonRao.ShortPaths


