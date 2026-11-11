-- Prove2me | Definitions.Def_SensLabelCover_DH_LabelCover
-- name    : SensLabelCover_DH_LabelCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:28.35054+00:00
-- url     : https://prove2.me/theorems/14f858d8-0881-4459-b6f1-948969b39688
-- title:
--   Left-predicate Label Cover on a fixed bipartite multigraph: instances, value, satisfiability, Hamming distance on $U\sqcup V$ and swaps
-- statement:
--   A **bipartite multigraph** $G=(U,V,E)$ has finite vertex sets $U,V$ and a finite set $E$ of edges, each edge $e$ having a left endpoint $u(e)\in U$ and a right endpoint $v(e)\in V$; parallel edges are distinct elements of $E$. The degree of a vertex counts its edges with multiplicity; $\Delta_U$ is the maximum left degree and $\delta_V$ the minimum right degree.
--
--   Given finite alphabets $\Sigma_U,\Sigma_V$, a **left-predicate Label Cover instance** on $G$ is $I=(P,F)$: a predicate $P_u:\Sigma_U\to\{0,1\}$ for each $u\in U$ and a projection $f_e:\Sigma_U\to\Sigma_V$ for each $e\in E$. An **assignment** is $\pi=(\pi_U,\pi_V)$ with $\pi_U:U\to\Sigma_U$, $\pi_V:V\to\Sigma_V$. An edge $e=(u,v)$ is **satisfied** if $P_u(\pi_U(u))=1$ and $f_e(\pi_U(u))=\pi_V(v)$, so a left label failing its predicate satisfies none of its edges. The value is
--   $$\mathrm{val}_I(\pi)=\begin{cases}1 & E=\emptyset,\\ \dfrac{|\{e\in E: e\text{ satisfied by }\pi\}|}{|E|} & E\neq\emptyset,\end{cases}$$
--   and $I$ is **satisfiable** if $\mathrm{val}_I(\pi)=1$ for some $\pi$. The **Hamming distance** of two assignments counts changed labels on both sides:
--   $$d_H(\pi,\tilde\pi)=|\{u:\pi_U(u)\neq\tilde\pi_U(u)\}|+|\{v:\pi_V(v)\neq\tilde\pi_V(v)\}|.$$
--   A **swap** replaces one projection, $I_{e\leftarrow f}$ with any $f:\Sigma_U\to\Sigma_V$, or one predicate, $I_{u\leftarrow Q}$ with any $Q:\Sigma_U\to\{0,1\}$; graph and alphabets never change.
--
--   This is the problem whose sensitivity the mission bounds; with these swaps and $d_H$, the general notions of swap closure, swap distance, EMD and swap sensitivity apply.
--
--   **Formalization Note** The graph `BGraph U V E` (endpoint maps `left`, `right`) and the alphabets are fixed parameters; an instance `LCInst U E SU SV` is the pair $(P,F)$ with `P u : SU → Bool` (`true` = 1). `lcVal` returns $1$ when `Fintype.card E = 0`. `lcDist` is the Hamming distance over $U\sqcup V$ as a real number. `maxLDeg` is `0` and `minRDeg` is `0` on an empty vertex set. `lcAdj I J` is "$J$ is $I$ with one projection or one predicate replaced" (replacing a component by itself is allowed and harmless).
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 14 (PDF 17) Definition 2.1; p. 15 (PDF 18) §2.2; p. 26 (PDF 29) degree notation

import Mathlib
import Definitions.Def_SensLabelCover_DH_Sensitivity

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), Definition 2.1 (p. 14, PDF p. 17)
and §2.2 (p. 15, PDF p. 18): left-predicate Label Cover on a fixed bipartite multigraph.

The graph and the alphabets are fixed data; an instance is the pair `(P, F)` of left predicates
and projections on it, since swaps never change the graph or the alphabets. -/

noncomputable section

/-- A bipartite multigraph `G = (U, V, E)`: `E` is an index type of edges, each with a left
endpoint `left e ∈ U` and a right endpoint `right e ∈ V`; parallel edges are distinct elements
of `E`. -/
structure BGraph (U V E : Type) where
  left : E → U
  right : E → V

variable {U V E SU SV : Type}

/-- Degree of a left vertex: the number of edges (with multiplicity) at `u`. -/
def BGraph.ldeg [Fintype E] [DecidableEq U] (G : BGraph U V E) (u : U) : ℕ :=
  (Finset.univ.filter (fun e => G.left e = u)).card

/-- Degree of a right vertex: the number of edges (with multiplicity) at `v`. -/
def BGraph.rdeg [Fintype E] [DecidableEq V] (G : BGraph U V E) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => G.right e = v)).card

/-- Maximum left degree `Δ_U` (`0` when `U` is empty). -/
def BGraph.maxLDeg [Fintype U] [Fintype E] [DecidableEq U] (G : BGraph U V E) : ℕ :=
  Finset.univ.sup G.ldeg

/-- Minimum right degree `δ_V` (`0` when `V` is empty). -/
def BGraph.minRDeg [Fintype E] [DecidableEq V] (G : BGraph U V E) : ℕ :=
  ⨅ v, G.rdeg v

/-- A left-predicate Label Cover instance on a graph with left vertices `U`, edges `E`, left
alphabet `SU` and right alphabet `SV` (Definition 2.1): a unary predicate `P u : Σ_U → {0,1}`
for each left vertex (`true` = 1) and a projection `F e : Σ_U → Σ_V` for each edge. -/
structure LCInst (U E SU SV : Type) where
  P : U → SU → Bool
  F : E → SU → SV

/-- An assignment `π = (π_U, π_V)` with `π_U : U → Σ_U`, `π_V : V → Σ_V`. -/
abbrev Assignment (U V SU SV : Type) := (U → SU) × (V → SV)

/-- Edge `e = (u, v)` is satisfied by `π` iff `P_u(π_U(u)) = 1` and `f_e(π_U(u)) = π_V(v)`. -/
def EdgeSat [DecidableEq SV] (G : BGraph U V E) (I : LCInst U E SU SV)
    (π : Assignment U V SU SV) (e : E) : Prop :=
  I.P (G.left e) (π.1 (G.left e)) = true ∧ I.F e (π.1 (G.left e)) = π.2 (G.right e)

instance [DecidableEq SV] (G : BGraph U V E) (I : LCInst U E SU SV) (π : Assignment U V SU SV) :
    DecidablePred (EdgeSat G I π) :=
  fun e => by unfold EdgeSat; infer_instance

/-- `val_I(π)`: `1` when `E = ∅`, otherwise the fraction of satisfied edges (Definition 2.1). -/
def lcVal [Fintype E] [DecidableEq SV] (G : BGraph U V E) (I : LCInst U E SU SV)
    (π : Assignment U V SU SV) : ℝ :=
  if Fintype.card E = 0 then 1
  else ((Finset.univ.filter (EdgeSat G I π)).card : ℝ) / (Fintype.card E : ℝ)

/-- `I` is satisfiable iff some assignment has `val_I(π) = 1`. -/
def lcSat [Fintype E] [DecidableEq SV] (G : BGraph U V E) (I : LCInst U E SU SV) : Prop :=
  ∃ π : Assignment U V SU SV, lcVal G I π = 1

/-- Hamming distance of two Label Cover assignments over the domain `U ⊔ V`: the number of left
vertices plus the number of right vertices whose labels differ. -/
def lcDist [Fintype U] [Fintype V] [DecidableEq SU] [DecidableEq SV]
    (π π' : Assignment U V SU SV) : ℝ :=
  (hammingDist π.1 π'.1 : ℝ) + (hammingDist π.2 π'.2 : ℝ)

/-- One swap (§2.2): `J = I_{e←f}` (replace the projection `f_e` by any `f : Σ_U → Σ_V`) or
`J = I_{u←Q}` (replace the predicate `P_u` by any `Q : Σ_U → {0,1}`). Graph and alphabets are
unchanged. -/
def lcAdj [DecidableEq U] [DecidableEq E] (I J : LCInst U E SU SV) : Prop :=
  (∃ (e : E) (f : SU → SV), J = { I with F := Function.update I.F e f }) ∨
  (∃ (u : U) (Q : SU → Bool), J = { I with P := Function.update I.P u Q })

end

end SensLabelCover.DH


