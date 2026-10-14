-- Prove2me | Definitions.Def_LNTopology_Hermetic_Degree
-- name    : LNTopology_Hermetic_Degree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:49.551458+00:00
-- url     : https://prove2.me/theorems/388e04f1-e18c-459f-b9ad-ceb7f8ac43c7
-- title:
--   Degree $d(v)$, flows $s(v)$, $S(v)$, minimum and average degree, and discrepancy $\mathrm{disc}$ of a Lightning Network
-- statement:
--   Let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on the finite node set $V$ and $c$ a channel cost. For a set of nodes $U\subseteq V$ and a node $v$, all quantities below are computed in the subnetwork **induced on $U$**, i.e. only channels from $v$ to nodes of $U$ are counted:
--
--   1. the degree $d_U(v)=|\{w\in U:\lambda_{v,w}\neq0\}|$;
--   2. the smallest flow $s_U(v)=\min\{|\lambda_{v,j}|: j\in U,\ \lambda_{v,j}\ne0\}$ of a channel of $v$ inside $U$;
--   3. the largest flow $S_U(v)=\max_{j\in U}|\lambda_{v,j}|$;
--   4. the minimum degree $\delta(U)=\min_{v\in U}d_U(v)$;
--   5. the discrepancy
--   $$\mathrm{disc}(U)=\max_{v}\frac{c(S_U(v))}{c(s_U(v))},$$
--   the maximum taken over the nodes $v\in U$ having at least one channel inside $U$.
--
--   For the whole network ($U=V$) these are the paper's $d(v)$, $s(v)$, $S(v)$, $\delta(G)$ and $\mathrm{disc}(G)$, and the average degree is
--
--   $$\bar d(G)=\sum_{v\in V}\frac{d(v)}{|V|}.$$
--
--   These are Definitions 3.4 and 3.5; Lemmas B.1 and B.2 use them for the subnetwork on $U$, Theorem 3.8 for the whole network.
--
--   **Formalization Note** $s(v)$ is undefined for a node without channels; Lean returns the junk value $0$ there, and every statement using it assumes the node has a channel. For the same reason the maximum defining $\mathrm{disc}$ is taken over nodes with at least one channel (value $0$ if there is none), and $\delta(\emptyset)=0$, $S_\emptyset(v)=0$. $\bar d(G)$ is a real-number quotient; statements using it assume $V\neq\emptyset$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 7 (PDF p. 8), Definitions 3.4 and 3.5; subnetwork on U as used in Lemmas B.1–B.2, pp. 11–12

import Mathlib
import Definitions.Def_LNTopology_Hermetic_Model

namespace LNTopology.Hermetic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `d_U(v)`: the number of channels of `v` towards nodes of `U`
(the degree of `v` in the subnetwork induced on `U`). -/
noncomputable def degIn (Λ : V → V → ℝ) (U : Finset V) (v : V) : ℕ :=
  (U.filter (fun w => Λ v w ≠ 0)).card

/-- `s_U(v) = min{|λ_{v,j}| : j ∈ U, λ_{v,j} ≠ 0}`; junk value `0` if `v` has no channel in `U`. -/
noncomputable def minFlowIn (Λ : V → V → ℝ) (U : Finset V) (v : V) : ℝ :=
  if h : (U.filter (fun j => Λ v j ≠ 0)).Nonempty then
    (U.filter (fun j => Λ v j ≠ 0)).inf' h (fun j => |Λ v j|)
  else 0

/-- `S_U(v) = max_{j ∈ U} |λ_{v,j}|`; value `0` if `U` is empty. -/
noncomputable def maxFlowIn (Λ : V → V → ℝ) (U : Finset V) (v : V) : ℝ :=
  if h : U.Nonempty then U.sup' h (fun j => |Λ v j|) else 0

/-- `δ(U) = min_{v ∈ U} d_U(v)`; value `0` if `U` is empty. -/
noncomputable def minDegIn (Λ : V → V → ℝ) (U : Finset V) : ℕ :=
  if h : U.Nonempty then U.inf' h (degIn Λ U) else 0

/-- `disc(U) = max c(S_U(v)) / c(s_U(v))`, the maximum taken over the nodes `v ∈ U` that have at
least one channel inside `U`; value `0` if there is no such node. -/
noncomputable def discIn (c : ℝ → ℝ) (Λ : V → V → ℝ) (U : Finset V) : ℝ :=
  if h : (U.filter (fun v => degIn Λ U v ≠ 0)).Nonempty then
    (U.filter (fun v => degIn Λ U v ≠ 0)).sup' h
      (fun v => c (maxFlowIn Λ U v) / c (minFlowIn Λ U v))
  else 0

/-- `d(v) = |{w ∈ V : λ_{v,w} ≠ 0}|`, the degree of `v` in the whole network. -/
noncomputable def deg (Λ : V → V → ℝ) (v : V) : ℕ := degIn Λ Finset.univ v

/-- `disc(G)` for the whole network (Definition 3.5). -/
noncomputable def disc (c : ℝ → ℝ) (Λ : V → V → ℝ) : ℝ := discIn c Λ Finset.univ

/-- The average degree `d̄(G) = ∑_v d(v) / |V|`. -/
noncomputable def avgDeg (Λ : V → V → ℝ) : ℝ :=
  (∑ v, (deg Λ v : ℝ)) / (Fintype.card V : ℝ)

end LNTopology.Hermetic


