-- Prove2me | Definitions.Def_LawlerWCT_RhoMax_Model
-- name    : LawlerWCT_RhoMax_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:28.595977+00:00
-- url     : https://prove2.me/theorems/b5e5cecf-8b42-4cc2-ad5c-53d3d50a50eb
-- title:
--   §4 Definitions 2–3, §7 pp. 14–15 — ratios ρ(I), initial sets, ρ-maximality, trial weights and the cut network G*
-- statement:
--   This definition file fixes the objects of §7 of Lawler's report, *Finding ρ-maximal initial sets*.
--
--   **Jobs and precedences.** A finite set $N$ of jobs carries an acyclic digraph $G=(N,A)$; job $i$ must precede job $j$ when $G$ has a directed path from $i$ to $j$. Each job $j$ has a processing time $p_j$ and a weight $w_j$.
--
--   **Ratio (Definition 2).** For a set $I\subseteq N$ of jobs,
--   $$\rho(I)=\frac{\sum_{j\in I} w_j}{\sum_{j\in I} p_j}.$$
--
--   **Initial set (Definition 2).** A subset $I\subseteq M$ is an *initial set* of $M$ if, for each $j\in I$, every predecessor of $j$ in $M$ (every $i\in M$ with a directed path from $i$ to $j$ in $G$) also lies in $I$.
--
--   **ρ-maximal initial set (Definition 3).** A nonempty initial set $I^*$ of $M$ is *ρ-maximal* if $\rho(I^*)\ge\rho(I)$ for every nonempty initial set $I$ of $M$.
--
--   **Trial weights (§7, p. 15).** For a trial value $\rho$, each job receives the weight $\bar w_j=w_j-\rho\,p_j$, and the weight of a set $I$ is $\sum_{j\in I}\bar w_j$.
--
--   **The network $G^*$ (§7, p. 14).** Add a source $s$ and a sink $t$ to $G$. The capacities are
--   $$c_{sj}=\max(0,-w_j),\qquad c_{jt}=\max(0,+w_j),\qquad c_{ij}=+\infty \text{ for each arc } (i,j) \text{ of } G .$$
--   A partition of the nodes of $G^*$ into $S\ni s$ and $T\ni t$ is an $(s,t)$ cutset, of capacity
--   $$c(S,T)=\sum_{i\in S}\sum_{j\in T}c_{ij}.$$
--   The job set of the cutset is $I=T-\{t\}$.
--
--   These objects are the vocabulary of every statement of the mission: the correspondence between finite cuts and initial sets, the three outcomes of a trial value, and the correctness of the last step of the binary search.
--
--   **Formalization Note.** Jobs are a `Finset N` in a type `ι`; "predecessor" is `Relation.TransGen G`. Lean evaluates $\rho(\emptyset)=0/0=0$, whereas the paper's ratio is undefined there, so ρ-maximality requires a nonempty set and compares only with nonempty initial sets. Capacities take values in `WithTop ℝ`, with $+\infty=\top$; a pair of nodes that is not an arc of $G^*$ gets capacity $0$, which leaves every sum unchanged. An infinite cut has capacity $\top$; no subtraction is ever done in `WithTop ℝ`. A cutset is given by its sink side $T$ inside the node set $\{s,t\}\cup N$, and $S$ is its complement there. The arc test uses classical decidability. The ratio $\rho$, initial sets and ρ-maximality are not redefined here: they are the shared definitions `LawlerWCT.SeriesPar.rho`, `IsInitialSet` and `IsRhoMaximal` of the companion mission on the series-parallel algorithm, which this file imports.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 1 (§1 model), p. 8 (Definitions 2 and 3), pp. 14–15 (§7, the network G*, cut capacity, trial weights)

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model

namespace LawlerWCT.RhoMax

/-- §7, p. 15: the weight of `I` with respect to the trial weights `w̄_j = w_j − ρ p_j`. -/
def trialWeight {ι : Type*} (p w : ι → ℝ) (ρ : ℝ) (I : Finset ι) : ℝ :=
  ∑ j ∈ I, (w j - ρ * p j)

/-- The nodes of the flow network `G*` of §7, p. 14: a source `s`, a sink `t`, and one node per job. -/
inductive Node (ι : Type*) where
  | s : Node ι
  | t : Node ι
  | job (j : ι) : Node ι
  deriving DecidableEq

open Classical in
/-- Capacities of `G*` (§7, p. 14): `c_sj = max(0, −w_j)`, `c_jt = max(0, +w_j)`, `c_ij = +∞` for
each arc `(i, j)` of `G`; a pair that is not an arc of `G*` has capacity `0`. -/
noncomputable def cap {ι : Type*} (G : ι → ι → Prop) (w : ι → ℝ) :
    Node ι → Node ι → WithTop ℝ
  | .s, .job j => ((max 0 (-w j) : ℝ) : WithTop ℝ)
  | .job j, .t => ((max 0 (w j) : ℝ) : WithTop ℝ)
  | .job i, .job j => if G i j then ⊤ else 0
  | _, _ => 0

/-- The node set `{s, t} ∪ N` of `G*`. -/
def nodes {ι : Type*} [DecidableEq ι] (N : Finset ι) : Finset (Node ι) :=
  {Node.s, Node.t} ∪ N.image Node.job

/-- The capacity `c(S, T) = ∑_{u ∈ S} ∑_{v ∈ T} c_uv` of the `(s, t)` cutset with sink side `T`
and source side `S = nodes N \ T`. -/
noncomputable def cutCapacity {ι : Type*} [DecidableEq ι] (N : Finset ι) (G : ι → ι → Prop)
    (w : ι → ℝ) (T : Finset (Node ι)) : WithTop ℝ :=
  ∑ u ∈ nodes N \ T, ∑ v ∈ T, cap G w u v

/-- The job set `I = T − {t}` of a sink side `T`. -/
def jobsOf {ι : Type*} [DecidableEq ι] (N : Finset ι) (T : Finset (Node ι)) : Finset ι :=
  N.filter (fun j => Node.job j ∈ T)

end LawlerWCT.RhoMax


