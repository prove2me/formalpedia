-- Prove2me | Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model
-- name    : GilmoreGomoryTSP_Bottleneck_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:21.871025+00:00
-- url     : https://prove2.me/theorems/29ab8a27-2763-4178-a9d3-a02bfb8c4e16
-- title:
--   pp. 655–671 — changeover cost (1), tours (4), interchanges, G_φ and adjacent-arc spanning trees, the bottleneck objective m, the tour ψ′, G_ψ* and G′_φ
-- statement:
--   **Jobs and costs.** There are $N = n+1$ jobs $J_1,\dots,J_N$ on a machine whose state is a single real variable $x$. Job $i$ starts in state $A_i$ and ends in state $B_i$. The jobs are numbered so that $j > i$ implies $B_j \ge B_i$. Given densities $f, g:\mathbb R\to\mathbb R$, the cost of having job $j$ follow job $i$ is (1)
--   $$c_{ij} = \begin{cases} \displaystyle\int_{B_i}^{A_j} f(x)\,dx & \text{if } A_j \ge B_i,\\[2mm] \displaystyle\int_{A_j}^{B_i} g(x)\,dx & \text{if } B_i > A_j.\end{cases}$$
--   A permutation $\psi$ of the jobs is read as "job $\psi(i)$ follows job $i$"; its cost (3) is $c(\psi) = \sum_{i} c_{i\psi(i)}$ and its **bottleneck cost** is
--   $$m(\psi) = \max_{1\le i\le N} c_{i\psi(i)}.$$
--   $\psi$ is a **tour** (4) if $\psi(s)\neq s$ for every nonempty proper subset $s$ of the jobs, i.e. $\psi$ is a single cycle through all jobs.
--
--   **Interchanges and graphs.** The interchange $\alpha_{ij}$ is the transposition of $i$ and $j$, and $\psi\alpha_{ij}$ means "first apply $\alpha_{ij}$, then $\psi$". The graph $G_\psi$ has the $N$ jobs as nodes and an undirected arc $R_{i\psi(i)}$ for every $i$. For $1\le q<N$, $R_{q,q+1}$ is the arc joining nodes $q$ and $q+1$. A set $T$ of such arcs is an (adjacent-arc) **spanning tree** of $G_\psi$ if $G_\psi\cup T$ is connected and no proper subset of $T$ connects $G_\psi$.
--
--   **Bottleneck data.** Let $\varphi$ be a permutation ranking the $A$'s. In the bottleneck case the arc $R_{q,q+1}$ gets the cost $c_{q\varphi(q+1)}$; a **minimum spanning tree** of $G_\varphi$ is a spanning tree $T$ minimizing $\sum_{q\in T} c_{q\varphi(q+1)}$ among all adjacent-arc spanning trees. If $T$ consists of the arcs $R_{j_1,j_1+1},\dots,R_{j_m,j_m+1}$ with $j_1<\dots<j_m$, then
--   $$\psi' = \varphi\,\alpha_{j_1 j_1+1}\cdots\alpha_{j_m j_m+1}.$$
--
--   **The graph $G_\psi^*$.** For a permutation $\psi$ and an index $q$, conditions (22a) and (22b) are
--   $$ i \le q < \varphi^{-1}\psi(i), \qquad \varphi^{-1}\psi(j) \le q < j .$$
--   $G_\psi^*$ consists of all arcs of $G_\varphi$ together with every arc $R_{q,q+1}$ for which (22a) holds for some $i$ or (22b) holds for some $j$.
--
--   **The graph $G'_\varphi$.** For a directed graph on the $N$ nodes given by out-neighbourhoods $\Gamma_i$ (the nodes $j$ with an arc from $i$ to $j$), $G'_\varphi$ is the undirected graph with an arc $R_{q\varphi(q)}$ if and only if $\varphi(q)\in\Gamma_q$ and an arc $R_{q,q+1}$ if and only if $\varphi(q+1)\in\Gamma_q$.
--
--   These objects carry every statement of the bottleneck mission.
--
--   **Formalization Note** Jobs are `Fin (n + 1)`, 0-based (the paper's job $i$ is index $i-1$). The arc $R_{q,q+1}$ is indexed by `q : Fin n` and joins `q.castSucc` and `q.succ`. $\psi\alpha_{ij}$ is `ψ * Equiv.swap i j`. The maximum $m$ is `Finset.sup'` over the nonempty set of jobs. The integrals are interval integrals; integrability and the sign conditions are hypotheses of the theorems, not part of the definitions. "Proper subset" in (4) is read as nonempty proper subset (the empty set is always fixed). Graphs are Mathlib simple graphs: loops $R_{ii}$ are dropped, which does not affect connectivity. "A minimal set of additional arcs that connect" (p. 660) is read as inclusion-minimal; for arcs between components of $G_\varphi$ this coincides with the minimum number $p-1$. Conditions (22a)/(22b) are compared as natural numbers.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), pp. 655–658, Eqs. (1)–(7); p. 660 (G_ψ, spanning tree); p. 666, (22a)–(22b); p. 668 (G_ψ*); p. 670 (m, arc costs c_{qφ(q+1)}, ψ′); p. 671 (G′_φ, Theorem 6)

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

namespace GilmoreGomoryTSP.Bottleneck

open MeasureTheory

/-- The bottleneck objective, p. 670: `m(ψ) = max_i c_{i ψ(i)}`, a maximum over the nonempty
finite set of jobs. -/
noncomputable def m {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i))

/-- The interchange `α_{ij}` applied to `ψ`, (5)–(7), p. 658: `ψ α_{ij}`, first apply `α_{ij}`,
then `ψ`. -/
def interchange {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  ψ * Equiv.swap i j

/-- The graph `G_ψ`, p. 660: an undirected arc linking `i` and `ψ(i)` for every `i`
(loops `ψ(i) = i` are dropped; they do not affect connectivity). -/
def graphOf {n : ℕ} (ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => ψ i = j)

/-- The arcs `R_{q,q+1}` for `q ∈ T`; the arc indexed by `q : Fin n` joins `q.castSucc` and
`q.succ` (the paper's nodes `q` and `q + 1`). -/
def adjArcs {n : ℕ} (T : Finset (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j => ∃ q ∈ T, i = q.castSucc ∧ j = q.succ)

/-- `G_φ ∪ {R_{q,q+1} : q ∈ T}` is connected. -/
def Connects {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  (graphOf φ ⊔ adjArcs T).Connected

/-- A spanning tree of `G_φ` made of arcs `R_{q,q+1}`, pp. 660 and 662: a set of such arcs that
connects `G_φ`, no proper subset of which connects it. -/
def IsAdjSpanningTree {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  Connects φ T ∧ ∀ T' ⊂ T, ¬ Connects φ T'

/-- The bottleneck arc cost, p. 670: the arc `R_{q,q+1}` has cost `c_{q φ(q+1)}`. -/
noncomputable def arcCost {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (φ : Equiv.Perm (Fin (n + 1))) (q : Fin n) : ℝ :=
  GilmoreGomoryTSP.MinCost.c f g A B q.castSucc (φ q.succ)

/-- A minimum spanning tree of `G_φ` with the costs `c_{q φ(q+1)}`, p. 670: an adjacent-arc
spanning tree whose total cost is at most that of every adjacent-arc spanning tree. -/
def IsMinSpanningTree {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsAdjSpanningTree φ T ∧
    ∀ T', IsAdjSpanningTree φ T' → ∑ q ∈ T, arcCost f g A B φ q ≤ ∑ q ∈ T', arcCost f g A B φ q

/-- The tour `ψ′ = φ α_{j_1 j_1+1} ⋯ α_{j_m j_m+1}`, p. 670, with `j_1 < ⋯ < j_m` the arcs of `T`
in increasing order: the interchanges are applied to `φ` one after another, lowest index first. -/
def psiPrime {n : ℕ} (φ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  ((List.finRange n).filter (fun q => q ∈ T)).foldl
    (fun ψ q => interchange ψ q.castSucc q.succ) φ

/-- Condition (22a), p. 666: `i ≤ q < φ⁻¹ψ(i)`. -/
def Cond22a {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (i : Fin (n + 1)) : Prop :=
  (i : ℕ) ≤ q ∧ (q : ℕ) < (φ.symm (ψ i) : ℕ)

/-- Condition (22b), p. 666: `φ⁻¹ψ(j) ≤ q < j`. -/
def Cond22b {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (j : Fin (n + 1)) : Prop :=
  (φ.symm (ψ j) : ℕ) ≤ q ∧ (q : ℕ) < j

/-- The arcs `R_{q,q+1}` added to `G_φ` to form `G_ψ*`, p. 668: those `q` for which (22a) holds
for some `i` or (22b) holds for some `j`. -/
noncomputable def starArcs {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun q => (∃ i, Cond22a φ ψ q i) ∨ ∃ j, Cond22b φ ψ q j)

/-- The graph `G_ψ*`, p. 668: all arcs `R_{q φ(q)}` of `G_φ` and the arcs `R_{q,q+1}` of
`starArcs φ ψ`. -/
noncomputable def Gstar {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  graphOf φ ⊔ adjArcs (starArcs φ ψ)

/-- The undirected graph `G′_φ` of Theorem 6, p. 671, for a directed graph given by its
out-neighbourhoods `Γ i`: an arc `R_{q φ(q)}` iff `φ(q) ∈ Γ_q`, and an arc `R_{q,q+1}` iff
`φ(q+1) ∈ Γ_q`. -/
def Gprime {n : ℕ} (Γ : Fin (n + 1) → Finset (Fin (n + 1))) (φ : Equiv.Perm (Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j =>
    (j = φ i ∧ φ i ∈ Γ i) ∨ ∃ q : Fin n, i = q.castSucc ∧ j = q.succ ∧ φ q.succ ∈ Γ q.castSucc)

end GilmoreGomoryTSP.Bottleneck


