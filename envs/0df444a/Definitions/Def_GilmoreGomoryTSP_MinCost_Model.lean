-- Prove2me | Definitions.Def_GilmoreGomoryTSP_MinCost_Model
-- name    : GilmoreGomoryTSP_MinCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:25:54.60087+00:00
-- url     : https://prove2.me/theorems/5831c4a9-b252-4e56-b328-1db3aa7b38c0
-- title:
--   pp. 655–665 — changeover costs (1), permutation cost (3), tours (4), interchanges (5)–(7), the graph G_ψ, spanning trees, node types and the tour ψ*
-- statement:
--   This file sets up the model of Gilmore and Gomory's one state-variable machine and the objects of Sections 2–5 of their paper.
--
--   **Jobs and costs.** There are $N = n+1$ jobs $J_1,\dots,J_N$ (indexed by $\{0,\dots,n\}$ in Lean). Job $i$ must be started when the state of the machine is $A_i$ and leaves the machine in state $B_i$. Changing the state upward costs $f(x)$ per unit, downward $g(x)$ per unit, so the cost of having job $j$ follow job $i$ is (1)
--   $$c_{ij} = \begin{cases} \int_{B_i}^{A_j} f(x)\,dx & \text{if } A_j \ge B_i,\\[2pt] \int_{A_j}^{B_i} g(x)\,dx & \text{if } B_i > A_j.\end{cases}$$
--   A permutation $\psi$ of the jobs, with $\psi(i)$ the job that follows job $i$, has total cost (3)
--   $$c(\psi) = \sum_{i=1}^{N} c_{i\psi(i)},$$
--   and is a **tour** if (4) $\psi(s) \ne s$ for every nonempty proper subset $s$ of the jobs, i.e. if it is a single cycle through all jobs.
--
--   **Ranking.** A permutation $\varphi$ **ranks the $A$** if $j > i$ implies $A_{\varphi(j)} \ge A_{\varphi(i)}$.
--
--   **Interchanges.** The interchange $\alpha_{ij}$ (5) exchanges $i$ and $j$ and fixes every other job. Applying it to $\psi$ gives $\bar\psi = \psi\alpha_{ij}$ (6): first apply $\alpha_{ij}$, then $\psi$, so $\bar\psi(i) = \psi(j)$ and $\bar\psi(j) = \psi(i)$ (7). Its cost is $c_\psi(\alpha_{ij}) = c(\psi\alpha_{ij}) - c(\psi)$.
--
--   **Graphs and trees.** $G_\psi$ is the undirected graph on the $N$ jobs with an arc linking $i$ and $\psi(i)$ for every $i$. For a set $E$ of additional arcs $R_{ij}$, $E$ is a **spanning tree** of $G_\psi$ if $G_\psi \cup E$ is connected and no proper subset of $E$ connects it (a minimal set of additional arcs that connect $G_\psi$). Its cost is $c_\psi(E) = \sum_{R_{ij}\in E} c_\psi(\alpha_{ij})$. An **adjacent-arc tree** is a spanning tree made only of arcs $R_{q,q+1}$; it is recorded as the set $T$ of the lower indices $q$, with cost $c_\psi(T)=\sum_{q\in T}c_\psi(\alpha_{q,q+1})$. A **minimal cost** adjacent-arc tree has cost at most that of every adjacent-arc tree.
--
--   **Node types and $\psi^*$.** Node $i$ is of **type 1** relative to $\psi$ if $B_i \le A_{\psi(i)}$, otherwise of type 2; the interchange $\alpha_{q,q+1}$ has the type of its lower node $q$. For a set $T$ of adjacent arcs, $\psi^*$ is obtained from $\varphi$ by executing first the type-1 interchanges of $T$ (types relative to $\varphi$) in decreasing order of index and then the type-2 interchanges in increasing order of index:
--   $$\psi^* = \varphi\,\alpha_{i_1,i_1+1}\cdots\alpha_{i_l,i_l+1}\,\alpha_{j_1,j_1+1}\cdots\alpha_{j_m,j_m+1},\qquad i_1>\dots>i_l,\quad j_1<\dots<j_m.$$
--
--   These objects carry the paper's solution of this special traveling salesman problem: $\psi^*$ built from a minimal cost tree is a minimal cost tour.
--
--   **Formalization Note** Jobs are `Fin (n + 1)`, so the paper's job $i$ is index $i-1$, and the arc $R_{q,q+1}$ is indexed by `q : Fin n` and joins `q.castSucc` and `q.succ`. The product `ψ * alpha i j` is Mathlib's composition $\psi\circ\alpha_{ij}$, which is the paper's $\psi\alpha_{ij}$. Integrals are oriented interval integrals; integrability hypotheses are placed on the theorems. "Proper subset" in (4) is read as nonempty proper subset, since $\psi(\emptyset)=\emptyset$ always. Loops $\psi(i)=i$ add no arc to $G_\psi$, which does not affect connectivity. The execution order in $\psi^*$ is the one of the proof of Lemma 5 (p. 664) and of steps T2–T4 (p. 673); the order printed in Theorem 3 (type 1 increasing, then type 2 decreasing) is a misprint, see the goal theorem.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), pp. 655–665, Eqs. (1), (3)–(7), Sections "Interchanges and their costs", "Tours and trees", "Tree costs and a special property of the minimal tree", "Tree costs and tour costs"; steps T1–T4, p. 673

import Mathlib

namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

/-- The changeover cost (1) of having job `j` follow job `i`: with `N = n + 1` jobs indexed by
`Fin (n + 1)`, job `i` starts in state `A i` and ends in state `B i`;
`c_ij = ∫_{B_i}^{A_j} f` if `A_j ≥ B_i` and `c_ij = ∫_{A_j}^{B_i} g` if `B_i > A_j`. -/
noncomputable def c (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : ℝ :=
  if B i ≤ A j then ∫ x in B i..A j, f x else ∫ x in A j..B i, g x

/-- The total changeover cost (3) of a permutation `ψ`, where `ψ i` is the job following job `i`:
`c(ψ) = ∑_i c_{i ψ(i)}`. -/
noncomputable def cost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∑ i, c f g A B i (ψ i)

/-- Condition (4): `ψ` is a tour if `ψ(s) ≠ s` for every nonempty proper subset `s` of the jobs. -/
def IsTour (ψ : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∀ s : Finset (Fin (n + 1)), s.Nonempty → s ≠ Finset.univ → s.map ψ.toEmbedding ≠ s

/-- `φ` ranks the `A`: `j > i` implies `A_{φ(j)} ≥ A_{φ(i)}` (Theorem 1, step P3). -/
def RanksA (A : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1))) : Prop :=
  Monotone (A ∘ φ)

/-- The interchange `α_ij` (5): it exchanges `i` and `j` and fixes every other job. Applying it to
`ψ` gives `ψ α_ij` (6), "first apply `α_ij`, then `ψ`", i.e. the product `ψ * alpha i j`. -/
def alpha (i j : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i j

/-- The cost of applying the interchange `α_ij` to `ψ`: `c_ψ(α_ij) = c(ψ α_ij) − c(ψ)` (p. 658). -/
noncomputable def interchangeCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1)) : ℝ :=
  cost f g A B (ψ * alpha i j) - cost f g A B ψ

/-- The graph `G_ψ` (p. 660): `N` nodes and an undirected arc linking the `i`th and `ψ(i)`th
nodes (loops `ψ(i) = i` are omitted, which does not affect connectivity). -/
def graph (ψ : Equiv.Perm (Fin (n + 1))) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun i j => ψ i = j

/-- `G_ψ` together with the additional undirected arcs `R_ij`, `(i, j) ∈ E`. -/
def graphWith (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  graph ψ ⊔ SimpleGraph.fromRel fun i j => (i, j) ∈ E

/-- A spanning tree of `G_ψ` (p. 660): "a minimal set of additional arcs that connect a graph
`G_ψ`", minimal under inclusion: `G_ψ ∪ E` is connected and no proper subset of `E` connects. -/
def IsSpanningTree (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) :
    Prop :=
  (graphWith ψ E).Connected ∧ ∀ E' ⊂ E, ¬ (graphWith ψ E').Connected

/-- The cost of a set of arcs `E` relative to `ψ`: `c_ψ(τ) = ∑ {c_ψ(α_ij) | R_ij ∈ τ}` (p. 662). -/
noncomputable def arcSetCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (E : Finset (Fin (n + 1) × Fin (n + 1))) : ℝ :=
  ∑ e ∈ E, interchangeCost f g A B ψ e.1 e.2

/-- The adjacent arc `R_{q,q+1}`, indexed by `q : Fin n`: it joins the jobs `q.castSucc` and
`q.succ` (the paper's jobs `q` and `q + 1`, 1-based). -/
def adjArc (q : Fin n) : Fin (n + 1) × Fin (n + 1) :=
  (q.castSucc, q.succ)

/-- The set of arcs `{R_{q,q+1} | q ∈ T}`. -/
def adjArcs (T : Finset (Fin n)) : Finset (Fin (n + 1) × Fin (n + 1)) :=
  T.image adjArc

/-- `T` is a spanning tree of `G_ψ` consisting only of adjacent arcs `R_{q,q+1}`. -/
def IsAdjTree (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsSpanningTree ψ (adjArcs T)

/-- The cost `c_ψ(T) = ∑_{q ∈ T} c_ψ(α_{q,q+1})` of a set of adjacent arcs. -/
noncomputable def adjTreeCost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : ℝ :=
  ∑ q ∈ T, interchangeCost f g A B ψ q.castSucc q.succ

/-- `T` is a minimal cost spanning tree of `G_ψ` among the spanning trees made of adjacent arcs
(what steps S1–S3 compute; by Lemma 2 its cost is also minimal among all spanning trees). -/
def IsMinCostAdjTree (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (T : Finset (Fin n)) : Prop :=
  IsAdjTree ψ T ∧ ∀ T' : Finset (Fin n), IsAdjTree ψ T' →
    adjTreeCost f g A B ψ T ≤ adjTreeCost f g A B ψ T'

/-- Node `i` is of type 1 relative to `ψ` if `B_i ≤ A_{ψ(i)}`, otherwise of type 2 (p. 663). -/
def IsType1 (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : Prop :=
  B i ≤ A (ψ i)

/-- Execute the adjacent interchanges `α_{q,q+1}` listed in `l` on `ψ`, first to last:
`ψ α_{l_1,l_1+1} α_{l_2,l_2+1} ⋯`. -/
def applyAdj (ψ : Equiv.Perm (Fin (n + 1))) (l : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  l.foldl (fun σ q => σ * alpha q.castSucc q.succ) ψ

/-- The execution order of Lemma 5 (p. 664) and steps T2–T4 (p. 673) for a set `T` of adjacent
arcs: first the type 1 interchanges (lower node of type 1 relative to `φ`) in decreasing order of
index, then the type 2 interchanges in increasing order of index. The filter conditions are
`IsType1 A B φ q.castSucc` and its negation, written out. -/
noncomputable def execOrder (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (T : Finset (Fin n)) : List (Fin n) :=
  ((T.filter fun q => B q.castSucc ≤ A (φ q.castSucc)).sort (· ≤ ·)).reverse ++
    (T.filter fun q => ¬ B q.castSucc ≤ A (φ q.castSucc)).sort (· ≤ ·)

/-- The tour `ψ* = φ α_{i_1,i_1+1} ⋯ α_{i_l,i_l+1} α_{j_1,j_1+1} ⋯ α_{j_m,j_m+1}` (T4, p. 673):
the interchanges of `T` executed on `φ` in the order `execOrder`. -/
noncomputable def psiStar (A B : Fin (n + 1) → ℝ) (φ : Equiv.Perm (Fin (n + 1)))
    (T : Finset (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  applyAdj φ (execOrder A B φ T)

end GilmoreGomoryTSP.MinCost


