-- Prove2me | Definitions.Def_SkutellaCQP_MaxCut_Setting
-- name    : SkutellaCQP_MaxCut_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:31.341301+00:00
-- url     : https://prove2.me/theorems/61f5387a-8bfd-4453-b258-6c1feedd406f
-- title:
--   §2.2 and §6, pp. 7, 12, 30 — identical machines, Smith order ≺, assignments, the graph G_J, c(E_J), m-cuts, (CQP) in form (11)
-- statement:
--   This file fixes the objects of §6 of Skutella's paper, the reduction of scheduling on identical parallel machines to the graph partitioning problem Max-$m$-Cut, together with the convex quadratic relaxation (CQP) of §2.2 specialised to identical machines.
--
--   **Instance** (p. 2). There are $n$ jobs $j\in J=\{1,\dots,n\}$ and $m$ identical parallel machines. Job $j$ has a processing time $p_j>0$, the same on every machine, and a weight $w_j\ge 0$. The objective is the total weighted completion time $\sum_j w_jC_j$ (the problem $P\,|\,|\sum w_jC_j$, or $Pm\,|\,|\sum w_jC_j$ when $m$ is fixed).
--
--   **Smith's order** (p. 7). $j\prec k$ if $w_j/p_j>w_k/p_k$, or $w_j/p_j=w_k/p_k$ and $j<k$. This is a strict total order on $J$.
--
--   **Schedules** (p. 7). An assignment $\sigma:J\to\{1,\dots,m\}$, equivalently a partition of $J$ into $m$ subsets $J_1,\dots,J_m$, sends each job to one machine; each machine processes its jobs without idle time in the order $\prec$ (Smith's ratio rule). The completion time of $j$ is
--   $$
--   C_j(\sigma)=p_j+\sum_{k\prec j,\ \sigma(k)=\sigma(j)}p_k ,
--   $$
--   and the value of $\sigma$ is $\sum_j w_jC_j(\sigma)$.
--
--   **The graph $G_J$** (p. 30). $G_J$ is the complete undirected graph on $J$; the edge $\{j,k\}$ with $k\prec j$ has weight $c(jk)=w_jp_k$. Its total weight is $c(E_J)$. The $m$-cut $E_{\mathrm{cut}}$ induced by $\sigma$ consists of the edges whose endpoints lie in different subsets $J_i$, and $c(E_{\mathrm{cut}})$ is its weight.
--
--   **(CQP) for identical machines** (p. 12, (11)). For $a\in\mathbb R^{m\times n}$ the objective of (CQP) is $\sum_j w_jC_j$ with
--   $$
--   C_j=\sum_{i=1}^m a_{ij}\Big(\frac{1+a_{ij}}{2}\,p_j+\sum_{k\prec j}a_{ik}\,p_k\Big),
--   $$
--   and $a$ is feasible when $\sum_i a_{ij}=1$ for every $j$ and $a\ge 0$ (constraints (5)–(6)). The vector $\bar a$ has $\bar a_{ij}=1/m$ for all $i,j$ (Lemma 2.5).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Jobs and machines are 0-based (`Fin n`, `Fin m`); the tie-break $j<k$ is the order of `Fin n`. $\prec$ is cross-multiplied ($w_jp_k>w_kp_j$, or equality and $j<k$), which equals the page's ratio definition because $p>0$. The edge weight is attached to the ordered pair $(j,k)$ with $k\prec j$ and is $0$ for the other orientation, so a double sum over ordered pairs counts each edge of $G_J$ once. The optimum $Z^*$ is never a primitive: by Smith's rule (p. 7) the scheduling problem is the minimum of the value over assignments, and statements about $Z^*$ or the maximum cut $Z^*_{\mathrm{cut}}$ are written against every assignment. The hypotheses $p>0$, $w\ge 0$, $m>0$ are carried by each theorem, not by these definitions.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 2 (standing assumptions), p. 7 (≺, Smith's rule), p. 12 ((11), Lemma 2.5's ā), p. 30 (G_J, c(jk), E_cut)

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

namespace SkutellaCQP.MaxCut

open Finset

variable {m n : ℕ}

/-- Smith's order `≺` for identical parallel machines (p. 7, with `p_ij = p_j`):
`j ≺ k` iff `w_j/p_j > w_k/p_k`, or the ratios are equal and `j < k`.
Cross-multiplied; equal to the page's definition when `p > 0`. -/
def prec (p w : Fin n → ℝ) (j k : Fin n) : Prop :=
  w j * p k > w k * p j ∨ (w j * p k = w k * p j ∧ j < k)

noncomputable instance (p w : Fin n → ℝ) (j k : Fin n) : Decidable (prec p w j k) := by
  unfold prec; infer_instance

/-- Completion time of job `j` under the assignment `σ : J → {machines}`, each machine sequencing
its jobs by `≺` (Smith's ratio rule, p. 7): `p_j` plus the processing times of the jobs
`k ≺ j` assigned to the same machine. -/
noncomputable def compl (p w : Fin n → ℝ) (σ : Fin n → Fin m) (j : Fin n) : ℝ :=
  p j + ∑ k ∈ univ.filter (fun k => prec p w k j ∧ σ k = σ j), p k

/-- The value `∑_j w_j C_j` of the schedule of the assignment `σ`. -/
noncomputable def val (p w : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∑ j, w j * compl p w σ j

/-- Weight `c(jk) = w_j p_k` of the edge `{j, k}` of the complete graph `G_J` (p. 30), attached
to the ordered pair `(j, k)` with `k ≺ j`, and `0` for the other orientation; each unordered edge
is therefore counted exactly once in a sum over ordered pairs. -/
noncomputable def edgeW (p w : Fin n → ℝ) (j k : Fin n) : ℝ :=
  if prec p w k j then w j * p k else 0

/-- `c(E_J)`, the total edge weight of `G_J`. -/
noncomputable def cE (p w : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ k, edgeW p w j k

/-- `c(E_cut)`, the weight of the `m`-cut induced by the partition `J_1, …, J_m` of `J` given by
`σ`: the edges whose endpoints lie in different parts. -/
noncomputable def cut (p w : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∑ j, ∑ k, if σ j ≠ σ k then edgeW p w j k else 0

/-- The objective of (CQP) for identical parallel machines, in the form (11) (p. 12) with
`p_ij = p_j`: `∑_j w_j C_j` where
`C_j = ∑_i a_ij ((1 + a_ij)/2 · p_j + ∑_{k ≺ j} a_ik p_k)`. -/
noncomputable def ZCQP (p w : Fin n → ℝ) (a : Fin m → Fin n → ℝ) : ℝ :=
  ∑ j, w j * ∑ i, a i j * ((1 + a i j) / 2 * p j +
    ∑ k ∈ univ.filter (fun k => prec p w k j), a i k * p k)

/-- The vector `ā` of Lemma 2.5 (p. 12): `ā_ij = 1/m` for all machines `i` and jobs `j`. -/
noncomputable def abar (m n : ℕ) : Fin m → Fin n → ℝ :=
  fun _ _ => 1 / (m : ℝ)

end SkutellaCQP.MaxCut


