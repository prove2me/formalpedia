-- Prove2me | Definitions.Def_SkutellaCQP_NoRel_Setting
-- name    : SkutellaCQP_NoRel_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:28.379182+00:00
-- url     : https://prove2.me/theorems/dece442c-5cb8-4510-b9e6-6b1211f16465
-- title:
--   §2, pp. 7–14 — unrelated machines, Smith orders ≺ᵢ, assignments, (IQP)/(QP), (CQP), (CQP′), randomized rounding
-- statement:
--   This file fixes the objects of §2 of Skutella's paper: scheduling $n$ jobs on $m$ unrelated parallel machines without release dates so as to minimize the total weighted completion time, the problem $R\,|\,|\sum w_jC_j$, together with its quadratic programming relaxations.
--
--   **Instance** (p. 2). Jobs are $j\in J=\{1,\dots,n\}$ and machines $i\in\{1,\dots,m\}$. Job $j$ has a weight $w_j\ge 0$ and a processing time $p_{ij}>0$ on machine $i$.
--
--   **Smith's order** (p. 7). For each machine $i$, $j\prec_i k$ if $w_j/p_{ij}>w_k/p_{ik}$, or $w_j/p_{ij}=w_k/p_{ik}$ and $j<k$. This is a strict total order on $J$.
--
--   **Schedules** (pp. 7–8). An assignment $\sigma:J\to\{1,\dots,m\}$ sends each job to one machine, and each machine processes its jobs without idle time in the order $\prec_i$ (Smith's ratio rule). The completion time of $j$ is
--   $$
--   C_j(\sigma)=p_{\sigma(j)j}+\sum_{k\prec_{\sigma(j)}j,\ \sigma(k)=\sigma(j)}p_{\sigma(j)k},
--   $$
--   which is (2) evaluated at the $0/1$ vector $a_{ij}=[\sigma(j)=i]$, and the value of $\sigma$ is $\sum_j w_jC_j(\sigma)$, the objective of (IQP).
--
--   **The programs** (pp. 10–13). For $a\in\mathbb R^{mn}$ let $c_{ij}=w_jp_{ij}$ and let $D$ be the symmetric $mn\times mn$ matrix
--   $$
--   d_{(ij)(hk)}=\begin{cases}0 & i\ne h\text{ or } j=k,\\ w_jp_{ik} & i=h,\ k\prec_i j,\\ w_kp_{ij} & i=h,\ j\prec_i k.\end{cases}
--   $$
--   The constraints (5)–(6) are $\sum_{i}a_{ij}=1$ for every $j$ and $a\ge 0$. The objectives are
--   $$
--   Z_{QP}(a)=c^Ta+\tfrac12a^TDa\quad(4),\qquad Z_{CQP}(a)=\tfrac12c^Ta+\tfrac12a^T(D+\operatorname{diag}(c))a .
--   $$
--   A pair $(a,Z)$ is feasible for (CQP′) when $a$ satisfies (5)–(6) and $Z\ge Z_{CQP}(a)$ (12) and $Z\ge c^Ta$ (13).
--
--   **Randomized rounding** (p. 8). Algorithm RANDOMIZED ROUNDING assigns each job $j$ to machine $i$ with probability $a_{ij}$, the random choices being pairwise independent for the jobs. It is encoded as a probability weight $\mu$ on assignments: $\mu\ge 0$, $\sum_\sigma\mu(\sigma)=1$, $\Pr_\mu[\sigma(j)=i]=a_{ij}$, and $\Pr_\mu[\sigma(j)=i,\ \sigma(k)=h]=a_{ij}a_{hk}$ for $j\ne k$. The expectation of $f$ is $\mathbb E_\mu[f]=\sum_\sigma\mu(\sigma)f(\sigma)$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Jobs and machines are 0-based (`Fin n`, `Fin m`); the tie-break $j<k$ is the order of `Fin n`. $\prec_i$ is cross-multiplied ($w_jp_{ik}>w_kp_{ij}$, or equality and $j<k$), which equals the page's ratio definition because $p>0$. Vectors in $\mathbb R^{mn}$ are functions on `Fin m × Fin n`; the page's lexicographic ordering of the variables only fixes a block layout and is not needed. The optimum $Z^*$ is never a primitive: by Smith's rule (p. 7) the scheduling problem is the minimum of the value over assignments, and statements "within a factor $\alpha$ of the optimum" are written as bounds against the value of every assignment. Rounding is a weight on the finite set of assignments, not a measure; pairwise independence is required, full independence is not. The positivity of $p$ and nonnegativity of $w$ are hypotheses of each theorem, not part of these definitions.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 2 (standing assumptions), p. 7 (≺ᵢ), p. 8 ((1)–(3), (QP), randomized rounding), p. 10 ((4)–(6), c, D), p. 11 ((CQP)), p. 13 ((CQP′), (12)–(13))

import Mathlib

namespace SkutellaCQP.NoRel

open Finset Matrix

variable {m n : ℕ}

/-- Smith's order `≺_i` on machine `i` (p. 7): `j ≺_i k` iff `w_j/p_ij > w_k/p_ik`, or the ratios
are equal and `j < k`. Cross-multiplied; equal to the page's definition when `p > 0`. -/
def prec (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (j k : Fin n) : Prop :=
  w j * p i k > w k * p i j ∨ (w j * p i k = w k * p i j ∧ j < k)

noncomputable instance (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin m) (j k : Fin n) :
    Decidable (prec p w i j k) := by
  unfold prec; infer_instance

/-- Completion time of job `j` when every job `k` is assigned to machine `σ k` and each machine
sequences its jobs by `≺_i` (Smith's ratio rule, p. 7): its own processing time plus the
processing times of the jobs `k ≺_{σ j} j` on the same machine. This is (2) at the 0/1 vector of
`σ`. -/
noncomputable def compl (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (σ : Fin n → Fin m) (j : Fin n) :
    ℝ :=
  p (σ j) j + ∑ k ∈ univ.filter (fun k => prec p w (σ j) k j ∧ σ k = σ j), p (σ j) k

/-- The objective `∑_j w_j C_j` of (IQP) for the assignment `σ`. -/
noncomputable def val (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∑ j, w j * compl p w σ j

/-- The vector `c ∈ ℝ^{mn}`, `c_ij = w_j p_ij` (p. 10). -/
def cvec (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) : Fin m × Fin n → ℝ :=
  fun x => w x.2 * p x.1 x.2

/-- The symmetric `mn × mn` matrix `D` of p. 10:
`d_{(ij)(hk)} = 0` if `i ≠ h` or `j = k`; `w_j p_ik` if `i = h` and `k ≺_i j`;
`w_k p_ij` if `i = h` and `j ≺_i k`. -/
noncomputable def Dmat (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  fun x y =>
    if x.1 ≠ y.1 ∨ x.2 = y.2 then 0
    else if prec p w x.1 y.2 x.2 then w x.2 * p x.1 y.2
    else if prec p w x.1 x.2 y.2 then w y.2 * p x.1 x.2
    else 0

/-- The vector `a ∈ ℝ^{mn}` of the variables `a_ij`. -/
def vec (a : Fin m → Fin n → ℝ) : Fin m × Fin n → ℝ :=
  fun x => a x.1 x.2

/-- The 0/1 vector of an assignment `σ`: `a_ij = 1` iff job `j` is assigned to machine `i`. -/
def ind (σ : Fin n → Fin m) : Fin m → Fin n → ℝ :=
  fun i j => if σ j = i then 1 else 0

/-- The objective (4) of (QP): `c^T a + ½ a^T D a`. -/
noncomputable def ZQP (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin m → Fin n → ℝ) : ℝ :=
  cvec p w ⬝ᵥ vec a + (1 / 2) * (vec a ⬝ᵥ (Dmat p w *ᵥ vec a))

/-- The objective of (CQP) (p. 11): `½ c^T a + ½ a^T (D + diag(c)) a`. -/
noncomputable def ZCQP (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin m → Fin n → ℝ) : ℝ :=
  (1 / 2) * (cvec p w ⬝ᵥ vec a) +
    (1 / 2) * (vec a ⬝ᵥ ((Dmat p w + Matrix.diagonal (cvec p w)) *ᵥ vec a))

/-- Constraints (5)–(6) (equivalently (1) with `a ≥ 0`): `∑_i a_ij = 1` for every job and `a ≥ 0`.
These are the feasible solutions of (QP) and of (CQP). -/
def Feasible (a : Fin m → Fin n → ℝ) : Prop :=
  (∀ j, ∑ i, a i j = 1) ∧ ∀ i j, 0 ≤ a i j

/-- `(a, Z)` is feasible for (CQP′) (p. 13): `a` satisfies (5)–(6), and (12) `Z ≥ Z_CQP(a)`,
(13) `Z ≥ c^T a`. -/
def CQP'Feasible (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (a : Fin m → Fin n → ℝ) (Z : ℝ) : Prop :=
  Feasible a ∧ ZCQP p w a ≤ Z ∧ cvec p w ⬝ᵥ vec a ≤ Z

/-- Algorithm RANDOMIZED ROUNDING (p. 8) as a probability weight `μ` on assignments: job `j` goes to
machine `i` with probability `a_ij`, and the choices are pairwise independent for the jobs. -/
def IsPairwiseRounding (a : Fin m → Fin n → ℝ) (μ : (Fin n → Fin m) → ℝ) : Prop :=
  (∀ σ, 0 ≤ μ σ) ∧ (∑ σ, μ σ = 1) ∧
  (∀ j i, ∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i), μ σ = a i j) ∧
  (∀ j k, j ≠ k → ∀ i h,
    ∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i ∧ σ k = h), μ σ = a i j * a h k)

/-- Expectation of `f` under the probability weight `μ`: `∑_σ μ(σ) f(σ)`. -/
noncomputable def E (μ : (Fin n → Fin m) → ℝ) (f : (Fin n → Fin m) → ℝ) : ℝ :=
  ∑ σ, μ σ * f σ

end SkutellaCQP.NoRel


