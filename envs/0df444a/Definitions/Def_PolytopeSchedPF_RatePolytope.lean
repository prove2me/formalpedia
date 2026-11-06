-- Prove2me | Definitions.Def_PolytopeSchedPF_RatePolytope
-- name    : PolytopeSchedPF_RatePolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:17:56.111202+00:00
-- url     : https://prove2.me/theorems/7b8bc379-51fc-4fe3-be84-4b94b7cf7912
-- title:
--   Rate polytope $\mathcal P=\{y\in\mathbb R^n_{\ge0} : By\le\mathbf 1\}$, restricted polytopes $\mathcal P_U$ and support function $H_\alpha(U)$
-- statement:
--   In the **Polytope Scheduling Problem (PSP)** there are $n$ jobs $J=[n]$ and $D$ resources. The resource consumption is a nonnegative matrix $B\in\mathbb R^{D\times n}_{\ge0}$ with **no zero column**, and the **rate polytope** is
--   $$
--   \mathcal P=\{\,y\in\mathbb R^n_{\ge0} : By\le\mathbf 1\,\}.
--   $$
--   Because no column of $B$ vanishes, $\mathcal P$ is bounded. For a set of jobs $U\subseteq J$ the **restricted polytope** is $\mathcal P_U=\{y\in\mathcal P : y_j=0\ \forall j\notin U\}$, and for a direction $\alpha\in\mathbb R^n$ the **support function** is
--   $$
--   H_\alpha(U)=\max\{\langle\alpha,y\rangle : y\in\mathcal P_U\},\qquad \langle\alpha,y\rangle=\sum_{j=1}^n\alpha_jy_j .
--   $$
--   The maximum rate of job $j$ is $y^{\max}_j=\max\{y_j : y\in\mathcal P\}$. The module also fixes the total weight $w(U)=\sum_{j\in U}w_j$ of a set of jobs and the vector $y\odot\mathbf 1_U$, which agrees with $y$ on $U$ and is $0$ elsewhere.
--
--   These objects are the instance layer of every statement of the mission: schedules choose their rate vectors in $\mathcal P$, and support submodularity is a property of $U\mapsto H_\alpha(U)$.
--
--   **Formalization Note** Jobs are `Fin n`, resources `Fin D`. The matrix and its two hypotheses (nonnegativity, no zero column) are bundled in the structure `RatePolytope n D`. $H_\alpha(U)$ and $y^{\max}_j$ are written as `sSup` of nonempty bounded sets of reals, so they are the paper's maxima. $\langle\alpha,y\rangle$ is `dot`, $w(U)$ is `wsum`, and $y\odot\mathbf 1_U$ is `mask`.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §3.1, p.12 (PDF p.14), P = {y ∈ ℝⁿ≥0 | By ≤ 1}, no zero column; p.13 (PDF p.15), y^max, w(J'), y ⊙ 1_J'; §4.1, p.16 (PDF p.18), P_U, H_α

import Mathlib

namespace PolytopeSchedPF

/-- **Rate polytope of a PSP instance** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §3.1,
p.12): a nonnegative matrix `B ∈ ℝ^{D×n}_{≥0}` with no zero column. The rate polytope is
`P = {y ∈ ℝⁿ_{≥0} | By ≤ 1}`; jobs are `Fin n` and resources `Fin D`.

**Formalization Note** The instance is the paper's B-form (reading R1); the no-zero-column
condition, which makes `P` bounded, is part of the structure, so every item carries it. -/
structure RatePolytope (n D : ℕ) where
  /-- The resource-consumption matrix `B`. -/
  B : Matrix (Fin D) (Fin n) ℝ
  /-- `B` is nonnegative. -/
  nonneg : ∀ d j, 0 ≤ B d j
  /-- `B` has no zero column. -/
  noZeroCol : ∀ j, ∃ d, B d j ≠ 0

namespace RatePolytope

variable {n D : ℕ}

/-- The rate polytope `P = {y ∈ ℝⁿ | y ≥ 0, By ≤ 1}` (p.12). -/
def rates (P : RatePolytope n D) : Set (Fin n → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ ∀ d, ∑ j, P.B d j * y j ≤ 1}

/-- The restricted polytope `P_U = {y ∈ P | y_j = 0 for all j ∉ U}` (§4.1, p.16). -/
def restricted (P : RatePolytope n D) (U : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {y | y ∈ P.rates ∧ ∀ j, j ∉ U → y j = 0}

/-- The support function `H_α(U) = max{⟨α, y⟩ | y ∈ P_U}` (§4.1, p.16; Definition 1.1, p.2).

**Formalization Note** Written as `sSup` of the image of `P_U` under `y ↦ ⟨α, y⟩`. The image is
nonempty (`0 ∈ P_U`) and bounded (no zero column makes `P` bounded), so this is the paper's
maximum. -/
noncomputable def H (P : RatePolytope n D) (α : Fin n → ℝ) (U : Finset (Fin n)) : ℝ :=
  sSup ((fun y : Fin n → ℝ => ∑ j, α j * y j) '' P.restricted U)

/-- The maximum rate `y^max_j = max{y_j | y ∈ P}` of job `j` (p.13), as `sSup` of a nonempty
bounded set. -/
noncomputable def yMax (P : RatePolytope n D) (j : Fin n) : ℝ :=
  sSup ((fun y : Fin n → ℝ => y j) '' P.rates)

end RatePolytope

/-- The total weight `w(U) = ∑_{j ∈ U} w_j` of a set of jobs (p.13). -/
def wsum {n : ℕ} (w : Fin n → ℝ) (U : Finset (Fin n)) : ℝ := ∑ j ∈ U, w j

/-- The inner product `⟨α, y⟩ = ∑_j α_j y_j` (§4.1, p.16). -/
def dot {n : ℕ} (α y : Fin n → ℝ) : ℝ := ∑ j, α j * y j

/-- The coordinate-wise product `y ⊙ 1_U`, which agrees with `y` on `U` and is `0` elsewhere
(p.13). -/
def mask {n : ℕ} (y : Fin n → ℝ) (U : Finset (Fin n)) : Fin n → ℝ :=
  fun j => if j ∈ U then y j else 0

end PolytopeSchedPF


