-- Prove2me | Definitions.Def_LPCommunity_LPRecovery_Setting
-- name    : LPCommunity_LPRecovery_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:59.393359+00:00
-- url     : https://prove2.me/theorems/ce1eb505-0b9f-4207-8ff0-f638765cd8a8
-- title:
--   §3, pp. 6–7 — the cut vector, the metric relaxation (LP-P) with constraints (1)–(3), and LP recovery of the planted bisection
-- statement:
--   Let $G=(V,E)$ be a simple graph on the vertex set $V=\{1,\dots,n\}$; an edge is written $(i,j)$ with $i<j$, and $a_{ij}=1$ if $(i,j)\in E$, $a_{ij}=0$ otherwise. Let $V_1,V_2$ be a bisection of $V$ (two sets of size $n/2$), as in §2.
--
--   1. **Cut vector.** The cut vector $\bar x\in\{0,1\}^{\binom n2}$ of the partition $V_1,V_2$ has $\bar x_{ij}=0$ if $i,j$ lie in the same set and $\bar x_{ij}=1$ otherwise. Throughout, $x_{ji}:=x_{ij}$.
--   2. **The metric relaxation (LP-P)** of the minimum bisection problem is
--   $$\min_x \sum_{1\le i<j\le n} a_{ij}x_{ij}\quad\text{s.t.}\quad \begin{cases} x_{ij}\le x_{ik}+x_{jk} & \text{for distinct } i,j,k\in[n],\ i<j, \quad (1)\\ x_{ij}+x_{ik}+x_{jk}\le 2 & \text{for } 1\le i<j<k\le n, \quad (2)\\ \sum_{1\le i<j\le n}x_{ij}=n^2/4. & (3)\end{cases}$$
--   3. **Optimality and recovery.** A feasible $x$ is *optimal* if no feasible point has a smaller objective value. (LP-P) *recovers the planted bisection* $V_1,V_2$ if the cut vector $\bar x$ is optimal and is the only optimal solution.
--
--   These objects are the vocabulary of the paper's sufficient and necessary conditions for LP recovery (Propositions 1–2, Lemmas 2–3, Theorems 4 and 5) and of its probabilistic analysis under the stochastic block model (Theorems 6–8).
--
--   **Formalization Note** Vertices are `Fin n` (0-based). Bisections and the predicate "same side" are those of the companion definition of §2 (`LPCommunity.MinBisect`), which this file imports. A point of $\mathbb R^{\binom n2}$ is encoded as an array $x:V\times V\to\mathbb R$ that is symmetric with zero diagonal; these two conditions are part of feasibility, so uniqueness of the optimum is uniqueness of the point of $\mathbb R^{\binom n2}$. No box constraints $0\le x\le 1$ are added: the LP is exactly (1)–(3). The right-hand side $n^2/4$ of (3) is real division.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 6–7, §3 (cut vector, a_ij, (LP-P), (1)–(3)); p. 4, §2 (recovery: "its unique optimal solution corresponds to the planted bisection")

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

/-! §3 of Del Pia, Khajavirad, Kunisky, *Linear Programming and Community Detection*
(arXiv:2006.03213v2): the cut vector, the metric relaxation (LP-P) with constraints (1)–(3)
(pp. 6–7), and LP recovery. Bisections, `sameSide` and the degrees inside and across the planted
bisection (§2, pp. 3–4) come from `LPCommunity.MinBisect`. Vertices are `Fin n` (the paper's
{1,…,n}, shifted to 0-based). -/

/-- The cut vector of the partition `V1, V1ᶜ` (p. 6): `x_ij = 0` on the same side, `1` across. -/
noncomputable def cutVec {n : ℕ} (V1 : Finset (Fin n)) : Fin n → Fin n → ℝ :=
  fun i j => if LPCommunity.MinBisect.sameSide V1 i j then 0 else 1

/-- Feasibility for (LP-P) (p. 7). A point of `ℝ^(n choose 2)` is encoded as a symmetric array with
zero diagonal (`x_ji := x_ij`, p. 6). Constraints:
(1) `x_ij ≤ x_ik + x_jk` for distinct `i, j, k` with `i < j`;
(2) `x_ij + x_ik + x_jk ≤ 2` for `i < j < k`;
(3) `∑_{i<j} x_ij = n²/4`. -/
def LPFeasible (n : ℕ) (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧
  (∀ i j k, i < j → k ≠ i → k ≠ j → x i j ≤ x i k + x j k) ∧
  (∀ i j k, i < j → j < k → x i j + x i k + x j k ≤ 2) ∧
  (∑ i, ∑ j, if i < j then x i j else 0) = (n : ℝ) ^ 2 / 4

/-- The objective of (LP-P): `∑_{i<j} a_ij x_ij`, with `a_ij = 1` iff `(i, j) ∈ E`. -/
noncomputable def lpObj {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j ∧ G.Adj i j then x i j else 0

/-- `x` is an optimal solution of (LP-P). -/
def LPOptimal {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Fin n → ℝ) : Prop :=
  LPFeasible n x ∧ ∀ y, LPFeasible n y → lpObj G x ≤ lpObj G y

/-- (LP-P) recovers the planted bisection `V1`: its unique optimal solution is the cut vector of `V1`. -/
def LPRecovers {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) : Prop :=
  LPOptimal G (cutVec V1) ∧ ∀ y, LPOptimal G y → y = cutVec V1

end LPCommunity.LPRecovery


