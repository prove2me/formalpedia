-- Prove2me | Definitions.Def_SymPolyOpt_PowerSumUB_Setting
-- name    : SymPolyOpt_PowerSumUB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:58.218987+00:00
-- url     : https://prove2.me/theorems/e15e315c-b6d6-48cc-aca7-61632cfd3af3
-- title:
--   (6.4), (6.7), pp. 26–27 — power sums, the problem P_nmq, Hankel matrices, Newton sums and the one-variable SDP value U_nmq
-- statement:
--   This file fixes the objects of §6.2 of Riener, Theobald, Jansson Andrén and Lasserre. Items 1–3 (power sums, problem (6.4), Hankel matrices) are the shared definitions it imports; items 4–5 are defined here.
--
--   1. **Power sums.** For $x \in \mathbb{R}^n$ and $j \in \mathbb{N}$, $s_j(x) = \sum_{i=1}^n x_i^j$; in particular $s_0(x) = n$.
--   2. **Problem (6.4).** Given $m \in \mathbb{N}$ and real numbers $\gamma_1, \dots, \gamma_{m-1}$, the feasible set of $\mathrm{P}_{nmq}$ is
--   $$F_{nm}(\gamma) = \Big\{ x \in \mathbb{R}^n : \sum_{i=1}^n x_i^j = \gamma_j,\ j = 1, \dots, m-1 \Big\},$$
--   and its optimal value is $\min \mathrm{P}_{nmq} = \inf_{x \in F_{nm}(\gamma)} \sum_{i=1}^n x_i^q$, taken in the extended reals $[-\infty, +\infty]$ (it is $+\infty$ when $F_{nm}(\gamma)$ is empty and may be $-\infty$).
--   3. **Hankel matrices.** For a sequence $s = (s_0, s_1, \dots)$ of reals, $H_k(s) = (s_{i+j-2})_{1 \le i, j \le k}$, the $k \times k$ matrix built from $s_0, \dots, s_{2k-2}$.
--   4. **Newton sums.** For a real polynomial $p$, $s_k(p) = \sum_{z} z^k$, the sum over the complex roots $z$ of $p$ counted with multiplicity. For $p$ of degree $m$, $s_0(p) = m$.
--   5. **The SDP (6.7).** Its feasible set is the set of monic real polynomials $p = X^m + \sum_{j=0}^{m-1} p_j X^j$ of degree $m$ whose Newton sums satisfy $s_j(p) = \gamma_j$ for $j = 1, \dots, m-1$ and whose Hankel matrix $H_m(s(p))$ (with $s_0 = m$) is positive semidefinite. Its value is
--   $$\mathrm{U}_{nmq} = \inf \{ s_q(p) : p \text{ feasible} \} \in [-\infty, +\infty].$$
--
--   By Newton's identities a monic $p$ of degree $m$ with prescribed $s_1, \dots, s_{m-1}$ is determined by its constant coefficient $p_0$, and every $p_0 \in \mathbb{R}$ occurs; its Newton sums $s_j(p)$, $j \ge m$, are the paper's $Q_j(p_0)$. So this feasible set is the feasible set of (6.7) in the coordinates $p \leftrightarrow p_0$, and $\mathrm{U}_{nmq}$ is the paper's value of (6.7). The entries $s_m, \dots, s_{2m-2}$ of $H_m$ are **not** free variables, as they are in the relaxation (6.6).
--
--   **Formalization Note** Values are infima in `EReal`, so an infeasible problem has value $+\infty$ rather than a junk $0$. The Newton sum is the real part of the complex sum $\sum_z z^k$, which is real for a real polynomial because non-real roots come in conjugate pairs. The Hankel matrix is indexed from $0$: entry $(i, j)$, $0 \le i, j < k$, is $s_{i+j}$, which is the paper's $(s_{i+j-2})_{1 \le i,j \le k}$. The data $\gamma$ is a sequence $\mathbb{N} \to \mathbb{R}$ of which only $\gamma_1, \dots, \gamma_{m-1}$ are read. The same power-sum problem and Hankel matrix are also defined, with the same encoding, in the companion mission on the lower bound (Theorem 6.6).
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, pp. 26-27, (6.4), Hankel matrix H_n(s), the monic polynomial p and its Newton sums, (6.7)

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

namespace SymPolyOpt.PowerSumUB

open Polynomial

/-- The Newton sums `s_k(p) = ∑_{z root of p in ℂ, with multiplicity} z^k` of a real
polynomial `p` (the real part; the sum is real since non-real roots come in conjugate
pairs). For `p` of degree `m`, `newtonSum p 0 = m`. -/
noncomputable def newtonSum (p : ℝ[X]) (k : ℕ) : ℝ :=
  (((p.aroots ℂ).map (· ^ k)).sum).re

/-- The feasible set of (6.7), parametrized by the monic polynomial `p` itself
(equivalently by its constant coefficient `p_0 = p.coeff 0`): `p` is monic of degree `m`,
its Newton sums satisfy `s_j(p) = γ_j` for `1 ≤ j ≤ m - 1`, and the Hankel matrix
`H_m(s(p))` (with `s_0 = m`) is positive semidefinite. -/
def feasU (m : ℕ) (γ : ℕ → ℝ) : Set ℝ[X] :=
  {p | p.Monic ∧ p.natDegree = m ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → newtonSum p j = γ j) ∧
    (SymPolyOpt.PowerSumLB.hankel m (newtonSum p)).PosSemidef}

/-- The value `U_nmq` of the one-variable SDP (6.7), as an infimum in `EReal`
(`⊤` if (6.7) is infeasible). It does not depend on `n`. -/
noncomputable def valU (m q : ℕ) (γ : ℕ → ℝ) : EReal :=
  ⨅ p ∈ feasU m γ, ((newtonSum p q : ℝ) : EReal)

end SymPolyOpt.PowerSumUB


