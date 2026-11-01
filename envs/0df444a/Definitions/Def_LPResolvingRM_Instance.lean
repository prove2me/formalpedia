-- Prove2me | Definitions.Def_LPResolvingRM_Instance
-- name    : LPResolvingRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:19.423379+00:00
-- url     : https://prove2.me/theorems/a6b78770-a2f2-4e12-93dc-efe50259db43
-- title:
--   Problem instance, Assumption 1, and the normalized data $(p_j\mu_j)$, $(p_jc_j)$
-- statement:
--   An instance of the online resource-allocation (network revenue management) problem consists of $n$ order types and $m$ resources. Type $j$ has a reward $\mu_j\in\mathbb R$, a consumption vector $c_j\in\mathbb R^m$ and an arrival probability $p_j$; the average capacity per period is $b\in\mathbb R^m$, and over a horizon of $T$ periods the total capacity is $B=Tb$.
--
--   **Assumption 1 (Distribution).**
--
--   1. The type of each period's order is drawn i.i.d. from $p$, where $p_j>0$ for every listed type and $\sum_j p_j=1$.
--   2. $0\le\mu_j\le1$, $c_j\ge0$ and $\|c_j\|_\infty\le1$.
--   3. $b>0$ coordinatewise (linear growth $B=Tb$).
--
--   The standard form (6) of the fluid LP uses the normalized data
--   $$\mu=(p_1\mu_1,\dots,p_n\mu_n)^\top,\qquad C=(p_1c_1,\dots,p_nc_n)\in\mathbb R^{m\times n}.$$
--
--   This is the data layer of every statement of the mission.
--
--   **Formalization Note** Types are `Fin n` and resources `Fin m`. The i.i.d. sampling is not a hypothesis: it is built into the law of the run of Algorithm 1 (`pathWeight`). The paper's support points are distinct pairs; distinctness is not required.
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, §2, Assumption 1, p.5; §3, (6), p.8

import Mathlib

namespace LPResolvingRM

/-- **An instance of the online resource-allocation problem** (Chen, Li, Ye, *An Improved
Analysis of LP-based Control for Revenue Management*, arXiv:2101.11092v3, §2, Assumption 1, p.5).

There are `n` order types and `m` resources. Type `j` has reward `μ j` and consumption vector
`c j : Fin m → ℝ`; it arrives in each period with probability `p j`. The average capacity per
period is `b`, so the total capacity over a horizon `T` is `B = T • b`.

**Formalization Note.** Order types are `Fin n` and resources `Fin m`: the paper's type `j` and
resource `i` are the Lean indices `j - 1`, `i - 1`. The horizon `T` is not part of the instance:
the regret is a function of `T` with `b` fixed, as in Assumption 1 (c). -/
structure Instance (n m : ℕ) where
  /-- the reward `μ_j` of type `j` -/
  μ : Fin n → ℝ
  /-- the consumption vector `c_j ∈ ℝ^m` of type `j` -/
  c : Fin n → Fin m → ℝ
  /-- the arrival probability `p_j` of type `j` -/
  p : Fin n → ℝ
  /-- the average capacity `b = B / T` -/
  b : Fin m → ℝ

/-- **Assumption 1 (Distribution)** (arXiv:2101.11092v3, p.5).

(a) The type of each order is drawn i.i.d. from the probability vector `p`, which is supported on
all `n` types: `p_j > 0` and `∑_j p_j = 1`. (b) `0 ≤ μ_j ≤ 1`, `c_j ≥ 0` and `‖c_j‖_∞ ≤ 1`.
(c) The capacity is `B = T b` with `b > 0` (every coordinate positive).

**Formalization Note.** The i.i.d. sampling of (a) is not a hypothesis: it is built into the
law of the algorithm's sample path (`LPResolvingRM.pathWeight`), where the type index of each
period is drawn from `p`. "Support" is read as `p_j > 0` for every listed type. The paper's
support points are distinct pairs `(μ_j, c_j)`; distinctness is not required here. -/
def Assumption1 {n m : ℕ} (I : Instance n m) : Prop :=
  (∀ j, 0 < I.p j) ∧ (∑ j, I.p j = 1) ∧ (∀ j, 0 ≤ I.μ j ∧ I.μ j ≤ 1) ∧
    (∀ j i, 0 ≤ I.c j i ∧ I.c j i ≤ 1) ∧ (∀ i, 0 < I.b i)

/-- The **normalized objective** `μ := (p₁μ₁, …, p_nμ_n)` of the standard form (6)
(arXiv:2101.11092v3, p.8: "with a slight abuse of notation … we use µ to denote the vector
(p₁µ₁, …, p_nµ_n)⊤"). -/
def normMu {n m : ℕ} (I : Instance n m) : Fin n → ℝ := fun j => I.p j * I.μ j

/-- The **normalized constraint matrix** `C := (p₁c₁, …, p_nc_n)` of the standard form (6)
(arXiv:2101.11092v3, p.8): entry `(i, j)` is `p_j c_{ij}`. -/
def normC {n m : ℕ} (I : Instance n m) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => I.p j * I.c j i

end LPResolvingRM


