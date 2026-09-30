-- Prove2me | Definitions.Def_ChenWhitt93_Reflection_Basic
-- name    : ChenWhitt93_Reflection_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:12:32.681121+00:00
-- url     : https://prove2.me/theorems/bf8a9471-c74a-4d65-a3a3-8502579cc3ae
-- title:
--   Section 2 — norms (2.5), the path space $D([0,T],\mathbb R^n)$, and the standing assumptions on $Q$
-- statement:
--   This file fixes the objects of Section 2 of Chen and Whitt (1993) that do not involve the reflection map itself.
--
--   1. For $c \in \mathbb R^n$, $\|c\| = \sum_{j=1}^n |c_j|$ (the $\ell^1$ norm).
--   2. For an $n\times n$ matrix $P$, the norm (2.5) is the maximum absolute **column** sum
--   $$
--   \|P\| = \max_{j} \sum_{i=1}^n |P_{ij}| ,
--   $$
--   which satisfies $\|P_1P_2\| \le \|P_1\|\,\|P_2\|$ and $\|Pc\| \le \|P\|\,\|c\|$.
--   3. $D([0,T],\mathbb R^n)$ is the space of paths $x:[0,T]\to\mathbb R^n$ that are right-continuous on $[0,T)$ and have left limits on $(0,T]$; such a path is bounded on $[0,T]$.
--   4. For a path $x$, $|x| \in \mathbb R^n$ is the vector of coordinatewise sup norms, $|x|_j = \sup_{0\le t\le T}|x_j(t)|$, and the norm of the path is
--   $$
--   \|x\| = \sum_{j=1}^n \sup_{0 \le t \le T} |x_j(t)| = \big\|\,|x|\,\big\| .
--   $$
--   5. The standing assumption on the $n \times n$ matrix $Q$: its transpose $Q^{\mathsf t}$ is substochastic (all entries of $Q$ are nonnegative and every column sum of $Q$ is at most $1$) and $Q^k \to 0$ as $k \to \infty$. With Markovian routing, $Q^{\mathsf t}$ is the routing matrix of an open network of $n$ queues.
--
--   These are the norms in which every Lipschitz bound of the mission is stated.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` and matrices `Matrix (Fin n) (Fin n) ℝ`. The matrix norm is a supremum over the finite index set `Fin n` (it is $0$ when $n = 0$). A path is a function `ℝ → Fin n → ℝ`; `IsCadlagOn T x` requires right-continuity on $[0,T)$, left limits on $(0,T]$ and, redundantly, boundedness on $[0,T]$, so the real suprema in `supVec` are suprema of bounded sets. The norm on paths is $\|x\| = \sum_{j=1}^n \sup_{0\le t\le T}|x_j(t)|$ (the $\ell^1$ norm of the vector $|x|$ of coordinatewise sup norms). The printed (2.6) reads $\sup_{0\le t\le T}\sum_j |x_j(t)|$; under that norm the Lipschitz bounds of Propositions 2.1 and 2.3 fail for $n \ge 2$ (with $Q = 0$, $n = 2$, $T=1$, $x_1 \equiv 0$, $x_2 = (-1_{[0.1,0.2)}, -1_{[0.3,0.4)})$ one has $\|x_1 - x_2\| = 1$ but $\|\psi(x_1)-\psi(x_2)\| = 2$), whereas every step of the paper's proofs is valid for the sum-of-sups norm.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 337–338, Section 2, the standing assumption on Q and Eqs. (2.5)–(2.6) (with (2.6) corrected to the sum of coordinatewise sup norms)

import Mathlib

open Filter Topology

namespace ChenWhitt93.Reflection

/-- The `ℓ¹` norm `‖c‖ = ∑ⱼ |cⱼ|` of a vector `c ∈ ℝⁿ` (Chen–Whitt 1993, p. 337). -/
noncomputable def l1 {n : ℕ} (c : Fin n → ℝ) : ℝ :=
  ∑ j, |c j|

/-- The matrix norm (2.5): `‖P‖ = maxⱼ ∑ᵢ |Pᵢⱼ|`, the maximum absolute **column** sum
(a maximum over the finite index set `Fin n`; it is `0` when `n = 0`). -/
noncomputable def colNorm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ j : Fin n, ∑ i, |P i j|

/-- A path `x : ℝ → ℝⁿ` lies in `D([0,T], ℝⁿ)`: it is right-continuous at every
`t ∈ [0,T)`, has a left limit at every `t ∈ (0,T]`, and is bounded on `[0,T]`
(boundedness follows from the first two conditions; it is stated for clarity).
Values of `x` outside `[0,T]` play no role. -/
def IsCadlagOn {n : ℕ} (T : ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  (∀ t ∈ Set.Ico (0 : ℝ) T, ContinuousWithinAt x (Set.Ici t) t) ∧
  (∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : Fin n → ℝ, Tendsto x (𝓝[<] t) (𝓝 l)) ∧
  Bornology.IsBounded (x '' Set.Icc (0 : ℝ) T)

/-- The vector of coordinatewise sup norms of a path on `[0,T]`:
`supVec T x j = sup_{0 ≤ t ≤ T} |xⱼ(t)|`. This is the paper's `|x|` for `x ∈ D`. -/
noncomputable def supVec {n : ℕ} (T : ℝ) (x : ℝ → Fin n → ℝ) : Fin n → ℝ :=
  fun j => ⨆ t : Set.Icc (0 : ℝ) T, |x t j|

/-- The norm on `D([0,T], ℝⁿ)` used in this formalization:
`‖x‖ = ∑ⱼ sup_{0 ≤ t ≤ T} |xⱼ(t)| = ‖ |x| ‖`. (The printed (2.6) reads
`sup_t ∑ⱼ |xⱼ(t)|`; the paper's proofs of Propositions 2.1–2.3 are valid for this
sum-of-sups norm, under which they are stated here.) -/
noncomputable def sumSupNorm {n : ℕ} (T : ℝ) (x : ℝ → Fin n → ℝ) : ℝ :=
  l1 (supVec T x)

/-- Standing assumptions on `Q` in Section 2 (p. 337): the transpose `Qᵗ` is
substochastic (entries of `Q` nonnegative, column sums of `Q` at most `1`) and
`Qᵏ → 0` as `k → ∞`. -/
structure IsTransientSubstochasticT {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ Q i j
  colSum_le_one : ∀ j, ∑ i, Q i j ≤ 1
  pow_tendsto_zero : Tendsto (fun k : ℕ => Q ^ k) atTop (𝓝 0)

end ChenWhitt93.Reflection


