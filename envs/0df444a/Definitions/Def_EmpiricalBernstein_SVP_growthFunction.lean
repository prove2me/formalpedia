-- Prove2me | Definitions.Def_EmpiricalBernstein_SVP_growthFunction
-- name    : EmpiricalBernstein_SVP_growthFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:27.464309+00:00
-- url     : https://prove2.me/theorems/0666f810-381c-41bf-b938-949c3e5bfe9f
-- title:
--   p. 2 — the growth function $\mathcal N_\infty(\epsilon,\mathcal F,m)$ and $\mathcal M(n)=10\mathcal N_\infty(1/n,\mathcal F,2n)$
-- statement:
--   Let $\mathcal F$ be a class of real functions on a set $\mathcal X$. For $x = (x_1,\dots,x_m) \in \mathcal X^m$ let
--
--   $$
--   \mathcal F(x) = \{(f(x_1),\dots,f(x_m)) : f \in \mathcal F\} \subseteq \mathbb R^m .
--   $$
--
--   For $A \subseteq \mathbb R^m$ and $\epsilon > 0$, the covering number $\mathcal N(\epsilon, A, \|\cdot\|_\infty)$ is the smallest cardinality $|A_0|$ of a set $A_0 \subseteq A$ such that $A$ is contained in the union of the $\epsilon$-balls, in the sup-norm metric, centred at points of $A_0$ ($+\infty$ if there is no finite such set). The **growth function** is
--
--   $$
--   \mathcal N_\infty(\epsilon, \mathcal F, m) = \sup_{x \in \mathcal X^m} \mathcal N(\epsilon, \mathcal F(x), \|\cdot\|_\infty) \in \mathbb N \cup \{+\infty\}.
--   $$
--
--   The theorems on function classes use the complexity term
--
--   $$
--   \mathcal M(n) = 10\, \mathcal N_\infty(1/n, \mathcal F, 2n).
--   $$
--
--   The growth function measures the complexity of $\mathcal F$ by how many sup-norm balls are needed to cover its restriction to any $m$ points; it replaces the cardinality $|\mathcal F|$ of finite classes in the uniform bounds.
--
--   **Formalization Note** $\mathcal N(\epsilon, A, \|\cdot\|_\infty)$ is Mathlib's `Metric.coveringNumber` (centres in $A$, **closed** balls, values in $\mathbb N\cup\{\infty\}$) on `Fin m → ℝ`, whose distance is the sup distance; the radius enters as $\max(\epsilon,0)$. $\mathcal M(n)$ (`calM`) is a real number obtained through `ENat.toNat`, which equals the growth function whenever it is finite; every theorem using `calM` assumes $\mathcal N_\infty(1/n,\mathcal F,2n) < \infty$. The body is the same as the namkoong-2017 definition `VarianceRegularization.Covering.empCoveringNumber`, whose module is not available in this environment.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, p. 2 (growth function) and Theorem 6, pp. 2–3 (M(n))

import Mathlib

namespace EmpiricalBernstein.SVP

/-- `F(x) = {(f(x_1), …, f(x_m)) : f ∈ F} ⊆ ℝ^m` for `x ∈ 𝒳^m` (arXiv:0907.3740v1, p. 2). -/
def evalSet {𝒳 : Type*} {m : ℕ} (F : Set (𝒳 → ℝ)) (x : Fin m → 𝒳) : Set (Fin m → ℝ) :=
  (fun f : 𝒳 → ℝ => fun i => f (x i)) '' F

/-- The growth function `N∞(ε, F, m) = sup_{x ∈ 𝒳^m} N(ε, F(x), ‖·‖∞)` (arXiv:0907.3740v1, p. 2).
`N(ε, A, ‖·‖∞)` is the least cardinality of a set `A₀ ⊆ A` such that the `ε`-balls centred at the
points of `A₀` cover `A`: Mathlib's `Metric.coveringNumber` (centres in `A`, closed balls, values in
`ℕ∞`, `⊤` if no finite cover exists) on `Fin m → ℝ`, whose distance is the sup distance. -/
noncomputable def growthFunction {𝒳 : Type*} (ε : ℝ) (F : Set (𝒳 → ℝ)) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → 𝒳, Metric.coveringNumber (Real.toNNReal ε) (evalSet F x)

/-- `ℳ(n) = 10 N∞(1/n, F, 2n)` (arXiv:0907.3740v1, Theorem 6, p. 2, and Theorem 15, p. 6), as a
real number. The theorems that use it assume `growthFunction (1/n) F (2n) < ⊤`, so `toNat` is the
value itself. -/
noncomputable def calM {𝒳 : Type*} (F : Set (𝒳 → ℝ)) (n : ℕ) : ℝ :=
  10 * ((growthFunction (1 / (n : ℝ)) F (2 * n)).toNat : ℝ)

end EmpiricalBernstein.SVP


