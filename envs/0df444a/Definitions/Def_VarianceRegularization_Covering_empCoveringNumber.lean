-- Prove2me | Definitions.Def_VarianceRegularization_Covering_empCoveringNumber
-- name    : VarianceRegularization_Covering_empCoveringNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:11:37.110239+00:00
-- url     : https://prove2.me/theorems/47357a11-7fc9-4e57-ac8d-bd81ae38f0a8
-- title:
--   §2.2.2 — empirical ℓ∞ covering numbers N∞(F, ε, n)
-- statement:
--   Let $V$ be a subset of a normed space. A collection $v_1, \dots, v_N \in V$ is an **$\epsilon$-cover** of $V$ if every $v \in V$ satisfies $\|v - v_i\| \le \epsilon$ for some $i$; the **covering number** $N(V, \epsilon, \|\cdot\|)$ is the least such $N$ (and $+\infty$ if there is no finite cover).
--
--   For a class $\mathcal F$ of functions $\mathcal X \to \mathbb R$ and a point $x = (x_1, \dots, x_m) \in \mathcal X^m$, let
--   $$
--   \mathcal F(x) = \{ (f(x_1), \dots, f(x_m)) : f \in \mathcal F \} \subset \mathbb R^m .
--   $$
--   The **empirical $\ell_\infty$ covering number** is
--   $$
--   N_\infty(\mathcal F, \epsilon, m) = \sup_{x \in \mathcal X^m} N\big(\mathcal F(x), \epsilon, \|\cdot\|_\infty\big) \in \mathbb N \cup \{+\infty\}.
--   $$
--
--   It measures the complexity of $\mathcal F$ through the number of sup-norm balls needed to cover its restriction to any $m$ points, and enters the probability bounds of Lemma C.1 and Theorem 3.
--
--   **Formalization Note** $N(V, \epsilon, \|\cdot\|_\infty)$ is Mathlib's internal covering number `Metric.coveringNumber` (centres in $V$, closed balls), valued in $\mathbb N \cup \{\infty\}$; the distance on $\mathbb R^m$ (`Fin m → ℝ`) is the sup distance. The radius enters as a nonnegative real, $\max(\epsilon, 0)$; all theorems assume $\epsilon > 0$.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 9, Section 2.2.2

import Mathlib

namespace VarianceRegularization.Covering

/-- `F(x) = {(f(x₁),…,f(x_m)) : f ∈ F}` for `x ∈ X^m` (p. 9, §2.2.2). -/
def evalSet {X : Type*} {m : ℕ} (F : Set (X → ℝ)) (x : Fin m → X) : Set (Fin m → ℝ) :=
  (fun f : X → ℝ => fun i => f (x i)) '' F

/-- The empirical `ℓ∞` covering number `N∞(F, ε, m) = sup_{x ∈ X^m} N(F(x), ε, ‖·‖∞)` (p. 9,
§2.2.2). `N(V, ε, ‖·‖)` is the least number of points `v₁,…,v_N ∈ V` with every `v ∈ V` within
`ε` of some `vᵢ`: Mathlib's internal covering number `Metric.coveringNumber` (closed balls,
centres in `V`, valued in `ℕ∞`), on `Fin m → ℝ`, whose distance is the sup norm. A class with
no finite cover has `N∞ = ⊤`. -/
noncomputable def empCoveringNumber {X : Type*} (F : Set (X → ℝ)) (ε : ℝ) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → X, Metric.coveringNumber (Real.toNNReal ε) (evalSet F x)

end VarianceRegularization.Covering


