-- Prove2me | Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA
-- name    : StochModelWC_ProxSubgrad_AssumptionA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:45:46.81941+00:00
-- url     : https://prove2.me/theorems/9998aee1-4508-4359-b4e2-1ad9da688a55
-- title:
--   Assumption A — the stochastic subgradient oracle
-- statement:
--   Consider the problem $\min_x \varphi(x) = f(x) + r(x)$ where $r : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ is closed convex with domain $D = \operatorname{dom} r$ and $f : \mathbb R^d \to \mathbb R$ is $\rho$-weakly convex. Fix a probability space $(\Omega, \mathcal F, P)$ and equip $\mathbb R^d$ with its Borel $\sigma$-algebra. **Assumption A** (stochastic subgradient oracle) consists of:
--
--   1. **(A1)** It is possible to generate i.i.d. realizations $\xi_1, \xi_2, \dots \sim P$.
--   2. **(A2)** There is an open set $U \supseteq D$ and a measurable map $G : U \times \Omega \to \mathbb R^d$ such that, for all $x \in U$, $G(x, \cdot)$ is integrable and
--   $$\mathbb E_\xi[G(x,\xi)] \in \partial f(x).$$
--   3. **(A3)** There is a real $L \ge 0$ with
--   $$\mathbb E_\xi\big[\|G(x,\xi)\|^2\big] \le L^2 \qquad \text{for all } x \in D.$$
--
--   This is the only access to $f$ that Algorithm 3.1 uses.
--
--   **Formalization Note.** (A1) is not part of this predicate: the theorems realize it as the product measure $P^{\otimes(T+1)}$ on sample paths. $G$ is a map on all of $\mathbb R^d \times \Omega$; its values off $U$ are irrelevant. Integrability of $G(x,\cdot)$ on $U$ and of $\|G(x,\cdot)\|^2$ on $D$ is stated explicitly, because the paper's expectations presuppose it. Since $f$ is real-valued, $\partial f$ is the subdifferential of $f$ with domain all of $\mathbb R^d$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 12, (3.1) and Assumption A

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Assumption A (p. 12), (A2)–(A3); (A1) is the product measure in the theorems. -/
def AssumptionA {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (L : ℝ) : Prop :=
  -- (A2)
  IsOpen U ∧ D ⊆ U ∧ Measurable (Function.uncurry G) ∧
  (∀ x ∈ U, Integrable (G x) P ∧ ∫ ξ, G x ξ ∂P ∈ frechetSubdiff Set.univ f x) ∧
  -- (A3)
  0 ≤ L ∧ ∀ x ∈ D, Integrable (fun ξ => ‖G x ξ‖ ^ 2) P ∧ ∫ ξ, ‖G x ξ‖ ^ 2 ∂P ≤ L ^ 2

end StochModelWC.ProxSubgrad


