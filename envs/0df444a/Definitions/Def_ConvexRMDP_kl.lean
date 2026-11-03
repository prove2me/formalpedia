-- Prove2me | Definitions.Def_ConvexRMDP_kl
-- name    : ConvexRMDP_kl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:28.489781+00:00
-- url     : https://prove2.me/theorems/648fc5c0-a868-4fc8-9c1d-b2c4b4544139
-- title:
--   Kullback–Leibler divergence $\mathrm{KL}(q, q_0)$ and absolute continuity $q \ll q_0$
-- statement:
--   Let $\mathcal A$ be a finite set and $q, q_0 \in \mathbb R^{\mathcal A}$. We say that $q$ is **absolutely continuous** with respect to $q_0$, written $q \ll q_0$, if $q_{0,a} = 0$ implies $q_a = 0$ for every $a \in \mathcal A$.
--
--   For distributions $q, q_0 \in \Delta(\mathcal A)$, the **Kullback–Leibler divergence** is
--   $$
--   \mathrm{KL}(q, q_0) = \begin{cases} \sum_{a \in \mathcal A} q_a \log\left(\dfrac{q_a}{q_{0,a}}\right) & \text{if } q \ll q_0, \\ +\infty & \text{otherwise,} \end{cases}
--   $$
--   with the convention $0 \log 0 = 0$.
--
--   The divergence is the entropic regularizer of the robust Bellman operator $\tilde T$ and the penalty in the Donsker–Varadhan formula (Lemma 4.1).
--
--   **Formalization Note** The Lean function `kl` is real valued and returns the finite sum $\sum_a q_a \log(q_a / q_{0,a})$ for all inputs; it equals the divergence above only when $q \ll q_0$ (the predicate `AbsCont`). Every statement that uses it either assumes `AbsCont q q₀` or uses a reference distribution with positive entries (the uniform policy), so the value $+\infty$ is never replaced by a finite number.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §4.1, p.10, the definition of KL after (4.1) and of πₛ ≪ νₛ

import Mathlib

namespace ConvexRMDP

/-- Absolute continuity `q ≪ q₀` of two vectors indexed by a finite set: `q₀ a = 0 ⇒ q a = 0` for
every `a` (Grand-Clément & Petrik, arXiv:2209.10187v2, §4.1, p.10). -/
def AbsCont {A : Type*} (q q₀ : A → ℝ) : Prop := ∀ a, q₀ a = 0 → q a = 0

/-- **The Kullback–Leibler divergence** `KL(q, q₀) = ∑_a q_a log(q_a / q₀_a)` of two distributions on
a finite set (Grand-Clément & Petrik, arXiv:2209.10187v2, §4.1, display after (4.1), p.10).

**Formalization Note.** The paper sets `KL(q, q₀) = +∞` unless `q ≪ q₀`; this real-valued function
is the paper's value only when `AbsCont q q₀` holds, and every statement using it carries that
condition or has `q₀ > 0` (the uniform policy). Lean's `0 * log 0 = 0` is the convention
`0 log 0 = 0`. -/
noncomputable def kl {A : Type*} [Fintype A] (q q₀ : A → ℝ) : ℝ :=
  ∑ a, q a * Real.log (q a / q₀ a)

end ConvexRMDP


