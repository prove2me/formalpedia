-- Prove2me | Definitions.Def_PConeEB_IsOneStepFRF
-- name    : PConeEB_IsOneStepFRF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:54.504988+00:00
-- url     : https://prove2.me/theorems/a87fd6b1-cc71-472b-9bcb-8b4cd6cd4aa2
-- title:
--   One-step facial residual function (1-FRF)
-- statement:
--   Let $K$ be a closed convex cone and $z\in K^*$. A function $\psi:\mathbb R_+\times\mathbb R_+\to\mathbb R_+$ is a **one-step facial residual function (1-FRF)** for $K$ and $z$ if:
--
--   1. $\psi$ is nonnegative, nondecreasing in each argument, and $\psi(0,t)=0$ for every $t\in\mathbb R_+$;
--   2. for every $x\in\operatorname{span}K$ and every $\epsilon\ge0$,
--   $$
--   \operatorname{dist}(x,K)\le\epsilon,\quad\langle x,z\rangle\le\epsilon\quad\Longrightarrow\quad\operatorname{dist}(x,K\cap\{z\}^\perp)\le\psi(\epsilon,\|x\|).
--   $$
--
--   A 1-FRF converts information on the distance to $K$ into information on the distance to the face $K\cap\{z\}^\perp$.
--
--   **Formalization Note** $\psi$ is a function on $\mathbb R\times\mathbb R$ with all its conditions on nonnegative arguments. The standing assumptions on $K$ and $z$ are hypotheses of the statements that use the predicate.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Definition 2.2, pp.4–5

import Mathlib
import Definitions.Def_PConeEB_hyperplane

namespace PConeEB

/-- Definition 2.2 (one-step facial residual function, 1-FRF). `ψ` is a 1-FRF for `K` and `z` if
(i) `ψ` is nonnegative, nondecreasing in each argument and `ψ(0, t) = 0` for `t ≥ 0`, and
(ii) for every `x ∈ span K` and `ε ≥ 0`, `dist(x, K) ≤ ε` and `⟨x, z⟩ ≤ ε` imply
`dist(x, K ∩ {z}^⊥) ≤ ψ(ε, ‖x‖)`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Definition 2.2,
pp.4–5.

**Formalization Note.** `ψ : ℝ₊ × ℝ₊ → ℝ₊` is a function `ℝ → ℝ → ℝ` with every condition on
nonnegative arguments only. The standing `K` closed convex cone and `z ∈ K*` are hypotheses of the
statements that use the predicate. The bound on `⟨x, z⟩` is one-sided, as printed. -/
structure IsOneStepFRF {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (z : E) (ψ : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ s t, 0 ≤ s → 0 ≤ t → 0 ≤ ψ s t
  mono_left : ∀ t, 0 ≤ t → MonotoneOn (fun s => ψ s t) (Set.Ici 0)
  mono_right : ∀ s, 0 ≤ s → MonotoneOn (ψ s) (Set.Ici 0)
  zero_left : ∀ t, 0 ≤ t → ψ 0 t = 0
  residual : ∀ x ∈ Submodule.span ℝ K, ∀ ε : ℝ, 0 ≤ ε →
    Metric.infDist x K ≤ ε → inner ℝ x z ≤ ε →
      Metric.infDist x (K ∩ hyperplane z) ≤ ψ ε ‖x‖

end PConeEB


