-- Prove2me | Definitions.Def_ModernOnlineLearning_LowerBounds_Protocol
-- name    : ModernOnlineLearning_LowerBounds_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:24.178165+00:00
-- url     : https://prove2.me/theorems/95fad640-ecf8-47d2-b352-2e373f4e0de4
-- title:
--   Online linear optimization: deterministic algorithms and regret
-- statement:
--   An **online linear optimization algorithm** chooses a point $x_t$ in a feasible set $V$ on each round $t=1,2,\ldots$, before seeing that round's loss vector $g_t$. Its loss is $\langle g_t,x_t\rangle$. A deterministic algorithm's choice depends only on $g_1,\ldots,g_{t-1}$, and every choice lies in $V$.
--
--   Against one fixed comparator $u$, its regret through round $T$ is
--
--   $$
--   \operatorname{Regret}_T(u)=\sum_{t=1}^{T}\bigl(\langle g_t,x_t\rangle-\langle g_t,u\rangle\bigr).
--   $$
--
--   This protocol fixes the order of play and the comparator convention for the lower bounds in Chapter 5.
--
--   **Formalization Note** The algorithm receives a full sequence as an argument, but a causality condition makes its round-$t$ output depend only on indices $1,\ldots,t-1$. Index zero is unused. The ambient space is Euclidean $\mathbb R^d$.
-- source:
--   Orabona, arXiv:1912.13213v10, §1, pp. 1–2; §2.3, p. 22; §5.1, p. 50

import Mathlib

namespace ModernOnlineLearning.LowerBounds

/-- A deterministic online linear optimization algorithm on `V`: its round-`t`
prediction is feasible and depends only on gradients from rounds `1,...,t-1`.
The value at round zero is unused. -/
def IsDeterministicOLOAlg {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t g, 1 ≤ t → A t g ∈ V) ∧
  (∀ t g h, 1 ≤ t →
    (∀ s, 1 ≤ s → s < t → g s = h s) → A t g = A t h)

/-- Regret through round `T` against one fixed comparator, for linear losses
`z ↦ ⟪g t, z⟫`. The first round is indexed by one. -/
noncomputable def oloRegret {d : ℕ}
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (inner ℝ (g t) (A t g) - inner ℝ (g t) u)

end ModernOnlineLearning.LowerBounds


