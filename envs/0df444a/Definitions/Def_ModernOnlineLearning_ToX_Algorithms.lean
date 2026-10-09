-- Prove2me | Definitions.Def_ModernOnlineLearning_ToX_Algorithms
-- name    : ModernOnlineLearning_ToX_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:53.509978+00:00
-- url     : https://prove2.me/theorems/918beaec-30ed-4062-8184-11f40d3bcc18
-- title:
--   Online linear regret protocol and Algorithm 6.2, Exponentiated Gradient
-- statement:
--   A **deterministic online linear algorithm** chooses $x_t\in V$ before seeing the round-$t$ gradient $g_t\in Z$. Its choice may depend on $g_1,\ldots,g_{t-1}$, and its regret guarantee $R(T)$ means that for every admissible gradient sequence and every fixed $u\in V$,
--
--   $$
--   \sum_{t=1}^T\bigl(\langle g_t,x_t\rangle-\langle g_t,u\rangle\bigr)\le R(T).
--   $$
--
--   **Exponentiated Gradient** starts from the uniform point of the simplex $\Delta^{d-1}$ and, with learning rate $\eta>0$, updates each coordinate by
--
--   $$
--   x_{t+1,i}=\frac{x_{t,i}e^{-\eta g_{t,i}}}{\sum_jx_{t,j}e^{-\eta g_{t,j}}}.
--   $$
--
--   These predicates supply the algorithmic assumptions used in Theorem 16.4 and the regret bound of §6.6.
--
--   **Formalization Note** A full gradient sequence is passed to the online algorithm, but the causality clause forces $x_t$ to depend only on earlier rounds. Index zero is unused. The Exponentiated Gradient run requires $\eta>0$ and records simplex membership through $x_{T+1}$; the denominator is positive for every admissible run with $d\ge1$.
-- source:
--   Orabona, arXiv:1912.13213v10, §1, pp. 1–2; Algorithm 6.2, p. 80; Theorem 16.4, p. 272

import Mathlib
import Definitions.Def_ModernOnlineLearning_ToX_Rademacher

namespace ModernOnlineLearning.ToX

/-- A deterministic online linear algorithm on rounds `1,...,T`. Its output at round
`t` depends only on gradients from earlier rounds, and its regret bound holds for
every sequence in the symmetric gradient domain `Z`. -/
def IsOnlineAlgorithm {d : ℕ} (T : ℕ) (Z V : Set (Fin d → ℝ)) (R : ℝ)
    (A : (ℕ → Fin d → ℝ) → ℕ → Fin d → ℝ) : Prop :=
  (∀ g h t, t ∈ Finset.Icc 1 T →
      (∀ s, s ∈ Finset.Ico 1 t → g s = h s) → A g t = A h t) ∧
  (∀ g, (∀ t ∈ Finset.Icc 1 T, g t ∈ Z) →
    (∀ t ∈ Finset.Icc 1 T, A g t ∈ V) ∧
    ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (pairing (g t) (A g t) - pairing (g t) u)) ≤ R)

/-- Algorithm 6.2 on linear losses, with the uniform initial distribution and the
componentwise exponentiated-gradient update. Membership is recorded for all
predictions, including the final updated point. -/
def IsEGRun {d : ℕ} (T : ℕ) (η : ℝ) (g x : ℕ → Fin d → ℝ) : Prop :=
  0 < η ∧
  (∀ t ∈ Finset.Icc 1 (T + 1), x t ∈ simplex d) ∧
  (∀ i, x 1 i = 1 / (d : ℝ)) ∧
  ∀ t ∈ Finset.Icc 1 T, ∀ i,
    x (t + 1) i =
      x t i * Real.exp (-η * g t i) /
        (∑ j, x t j * Real.exp (-η * g t j))

end ModernOnlineLearning.ToX


