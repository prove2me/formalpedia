-- Prove2me | Definitions.Def_CorruptRobustRL_Supervised_Supplement_Error
-- name    : CorruptRobustRL_Supervised_Supplement_Error
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:08:42.760729+00:00
-- url     : https://prove2.me/theorems/e77cefe4-1b32-4098-977d-cb7e34205d75
-- title:
--   Refined error and its horizon truncation, (C.4)
-- statement:
--   Let $M$ have nominal transition probabilities $p^\star$, let $m=(\widehat r,\widehat p,b)$ be a model estimate and let $H$ be the horizon. For a state-action pair $(x,a)$, define
--   $$\operatorname{Err}(x,a)=2b(x,a)+\max_{V:\mathcal X\to\mathbb R,\ |V(y)|\le H\ \forall y}\left(\left|\sum_y(\widehat p(y\mid x,a)-p^\star(y\mid x,a))V(y)\right|-\frac{\sum_y p^\star(y\mid x,a)V(y)^2}{H^2}\right),$$
--   $$\overline{\operatorname{Err}}(x,a)=\min\{H,\operatorname{Err}(x,a)\}.$$
--   The quadratic penalty is part of the maximized expression. These errors are stage-independent, and form the input to both refined clipping operations.
--
--   **Formalization Note** The real supremum is taken over the continuous objective on the finite-dimensional closed box. The box contains zero and is compact, so the supremum is finite and attained. The theorem domain has $H\ge1$.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 44, (C.4) and its following truncation

import Definitions.Def_CorruptRobustRL_Supervised_Supervisor

namespace CorruptRobustRL.Supervised.Supplement

variable {X A : Type} [Fintype X]

/-- Objective of (C.4). The quadratic penalty is inside the maximum. -/
noncomputable def errorObjective (M : NominalMDP X A) (m : ModelEst X A)
    (H : ℕ) (x : X) (a : A) (V : X → ℝ) : ℝ :=
  |∑ y, (m.p x a y - M.pstar x a y) * V y| -
    (∑ y, M.pstar x a y * (V y) ^ 2) / (H : ℝ) ^ 2

/-- Err of (C.4). On the finite-dimensional closed H-box the continuous objective
attains its maximum; sSup is its real value, not an unbounded or empty-set default. -/
noncomputable def refinedError (M : NominalMDP X A) (m : ModelEst X A)
    (H : ℕ) (x : X) (a : A) : ℝ :=
  2 * m.b x a + sSup {v : ℝ | ∃ V : X → ℝ,
    (∀ y, |V y| ≤ (H : ℝ)) ∧ v = errorObjective M m H x a V}

/-- Overlined Err, p. 44, the truncation used in both (C.6) and (C.7). -/
noncomputable def truncatedError (M : NominalMDP X A) (m : ModelEst X A)
    (H : ℕ) (x : X) (a : A) : ℝ :=
  min (H : ℝ) (refinedError M m H x a)

end CorruptRobustRL.Supervised.Supplement


