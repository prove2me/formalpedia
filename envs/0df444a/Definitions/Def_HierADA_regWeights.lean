-- Prove2me | Definitions.Def_HierADA_regWeights
-- name    : HierADA_regWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:10.067284+00:00
-- url     : https://prove2.me/theorems/c37f0f8d-ae2c-49c9-8190-23bab404329d
-- title:
--   Regularized weights $w(G)$ of Equation (2)
-- statement:
--   For a threshold $\tau$, a block of $r$ samples and scores $G\in\mathbb R^r$, the **weights** $w(G)$ are
--
--   $$
--   w(G)=\operatorname*{argmax}_{w\ge0,\ \sum_iw_i=1,\ w_i\le 8/r}\Big(\frac\tau4\langle G,w\rangle-\frac r2\Big\|w-\frac{\mathbf 1}r\Big\|_2^2\Big).
--   $$
--
--   These are the weights a learned block uses after every change of its scores; Lemma 3.6 gives their closed form.
--
--   **Formalization Note** The feasible set is the published `NondualOpt.cappedSimplex r 8`. The maximizer is chosen with Hilbert's choice operator among the feasible maximizers. For $r\ge1$ the objective is strictly concave on a nonempty compact convex set, so the maximizer exists and is unique; for $r=0$ the value is immaterial.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Equation (2), p.14

import Mathlib
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_objective

set_option autoImplicit false

namespace HierADA

/-- **The regularized weights `w(G)` of Equation (2)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Equation (2), p.14:
$$w(G)=\operatorname*{argmax}_{w\ge0,\ \sum_iw_i=1,\ w_i\le 8/r}\Bigl(\frac\tau4\langle G,w\rangle-\frac r2\Bigl\|w-\frac{\mathbf 1}r\Bigr\|_2^2\Bigr).$$

**Formalization Note.** The maximizer is chosen with `Classical.epsilon` among the feasible points that
maximize the objective. For `r ≥ 1` the objective is strictly concave on the nonempty compact set
`W`, so the maximizer exists and is unique and this is the paper's `w(G)` (Lemma 3.6 gives its
closed form). For `r = 0` the value is an arbitrary vector of the empty type. -/
noncomputable def regWeights (τ : ℝ) (r : ℕ) (G : Fin r → ℝ) : Fin r → ℝ :=
  Classical.epsilon fun w =>
    w ∈ NondualOpt.cappedSimplex r 8 ∧ ∀ v ∈ NondualOpt.cappedSimplex r 8, objective τ r G v ≤ objective τ r G w

end HierADA


