-- Prove2me | Definitions.Def_HierADA_Phi
-- name    : HierADA_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:02.561197+00:00
-- url     : https://prove2.me/theorems/eaf8564b-6e4e-4483-a43c-271bda2b77a5
-- title:
--   Value function $\Phi(G)=\max_{w\in W}(\frac\tau4\langle G,w\rangle-R(w))$
-- statement:
--   For a threshold $\tau$, a block of $r$ samples and scores $G\in\mathbb R^r$,
--
--   $$
--   \Phi(G)=\max_{w\in W}\Big(\frac\tau4\langle G,w\rangle-R(w)\Big).
--   $$
--
--   This is the value function whose increments Lemma 3.3 bounds and from which the potential of Proposition 3.4 is built.
--
--   **Formalization Note** $W$ is the published `NondualOpt.cappedSimplex r 8`, the capped simplex $\{w\ge0,\ \sum_iw_i=1,\ w_i\le8/r\}$ of Equation (2). Written as the supremum over $W$. For $r\ge1$ the supremum is attained (a continuous function on a nonempty compact set), so it is the paper's maximum; for $r=0$ Lean's value is $\sup\emptyset=0$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Equation (8), p.20

import Mathlib
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_HierADA_objective

set_option autoImplicit false

namespace HierADA

/-- **The value function `Φ`** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data Analysis and
Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03, sha256
f220ae51…), Equation (8), p.20:
$$\Phi(G)=\max_{w\in W}\Bigl(\frac\tau4\langle G,w\rangle-R(w)\Bigr).$$

**Formalization Note.** Written as the supremum of the objective over the capped simplex. For `r ≥ 1`
the set `W` is nonempty and compact and the objective is continuous, so the supremum is attained and
equals the paper's maximum; for `r = 0` (no block) the value is Lean's `sSup ∅ = 0`. -/
noncomputable def Phi (τ : ℝ) (r : ℕ) (G : Fin r → ℝ) : ℝ :=
  sSup (objective τ r G '' NondualOpt.cappedSimplex r 8)

end HierADA


