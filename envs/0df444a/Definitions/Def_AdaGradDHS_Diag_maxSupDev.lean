-- Prove2me | Definitions.Def_AdaGradDHS_Diag_maxSupDev
-- name    : AdaGradDHS_Diag_maxSupDev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:18:07.617311+00:00
-- url     : https://prove2.me/theorems/6c682d86-6603-4265-be70-ddceabbecb6b
-- title:
--   $\max_{t \le T}\|x^* - x_t\|_\infty$
-- statement:
--   For iterates $x_1, x_2, \dots \in \mathbb{R}^d$, a point $x^* \in \mathbb{R}^d$ and $T \ge 1$,
--   $$\max_{1 \le t \le T} \|x^* - x_t\|_\infty = \max_{1 \le t \le T}\, \max_{1 \le i \le d} |x^*_i - x_{t,i}| .$$
--
--   This is the largest $\ell_\infty$ distance between the comparator and an iterate during the first $T$ rounds; it appears in the composite mirror-descent bound of Theorem 5 and in (14).
--
--   **Formalization Note** The maximum ranges over the rounds $t = 1, \dots, T$ and is a finite supremum in $\mathbb{R}_{\ge 0}$: it is the true maximum for $T \ge 1$ and $0$ for $T = 0$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), Theorem 5 and eq. (14), pp. 2131–2132 ("max_{t≤T} ‖x∗ − xt‖∞")

import Mathlib

namespace AdaGradDHS.Diag

/-- **`max_{t≤T} ‖x* − x_t‖∞`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), Theorem 5 and (14), pp. 2131–2132: "max_{t≤T} ‖x∗ − xt‖∞²".

`maxSupDev x xstar T = max_{1 ≤ t ≤ T} max_i |x*_i − (x_t)_i|`, a finite supremum in `ℝ≥0`
cast to `ℝ`.

**Formalization Note.** The maximum ranges over the rounds `t ∈ {1, …, T}` (index `0` is unused).
It is a `Finset.sup` in `ℝ≥0`, so it is the true maximum for `T ≥ 1` and `0` for `T = 0`; no
real `⨆` is involved. -/
noncomputable def maxSupDev {d : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin d))
    (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  (((Finset.Icc 1 T).sup fun t => Finset.univ.sup fun i => ‖xstar i - x t i‖₊ : NNReal) : ℝ)

end AdaGradDHS.Diag


