-- Prove2me | Definitions.Def_TeschlODE_Shared_symDist
-- name    : TeschlODE_Shared_symDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:14:32.602239+00:00
-- url     : https://prove2.me/theorems/56b1c7cc-f16a-4da9-aeda-2a3b8529113e
-- title:
--   The metric $d(x,y) = \sum_n |x_n - y_n| / N^n$ on $\Sigma_N$ (11.28)
-- statement:
--   On $\Sigma_N = \{0, \dots, N-1\}^{\mathbb{N}_0}$ define
--   $$d(x, y) = \sum_{n \in \mathbb{N}_0} \frac{|x_n - y_n|}{N^n}.$$
--   For $N = 2$ this is the metric (11.24) on $\Sigma_2$. For $N \ge 2$ the series converges (its terms are at most $(N-1)/N^n$) and $d$ is a metric; the book leaves this as an exercise.
--
--   This one definition serves chunk 09-interval-maps (Theorem 11.5, p. 301; Lemma 11.6, p. 302; Lemmas 11.8 and 11.9, p. 303) and chunk 11-horseshoe (Theorem 11.5, p. 301; Lemmas 11.8 and 11.9, p. 303).
--
--   **Formalization Note.** The symbols are the natural numbers $0, \dots, N-1$ viewed as reals. The definition is an infinite sum (`tsum`), which Lean evaluates to $0$ for a non-summable series; for $N \ge 2$ (the book's $N \in \mathbb{N} \setminus \{1\}$, assumed by every theorem using it) the series is summable, so this never arises. All density and continuity statements about $\Sigma_N$ in this mission are phrased with this function directly (in $\varepsilon$–$\delta$ form), not through a topology instance.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 302, §11.5, Eq. (11.28); p. 300, Eq. (11.24)

import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.5, p. 302, (11.28) (and (11.24) for `N = 2`): the metric on
`Σ_N = {0, …, N − 1}^{ℕ₀}`, `d(x, y) = ∑_{n ∈ ℕ₀} |xₙ − yₙ| / Nⁿ`. For `N ≥ 2` (the book's
`N ∈ ℕ \ {1}`) the series converges, being bounded termwise by `(N − 1)/Nⁿ`. -/
noncomputable def symDist (N : ℕ) (x y : ℕ → Fin N) : ℝ :=
  ∑' n : ℕ, |((x n : ℕ) : ℝ) - ((y n : ℕ) : ℝ)| / (N : ℝ) ^ n

end TeschlODE.Shared


