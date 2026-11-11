-- Prove2me | Definitions.Def_QVolTransducer_speedyStat
-- name    : QVolTransducer_speedyStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:42.809046+00:00
-- url     : https://prove2.me/theorems/cc4d1d28-3abf-4909-92aa-1ec8683bba09
-- title:
--   Discrete local conductance $\ell_{\delta,\zeta}$ and speedy-walk stationary distribution $\pi_{\beta,\delta,\zeta}$
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a convex body, $\beta\ge0$, $\delta>0$, $\zeta>0$ and $f(x)=e^{-\beta\|x\|^2}$. The **discretized speedy walk** at $x\in K_\zeta$ selects $y\in(K\cap(x+\delta B_d))_\zeta$ uniformly at random and moves to $y$ with probability $\min\{1,f(y)/f(x)\}$, else stays at $x$. Its **local conductance** at $x\in K_\zeta$ is
--
--   $$
--   \ell_{\delta,\zeta}(x):=\frac{|(x+\delta B_d)\cap K_\zeta|}{|(\delta B_d)_\zeta|},
--   $$
--
--   and its stationary distribution is
--
--   $$
--   \pi_{\beta,\delta,\zeta}(x)=\frac{e^{-\beta\|x\|^2}\,\ell_{\delta,\zeta}(x)}{\sum_{y\in K_\zeta}e^{-\beta\|y\|^2}\,\ell_{\delta,\zeta}(y)},\qquad x\in K_\zeta,
--   $$
--
--   extended by $0$ off $K_\zeta$. With $K\cap rB_d$ in place of $K$ these are the clipped objects $\ell_{\delta,r,\zeta}$ and $\pi_{\beta,\delta,r,\zeta}$ on $(K\cap rB_d)_\zeta$. The quantum algorithm prepares and reflects through the state $|\pi_{\beta,\delta,r,\zeta}\rangle$.
--
--   **Formalization Note** The distribution is defined by the formula stated on p.51 ("proportional to $\exp(-\beta\|x\|^2)\ell_{\delta,\zeta}(x)$"), which satisfies detailed balance for the walk. Grid points of $K$ are counted inside $(RB_d)_\zeta$, which is all of $K_\zeta$ when $K\subseteq RB_d$, as in every statement using these objects.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definitions 8.13 and 8.14, p.51; p.56 (PDF pp.53, 58)

import Mathlib
import Definitions.Def_QVolTransducer_gridIdx

namespace QVolTransducer

open Classical in
/-- The discrete local conductance (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Definition 8.14, p.51): for a grid point `x = ζ z ∈ K_ζ`,
`ℓ_{δ,ζ}(x) := |(x + δB_d) ∩ K_ζ| / |(δB_d)_ζ|`. With `K ∩ rB_d` in place of `K` it is the
clipped local conductance `ℓ_{δ,r,ζ}` (p.56).

**Formalization Note** The points of `K_ζ` are counted inside the grid `(RB_d)_ζ`; for
`K ⊆ RB_d`, the hypothesis of every statement using it, this is all of `K_ζ`. The value at grid
points outside `K` is never used. -/
noncomputable def localCondGrid {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (δ ζ R : ℝ)
    (z : Fin d → ℤ) : ℝ :=
  (((gridIdx d ζ R).filter fun y =>
      latticePt ζ y ∈ K ∧ dist (latticePt ζ y) (latticePt ζ z) ≤ δ).card : ℝ) /
    ((gridIdx d ζ δ).card : ℝ)

open Classical in
/-- The stationary distribution `π_{β,δ,ζ}` of the discretized speedy walk on `K`
(arXiv:2609.40217, Definition 8.13, p.51: at `x ∈ K_ζ` select `y ∈ (K ∩ (x + δB_d))_ζ` uniformly
and move there with probability `min{1, f(y)/f(x)}`, `f(x) = exp(−β‖x‖²)`; "The stationary
distribution π_{β,δ,ζ} is proportional to exp(−β‖x‖²) ℓ_{δ,ζ}(x)"):
`π_{β,δ,ζ}(x) = exp(−β‖x‖²) ℓ_{δ,ζ}(x) / Σ_{y ∈ K_ζ} exp(−β‖y‖²) ℓ_{δ,ζ}(y)` for `x ∈ K_ζ`, and
`0` elsewhere (the zero extension of p.53). With `K ∩ rB_d` in place of `K` it is the clipped
distribution `π_{β,δ,r,ζ}` on `(K ∩ rB_d)_ζ` (p.56).

**Formalization Note** The distribution is defined by the formula the paper states on p.51 (which
satisfies detailed balance for the walk of Definition 8.13). It is a function on `ℤ^d`, where `z`
stands for the grid point `ζ z`; the grid of `K` is taken inside `(RB_d)_ζ`, which is all of `K_ζ`
when `K ⊆ RB_d`. -/
noncomputable def speedyStat {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ ζ R : ℝ)
    (z : Fin d → ℤ) : ℝ :=
  if z ∈ gridIdx d ζ R ∧ latticePt ζ z ∈ K then
    Real.exp (-β * ‖latticePt ζ z‖ ^ 2) * localCondGrid K δ ζ R z /
      ∑ y ∈ (gridIdx d ζ R).filter (fun y => latticePt ζ y ∈ K),
        Real.exp (-β * ‖latticePt ζ y‖ ^ 2) * localCondGrid K δ ζ R y
  else 0

end QVolTransducer


