-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_canonLoss
-- name    : UCalibDirichlet_Supplement_canonLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:09:17.546067+00:00
-- url     : https://prove2.me/theorems/37974dd3-6159-4ead-a83f-1fac62a0ba0a
-- title:
--   Canonical binary loss $\ell_F(p,y)=-F(p)-F'(p)(y-p)$
-- statement:
--   For a binary potential $F:[0,1]\to\mathbb R$, the **canonical loss** is
--   $$\ell_F(p,y)=-F(p)-F'(p)\,(y-p),\qquad p\in[0,1],\ y\in\{0,1\},$$
--   where $p$ is the forecast probability of label $1$ and $F'$ is the derivative of $F$ (one-sided at $p=0$ and $p=1$). Its expected loss under the true probability $p$ is $-F(p)$, so $-F$ is its Bayes risk; when $F$ is convex and differentiable on $[0,1]$, $\ell_F$ is a proper loss.
--
--   This is the loss under which the binary results of the paper (Theorems 1.14, E.1 and E.8) measure the regret of the Laplace forecaster and the minimax regret.
--
--   **Formalization Note** The loss is a function of the simplex point $q=(1-p,p)$ and the label $y$ (index $0$ or $1$), real-valued and cast to the extended reals as in the base model. $F'$ is the derivative of $F$ within $[0,1]$; the paper writes the loss for $p\in(0,1)$, and in every theorem using it $F'$ is continuous on $[0,1]$, so the endpoint values are the continuous extensions.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), App. E.1.1, p.40 (canonical loss)

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **The canonical binary loss `ℓ_F`.** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), App. E.1.1, p.40: "Write `ℓ_F(p, y) = −F(p) − F′(p)(y − p)` for the canonical loss".
Used in Theorems 1.14 (p.8), E.1 (p.41) and E.8 (p.46).

`canonLoss F q y = −F(p) − F′(p)(y − p)` with `p = q 1`, `y ∈ {0, 1}` the label (`Fin` index), and
`F′ = derivWithin F [0, 1]`.

**Formalization Note.** The loss is typed as a base-model loss `(Fin 2 → ℝ) → Fin 2 → EReal`
(real-valued). The derivative is taken within `[0, 1]`, so at `p = 0` and `p = 1` it is the
one-sided derivative; the paper writes the loss for `p ∈ (0, 1)`. In the theorems that use it,
`F` is differentiable on `[0, 1]` with continuous derivative, so the endpoint values are the
continuous extensions and change no infimum over the simplex. If `F` were not differentiable
within `[0, 1]` at `p`, `derivWithin` would be the junk value `0`; no statement uses such an `F`. -/
noncomputable def canonLoss (F : ℝ → ℝ) (q : Fin 2 → ℝ) (y : Fin 2) : EReal :=
  ((-F (q 1) - derivWithin F (Set.Icc 0 1) (q 1) * ((if y = 1 then 1 else 0) - q 1) : ℝ) : EReal)

end UCalibDirichlet.Supplement


