-- Prove2me | Definitions.Def_ProperHalfspace_AffineERM
-- name    : ProperHalfspace_AffineERM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:44.945708+00:00
-- url     : https://prove2.me/theorems/36560714-ac71-4b1f-b14b-0f7403e3429d
-- title:
--   Empirical and true error of affine halfspaces after a feature map
-- statement:
--   For $\varphi_1,\dots,\varphi_m\in\mathbb R^D$ and labels $y_1,\dots,y_m\in[-1,1]$, the empirical error of the affine halfspace $h(\varphi)=\operatorname{sign}(w\cdot\varphi-\theta)$ is
--   $$\widehat{\mathrm{err}}_S(h\circ\Phi)=\frac1m\sum_{j=1}^m\frac{1-y_jh(\varphi_j)}2.$$
--   For a distribution $P$ on $\{\pm1\}^n\times[-1,1]$ and a map $\Phi:\{\pm1\}^n\to\mathbb R^D$, the true error is $\mathbf E_{(x,y)\sim P}[(1-y\,h(\Phi(x)))/2]$.
--
--   On labels $y=\pm1$ these are the indicator errors $\mathbf 1\{h\ne y\}$.
--
--   **Formalization Note** $P$ is a probability measure on `Cube n × ℝ` carried by labels in $[-1,1]$. The cube's σ-algebra is discrete, so $\Phi$ needs no measurability hypothesis.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 10, pp.16–17

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace

open MeasureTheory

namespace ProperHalfspace

/-!
# Empirical and true error of affine halfspaces after a feature map

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Proposition 10, pp.16–17.

**Formalization Note.** The errors are the weighted ones of the last sentence of Proposition 10,
`(1 − y h)/2`, which on labels `y = ±1` equal the page's indicators `1{h ≠ y}`. A distribution on `{±1}ⁿ × [−1, 1]` is a
probability measure on `Cube n × ℝ` carried by the labels `[−1, 1]`. The cube's σ-algebra is discrete.
-/

/-- The affine halfspace `h(φ) = sign(w · φ − θ)` on `ℝᴰ`. -/
noncomputable def affineSign {D : ℕ} (w : Fin D → ℝ) (θ : ℝ) (φ : Fin D → ℝ) : ℝ :=
  sgn (∑ i, w i * φ i - θ)

/-- The weighted empirical error `(1/m) Σ_j (1 − y_j h(φ_j))/2` on mapped points. -/
noncomputable def empErr {m D : ℕ} (φ : Fin m → Fin D → ℝ) (y : Fin m → ℝ) (w : Fin D → ℝ) (θ : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, (1 - y j * affineSign w θ (φ j)) / 2

/-- The weighted true error `E_{(x,y)∼P}[(1 − y h(Φ(x)))/2]`. -/
noncomputable def popErr {n D : ℕ} (P : Measure (Cube n × ℝ)) (Φ : Cube n → Fin D → ℝ)
    (w : Fin D → ℝ) (θ : ℝ) : ℝ :=
  ∫ p, (1 - p.2 * affineSign w θ (Φ p.1)) / 2 ∂P

end ProperHalfspace


