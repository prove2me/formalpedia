-- Prove2me | Definitions.Def_KramerSaglam_Model
-- name    : KramerSaglam_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:30.937652+00:00
-- url     : https://prove2.me/theorems/cd611cf7-8f4b-466d-9216-f202ef5f8826
-- title:
--   The noisy-cube model of Theorem 1.1, with a bit $C$ obtained from $Y$
-- statement:
--   Fix $n\ge0$, $p\in\mathbb R$ and a function $g:\{0,1\}^n\to[0,1]$. Random strings $X,Y:\Omega\to\{0,1\}^n$ and an event $C$ on a probability space form the **model** when $X,Y,C$ are measurable and, for all $x,y\in\{0,1\}^n$,
--   $$
--   P(X=x,\,Y=y,\,C)=2^{-n}K_p(x,y)\,g(y),\qquad P(X=x,\,Y=y,\,C^{\mathrm c})=2^{-n}K_p(x,y)\,(1-g(y)),
--   $$
--   where $K_p(x,y)=\prod_i\big((1-p)\mathbf 1[x_i=y_i]+p\,\mathbf 1[x_i\ne y_i]\big)$ is the noise kernel. So $X$ is uniform on $\{0,1\}^n$, $Y$ flips each coordinate of $X$ independently with probability $p$, and the bit $C$ is obtained from $Y$: given $X=x$ and $Y=y$ it equals $1$ with probability $g(y)$. The event $\{Y_i=1\}$ is the bit $Y_i$.
--
--   This is the setting of Theorem 1.1 and of Lemma 3.2. A deterministic bit $C=h(Y)$ is the case $g=\mathbf 1_{h=1}$; a general $g$ also covers the private randomness the paper allows in §1.3 and §3.1.
--
--   **Formalization Note** The model is any probability space carrying this joint law of $(X,Y,C)$; only the law enters the statements. The cube and the kernel are the published `GeneralCK.Cube` and `GeneralCK.noiseKernel`.
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §1 p.1 ("Let X be distributed uniformly on {0,1}^n and let Y be obtained by flipping each coordinate of X with probability p, independently"), Theorem 1.1 p.1

import Mathlib
import Definitions.Def_GeneralCK_statement

open MeasureTheory

namespace KramerSaglam

/-- The model of Theorem 1.1 (D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.1): `X` is uniform on `{0,1}ⁿ`, `Y` flips each coordinate of
`X` independently with probability `p`, and the bit `C` is obtained from `Y`, with
`P(C | X = x, Y = y) = g(y)`.

**Formalization Note.** A deterministic `C = h(Y)` is the case `g = 1_S`. The soft function `g` also
covers the private randomness of §1.3 and §3.1. The structure pins the joint law of `(X, Y, C)` on any
probability space carrying it. -/
structure IsModel {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) {n : ℕ} (p : ℝ)
    (g : GeneralCK.Cube n → ℝ) (X Y : Ω → GeneralCK.Cube n) (C : Set Ω) : Prop where
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  measurableSet_C : MeasurableSet C
  g_mem : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1
  mass_C : ∀ x y, P.real (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ C) =
    (2 : ℝ) ^ (-(n : ℤ)) * GeneralCK.noiseKernel p x y * g y
  mass_compl : ∀ x y, P.real (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Cᶜ) =
    (2 : ℝ) ^ (-(n : ℤ)) * GeneralCK.noiseKernel p x y * (1 - g y)

/-- The event `Y_i = 1`, the bit `Y_i` as a set. -/
def coordSet {Ω : Type*} {n : ℕ} (Y : Ω → GeneralCK.Cube n) (i : Fin n) : Set Ω :=
  {ω | Y ω i = true}

end KramerSaglam


