-- Prove2me | Definitions.Def_PorteusGenSS_conv
-- name    : PorteusGenSS_conv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:52.055566+00:00
-- url     : https://prove2.me/theorems/2c0c96b5-5f33-4805-ad2c-04a86f1c3f80
-- title:
--   Convolution $f*g$
-- statement:
--   For $f,g:\mathbb R\to\mathbb R$ the **convolution** is
--
--   $$
--   (f*g)(y)=\int_{-\infty}^{\infty}f(y-\xi)\,g(\xi)\,d\xi .
--   $$
--
--   With $g=\varphi$ the demand density, $(m*\varphi)(y)$ is the expected one-period cost when the inventory after ordering is $y$.
--
--   **Formalization Note** The integral is the Lebesgue (Bochner) integral, which Lean sets to $0$ when the integrand is not integrable; every statement of the mission applies it only where the integrand is integrable.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §X Summary of Terminology, p. 425

import Mathlib

open MeasureTheory

namespace PorteusGenSS

/-- **Convolution (§X).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §X Summary of Terminology, p. 425: "Convolution shorthand is utilized; i.e.,
f∗g(y) = [f∗g](y) = ∫_{−∞}^∞ f(y − x)g(x) dx."

`conv f g y = ∫ ξ, f (y - ξ) * g ξ`, the Lebesgue integral over ℝ.

**Formalization Note.** This is Mathlib's Bochner integral, which is `0` when the integrand is
not integrable. Every statement of the mission applies `conv` only under hypotheses that make
the integrand integrable (PF-integrability, as in the paper), so this default value is not
reached there. -/
noncomputable def conv (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ ξ, f (y - ξ) * g ξ

end PorteusGenSS


