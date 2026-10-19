-- Prove2me | Definitions.Def_StartupExit_ExitChoice_OrderStats
-- name    : StartupExit_ExitChoice_OrderStats
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:23.765162+00:00
-- url     : https://prove2.me/theorems/48a2e04f-8220-441a-a740-809b23e9e1ec
-- title:
--   §3.2, pp. 11–12 — uniform idiosyncratic values on [−1, 1]: H, h, Lemma 1's F, f, G, g, and X(1, z), X(2, z)
-- statement:
--   Each buyer's idiosyncratic valuation $v$ is drawn independently from the uniform law $\mu$ on $[-1,1]$, whose distribution function and density are
--
--   $$H(x)=\frac{x+1}{2},\qquad h(x)=\frac12 .$$
--
--   For $z$ independent draws, the distribution functions and densities of the highest and of the second-highest draw are, by Lemma 1 of the paper,
--
--   $$F(x,z)=H(x)^z,\qquad f(x,z)=zH(x)^{z-1}h(x),$$
--
--   $$G(x,z)=zH(x)^{z-1}-(z-1)H(x)^z,\qquad g(x,z)=z(z-1)H(x)^{z-2}\bigl(1-H(x)\bigr)h(x).$$
--
--   The expected highest and second-highest values are
--
--   $$X(1,z)=\int_{-1}^{1}x\,f(x,z)\,dx,\qquad X(2,z)=\int_{-1}^{1}x\,g(x,z)\,dx .$$
--
--   The uniform probability measure $\mu$ (one half of Lebesgue measure restricted to $[-1,1]$) is defined as well, so that Lemma 1 can be stated as a theorem about $z$ independent draws.
--
--   These objects carry the auction payoffs of the whole model: the seller's expected revenue with $z$ bidders is $w+X(2,z)$ and a bidder's expected surplus is $\frac1z[X(1,z)-X(2,z)]$.
--
--   **Formalization Note** $F,f,G,g$ are given by Lemma 1's closed forms; their identification with the order statistics of $\mu^{\otimes z}$ is the separate theorem `lemma_1`. $X(1,z)$ and $X(2,z)$ are integrals, not Lemma 3's closed forms, which are the separate theorem `lemma_3`. The exponents $z-1$ and $z-2$ are natural-number subtractions and are meaningful for $z\ge1$ and $z\ge2$ respectively; every use in the mission has $z\in\{m,n\}$ with $2\le m<n$. Coefficients such as $z-1$ are computed in $\mathbb R$. $H$ is not clamped outside $[-1,1]$; it is only evaluated on $[-1,1]$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), pp. 10–12 (PDF 11–13), §3.1 (uniform v on [−1, 1]), §3.2, Lemma 1

import Mathlib

open MeasureTheory

namespace StartupExit.ExitChoice

/-- The uniform law on `[-1, 1]`: one half of Lebesgue measure restricted to `[-1, 1]`. -/
noncomputable def unifMeasure : Measure ℝ :=
  (2 : ENNReal)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

/-- The distribution function `H(x) = (x + 1) / 2` of the uniform law on `[-1, 1]`
(only evaluated on `[-1, 1]`). -/
noncomputable def H (x : ℝ) : ℝ := (x + 1) / 2

/-- The density `h = 1 / 2` of the uniform law on `[-1, 1]`. -/
noncomputable def h : ℝ := 1 / 2

/-- `F(x, z) = H(x)^z`, Lemma 1 (i): distribution function of the highest of `z` draws. -/
noncomputable def Fcdf (x : ℝ) (z : ℕ) : ℝ := H x ^ z

/-- `f(x, z) = z H(x)^(z-1) h(x)`, Lemma 1 (i): its density (used for `z ≥ 1`). -/
noncomputable def fdens (x : ℝ) (z : ℕ) : ℝ := (z : ℝ) * H x ^ (z - 1) * h

/-- `G(x, z) = z H(x)^(z-1) - (z-1) H(x)^z`, Lemma 1 (ii): distribution function of the
second highest of `z` draws (used for `z ≥ 2`). -/
noncomputable def Gcdf (x : ℝ) (z : ℕ) : ℝ :=
  (z : ℝ) * H x ^ (z - 1) - ((z : ℝ) - 1) * H x ^ z

/-- `g(x, z) = z (z-1) H(x)^(z-2) (1 - H(x)) h(x)`, Lemma 1 (ii): its density
(used for `z ≥ 2`). -/
noncomputable def gdens (x : ℝ) (z : ℕ) : ℝ :=
  (z : ℝ) * ((z : ℝ) - 1) * H x ^ (z - 2) * (1 - H x) * h

/-- `X(1, z)`: expected highest of `z` i.i.d. uniform draws on `[-1, 1]`,
`∫_{-1}^{1} x f(x, z) dx`. -/
noncomputable def X1 (z : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, x * fdens x z

/-- `X(2, z)`: expected second highest of `z` i.i.d. uniform draws on `[-1, 1]`,
`∫_{-1}^{1} x g(x, z) dx`. -/
noncomputable def X2 (z : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, x * gdens x z

end StartupExit.ExitChoice


