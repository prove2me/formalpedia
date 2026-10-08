-- Prove2me | Definitions.Def_BoundedNV_Uniform_Logit
-- name    : BoundedNV_Uniform_Logit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:04.503677+00:00
-- url     : https://prove2.me/theorems/e1788880-7277-4662-9a0f-9535060c1342
-- title:
--   §3–§4, pp. 571–572 — the logit choice density (2), its expectations, and the newsvendor profit (3)
-- statement:
--   This file fixes the boundedly rational choice model of §3 and the newsvendor profit of §4.
--
--   1. **Logit choice density** (eq. (2), p. 571). A decision maker with utility $u$ over a decision domain $S \subseteq \mathbb R$ and bounded-rationality parameter $\beta > 0$ chooses a random $Y \in S$ with density
--   $$\psi(y) = \frac{e^{u(y)/\beta}}{\int_S e^{u(v)/\beta}\,dv}, \qquad y \in S,$$
--   and $\psi(y) = 0$ for $y \notin S$.
--   2. **Logit expectation.** For a function $g$, $\mathbb E\, g(Y) = \int_{\mathbb R} g(y)\,\psi(y)\,dy$; with $g(y) = y$ this is the expected choice.
--   3. **Demand distribution function.** For a demand density $f$, $F(x) = \int_{-\infty}^{x} f(t)\,dt$.
--   4. **Expected sales.** $\mathbb E \min(D, x) = \int_{\mathbb R} \min(t, x)\, f(t)\,dt$.
--   5. **Expected profit** (eq. (3), p. 572). A newsvendor who buys $x$ copies at unit cost $c$ and sells at price $p$ earns in expectation
--   $$\pi(x) = p\,\mathbb E\min(D, x) - c x.$$
--
--   The behavioral solution $X^\flat$ of the newsvendor problem (eq. (4), p. 572) is the logit choice with utility $u = \pi$; its density is $\psi$ above with $u = \pi$.
--
--   **Formalization Note** The density is $0$ off $S$, and integrals are Lebesgue integrals over $\mathbb R$; on a bounded interval of positive length with a continuous utility, the normalizer is a genuine positive number, so no junk value enters. The parameters $\beta$, $p$, $c$ are unconstrained here; the theorems that use these objects state the paper's standing assumptions $\beta > 0$ and $0 < c < p$.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 571–572 (PDF 6–7), eqs. (2), (3), (4)

import Mathlib

namespace BoundedNV.Uniform

/-- The logit choice density (2) of a utility `u` over a decision domain `S`, with bounded-rationality
parameter `β`: `ψ(y) = e^{u(y)/β} / ∫_S e^{u(v)/β} dv` on `S`, and `0` off `S`. -/
noncomputable def logitDensity (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y

/-- `E g(Y)` for the logit choice `Y` (expected order: `g = id`; expected profit: `g = π`). -/
noncomputable def logitExp (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * logitDensity S u β y

/-- The demand distribution function `F(x) = ∫_{-∞}^{x} f`. -/
noncomputable def demandCDF (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Set.Iic x, f t

/-- `E min(D, x)`. -/
noncomputable def expMin (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, min t x * f t

/-- The newsvendor's expected profit (3): `π(x) = p E min(D, x) − c x`. -/
noncomputable def nvProfit (f : ℝ → ℝ) (p c : ℝ) (x : ℝ) : ℝ := p * expMin f x - c * x

end BoundedNV.Uniform


