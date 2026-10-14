-- Prove2me | Definitions.Def_CostlyShort_OneAsset_Setting
-- name    : CostlyShort_OneAsset_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:48.818793+00:00
-- url     : https://prove2.me/theorems/d772d0a1-3f34-4147-8df0-11d4ba533de2
-- title:
--   §3.3 and §4.1, pp. 22, 27 and 50 — shorting region s > s*, the one-asset system (29)–(30), closed forms (31)–(32), quadratic g
-- statement:
--   This file fixes the objects of the one-risky-asset economy of Evgeniou, Hugonnier and Prieto at a single state. Let $\sigma>0$ be the volatility of aggregate consumption, let $\delta=\sigma\Delta=\mu^{(o)}-\mu^{(p)}\ge 0$ be the unscaled difference in beliefs between the optimist $o$ and the pessimist $p$, and let $s\in(0,1)$ be the optimist's consumption share. The **shorting region** is the set of shares above the threshold
--   $$
--   s^*=\min\Big\{1,\frac{\sigma}{\Delta}\Big\}=\min\Big\{1,\frac{\sigma^2}{\delta}\Big\},
--   $$
--   and on $s\in(0,1)$ the condition $s>s^*$ is equivalent to $\sigma^2<s\delta$ (when $\delta=0$ the region is empty).
--
--   1. The **equilibrium shorting cost** (31) is
--   $$
--   \Phi(\sigma,\delta,s)=\mathbb 1_{\{s>s^*\}}\,\frac{s(1-s)\delta-2\sigma^2+\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2(1-s)}.
--   $$
--   2. The **equilibrium lending yield** (32) is
--   $$
--   \Gamma(\sigma,\delta,s)=\mathbb 1_{\{s>s^*\}}\,\frac{-s\big((1-s)^2\delta+4\sigma^2\big)+(1+s)\sqrt{s^2(1-s)^2\delta^2+4\sigma^4 s}}{2s(1-s)}.
--   $$
--   3. A pair $(\Phi,\Gamma)$ **solves the one-asset system** (29)–(30) if
--   $$
--   \Phi=\mathbb 1_{\{s>s^*\}}\frac{(\delta+\Gamma)s-\sigma^2}{1+s},\qquad
--   \Gamma=\mathbb 1_{\{s>s^*\}}\frac{(1-s)(s\delta-\Gamma-\sigma^2)\big((\delta+\Gamma)s-\sigma^2\big)}{\sigma^2(1+s)^2}.
--   $$
--   4. The **quadratic** of the proof of Proposition 3, in units per unit of volatility ($\gamma=\Gamma/\sigma$, $\Delta=\delta/\sigma$), is
--   $$
--   g(\gamma)=(1-s)(s\Delta-\gamma-\sigma)\big((\gamma+\Delta)s-\sigma\big)-\gamma\sigma(1+s)^2.
--   $$
--
--   These are the objects of Proposition 3: the system (29)–(30) is what the equilibrium conditions of the paper reduce to when the single risky asset is the market portfolio, and (31)–(32) are its closed-form solution.
--
--   **Formalization Note** The indicator $\mathbb 1_{\{s>s^*\}}$ is encoded as the test $\sigma^2<s\delta$, never as $s>\min\{1,\sigma/\Delta\}$, because Lean's $\sigma/0=0$ would turn every $s>0$ into a shorting state when $\Delta=0$; the two agree for $\sigma>0$, $\delta\ge 0$, $s\in(0,1)$. The definitions are total functions of real numbers; every theorem that uses them assumes $\sigma>0$ and $0<s<1$, where the divisions by $1-s$, $s(1-s)$ and $\sigma^2(1+s)^2$ are non-degenerate and the radicand is at least $4\sigma^4 s>0$. The continuous-time economy (consumption, Brownian motion, portfolios) from which (29)–(30) are derived is not formalized.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), §3.3, p. 22 (threshold s*); §4.1, p. 27, (29)–(32); App. A, proof of Proposition 3, p. 50 (g)

import Mathlib

namespace CostlyShort.OneAsset

/-- (31), p. 27: the equilibrium shorting cost `Φ` as a function of the volatility `σ`, the
unscaled belief gap `δ` and the optimist's consumption share `s`. The guard `σ ^ 2 < s * δ` is the
shorting region `s > s* = min {1, σ / Δ}` (with `δ = σ Δ`) for `s ∈ (0, 1)`, `σ > 0`, `δ ≥ 0`. -/
noncomputable def costOne (σ δ s : ℝ) : ℝ :=
  if σ ^ 2 < s * δ then
    (s * (1 - s) * δ - 2 * σ ^ 2 + Real.sqrt (s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s)) / (2 * (1 - s))
  else 0

/-- (32), p. 27: the equilibrium lending yield `Γ`, with the same guard as `costOne`. -/
noncomputable def yieldOne (σ δ s : ℝ) : ℝ :=
  if σ ^ 2 < s * δ then
    (-(s * ((1 - s) ^ 2 * δ + 4 * σ ^ 2)) + (1 + s) * Real.sqrt (s ^ 2 * (1 - s) ^ 2 * δ ^ 2 + 4 * σ ^ 4 * s))
      / (2 * s * (1 - s))
  else 0

/-- (29)–(30), p. 27: the pair `(Φ, Γ)` solves the one-asset equilibrium system at consumption
share `s`, volatility `σ` and belief gap `δ`. -/
def IsOneAssetSystem (σ δ s Φ Γ : ℝ) : Prop :=
  Φ = (if σ ^ 2 < s * δ then ((δ + Γ) * s - σ ^ 2) / (1 + s) else 0) ∧
  Γ = (if σ ^ 2 < s * δ then
        (1 - s) * (s * δ - Γ - σ ^ 2) * ((δ + Γ) * s - σ ^ 2) / (σ ^ 2 * (1 + s) ^ 2) else 0)

/-- Proof of Proposition 3, p. 50: the quadratic
`g(γ) = (1 − s)(sΔ − γ − σ)((γ + Δ)s − σ) − γσ(1 + s)²`, in units per unit of volatility. -/
def gQuad (σ Δ s γ : ℝ) : ℝ :=
  (1 - s) * (s * Δ - γ - σ) * ((γ + Δ) * s - σ) - γ * σ * (1 + s) ^ 2

end CostlyShort.OneAsset


