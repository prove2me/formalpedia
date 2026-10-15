-- Prove2me | Definitions.Def_SuperstarExcl_Complementors_Model
-- name    : SuperstarExcl_Complementors_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:28:45.735286+00:00
-- url     : https://prove2.me/theorems/d10ca010-0b6c-491a-9e33-4c9ffa4f0030
-- title:
--   Two-sided Hotelling market with a Superstar: primitives and Assumptions 1–3 (Sec. 3, pp. 7–10)
-- statement:
--   Two platforms $1$ and $2$ sit at the endpoints of a Hotelling line. A unit mass of consumers has types $m\in[-\bar m,\bar m]$, $\bar m>0$, where $m$ measures the relative preference for platform $2$. Types are distributed with cumulative distribution function $F$ and density $f$. A fringe of complementors has opportunity costs $k\ge 0$ of joining each platform, distributed with mass function $\Lambda$ and density $\lambda$. A complementor receives $\gamma>0$ per unit mass of consumers on a platform it joins, and a consumer receives $\theta>0$ per unit mass of complementors on the platform it joins.
--
--   The structure records these primitives together with the paper's standing assumptions, in the following form.
--
--   1. **Consumer distribution (Assumption 2).** $F$ is continuous and nondecreasing on $\mathbb R$, with $F(x)=0$ for $x\le-\bar m$ and $F(x)=1$ for $x\ge\bar m$. On $(-\bar m,\bar m)$ it is twice continuously differentiable, with $F'=f>0$. It is symmetric around zero: $F(-x)=1-F(x)$ for all $x$.
--   2. **Complementor distribution (Assumption 1).** $\Lambda(0)=0$, and $\Lambda$ is twice continuously differentiable with $\Lambda'=\lambda$. On $[0,\gamma]$ the density is strictly positive and nondecreasing ($\lambda'\ge 0$).
--   3. **Assumption 3.** For every $x\in(-\bar m,\bar m)$,
--   $$
--   f(x)\,\gamma\,\theta\,\bigl[\lambda(\gamma F(x))+\lambda(\gamma(1-F(x)))\bigr]<1 .
--   $$
--
--   Every result of the mission is stated for an arbitrary model of this kind. Assumption 3 bounds the cross-group externalities relative to consumer differentiation, which is normalised to $1$. It rules out tipping and makes fulfilled-expectations demand decrease in the platform's own price.
--
--   **Formalization Note** The density conditions of Assumption 1 are imposed on $[0,\gamma]$ only. Complementor masses enter the model only through $\Lambda(\gamma D)$ with $D\in[0,1]$. Moreover, $\lambda>0$ and $\lambda'\ge0$ on all of $[0,\infty)$ cannot hold for a probability distribution, so $\Lambda$ is not required to tend to $1$. The bounds $\underline{f'}<f'<\overline{f'}$ of Assumption 2 are omitted. The paper defines them (App. A.1, p. 36) as functions of unspecified equilibrium arguments, and no statement of the mission uses them. The assumption that $\bar m$ is large enough for two active platforms is replaced, in each theorem, by the requirement that the equilibria considered are interior. The standalone value $v$ cancels from every comparison and is not a parameter.
-- source:
--   Carroni, Madio & Shekhar, Superstar Exclusivity in Two-Sided Markets, accepted manuscript (hdl:11585/922035), pp. 7–8, Section 3 (Consumers, Complementors); p. 10, Assumptions 1–3

import Mathlib

namespace SuperstarExcl.Complementors

open Set

/-- Primitives of the two-sided Hotelling market of Carroni, Madio & Shekhar (Section 3) and
Assumptions 1–3 (p. 10), in the pinned-down readings recorded in the mission notes.

* Consumers have type `m ∈ [-mbar, mbar]` with c.d.f. `F` and density `f`; `F` vanishes left of
  `-mbar`, equals `1` right of `mbar`, is `C²` with derivative `f > 0` on `(-mbar, mbar)` and is
  symmetric around `0` (Assumption 2, without the bounds on `f'`).
* Complementors have opportunity cost `k ≥ 0` with mass function `Λ` and density `lam`: `Λ 0 = 0`,
  `Λ` is `C²` with `Λ' = lam`, and `lam > 0`, `lam` nondecreasing on `[0, γ]` (Assumption 1 on the
  range `[0, γ]` of the argument `γ D` that the model ever uses).
* `γ > 0` is the complementors' value of a consumer, `θ > 0` the consumers' value of a complementor.
* Assumption 3: `f(x) γ θ [lam(γ F x) + lam(γ (1 - F x))] < 1` on `(-mbar, mbar)`. -/
structure Model where
  /-- upper end `m̄` of the consumer-type support `[-m̄, m̄]` -/
  mbar : ℝ
  /-- value `γ` a complementor receives per unit mass of consumers -/
  γ : ℝ
  /-- network benefit `θ` a consumer receives per unit mass of complementors -/
  θ : ℝ
  /-- c.d.f. `F` of consumer types -/
  F : ℝ → ℝ
  /-- density `f` of consumer types -/
  f : ℝ → ℝ
  /-- c.d.f. (mass function) `Λ` of complementor opportunity costs -/
  Λ : ℝ → ℝ
  /-- density `λ` of complementor opportunity costs -/
  lam : ℝ → ℝ
  mbar_pos : 0 < mbar
  γ_pos : 0 < γ
  θ_pos : 0 < θ
  F_continuous : Continuous F
  F_monotone : Monotone F
  F_eq_zero : ∀ x, x ≤ -mbar → F x = 0
  F_eq_one : ∀ x, mbar ≤ x → F x = 1
  F_contDiffOn : ContDiffOn ℝ 2 F (Ioo (-mbar) mbar)
  F_hasDerivAt : ∀ x ∈ Ioo (-mbar) mbar, HasDerivAt F (f x) x
  f_pos : ∀ x ∈ Ioo (-mbar) mbar, 0 < f x
  F_symm : ∀ x, F (-x) = 1 - F x
  Λ_zero : Λ 0 = 0
  Λ_contDiff : ContDiff ℝ 2 Λ
  Λ_hasDerivAt : ∀ k, HasDerivAt Λ (lam k) k
  lam_pos : ∀ k ∈ Icc 0 γ, 0 < lam k
  lam_monotoneOn : MonotoneOn lam (Icc 0 γ)
  assumption3 : ∀ x ∈ Ioo (-mbar) mbar,
    f x * γ * θ * (lam (γ * F x) + lam (γ * (1 - F x))) < 1

end SuperstarExcl.Complementors


