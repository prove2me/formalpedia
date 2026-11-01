-- Prove2me | Definitions.Def_ParetoDDO_RateFunction
-- name    : ParetoDDO_RateFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:26.228125+00:00
-- url     : https://prove2.me/theorems/68e7dba1-d6d8-430e-b158-7ddb52964859
-- title:
--   Rate functions, the LDP (Definition 3.2), good and regular rate functions (Definition 3.3)
-- statement:
--   Let $\widehat S$ be a statistic with closed state space $\mathbb S$ and $\mathbb S_\infty=S_\infty(\Theta)$.
--
--   1. **Definition 3.1.** $I:\mathbb S\times\operatorname{cl}\Theta\to[0,\infty]$ is a rate function if $s\mapsto I(s,\theta)$ is lower semicontinuous on $\mathbb S$ for every $\theta\in\operatorname{cl}\Theta$.
--   2. **Definition 3.2 (LDP).** $\widehat S$ satisfies an LDP with rate function $I$ if for all $\theta\in\Theta$ and Borel $\mathcal D\subseteq\mathbb S$
--   $$
--   -\inf_{s\in\operatorname{int}\mathcal D}I(s,\theta)\le\liminf_{T\to\infty}\frac1T\log\mathbb P_\theta[\widehat S_T\in\mathcal D]\le\limsup_{T\to\infty}\frac1T\log\mathbb P_\theta[\widehat S_T\in\mathcal D]\le-\inf_{s\in\operatorname{cl}\mathcal D}I(s,\theta),
--   $$
--   with interior and closure in the subspace topology of $\mathbb S$.
--   3. $I$ is **good** if $\{s\in\mathbb S:I(s,\theta)\le\rho\}$ is compact for all $\rho\ge0$ and $\theta\in\Theta$.
--   4. **Definition 3.3 (regular).** A rate function $I$ is regular if (i) $\operatorname{cl}\{\theta\in\Theta:I(s,\theta)<\rho\}=\{\theta\in\operatorname{cl}\Theta:I(s,\theta)\le\rho\}$ for all $s\in\mathbb S_\infty$ and $\rho>0$; (ii) $I$ is continuous on $\mathbb S\times\Theta$; (iii) $\{(s,\theta)\in\mathbb S\times\operatorname{cl}\Theta:I(s,\theta)\le\rho\}$ is compact for every $\rho\ge0$.
--
--   Regularity is what makes the distributionally robust predictor continuous and optimal.
--
--   **Formalization Note** $I$ is a $[0,\infty]$-valued function on $\mathbb R^d\times\mathbb R^d$; only its values on $\mathbb S\times\operatorname{cl}\Theta$ are read. The relative interior of $\mathcal D$ in $\mathbb S$ is `relInterior S D`; the relative closure is `closure D ∩ S`. Infima are taken in $[0,\infty]$ (the empty infimum is $+\infty$) and logarithms in $[-\infty,\infty]$. The radius $\rho$ of (i) and (iii) is a bound variable, written $r$ in the paper; it is not the risk parameter.
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Definitions 3.1–3.2, p.19; Definition 3.3, pp.19–20; good rate function, p.20

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ParetoDDO

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- **Definition 3.1** (rate function; arXiv:2010.06606v4, p.19). `I : S × cl Θ → [0, ∞]` is a rate
function if `I(s, θ)` is lower semicontinuous in `s` throughout `S × cl Θ`, i.e. `s ↦ I(s, θ)` is
lower semicontinuous on `S` for every `θ ∈ cl Θ`.

**Formalization Note** `I` is a function on `ℝ^d × ℝ^d`; only its values on `S × cl Θ` matter. -/
def IsRateFunction (S Θ : Set (Vec d)) (I : Vec d → Vec d → ℝ≥0∞) : Prop :=
  ∀ θ ∈ closure Θ, LowerSemicontinuousOn (fun s => I s θ) S

/-- The interior of `D` relative to `S` (in the subspace topology of `S`): the points `s ∈ S` with an
open `U ∋ s` such that `U ∩ S ⊆ D` (arXiv:2010.06606v4, §3.1, p.19). -/
def relInterior (S D : Set (Vec d)) : Set (Vec d) :=
  {s | s ∈ S ∧ ∃ U : Set (Vec d), IsOpen U ∧ s ∈ U ∧ U ∩ S ⊆ D}

/-- **Definition 3.2** (large deviation principle; arXiv:2010.06606v4, p.19). The statistic `Ŝ` with
state space `S` satisfies an LDP with rate function `I` if, for all `θ ∈ Θ` and Borel `D ⊆ S`,
`−inf_{s ∈ int D} I(s, θ) ≤ liminf_T (1/T) log P_θ[Ŝ_T ∈ D]` (3.1a) and
`limsup_T (1/T) log P_θ[Ŝ_T ∈ D] ≤ −inf_{s ∈ cl D} I(s, θ)` (3.1b).

**Formalization Note** `int D` and `cl D` are taken in the subspace topology of `S` (§3.1 works in
"the subspace topology on S induced by the Euclidean topology"); `cl D` in `S` is `closure D ∩ S`.
Logarithms are `ENNReal.log` into `[−∞, ∞]` (`log 0 = −∞`) and infima are in `[0, ∞]`
(the empty infimum is `+∞`). The middle inequality `liminf ≤ limsup` of (3.1) always holds. -/
def IsLDP (P : Vec d → Measure Ω) (Θ : Set (Vec d)) (Ŝ : ℕ → Ω → Vec d) (S : Set (Vec d))
    (I : Vec d → Vec d → ℝ≥0∞) : Prop :=
  ∀ θ ∈ Θ, ∀ D : Set (Vec d), MeasurableSet D → D ⊆ S →
    -(((⨅ s ∈ relInterior S D, I s θ : ℝ≥0∞)) : EReal) ≤
        liminf (fun T : ℕ => (((T : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P θ (Ŝ T ⁻¹' D))) atTop ∧
      limsup (fun T : ℕ => (((T : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P θ (Ŝ T ⁻¹' D))) atTop ≤
        -(((⨅ s ∈ closure D ∩ S, I s θ : ℝ≥0∞)) : EReal)

/-- A **good** rate function (arXiv:2010.06606v4, p.20): `{s ∈ S : I(s, θ) ≤ r}` is compact for every
`r ≥ 0` and `θ ∈ Θ`. -/
def IsGoodRateFunction (S Θ : Set (Vec d)) (I : Vec d → Vec d → ℝ≥0∞) : Prop :=
  ∀ θ ∈ Θ, ∀ ρ : ℝ≥0, IsCompact {s | s ∈ S ∧ I s θ ≤ ρ}

/-- **Definition 3.3** (regular rate function; arXiv:2010.06606v4, pp.19–20). A rate function `I` is
regular if
(i) (radial monotonicity in `θ`) `cl{θ ∈ Θ : I(s, θ) < ρ} = {θ ∈ cl Θ : I(s, θ) ≤ ρ}` for all
`s ∈ S∞ = {S∞(θ) : θ ∈ Θ}` and `ρ > 0`;
(ii) (continuity) `I` is continuous on `S × Θ`;
(iii) (level-compactness) `{(s, θ) ∈ S × cl Θ : I(s, θ) ≤ ρ}` is compact for every `ρ ≥ 0`.

**Formalization Note** The radius `ρ` of (i) and (iii) is a bound variable (the paper writes `r`); it
is not the risk-aversion parameter. Continuity in (ii) is as a `[0, ∞]`-valued map. -/
structure IsRegularRateFunction (S Θ : Set (Vec d)) (Sinf : Vec d → Vec d)
    (I : Vec d → Vec d → ℝ≥0∞) : Prop where
  /-- `I` is a rate function (Definition 3.1). -/
  isRateFunction : IsRateFunction S Θ I
  /-- (i) Radial monotonicity in `θ`. -/
  radial : ∀ s ∈ Sinf '' Θ, ∀ ρ : ℝ≥0, 0 < ρ →
    closure {θ | θ ∈ Θ ∧ I s θ < ρ} = {θ | θ ∈ closure Θ ∧ I s θ ≤ ρ}
  /-- (ii) Continuity on `S × Θ`. -/
  continuousOn : ContinuousOn (fun p : Vec d × Vec d => I p.1 p.2) (S ×ˢ Θ)
  /-- (iii) Level-compactness on `S × cl Θ`. -/
  levelCompact : ∀ ρ : ℝ≥0,
    IsCompact {p : Vec d × Vec d | p ∈ S ×ˢ closure Θ ∧ I p.1 p.2 ≤ ρ}

end ParetoDDO


