-- Prove2me | Definitions.Def_FixedPriceTrade_Supplement_J2
-- name    : FixedPriceTrade_Supplement_J2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:15:59.818419+00:00
-- url     : https://prove2.me/theorems/f60ea853-d881-4443-8405-e423dbd2a595
-- title:
--   The two-unit pricing functional: $\bar L_i$, $g_i$, potentials, compensations, $\mathcal T_{d,\vartheta}$, $\varpi_{d,\vartheta}$ and $\mathcal J^{(2)}_d$
-- statement:
--   Fix buyer bodies $Z_1\ge_{\mathrm{st}}Z_2$ supported on $[0,\bar b]$, with survival functions $H_i(s)=\Pr(Z_i>s)$ (so $H_1\ge H_2$), and $d>0$. For $s,z\ge0$ let
--   $$
--   \bar L_i(s)=1+\mathbb E(Z_i-s)_+,\qquad g_i(s,z)=\mathbf 1\{s<z\}\big[1+\mathbb E\big((Z_i-s)\mathbf 1\{z\le Z_i\}\big)\big].
--   $$
--   For a cumulative price mass $\varpi$ on $[0,\bar b]$ define the gain and seller potential of unit $i$,
--   $$
--   G^\varpi_i(s)=\bar L_i(s)\varpi(s)-\int_{(s,\bar b]}(t-s)\varpi(t)\,(-dH_i(t)),\qquad \psi^\varpi_i(s)=d\,s-\bar L_i(s)+G^\varpi_i(s).
--   $$
--   The set $\mathcal V$ of **compensations** consists of the bounded, nondecreasing, right-continuous $\vartheta:[0,\bar b]\to\mathbb R$. A nonnegative, nonincreasing, bounded $\varpi$ is a **feasible cumulative mass** for $\vartheta$ if $\psi^\varpi_1\ge-\vartheta$ and $\psi^\varpi_2\ge\vartheta$ on $[0,\bar b]$. With $\epsilon_1=-1$, $\epsilon_2=1$, define on bounded Borel $\varpi$
--   $$
--   \mathcal A_{i,d,\vartheta}\varpi(t)=1-\frac{d\,t}{\bar L_i(t)}+\frac{\epsilon_i\vartheta(t)}{\bar L_i(t)}+\frac{\int_{(t,\bar b]}(v-t)\varpi(v)\,(-dH_i(v))}{\bar L_i(t)},\qquad
--   (\mathcal T_{d,\vartheta}\varpi)(s)=\sup_{s\le t\le\bar b}\max\{0,\mathcal A_{1,d,\vartheta}\varpi(t),\mathcal A_{2,d,\vartheta}\varpi(t)\}.
--   $$
--   Let $\varpi_{d,\vartheta}$ be the pointwise least feasible cumulative mass, and
--   $$
--   \mathcal J^{(2)}_d(H_1,H_2)=\min_{\vartheta\in\mathcal V}\varpi_{d,\vartheta}(0).
--   $$
--   Finally, a **price probability with bounded support** is a probability measure on prices $z\ge0$ carried by a bounded interval, and condition (62) at $(\beta,d)$ asks
--   $$
--   \sum_{i=1}^2\int g_i(s_i,z)\,\pi(dz)\ \ge\ \beta\sum_{i=1}^2\bar L_i(s_i)-\beta d(s_1+s_2)\qquad(0\le s_1\le s_2).
--   $$
--
--   These objects describe the least total price mass that meets a welfare target against every ordered pair of seller costs; Theorem E characterizes them.
--
--   **Formalization Note** The buyer pair is given by the marginal laws $\mu_1,\mu_2$ of $Z_1,Z_2$ (only they enter); $-dH_i$ is $\mu_i$ and $H_1\ge H_2$ is $\mu_2(s,\infty)\le\mu_1(s,\infty)$. Functions are defined on $\mathbb R$ and only their values on $[0,\bar b]$ matter. The paper introduces $\varpi_{d,\vartheta}$ as the fixed point of $\mathcal T_{d,\vartheta}$; here it is the pointwise infimum of feasible masses, and Theorem E(i) asserts that it is that fixed point. Feasibility does not require right-continuity. $\bar b$ is an explicit argument of $\mathcal J^{(2)}_d$. The minimum is written as an infimum whose attainment is Theorem E(ii).
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 2683234615efe3b875b8a3f0cde6b0637c6b82cf550767823ebc24d5cd1bca0e), §13.3, (58), p.27; (59)–(61), p.28; (62), Theorem E(iii), p.28 (PDF pp.27–28)

import Mathlib

set_option autoImplicit false

namespace FixedPriceTrade.Supplement

open MeasureTheory Set

/-- **An ordered buyer pair supported on `[0, b̄]`** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
§13.3, p.27: buyer bodies `Z₁ ≥_st Z₂` supported on `[0, b̄]`, `Hᵢ(s) = Pr(Zᵢ > s)`.

`μ₁`, `μ₂` are the marginal laws of `Z₁`, `Z₂`.

**Formalization Note.** Only the marginal laws enter the pricing functional (p.27), so the pair is
given by its two marginals; `Z₁ ≥_st Z₂` is `H₁ ≥ H₂` pointwise, `μ₂(s, ∞) ≤ μ₁(s, ∞)`. The buyer
Stieltjes measure `−dHᵢ` is the law `μᵢ`. -/
def IsBuyerPair (μ1 μ2 : Measure ℝ) (b : ℝ) : Prop :=
  IsProbabilityMeasure μ1 ∧ IsProbabilityMeasure μ2 ∧
    μ1 (Icc 0 b)ᶜ = 0 ∧ μ2 (Icc 0 b)ᶜ = 0 ∧ ∀ s : ℝ, μ2 (Ioi s) ≤ μ1 (Ioi s)

/-- `L̄ᵢ(s) = 1 + E(Zᵢ − s)₊` ((58), p.27); always `≥ 1`. -/
noncomputable def Lbar (μ : Measure ℝ) (s : ℝ) : ℝ := 1 + ∫ v, max (v - s) 0 ∂μ

/-- `gᵢ(s, z) = 1{s < z}[1 + E((Zᵢ − s) 1{z ≤ Zᵢ})]` ((58), p.27). -/
noncomputable def gUnit (μ : Measure ℝ) (s z : ℝ) : ℝ :=
  (if s < z then 1 else 0) * (1 + ∫ v, (v - s) * (if z ≤ v then 1 else 0) ∂μ)

/-- The kernel integral `∫_{(t, b̄]} (v − t) ϖ(v) (−dHᵢ(v))` of (59)–(60). -/
noncomputable def kernelInt (μ : Measure ℝ) (b : ℝ) (ϖ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v in Ioc t b, (v - t) * ϖ v ∂μ

/-- The gain `G^ϖᵢ(s) = L̄ᵢ(s)ϖ(s) − ∫_{(s,b̄]} (t − s)ϖ(t)(−dHᵢ(t))` ((59), p.28). -/
noncomputable def gainMass (μ : Measure ℝ) (b : ℝ) (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  Lbar μ s * ϖ s - kernelInt μ b ϖ s

/-- The seller potential `ψ^ϖᵢ(s) = d·s − L̄ᵢ(s) + G^ϖᵢ(s)` ((59), p.28). -/
noncomputable def potential (μ : Measure ℝ) (b d : ℝ) (ϖ : ℝ → ℝ) (s : ℝ) : ℝ :=
  d * s - Lbar μ s + gainMass μ b ϖ s

/-- The compensations `V` (p.28): bounded, nondecreasing, right-continuous `ϑ : [0, b̄] → ℝ`.

**Formalization Note.** `ϑ` is a function on `ℝ` of which only the values on `[0, b̄]` matter;
right-continuity is within `[s, b̄]` at each `s ∈ [0, b̄]`. -/
def IsCompensation (b : ℝ) (ϑ : ℝ → ℝ) : Prop :=
  BddAbove (ϑ '' Icc 0 b) ∧ BddBelow (ϑ '' Icc 0 b) ∧ MonotoneOn ϑ (Icc 0 b) ∧
    ∀ s ∈ Icc 0 b, ContinuousWithinAt ϑ (Icc s b) s

/-- A **feasible cumulative mass** for the compensation `ϑ` (pp.27–28): a nonnegative,
nonincreasing, bounded `ϖ` on `[0, b̄]` with `ψ^ϖ₁ ≥ −ϑ` and `ψ^ϖ₂ ≥ ϑ` on `[0, b̄]`.

**Formalization Note.** Right-continuity is not imposed: a mass coming from a price is
right-continuous, but leastness in Theorem E(i) is stated against this larger class. -/
def IsFeasibleMass (μ1 μ2 : Measure ℝ) (b d : ℝ) (ϑ ϖ : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 b, 0 ≤ ϖ s) ∧ AntitoneOn ϖ (Icc 0 b) ∧ BddAbove (ϖ '' Icc 0 b) ∧
    ∀ s ∈ Icc 0 b, -ϑ s ≤ potential μ1 b d ϖ s ∧ ϑ s ≤ potential μ2 b d ϖ s

/-- `A_{i,d,ϑ}ϖ(t) = 1 − d·t/L̄ᵢ(t) + εᵢϑ(t)/L̄ᵢ(t) + ∫_{(t,b̄]}(v − t)ϖ(v)(−dHᵢ(v))/L̄ᵢ(t)`
((60), p.28), with the sign `ε` passed explicitly (`ε₁ = −1`, `ε₂ = 1`). -/
noncomputable def Aop (μ : Measure ℝ) (b d ε : ℝ) (ϑ ϖ : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - d * t / Lbar μ t + ε * ϑ t / Lbar μ t + kernelInt μ b ϖ t / Lbar μ t

/-- The operator `(T_{d,ϑ}ϖ)(s) = sup_{s ≤ t ≤ b̄} max{0, A_{1,d,ϑ}ϖ(t), A_{2,d,ϑ}ϖ(t)}`
((60), p.28), acting on bounded Borel `ϖ` on `[0, b̄]`.

**Formalization Note.** The supremum is Lean's `sSup` over `t ∈ [s, b̄]`; for bounded Borel `ϖ`
and bounded `ϑ` the set is nonempty (for `s ∈ [0, b̄]`) and bounded, so this is the real
supremum. Values at `s ∉ [0, b̄]` are irrelevant. -/
noncomputable def Tmass (μ1 μ2 : Measure ℝ) (b d : ℝ) (ϑ : ℝ → ℝ) (ϖ : ℝ → ℝ) : ℝ → ℝ :=
  fun s => sSup ((fun t => max 0 (max (Aop μ1 b d (-1) ϑ ϖ t) (Aop μ2 b d 1 ϑ ϖ t))) '' Icc s b)

/-- `ϖ_{d,ϑ}`, the pointwise least feasible cumulative mass (Theorem E(i), p.28): at each `s`, the
infimum of `ϖ(s)` over feasible masses `ϖ`.

**Formalization Note.** The paper introduces `ϖ_{d,ϑ}` as the fixed point of `T_{d,ϑ}` and proves
it is the pointwise least feasible mass. Here it is defined as the pointwise infimum, and
Theorem E(i) asserts that this function is feasible, is the unique bounded Borel fixed point of
`T_{d,ϑ}` on `[0, b̄]`, and is the uniform limit of the iterates from zero. -/
noncomputable def fixedMass (μ1 μ2 : Measure ℝ) (b d : ℝ) (ϑ : ℝ → ℝ) : ℝ → ℝ :=
  fun s => sInf {x : ℝ | ∃ ϖ : ℝ → ℝ, IsFeasibleMass μ1 μ2 b d ϑ ϖ ∧ ϖ s = x}

/-- **The pricing functional** `J^{(2)}_d(H₁, H₂) = min_{ϑ ∈ V} ϖ_{d,ϑ}(0)` ((61), p.28).

**Formalization Note.** `b̄` is an explicit argument (the paper proves in Appendix B.4 that the
value does not depend on it); the buyer pair is given by its marginal laws. The minimum is written
as `sInf`; Theorem E(ii) asserts that it is attained. -/
noncomputable def J2 (μ1 μ2 : Measure ℝ) (b d : ℝ) : ℝ :=
  sInf {x : ℝ | ∃ ϑ : ℝ → ℝ, IsCompensation b ϑ ∧ fixedMass μ1 μ2 b d ϑ 0 = x}

/-- A **price probability with bounded support** (Theorem E(iii), p.28): a probability measure on
prices `z ≥ 0` (mass at the zero price allowed) carried by some bounded interval. -/
def IsPriceProb (π : Measure ℝ) : Prop :=
  IsProbabilityMeasure π ∧ π (Iio 0) = 0 ∧ ∃ R : ℝ, π (Ioi R) = 0

/-- The price condition (62), p.28: for all `0 ≤ s₁ ≤ s₂`,
`Σᵢ ∫ gᵢ(sᵢ, z) π(dz) ≥ β Σᵢ L̄ᵢ(sᵢ) − βd(s₁ + s₂)`. -/
def Satisfies62 (μ1 μ2 : Measure ℝ) (β d : ℝ) (π : Measure ℝ) : Prop :=
  ∀ s1 s2 : ℝ, 0 ≤ s1 → s1 ≤ s2 →
    β * (Lbar μ1 s1 + Lbar μ2 s2) - β * d * (s1 + s2) ≤
      (∫ z, gUnit μ1 s1 z ∂π) + ∫ z, gUnit μ2 s2 z ∂π

end FixedPriceTrade.Supplement


