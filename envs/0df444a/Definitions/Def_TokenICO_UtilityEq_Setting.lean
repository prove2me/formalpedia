-- Prove2me | Definitions.Def_TokenICO_UtilityEq_Setting
-- name    : TokenICO_UtilityEq_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:00.807983+00:00
-- url     : https://prove2.me/theorems/a3802b0a-e86a-4c3f-b143-61a9fdb9ed1d
-- title:
--   Utility-token ICO model: demand, production, participation, wealth and equilibrium
-- statement:
--   The base model has $m>0$ utility tokens, unit production cost $c>0$, customer value $v>c$, and a pool of $z\ge m$ speculators. Demand $D$ has probability law $\mu$ and continuous distribution function $F$. Its support begins at zero, and on the positive interior of its support $F$ has a positive differentiable density $f$ with derivative $f'$. The quantile expression and expected sales are
--
--   $$F^{-1}(y)=\inf\{x\ge0:y\le F(x)\},\qquad S(Q)=\mathbb E_\mu[\min(D,Q)].$$
--
--   At ICO price $\tau$ and with $s$ tokens sold, production $Q$ maximizes $(m-s)(v/m)S(Q)-cQ$ over $0\le Q\le\tau s/c$. A production rule selects a maximizer in every feasible subgame. Speculator utility is $u(s)=(s/z)((v/m)S(Q(\tau,s))-\tau)$, and the simultaneous-arrival rule sells all $n$ tokens when $u(n)\ge0$, and none otherwise. The firm's wealth is $\tau s-cQ+(m-s)(v/m)S(Q)$. An equilibrium production rule is optimal after every history, and its ICO price and cap maximize that wealth over $\tau\ge0$ and $0\le n\le m$.
--
--   These definitions connect the paper's market-clearing price in Lemma 1 and participation rule in Lemma 2(i) to the production and ICO decisions. The separate technical condition from Appendix B.1 constrains $f'/f^2$ on interior quantiles for uniqueness; $Q_{\mathrm{cap}}$ is only a closed-form expression used in conclusions.
--
--   **Formalization Note** Quantities and token counts are real. The same law $\mu$ supplies both $F$ and expected sales. The paper states $F^{-1}(0)=0$; this model reads it as $F(x)=0$ for $x\le0$ and $F(x)>0$ for $x>0$. Positive differentiable density is added where the paper's proofs use it. The informal $z\gg m$ is represented by $m\le z$. The technical condition is restricted to interior quantiles, where $f'/f^2$ is defined.
-- source:
--   Gan, Tsoukalas & Netessine, Initial Coin Offerings, Speculation and Asset Tokenization, SSRN 3361121 (June 29, 2020), pp. 7–10, 12, 34, (1)–(3), (10), Lemmas 1 and 2(i)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq

/-- The standing assumptions of the utility-token model and the density regularity
used in Appendix B.1. -/
structure Standing (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ) : Prop where
  cost_pos : 0 < c
  value_gt_cost : c < v
  tokens_pos : 0 < m
  pool_ge_tokens : m ≤ z
  probability : IsProbabilityMeasure μ
  cdf_continuous : Continuous (cdf μ)
  cdf_nonpositive : ∀ x : ℝ, x ≤ 0 → cdf μ x = 0
  cdf_positive : ∀ x : ℝ, 0 < x → 0 < cdf μ x
  density : ∀ x : ℝ, 0 < x → cdf μ x < 1 →
    HasDerivAt (cdf μ) (f x) x ∧ 0 < f x ∧ HasDerivAt f (f' x) x

/-- The nonnegative inverse-cdf expression used in the paper. -/
noncomputable def Finv (μ : Measure ℝ) (y : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ y ≤ cdf μ x}

/-- Expected sales when production is `Q` and demand has law `μ`. -/
noncomputable def ES (μ : Measure ℝ) (Q : ℝ) : ℝ :=
  ∫ x, min x Q ∂μ

/-- The firm's production-period objective, for `s` tokens already sold. -/
noncomputable def prodObj (m c v : ℝ) (μ : Measure ℝ) (s Q : ℝ) : ℝ :=
  (m - s) * (v / m * ES μ Q) - c * Q

/-- A production rule that maximizes the production-period objective in every
feasible subgame. The budget is the proceeds of the ICO. -/
def ProdOptimal (m c v : ℝ) (μ : Measure ℝ) (Qr : ℝ → ℝ → ℝ) : Prop :=
  ∀ τ s : ℝ, 0 ≤ τ → 0 ≤ s → s ≤ m →
    Qr τ s ∈ Set.Icc 0 (τ * s / c) ∧
    IsMaxOn (prodObj m c v μ s) (Set.Icc 0 (τ * s / c)) (Qr τ s)

/-- The expected resale margin of one token, conditional on `s` buyers. -/
noncomputable def margin (m v : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (τ s : ℝ) : ℝ :=
  v / m * ES μ (Qr τ s) - τ

/-- Speculators' expected profit (1), including random allocation. -/
noncomputable def u (m v z : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (τ s : ℝ) : ℝ :=
  s / z * margin m v μ Qr τ s

/-- The simultaneous-arrival all-or-nothing participation rule of Lemma 2(i). -/
noncomputable def sstar (m v z : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (τ n : ℝ) : ℝ :=
  if 0 ≤ u m v z μ Qr τ n then n else 0

/-- The firm's expected terminal wealth in (3) and (10). -/
noncomputable def wealth (m c v z : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (τ n : ℝ) : ℝ :=
  let s := sstar m v z μ Qr τ n
  τ * s - c * Qr τ s + (m - s) * (v / m * ES μ (Qr τ s))

/-- A subgame-perfect equilibrium: production is optimal at every feasible
history, and the ICO design maximizes expected wealth. -/
def IsEquilibrium (m c v z : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (τ n : ℝ) : Prop :=
  ProdOptimal m c v μ Qr ∧ 0 ≤ τ ∧ 0 ≤ n ∧ n ≤ m ∧
  ∀ τ' n' : ℝ, 0 ≤ τ' → 0 ≤ n' → n' ≤ m →
    wealth m c v z μ Qr τ' n' ≤ wealth m c v z μ Qr τ n

/-- The technical uniqueness condition in Appendix B.1, on the interior of
the stated quantile range. -/
noncomputable def TechCond (c v : ℝ) (μ : Measure ℝ)
    (f f' : ℝ → ℝ) : Prop :=
  ∀ y ∈ Set.Ioo (0 : ℝ) (1 - 2 * c / v),
    let k := 1 - c / ((1 - y) * v)
    f' (Finv μ y) / (f (Finv μ y)) ^ 2 >
      -(3 * v / c) * k * ((1 - k) / (2 * k - 1))

/-- The closed-form production expression in Proposition 3(c), not the
production rule of the game. -/
noncomputable def Qcap (m c v : ℝ) (μ : Measure ℝ) (n : ℝ) : ℝ :=
  Finv μ (1 - m / (m - n) * (c / v))

/-- The two regimes of the threshold in Proposition 12(ii). This states the
properties of a threshold and does not prescribe a production rule. -/
noncomputable def IsSwitch (m c v z : ℝ) (μ : Measure ℝ)
    (Qr : ℝ → ℝ → ℝ) (nh : ℝ) : Prop :=
  (∀ n ∈ Set.Ioo (m * c / v) nh, ∀ τ : ℝ,
      0 < τ → u m v z μ Qr τ n = 0 →
        τ = v / m * ES μ (τ * n / c) ∧
        ∀ τ' : ℝ, 0 < τ' → τ' = v / m * ES μ (τ' * n / c) → τ' = τ) ∧
  (∀ n ∈ Set.Ico nh (m * (1 - c / v)), ∀ τ : ℝ,
      0 < τ → u m v z μ Qr τ n = 0 →
        τ = v / m * ES μ (Finv μ (1 - c * m / ((m - n) * v))))

end TokenICO.UtilityEq


