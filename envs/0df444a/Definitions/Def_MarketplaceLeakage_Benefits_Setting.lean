-- Prove2me | Definitions.Def_MarketplaceLeakage_Benefits_Setting
-- name    : MarketplaceLeakage_Benefits_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:29.880076+00:00
-- url     : https://prove2.me/theorems/fa8af480-ad7e-4b86-a039-a1326913c9ab
-- title:
--   §3.1, §4, §5.1, pp. 5–12 — the leakage game with transaction benefits: uniform G, seller profit with benefit b, seller-optimal prices, M's profit with K(b) = (k/2)b², optima, μ̄
-- statement:
--   A single marketplace $M$, a single seller $S$ and a unit mass of buyers with unit demand. Every buyer values $S$'s product at $v$, $S$'s marginal cost is $c$ with $c < v$, and buyers' outside option is worth $0$. A buyer who buys directly from $S$ rather than on $M$ bears a switching cost $s$, distributed uniformly on $[0,\mu]$, $\mu > 0$:
--
--   $$
--   G(s) = \min\{\max\{s/\mu,\, 0\},\, 1\},
--   $$
--
--   that is, $G(s) = s/\mu$ on $[0,\mu]$, $G(s)=0$ for $s<0$ and $G(s)=1$ for $s>\mu$.
--
--   The marketplace first chooses a **transaction benefit** $b$ that buyers receive when they complete their purchase on $M$, at investment cost $K(b) = \tfrac{k}{2}b^2$, and a per-transaction fee $f$. The feasible choices are
--   $$
--   b \ge 0, \qquad b \le f \le v - c + b .
--   $$
--   Given $(b,f)$, the seller lists on $M$ at price $p_m = v + b$ and chooses its direct price $p_d \le v$ to maximize
--   $$
--   \pi_b(f, p_d) = (p_d - c)\,G(v - p_d) + (v + b - c - f)\,\bigl(1 - G(v - p_d)\bigr).
--   $$
--   A direct price $p_d$ is **seller-optimal** at $(b,f)$ if $p_d \le v$ and $\pi_b(f,p_d) \ge \pi_b(f,p)$ for every $p \le v$. The **leakage** at $p_d$ is the share $G(v-p_d)$ of buyers who buy directly. The marketplace's realized profit when the seller answers with $p_d$ is
--   $$
--   \Pi(b, f, p_d) = f\,\bigl(1 - G(v - p_d)\bigr) - \tfrac{k}{2} b^2 .
--   $$
--   A triple $(b, f, p_d)$ is an **optimum** of the game if $(b,f)$ is feasible, $p_d$ is seller-optimal at $(b,f)$, and no feasible $(b', f')$ together with a seller-optimal $p_d'$ gives the marketplace a strictly larger profit.
--
--   Finally, the threshold of Proposition 2 is
--   $$
--   \bar\mu = \frac{v-c}{2} + \frac{1}{4k} + \sqrt{\Bigl(\frac{v-c}{2}\Bigr)^2 + \frac{1}{16k^2}} .
--   $$
--
--   These objects carry the paper's analysis of whether a marketplace should fight leakage by investing in benefits from transacting on it.
--
--   **Formalization Note** The seller's response and the marketplace's optimal choice are optimality predicates, not closed-form functions; the closed forms are theorems of the mission. The model uses the reduced seller problem the paper writes after Lemma 1 ($p_m = v + b$, $p_d \le v$). Greek $\mu$ is the Lean variable `μ`; the clamped $G$ is `G μ s`.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 5–12, §3.1, §4 (uniform G, p. 9), §5.1 (pp. 11–12), Proposition 2 (μ̄)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Benefits

/-- The seller's reduced profit with transaction benefit `b` (§5.1, p. 11):
`π = (pd − c) G(v − pd) + (v + b − c − f)(1 − G(v − pd))`. -/
noncomputable def sProfitB (v c μ b f pd : ℝ) : ℝ :=
  (pd - c) * MarketplaceLeakage.Baseline.G μ (v - pd) + (v + b - c - f) * (1 - MarketplaceLeakage.Baseline.G μ (v - pd))

/-- `pd` is a profit-maximizing direct price of the seller at benefit `b` and fee `f`:
`pd ≤ v` and `pd` maximizes `sProfitB` over all direct prices `p ≤ v`. -/
def IsSOptB (v c μ b f pd : ℝ) : Prop :=
  pd ≤ v ∧ ∀ p : ℝ, p ≤ v → sProfitB v c μ b f p ≤ sProfitB v c μ b f pd

/-- The marketplace's realized profit when it chooses benefit `b` and fee `f` and the seller
answers with direct price `pd`: `f (1 − G(v − pd)) − K(b)` with `K(b) = (k/2) b²` (p. 12). -/
noncomputable def MProfitB (v μ k b f pd : ℝ) : ℝ :=
  f * (1 - MarketplaceLeakage.Baseline.G μ (v - pd)) - k / 2 * b ^ 2

/-- The marketplace's feasible choices (p. 12): `b ≥ 0` and `b ≤ f ≤ v − c + b`. -/
def Feasible (v c b f : ℝ) : Prop :=
  0 ≤ b ∧ b ≤ f ∧ f ≤ v - c + b

/-- `(b, f, pd)` is an optimum of the game: `(b, f)` is feasible, `pd` is the seller's optimal
response, and no feasible `(b', f')` together with an optimal seller response `pd'` gives the
marketplace a higher profit. -/
def IsOpt (v c μ k b f pd : ℝ) : Prop :=
  Feasible v c b f ∧ IsSOptB v c μ b f pd ∧
    ∀ b' f' pd' : ℝ, Feasible v c b' f' → IsSOptB v c μ b' f' pd' →
      MProfitB v μ k b' f' pd' ≤ MProfitB v μ k b f pd

/-- The threshold `μ̄ = (v − c)/2 + 1/(4k) + √(((v − c)/2)² + 1/(16k²))` of Proposition 2. -/
noncomputable def muBar (v c k : ℝ) : ℝ :=
  (v - c) / 2 + 1 / (4 * k) + Real.sqrt (((v - c) / 2) ^ 2 + 1 / (16 * k ^ 2))

end MarketplaceLeakage.Benefits


