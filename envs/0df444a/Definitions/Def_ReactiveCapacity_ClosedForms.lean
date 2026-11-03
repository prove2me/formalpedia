-- Prove2me | Definitions.Def_ReactiveCapacity_ClosedForms
-- name    : ReactiveCapacity_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:29.355486+00:00
-- url     : https://prove2.me/theorems/60d244f8-b540-4b45-ad86-c23bce69d25e
-- title:
--   The closed forms $S(\bar Q)$, $Y(S)$, $X$, $V_{OS}$, $V_{OO}$, the focus condition and the domain
-- statement:
--   The quantities the statements name, transcribed from Tables B and C (pp.17–20) and footnote 1 of the Online Appendix.
--
--   1. Supply in the bad market when the supplier holds $\alpha_g$: $S(\bar Q)=\min\{\alpha_g+\bar Q,1\}$.
--   2. The average valuation of the targeted consumers:
--   $$
--   Y(S)=\frac{\rho\alpha_g\theta_H+(1-\rho)S\theta_L}{\rho\alpha_g+(1-\rho)S},\qquad X=Y(1)=\frac{\rho\alpha_g\theta_H+(1-\rho)\theta_L}{\rho\alpha_g+1-\rho}.
--   $$
--   3. The retailer's profits in the two columns of Table B:
--   $$
--   V_{OS}(\bar Q)=\frac{(\rho\alpha_g+(1-\rho)S(\bar Q))\,Y(S(\bar Q))^2}{4k},\qquad V_{OO}=\frac{(1-\rho)(\rho\alpha_g+1-\rho)X^2}{4k}.
--   $$
--   4. The **focus condition** (footnote 1 of the Online Appendix at the equilibrium quality, for every $\bar Q\ge 0$):
--   $$
--   (\rho\theta_H+(1-\rho)\theta_L)(\alpha_g-\alpha_b)<2(\theta_L\alpha_g-\theta_H\alpha_b).
--   $$
--   5. **High-only dominated** (not in the paper):
--   $$
--   (\rho\alpha_g+(1-\rho)\alpha_b)\theta_H^2<\max\Bigl\{\frac{(1-\rho)(\rho\alpha_g\theta_H+(1-\rho)\theta_L)^2}{\rho\alpha_g+1-\rho},\ \alpha_g(\rho\theta_H+(1-\rho)\theta_L)^2\Bigr\},
--   $$
--   i.e. $(\rho\alpha_g+(1-\rho)\alpha_b)\theta_H^2/(4k)<\max\{V_{OO},V_{OS}(0)\}$: targeting only the high-valuation consumers in both states is worth less to the retailer than the better of the two Table B outcomes at $\bar Q=0$.
--   6. The **domain** of the mission's main statements: the standing assumptions, the focus condition and high-only dominance.
--
--   The focus condition formalizes the paper's restriction to "the interesting parameter region where the retailer will target all consumers" once the supplier's inventory is high enough (OA p.3). The high-only condition formalizes its exclusion of the case where "the retailer will always target only high-valuation consumers regardless of the supplier's inventory decision, which is not interesting" (OA p.3). Without it the printed Proposition 1 and Tables B and C fail in the game.
--
--   **Formalization Note** Footnote 1 reads $Y(S)^2/(4k)<q(\theta_LS-\theta_H\alpha_b)/(S-\alpha_b)$; at $q=Y(S)/(2k)$ it does not involve $k$, and it holds for every $\bar Q\ge 0$ exactly when it holds at $S=\alpha_g$, which is the displayed inequality. It implies $\alpha_g>(\theta_H/\theta_L)\alpha_b$, so the paper's low-capacity range (Table A) is empty on the domain.
-- source:
--   Jiang–Tian, Effects of Reactive Capacity, SSRN 3308215 (version of May 5, 2022), Table B pp.17–18 (PDF 17–18), Table C pp.19–20 (PDF 19–20); focus condition, Online Appendix fn 1, OA p.3 (PDF 48) and fn 2, OA p.5 (PDF 50); exclusion of the high-only case, OA p.3 (PDF 48)

import Mathlib
import Definitions.Def_ReactiveCapacity_Model

namespace ReactiveCapacity

/-- Supply in the bad market when the supplier holds `I = α_g`: `S(Q̄) = min[α_g + Q̄, 1]`
(Online Appendix fn 1, OA p.3; Tables B and C, pp.17–20). -/
noncomputable def Params.supplyS (P : Params) (Qbar : ℝ) : ℝ := min (P.αg + Qbar) 1

/-- The average valuation of the targeted consumers, `Y(S) = (ρα_gθ_H + (1 − ρ)Sθ_L)/(ρα_g + (1 − ρ)S)`,
the ratio in Table B, column (1), p.17 (with `S = α_g + Q̄`). -/
noncomputable def Params.Y (P : Params) (S : ℝ) : ℝ :=
  (P.ρ * P.αg * P.θH + (1 - P.ρ) * S * P.θL) / (P.ρ * P.αg + (1 - P.ρ) * S)

/-- `X = Y(1) = (ρα_gθ_H + (1 − ρ)θ_L)/(ρα_g + 1 − ρ)`, the ratio in Table B, column (2), p.17, and
in Table C, pp.19–20. -/
noncomputable def Params.X (P : Params) : ℝ := P.Y 1

/-- The retailer's profit in "opportunistic targeting with stockout", Table B, column (1), p.17,
`V_OS(Q̄) = (ρα_g + (1 − ρ)S) Y(S)² / (4k)` with `S = min[α_g + Q̄, 1]`; equal to Table B's
`[ρα_gθ_H + (1 − ρ)(α_g + Q̄)θ_L]² / (4k[ρα_g + (1 − ρ)(α_g + Q̄)])` for `Q̄ ≤ 1 − α_g`. -/
noncomputable def Params.V_OS (P : Params) (Qbar : ℝ) : ℝ :=
  (P.ρ * P.αg + (1 - P.ρ) * P.supplyS Qbar) * P.Y (P.supplyS Qbar) ^ 2 / (4 * P.k)

/-- The retailer's profit in "opportunistic targeting with overstock", Table B, column (2), p.17:
`V_OO = (1 − ρ)(ρα_g + 1 − ρ) X² / (4k)`. -/
noncomputable def Params.V_OO (P : Params) : ℝ :=
  (1 - P.ρ) * (P.ρ * P.αg + 1 - P.ρ) * P.X ^ 2 / (4 * P.k)

/-- The paper's focus condition, footnote 1 of the Online Appendix (OA p.3, PDF 48; repeated as
footnote 2, OA p.5), in the medium and high ranges, evaluated at the equilibrium quality:
`(ρθ_H + (1 − ρ)θ_L)(α_g − α_b) < 2(θ_Lα_g − θ_Hα_b)`.

**Formalization Note** Footnote 1 reads `Y(S)²/(4k) < q(θ_L S − θ_Hα_b)/(S − α_b)` with
`S = min[α_g + Q̄, 1]`; at `q = Y(S)/(2k)` it does not involve `k`, and it holds for every `Q̄ ≥ 0`
exactly when it holds at `S = α_g`, where `Y(α_g) = ρθ_H + (1 − ρ)θ_L`. That case is this
inequality (proved equivalent under the standing assumptions in the verification file). -/
def Params.Focus (P : Params) : Prop :=
  (P.ρ * P.θH + (1 - P.ρ) * P.θL) * (P.αg - P.αb) < 2 * (P.θL * P.αg - P.θH * P.αb)

/-- **Not in the paper.** The retailer's best profit from contracts under which it targets only
high-valuation consumers in both states (at most `(ρα_g + (1 − ρ)α_b)θ_H²/(4k)`) lies strictly below
the larger of the two medium-range profits at `Q̄ = 0`:
`(ρα_g + (1 − ρ)α_b)θ_H² < max{(1 − ρ)(ρα_gθ_H + (1 − ρ)θ_L)²/(ρα_g + 1 − ρ), α_g(ρθ_H + (1 − ρ)θ_L)²}`,
i.e. `(ρα_g + (1 − ρ)α_b)θ_H²/(4k) < max{V_OO, V_OS(0)}`.

It formalizes the paper's exclusion of the case where "the retailer will always target only
high-valuation consumers regardless of the supplier's inventory decision, which is not interesting"
(OA p.3, PDF 48). -/
def Params.HighOnlyDominated (P : Params) : Prop :=
  (P.ρ * P.αg + (1 - P.ρ) * P.αb) * P.θH ^ 2 <
    max ((1 - P.ρ) * (P.ρ * P.αg * P.θH + (1 - P.ρ) * P.θL) ^ 2 / (P.ρ * P.αg + 1 - P.ρ))
      (P.αg * (P.ρ * P.θH + (1 - P.ρ) * P.θL) ^ 2)

/-- The parameter domain of the mission's statements: the standing assumptions, the paper's focus
condition, and `HighOnlyDominated`. -/
def Params.Dom (P : Params) : Prop :=
  P.Standing ∧ P.Focus ∧ P.HighOnlyDominated

end ReactiveCapacity


