-- Prove2me | Definitions.Def_LemonsPoA_TwoSided_Regular
-- name    : LemonsPoA_TwoSided_Regular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:32.638549+00:00
-- url     : https://prove2.me/theorems/a24f5b2d-ac6f-4afd-9425-7014a829c602
-- title:
--   Definition 5.2 — $(\pi^-,\pi^+,\rho)$-regular market instance
-- statement:
--   **Definition 5.2.** A market instance is $(\pi^-,\pi^+,\rho)$-regular, for its most pessimistic seller signal $\sigma^-_S$ and most optimistic buyer signal $\sigma^+_B$, if
--
--   1. $C\ge 0$ almost surely and $C$ is dominated in convex order by an exponential variable of mean $\mu=E[C]\in(0,\infty)$;
--   2. $\displaystyle\min_{\sigma_B}\Pr[\Sigma_S=\sigma^-_S\mid\Sigma_B=\sigma_B]\ge\pi^->0$;
--   3. $\displaystyle\min_{\sigma_S}\Pr[\Sigma_B=\sigma^+_B\mid\Sigma_S=\sigma_S]\ge\pi^+>0$;
--   4. under $\theta\sim G$, $(x(\theta),y(\theta))$ has a log-concave density (or, by Definition 1.4, one coordinate is constant and the other has a log-concave density), and $E[x(\theta)+|y(\theta)|]<\infty$;
--   5. $\mathrm{Corr}(x(\theta),y(\theta))\ge\rho>-1$; if $x(\theta)$ or $y(\theta)$ is constant, this is taken to hold for $\rho=0$.
--
--   **Formalization Note** `Regular M σm σp πm πp ρ` takes $\sigma^-_S$ (`σm`) and $\sigma^+_B$ (`σp`) as arguments; their extremality is the separate hypotheses `IsPessimistic`, `IsOptimistic`. Items 2-3 range over signals of positive probability (Definition 1.4 writes $\sigma_B\in\mathrm{supp}\,\Sigma_B$). Item 1 is `lawC (Iio 0) = 0`, integrability of $C$, $0<\mu$ and `CxLeExp`. Item 4 is `LogConcavePrefs` with integrability of $x$ and $y$ (equivalent to $E[x+|y|]<\infty$ since $x\ge 0$); it includes Definition 1.4's constant-coordinate clause, which item 5 presupposes (INSIGHTS I1). Item 5 uses the plain-quotient correlation, which is $0$ for a constant coordinate, so it then reads $-1<\rho\le 0$.
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), pp. 27-28, Definition 5.2 (with Definition 1.4 item 1, p. 10)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory ProbabilityTheory

namespace LemonsPoA.TwoSided

namespace Market

variable {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]

/-- Definition 5.2: the market `M` is `(π⁻, π⁺, ρ)`-regular, for the most pessimistic seller
signal `σm` (= σ⁻_S) and most optimistic buyer signal `σp` (= σ⁺_B).
1. `C ≥ 0` a.s., `µ = E[C] ∈ (0, ∞)`, and `C` is dominated in convex order by an exponential
   variable with mean `µ`;
2. `Pr[Σ_S = σm | Σ_B = σB] ≥ π⁻ > 0` for every buyer signal of positive probability;
3. `Pr[Σ_B = σp | Σ_S = σS] ≥ π⁺ > 0` for every seller signal of positive probability;
4. `(x, y)` log-concave in the sense of `LogConcavePrefs`, and `E[x + |y|] < ∞`;
5. `Corr(x, y) ≥ ρ > -1` (with a constant coordinate, `Corr = 0`, so this reads `ρ ≤ 0`). -/
structure Regular (M : Market Θ SS SB) (σm : SS) (σp : SB) (πm πp ρ : ℝ) : Prop where
  C_nonneg : M.lawC (Set.Iio 0) = 0
  C_integrable : Integrable id M.lawC
  meanC_pos : 0 < M.meanC
  convex_order : CxLeExp M.lawC M.meanC
  πm_pos : 0 < πm
  rarity_pess : ∀ σB : SB, 0 < M.probB σB → πm ≤ M.condS σm σB
  πp_pos : 0 < πp
  rarity_opt : ∀ σS : SS, 0 < M.probS σS → πp ≤ M.condB σS σp
  prefs : LogConcavePrefs M.G M.x M.y
  x_integrable : Integrable M.x M.G
  y_integrable : Integrable M.y M.G
  ρ_gt : -1 < ρ
  corr_ge : ρ ≤ corr M.G M.x M.y

end Market

end LemonsPoA.TwoSided


