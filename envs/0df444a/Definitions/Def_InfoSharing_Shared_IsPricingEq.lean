-- Prove2me | Definitions.Def_InfoSharing_Shared_IsPricingEq
-- name    : InfoSharing_Shared_IsPricingEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:34:30.115858+00:00
-- url     : https://prove2.me/theorems/3ac537be-f3d1-4633-ba2f-a28b4d84fb86
-- title:
--   Bayesian Nash equilibrium of the wholesale/retail pricing game, §4.1
-- statement:
--   Fix demand parameters $a$, $\phi$, production cost parameters $b$, $c$ (cost $bq + cq^2$), the signal weight $\beta$, and a status profile $X$. Demand for product $i$ is
--
--   $$q_i = a + \theta - (1+\phi)p_i + \phi p_j.$$
--
--   The manufacturers set wholesale prices $w_i = f_i(Y)$ simultaneously, and then the retailer, knowing $w$ and $Y = y$, sets retail prices $p = \rho(w, y)$. A triple $(\rho, f_1, f_2)$ is a **pricing equilibrium** for $X$ when:
--
--   1. for every $w \in \mathbb R^2$ and every $y$, $\rho(w,y)$ maximizes the retailer's expected profit $\sum_i (p_i - w_i)(a + \beta y - (1+\phi)p_i + \phi p_j)$ over $p \in \mathbb R^2$ (her conditional mean of $\theta$ is $\beta y$);
--   2. each $f_i$ is admissible for $X_i$: measurable, with $E[f_i(Y)^2] < \infty$, and constant if $X_i = U$;
--   3. no manufacturer $i$ can increase his ex ante profit $E[(w_i - b)q_i - c q_i^2]$ by switching to another admissible strategy, the retailer responding by $\rho$.
--
--   The retailer's ex ante profit is $E[\sum_i (p_i - w_i) q_i]$.
--
--   **Formalization Note.** Ex ante optimality over measurable square-integrable functions of the signal is equivalent to the paper's conditional optimization for an informed manufacturer; for an uninformed one the strategies are constants, as in the paper. Square integrability of deviations keeps every profit a genuine expectation.
--
--   **Formalization Note (production economy).** The cost is the uncapped quadratic $bq + cq^2$; the production economy model takes $c = -c_e$ and the paper assumes its cap at $\bar q = b/(2c_e)$ never binds (footnote 11, p. 251).
--
--   This is a shared definition of the series, reviewed once for both missions: `01-diseconomy-sequential` (production diseconomy, §5; Shang, Ha & Tong 2016, pp. 250–251, §4.1 (with $c = c_d > 0$)) and `02-economy-sequential` (production economy, §6; pp. 249–251, §3 and §4.1, and footnote 11, p. 251 (with $c = -c_e$, uncapped cost)). The cost parameter $c$ is a plain real; the missions differ only in the hypotheses their theorems put on it: $c > 0$ in the first, $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ in the second.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, pp. 250–251, §4.1; p. 251, footnote 11

import Mathlib
import Definitions.Def_InfoSharing_Shared_Status
open MeasureTheory

namespace InfoSharing.Shared

/-- The retailer's expected profit at the pricing stage (Shang, Ha & Tong 2016, §4.1, p. 250),
given wholesale prices `w`, the conditional mean `m = E[θ | Y]` and retail prices `p`:
`Σᵢ (pᵢ − wᵢ)(a + m − (1+φ)pᵢ + φpⱼ)`. The retailing cost is `0` (p. 249). -/
def retailerInterim (a φ : ℝ) (w : Fin 2 → ℝ) (m : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, (p i - w i) * (a + m - (1 + φ) * p i + φ * p (other i))

/-- `ρ` is a retailer best-response rule: for every pair of wholesale prices `w` and every
signal value `y`, the retail prices `ρ w y` maximize the retailer's expected profit with
`E[θ | Y = y] = β y`, over all of `ℝ²` (§4.1, p. 250). -/
def IsRetailerBR (a φ β : ℝ) (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) : Prop :=
  ∀ (w : Fin 2 → ℝ) (y : ℝ) (p : Fin 2 → ℝ),
    retailerInterim a φ w (β * y) p ≤ retailerInterim a φ w (β * y) (ρ w y)

/-- A wholesale-price strategy `f` (a function of the signal value) is admissible for status
`s`: it is measurable, `f ∘ Y` is square integrable, and an uninformed manufacturer's strategy
is constant (he does not observe `Y`) (p. 251). -/
def IsAdmissible {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (s : Status)
    (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ MemLp (fun ω => f (Y ω)) 2 μ ∧
  (s = Status.uninformed → ∃ k : ℝ, ∀ y, f y = k)

/-- The realized demand of product `i` in state `ω` (§3, p. 249): `qᵢ = a + θ − (1+φ)pᵢ + φpⱼ`,
where the wholesale prices are `wⱼ = fⱼ(Y(ω))` and the retail prices are
`p = ρ(w, Y(ω))`. -/
def demand {Ω : Type*} (a φ : ℝ) (θ Y : Ω → ℝ) (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ))
    (f : Fin 2 → ℝ → ℝ) (i : Fin 2) (ω : Ω) : ℝ :=
  a + θ ω - (1 + φ) * ρ (fun j => f j (Y ω)) (Y ω) i
    + φ * ρ (fun j => f j (Y ω)) (Y ω) (other i)

/-- Manufacturer `i`'s ex ante profit `E[(wᵢ − b)qᵢ − c qᵢ²]` (production cost `bq + cq²`,
p. 249, with `c = c_d` in the diseconomy model; the production economy model takes `c = −c_e`,
p. 251).

**Formalization Note.** The cost is the uncapped quadratic `bq + cq²`. The paper's production
economy cost caps the quantity at `q̄ = b/(2c_e)` (p. 249) but assumes the cap is reached with
negligible probability (footnote 11, p. 251), and every formula of §4.2 and result of §6 is
computed with the uncapped cost. -/
noncomputable def manufacturerProfit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
    (a b c φ : ℝ) (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ) (i : Fin 2) : ℝ :=
  ∫ ω, (f i (Y ω) - b) * demand a φ θ Y ρ f i ω - c * demand a φ θ Y ρ f i ω ^ 2 ∂μ

/-- The retailer's ex ante profit `E[Σᵢ (pᵢ − wᵢ) qᵢ]`. -/
noncomputable def retailerProfit {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
    (a φ : ℝ) (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)) (f : Fin 2 → ℝ → ℝ) : ℝ :=
  ∫ ω, ∑ i : Fin 2,
    (ρ (fun j => f j (Y ω)) (Y ω) i - f i (Y ω)) * demand a φ θ Y ρ f i ω ∂μ

/-- Bayesian Nash equilibrium of the pricing stage for the status profile `X`
(§4.1, pp. 250–251): the retailer's rule `ρ` is a best response to every wholesale-price pair,
each manufacturer's strategy `f i` is admissible for his status, and no manufacturer can raise
his ex ante profit by switching to another admissible strategy (the retailer responding with
`ρ`).

**Formalization Note.** Ex ante optimality over measurable square-integrable functions of the
signal value is equivalent to the paper's conditional (interim) optimization for an informed
manufacturer, and coincides with it for an uninformed one (constant strategies). -/
def IsPricingEq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ Y : Ω → ℝ)
    (a b c φ β : ℝ) (X : Fin 2 → Status) (ρ : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ))
    (f : Fin 2 → ℝ → ℝ) : Prop :=
  IsRetailerBR a φ β ρ ∧ (∀ i, IsAdmissible μ Y (X i) (f i)) ∧
  ∀ (i : Fin 2) (g : ℝ → ℝ), IsAdmissible μ Y (X i) g →
    manufacturerProfit μ θ Y a b c φ ρ (Function.update f i g) i ≤
      manufacturerProfit μ θ Y a b c φ ρ f i

end InfoSharing.Shared


