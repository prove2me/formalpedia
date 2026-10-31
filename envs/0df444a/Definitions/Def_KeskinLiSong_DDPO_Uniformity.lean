-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_Uniformity
-- name    : KeskinLiSong_DDPO_Uniformity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:49:25.997141+00:00
-- url     : https://prove2.me/theorems/bdb8fc1b-0b28-413d-90b2-cc7f1034dd78
-- title:
--   Unknown-parameter uniformity and operational regret guarantee
-- statement:
--   The public data are held fixed while noise law, change count and separation vary. Tuning is transported without changing its values. A performance assertion requires execution at every T>=3 for every allowed environment with the source-assumed FIA optimum, and integrable regret bounded by K times the appropriate rate for every executing measurable tie selection. Learner rules are selected before the unknown noise law, changes and environments. OmegaAt recomputes the estimated beta parameter and chosen price from the same observed history, retaining the actual innovation at the selected index.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 7–12; ec8

import Definitions.Def_KeskinLiSong_DDPO_TailEvents

open MeasureTheory ProbabilityTheory
noncomputable section

namespace KeskinLiSong.DDPO

/-- Vary precisely the unknown noise law and change parameters, retaining public
costs, compact parameter bounds, and link function. -/
def instanceWith (A : Model) (noise : LocalMGF) (C : ℕ) (delta : ℝ)
    (hdelta : 0 < delta) : Model :=
  { A with noise := noise, changes := C, separation := delta, separation_pos := hdelta }

def retune (A : Model) (u : Tuning A) (noise : LocalMGF) (C : ℕ) (delta : ℝ)
    (hdelta : 0 < delta) : Tuning (instanceWith A noise C delta hdelta) where
  eta := u.eta
  kappa := u.kappa
  rho := u.rho
  omega1 := u.omega1
  omega2 := u.omega2
  upsilon := u.upsilon
  positive := u.positive
  test_prices := u.test_prices
  test_stock := u.test_stock

/-- A horizon-uniform guarantee includes operational existence and integrability;
all genuine measurable tie selections satisfy the stated regret bound. -/
def Performance (mode : NoiseMode) (A : Model) (u : Tuning A)
    (algorithm : ℕ → Learner mode) (K : ℝ) : Prop :=
  ∀ T : ℕ, 3 ≤ T → ∀ E : Environment A T, HasFIA A E →
    Executes mode A u E (algorithm T) ∧
    ∀ (L : Learner mode) (benchmark : Policy),
      Executes mode A u E L → FIA A E benchmark →
      Integrable (regretSample A E benchmark L.policy) (primitiveLaw A E) ∧
      regret A E benchmark L.policy ≤ K * rate mode.version T

/-- The Omega summand retains its data-dependent price, beta estimate and stock
optimizer. The innovation in coordinate s is not replaced by a fresh draw. -/
def omegaAt (A : Model) {T : ℕ} (E : Environment A T)
    (L : Learner .nonparametric) (p : PriceSelection) (y : Paths T → ℝ)
    (z : Paths T) (t s : ℕ) : ℝ :=
  omega A (E.theta t) (xiEstimate .nonparametric A E L z t)
    (priceAt A E L.policy p z t) (y z) (innovation z s).1

end KeskinLiSong.DDPO


