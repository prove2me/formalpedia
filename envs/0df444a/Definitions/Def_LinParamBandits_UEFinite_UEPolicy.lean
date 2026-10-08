-- Prove2me | Definitions.Def_LinParamBandits_UEFinite_UEPolicy
-- name    : LinParamBandits_UEFinite_UEPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:39.019057+00:00
-- url     : https://prove2.me/theorems/75c66d56-cfac-43aa-bf9b-28ac84b02412
-- title:
--   Eqs. (3)–(7) — the Uncertainty Ellipsoid (UE) policy: κ₀, α, OLS estimate Ẑ_t, C_t, uncertainty radius R^u_t
-- statement:
--   The Uncertainty Ellipsoid (UE) policy of Section 4 of Rusmevichientong and Tsitsiklis.
--
--   **Constants.** With $\sigma_0, \bar u, \lambda_0$ from Assumption 1,
--   $$\kappa_0 = 2\sqrt{1 + \log\Big(1 + \frac{36\bar u^2}{\lambda_0}\Big)}, \qquad \alpha = 4\sigma_0\kappa_0^2 .$$
--
--   **Least squares.** After $t$ periods with arms $U_1, \dots, U_t$ and rewards $X_1, \dots, X_t$,
--   $$C_t = \Big(\sum_{s=1}^t U_sU_s'\Big)^{-1}, \qquad \widehat Z_t = C_t \sum_{s=1}^t U_s X_s ,$$
--   and $\|v\|_{C_t} = \sqrt{v'C_tv}$.
--
--   **Uncertainty radius.** For every arm $v$,
--   $$R^v_t = \alpha \sqrt{\log t}\,\sqrt{\min\{r \log t, |\mathcal U_r|\}}\;\|v\|_{C_t},$$
--   with $|\mathcal U_r| = \infty$ when the arm set is infinite.
--
--   **The policy.** In periods $1, \dots, r$, play $b_1, \dots, b_r$ of Assumption 1(b), in this order. In every period $t+1 \ge r+1$, play an arm
--   $$U_{t+1} \in \arg\max_{v \in \mathcal U_r}\big\{ v'\widehat Z_t + R^v_t \big\},$$
--   ties being broken arbitrarily. A policy is a UE run if it does this.
--
--   Every statement of the mission concerns an arbitrary UE run, i.e. holds for every tie-breaking rule.
--
--   **Formalization Note** `width 𝒰 t` is $\min\{r\log t, |\mathcal U_r|\}$ when `𝒰` is finite and $r\log t$ otherwise (Lean's `Set.ncard` is $0$ on infinite sets, hence the split; this mission only uses finite arm sets, and the definition is kept identical to the general one so the two missions can share it). `Cmat h` is Mathlib's matrix inverse of the Gram matrix; it is the true inverse whenever the Gram matrix is positive definite, which holds for $t \ge r$ on the histories a UE run generates, and every theorem of the mission uses it only for $t \ge r$. `IsUE` asks the arg max property for every history of length $t \ge r$ (including histories a UE run never produces, where it only constrains $\psi$ on a null set), so a tie-breaking rule may depend on the whole history, as in the paper; a measurable rule exists (e.g. the first maximizer in a fixed enumeration of the finite arm set).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 4, eqs. (3)–(7) and the box 'Uncertainty Ellipsoid (UE)', pp. 19–20

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

variable {r : ℕ}

/-- The constant `κ₀ = 2 √(1 + log(1 + 36 ū²/λ₀))` of eq. (3), p. 19. -/
noncomputable def kappa0 (ū lam₀ : ℝ) : ℝ :=
  2 * Real.sqrt (1 + Real.log (1 + 36 * ū ^ 2 / lam₀))

/-- The constant `α = 4 σ₀ κ₀²` of eq. (5), p. 20. -/
noncomputable def alpha (σ₀ ū lam₀ : ℝ) : ℝ :=
  4 * σ₀ * kappa0 ū lam₀ ^ 2

/-- The Gram matrix `∑_{s=1}^t U_s U_s′` of the arms of a history of `t` periods (eq. (4), p. 19). -/
noncomputable def gram {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ s, Matrix.vecMulVec (WithLp.ofLp (h s).1) (WithLp.ofLp (h s).1)

/-- `C_t = (∑_{s=1}^t U_s U_s′)⁻¹` (eq. (4), p. 19). It is a true inverse when the Gram matrix is
positive definite, which holds for `t ≥ r` on the histories the UE policy generates (the first `r`
arms are linearly independent). -/
noncomputable def Cmat {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : Matrix (Fin r) (Fin r) ℝ :=
  (gram h)⁻¹

/-- The weighted norm `‖v‖_{C_t} = √(v′ C_t v)` (p. 3). -/
noncomputable def normC {t : ℕ} (h : LinParamBandits.LowerBound.History r t) (v : LinParamBandits.LowerBound.Vec r) : ℝ :=
  Real.sqrt (dotProduct (WithLp.ofLp v) (Matrix.mulVec (Cmat h) (WithLp.ofLp v)))

/-- The uncertainty radius `R^v_t = α √(log t) √(min{r log t, |𝒰_r|}) ‖v‖_{C_t}` of eq. (6),
p. 20, computed from a history of `t` periods. -/
noncomputable def radius (σ₀ ū lam₀ : ℝ) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) {t : ℕ} (h : LinParamBandits.LowerBound.History r t)
    (v : LinParamBandits.LowerBound.Vec r) : ℝ :=
  alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) * Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) * normC h v

/-- `ψ` is a run of the Uncertainty Ellipsoid policy (pp. 19–20) on the arm set `𝒰`, with initial
arms `b_1, …, b_r` and parameters `σ₀, ū, λ₀`:
1. every arm chosen lies in `𝒰_r`;
2. initialization: in periods `1, …, r` the arms `b_1, …, b_r` are played, in this order;
3. for every period `t + 1 ≥ r + 1`, the arm `U_{t+1}` maximizes `v′Ẑ_t + R^v_t` over `v ∈ 𝒰_r`
   (eq. (7)); ties may be broken in any (measurable, history-dependent) way. -/
def IsUE (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r) (σ₀ ū lam₀ : ℝ) (ψ : LinParamBandits.UEGeneral.Policy r) : Prop :=
  (∀ t (h : LinParamBandits.LowerBound.History r t), ψ.act t h ∈ 𝒰) ∧
  (∀ t (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩) ∧
  (∀ t (h : LinParamBandits.LowerBound.History r t), r ≤ t → ∀ v ∈ 𝒰,
    inner ℝ v (LinParamBandits.UEGeneral.Zhat h) + radius σ₀ ū lam₀ 𝒰 h v ≤
      inner ℝ (ψ.act t h) (LinParamBandits.UEGeneral.Zhat h) + radius σ₀ ū lam₀ 𝒰 h (ψ.act t h))

end LinParamBandits.UEFinite


