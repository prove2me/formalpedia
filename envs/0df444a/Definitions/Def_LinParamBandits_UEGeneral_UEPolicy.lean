-- Prove2me | Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
-- name    : LinParamBandits_UEGeneral_UEPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:21.72154+00:00
-- url     : https://prove2.me/theorems/d27a34db-1517-4a9c-8205-6d9e8b47cc6b
-- title:
--   Sec. 4, eqs. (3)–(7) — OLS estimate Ẑ_t, C_t, M_t, κ₀, α, uncertainty radius R^u_t and the Uncertainty Ellipsoid policy
-- statement:
--   This file defines the Uncertainty Ellipsoid (UE) policy of Section 4 and the quantities of its analysis.
--
--   **Least squares.** If $U_1, \dots, U_t$ are the arms of the first $t$ periods,
--   $$C_t = \Big(\sum_{s=1}^t U_sU_s'\Big)^{-1}, \qquad M_t = \sum_{s=1}^t U_sW_s, \qquad \widehat Z_t = C_t\sum_{s=1}^t U_sX_s = Z + C_tM_t,$$
--   and $\|v\|_A = \sqrt{v'Av}$ is the weighted norm of $v$ for a matrix $A$.
--
--   **Constants.** With $\sigma_0, \bar u, \lambda_0$ from Assumption 1,
--   $$\kappa_0 = 2\sqrt{1 + \log\Big(1 + \frac{36\bar u^2}{\lambda_0}\Big)}, \qquad \alpha = 4\sigma_0\kappa_0^2 .$$
--
--   **Uncertainty radius.** For an arm $u$, after $t$ periods,
--   $$R^u_t = \alpha\sqrt{\log t}\,\sqrt{\min\{r\log t, |\mathcal U_r|\}}\;\|u\|_{C_t},$$
--   with $|\mathcal U_r| = \infty$ when the arm set is infinite.
--
--   **The UE policy.** During the first $r$ periods it plays $b_1, \dots, b_r$ of Assumption 1(b). For $t \ge r+1$ it plays an arm
--   $$U_t \in \arg\max_{v \in \mathcal U_r}\big\{v'\widehat Z_{t-1} + R^v_{t-1}\big\},$$
--   ties broken arbitrarily. A policy is a *UE run* if it plays arms of $\mathcal U_r$, follows the initialization, and makes a maximizing choice after every history that starts with $b_1, \dots, b_r$.
--
--   **Potentials.** For an arm sequence, $\|U_{t+1}\|^2_{C_t}$ is the squared $C_t$-norm of the arm of period $t+1$; it drives the analysis of Lemmas B.8–B.10.
--
--   **Formalization Note** `design` is $\sum_s U_sU_s'$ and `Cmat` its matrix inverse; for $t \ge r$ on a history starting with $b_1, \dots, b_r$ the design matrix is positive definite (Assumption 1(b)), so the inverse is genuine, and the policy is only constrained on such histories. `width 𝒰 t` is $\min\{r\log t, |\mathcal U_r|\}$ for a finite set and $r\log t$ for an infinite one (Lean's `ncard` is $0$ on infinite sets, so the case split is needed). `radiusFactor` is $\alpha\sqrt{\log t}\sqrt{\min\{r\log t, |\mathcal U_r|\}}$. Periods are 0-based: `ψ.act t h` with `h` of length $t$ is $U_{t+1}$, chosen from $\widehat Z_t$ and $R^v_t$; `potential U t` is $\|U_{t+1}\|^2_{C_t}$ for a sequence `U` whose entry `s` is $U_{s+1}$; `armSeq h` lists the arms of a history. `Mvec z h` computes $M_t$ with $W_s = X_s - U_s'z$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 4, eqs. (3)–(7), pp. 19–20; notation ‖v‖_A, p. 3; App. B.2, pp. 35–38

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory Matrix

variable {r : ℕ}

/-- The design matrix `∑_{s=1}^t U_s U_s′` of the arms `U_1, …, U_t` (eq. (4), p. 19, where it
is `C_t^{-1}`; called `Υ_t` on p. 37). -/
noncomputable def design {t : ℕ} (U : Fin t → LinParamBandits.LowerBound.Vec r) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ s, Matrix.vecMulVec (U s).ofLp (U s).ofLp

/-- `C_t = (∑_{s=1}^t U_s U_s′)^{-1}` (eq. (4), p. 19). It is a true inverse whenever the design
matrix is positive definite, which is the case for `t ≥ r` on every history that starts with
`b_1, …, b_r` (Assumption 1(b)); only such histories are used. -/
noncomputable def Cmat {t : ℕ} (U : Fin t → LinParamBandits.LowerBound.Vec r) : Matrix (Fin r) (Fin r) ℝ :=
  (design U)⁻¹

/-- The quadratic form `v′Av`. -/
noncomputable def quadForm (A : Matrix (Fin r) (Fin r) ℝ) (v : LinParamBandits.LowerBound.Vec r) : ℝ :=
  v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)

/-- The weighted norm `‖v‖_A = √(v′Av)` (p. 3). -/
noncomputable def wnorm (A : Matrix (Fin r) (Fin r) ℝ) (v : LinParamBandits.LowerBound.Vec r) : ℝ :=
  Real.sqrt (quadForm A v)

/-- The arms `U_1, …, U_t` of a history of `t` periods. -/
def armsOf {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : Fin t → LinParamBandits.LowerBound.Vec r :=
  fun s => (h s).1

/-- The OLS estimate `Ẑ_t = C_t ∑_{s=1}^t U_s X_s` (eq. (4), p. 19). -/
noncomputable def Zhat {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : LinParamBandits.LowerBound.Vec r :=
  WithLp.toLp 2 (Cmat (armsOf h) *ᵥ (∑ s, (h s).2 • (h s).1).ofLp)

/-- `M_t = ∑_{s=1}^t U_s W_s` (eq. (4), p. 19), the noises being read off the history given
`Z = z` as `W_s = X_s − U_s′z`. -/
noncomputable def Mvec (z : LinParamBandits.LowerBound.Vec r) {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : LinParamBandits.LowerBound.Vec r :=
  ∑ s, ((h s).2 - inner ℝ (h s).1 z) • (h s).1

/-- `κ₀ = 2 √(1 + log(1 + 36 ū² / λ₀))` (eq. (3), p. 19). -/
noncomputable def kappa0 (ubar lam0 : ℝ) : ℝ :=
  2 * Real.sqrt (1 + Real.log (1 + 36 * ubar ^ 2 / lam0))

/-- `α = 4 σ₀ κ₀²` (eq. (5), p. 20). -/
noncomputable def alpha (σ₀ ubar lam0 : ℝ) : ℝ :=
  4 * σ₀ * kappa0 ubar lam0 ^ 2

open scoped Classical in
/-- `min{r log t, |𝒰_r|}` (eqs. (5)–(6), p. 20), with `|𝒰_r| = ∞` for an infinite arm set, so
that the minimum is `r log t` then. -/
noncomputable def width (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (t : ℕ) : ℝ :=
  if 𝒰.Finite then min ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) else (r : ℝ) * Real.log t

/-- The factor `α √(log t) √(min{r log t, |𝒰_r|})` of the uncertainty ellipsoid (5) and the
uncertainty radius (6), p. 20. -/
noncomputable def radiusFactor (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (σ₀ ubar lam0 : ℝ) (t : ℕ) : ℝ :=
  alpha σ₀ ubar lam0 * Real.sqrt (Real.log t) * Real.sqrt (width 𝒰 t)

/-- The uncertainty radius `R^u_t = α √(log t) √(min{r log t, |𝒰_r|}) ‖u‖_{C_t}` of arm `u`
after the history `h` of `t` periods (eq. (6), p. 20). -/
noncomputable def radius (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (σ₀ ubar lam0 : ℝ) {t : ℕ} (h : LinParamBandits.LowerBound.History r t)
    (u : LinParamBandits.LowerBound.Vec r) : ℝ :=
  radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) u

/-- The policy `ψ` is a run of the Uncertainty Ellipsoid (UE) policy (p. 20) on the arm set `𝒰`,
with initial arms `b_1, …, b_r` and constants `σ₀, ū = ubar, λ₀ = lam0`; ties in (7) are broken
arbitrarily, so every maximizing selection is allowed. -/
structure IsUE (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r) (σ₀ ubar lam0 : ℝ) (ψ : Policy r) :
    Prop where
  /-- Every arm played belongs to `𝒰_r`. -/
  act_mem : ∀ t h, ψ.act t h ∈ 𝒰
  /-- Initialization: during the first `r` periods the arms `b_1, …, b_r` are played in order. -/
  act_init : ∀ (t : ℕ) (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩
  /-- Step (i), eq. (7): for `t ≥ r`, after a history `h` of `t` periods that starts with
  `b_1, …, b_r`, the arm `U_{t+1}` maximizes `v′Ẑ_t + R^v_t` over `v ∈ 𝒰_r`. -/
  act_argmax : ∀ (t : ℕ), r ≤ t → ∀ h : LinParamBandits.LowerBound.History r t,
    (∀ (k : Fin t) (hk : (k : ℕ) < r), (h k).1 = b ⟨k, hk⟩) →
    ∀ v ∈ 𝒰, inner ℝ v (Zhat h) + radius 𝒰 σ₀ ubar lam0 h v ≤
      inner ℝ (ψ.act t h) (Zhat h) + radius 𝒰 σ₀ ubar lam0 h (ψ.act t h)

/-- The arm sequence of a history of `T` periods, extended by `0` beyond period `T`:
`armSeq h s = U_{s+1}` for `s < T`. -/
noncomputable def armSeq {T : ℕ} (h : LinParamBandits.LowerBound.History r T) : ℕ → LinParamBandits.LowerBound.Vec r :=
  fun s => if hs : s < T then (h ⟨s, hs⟩).1 else 0

/-- `‖U_{t+1}‖²_{C_t}` for an arm sequence `U` (with `U s` the paper's `U_{s+1}`):
the squared `C_t`-norm of the arm of period `t + 1`, `C_t` built from the arms of periods
`1, …, t` (pp. 35–38). -/
noncomputable def potential (U : ℕ → LinParamBandits.LowerBound.Vec r) (t : ℕ) : ℝ :=
  quadForm (Cmat (fun s : Fin t => U s)) (U t)

end LinParamBandits.UEGeneral


