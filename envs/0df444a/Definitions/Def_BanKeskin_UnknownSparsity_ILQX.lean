-- Prove2me | Definitions.Def_BanKeskin_UnknownSparsity_ILQX
-- name    : BanKeskin_UnknownSparsity_ILQX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:51.394916+00:00
-- url     : https://prove2.me/theorems/eef1fcb4-7883-4ae9-9485-b36ca15ebd6c
-- title:
--   pp. 5552–5557 — features, sub-Gaussian shocks, the ILQX(m₁, m₂, λ) pricing policy (18)–(19) and its expected regret (3)–(4)
-- statement:
--   This definition builds the stochastic part of the model of Ban and Keskin (2021) on top of the static model $M$ (prices, $\Theta$, link $g$, clairvoyant price $\varphi$).
--
--   **Standing assumptions** (§2.1). On a probability space $(\Omega,\mathbb P)$ live raw features $Z_t\in\mathbb R^d$ and shocks $\varepsilon_t\in\mathbb R$, $t\ge1$; $X_t = [1;Z_t]$. Write $\mathcal G_t = \sigma(Z_1,\dots,Z_{t+1},\varepsilon_1,\dots,\varepsilon_t)$. The setting requires, for periods $t\ge1$:
--
--   1. $(Z_t)$ i.i.d., measurable, with values in the support $\mathcal Z$, $\mathbb E[Z_1]=0$, and $\Sigma_Z = \mathbb E[Z_1Z_1^\top]$ positive definite ($\mathbb E[(v\cdot Z_1)^2]>0$ for $v\ne0$);
--   2. fresh customers: $Z_{t+1}$ is independent of $\sigma(Z_1,\dots,Z_t,\varepsilon_1,\dots,\varepsilon_t)$;
--   3. $(\varepsilon_t)$ is a sub-Gaussian martingale difference sequence: $\varepsilon_t$ integrable, $\mathbb E[\varepsilon_t\mid\mathcal G_{t-1}] = 0$, $\mathbb E[\varepsilon_t^2\mid\mathcal G_{t-1}]\le\sigma_0^2$ and $\mathbb E[e^{\eta\varepsilon_t}\mid\mathcal G_{t-1}]<\infty$ for $|\eta|<\eta_0$, with $\sigma_0,\eta_0>0$.
--
--   **Estimator** (18). A sequence of maps $\mathrm{est}_n$, from histories $(x_k,p_k,D_k)_{k=1}^n$ to $\mathbb R^{2(d+1)}$, is a *maximum quasi-likelihood lasso estimate* if every $\mathrm{est}_n$ is measurable and, for $n\ge2$, whenever $\tilde\theta\mapsto\bar Q_n(\tilde\theta,\lambda_{n+1})$ has a maximizer, $\mathrm{est}_n$ is one of them. Thus $\mathrm{est}_n = \hat\theta^{(\mathrm{lasso})}_{n+1}(\lambda_{n+1})$.
--
--   **Policy** (19). For the true parameter $\theta$, ILQX$(m_1,m_2,\lambda)$ charges
--
--   $$p_t = \begin{cases} m_1 & t\in M_1,\\ m_2 & t\in M_2,\\ \varphi\big(\mathcal P_\Theta(\mathrm{est}_{t-1}(H_{t-1})),\,X_t\big) & \text{otherwise,}\end{cases}$$
--
--   where $H_{t-1} = (X_k,p_k,D_k)_{k=1}^{t-1}$ is the realized history and $D_k = g(\theta\cdot u(p_k,X_k))+\varepsilon_k$ (1). The estimator sees $\theta$ only through the demands.
--
--   **Regret** (3)–(4):
--
--   $$\Delta_\theta(T) = \mathbb E\Big[\sum_{t=1}^T \big(r^*(\theta,X_t) - r(p_t,\theta,X_t)\big)\Big].$$
--
--   This is the expected regret of the paper; by the tower property it equals $\mathbb E_X$ of the conditional regret (3).
--
--   **Formalization Note.** The price is defined by strong recursion on $t$, and the pricing map after projection and feature augmentation is measurable so this policy is admissible. The paper's $\mathcal F_t$ also contains $p_1,\dots,p_t$; under ILQX these are functions of the primitives, so $\mathcal G_t$ is that σ-algebra. The shocks are one fixed process on $(\Omega,\mathbb P)$ for every $\theta$; the paper lets the law of $\varepsilon_t$ depend on prices, which for a fixed $\theta$ is representable since prices are functions of the primitives. Conditional second and exponential moments use the conditional Lebesgue expectation `condLExp` ($\mathbb P^-[\cdot\mid\cdot]$), which has no junk value on non-integrable functions. The paper says (18) has a unique maximizer; this is false when $2(d+1)$ exceeds the rank of the design, so any measurable maximizer selection is allowed, and the theorems hold for every one. The regret is a lower Lebesgue integral of the nonnegative per-period losses, so it cannot vanish by non-integrability. The fresh-customer independence is the reading of the paper's product construction of $\mathbb P^\pi_\theta$ (p. 5553).
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), pp. 5552–5553, §2.1–2.2 and (1)–(3); p. 5554, (4); p. 5557, (18)–(19); p. 5568, endnote 1

import Mathlib
import Definitions.Def_BanKeskin_UnknownSparsity_Model

namespace BanKeskin.UnknownSparsity

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The augmented feature process `X_t = [1; Z_t]`. -/
def featProc (Z : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Feat d := featX (Z t ω)

/-- The σ-algebra `σ(Z_1, …, Z_t, ε_1, …, ε_t)` of the primitives up to period `t`. -/
def pastSigma (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  (⨆ k ∈ Finset.Icc 1 t, MeasurableSpace.comap (Z k) inferInstance) ⊔
    (⨆ k ∈ Finset.Icc 1 t, MeasurableSpace.comap (ε k) inferInstance)

/-- The σ-algebra `𝒢_t = σ(Z_1, …, Z_{t+1}, ε_1, …, ε_t)`. Under ILQX the prices
`p_1, …, p_t` are functions of these primitives, so `𝒢_t` is the paper's `ℱ_t`. -/
def infoSigma (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  pastSigma Z ε t ⊔ MeasurableSpace.comap (Z (t + 1)) inferInstance

/-- The stochastic standing assumptions of §2.1 (pp. 5552–5553) on a probability space
`(Ω, P)` carrying the raw features `Z_t` and the demand shocks `ε_t` (`t ≥ 1`):
* the features are i.i.d., measurable, take values in the support `𝒵`, have mean zero and a
  positive definite second-moment matrix `Σ_Z`;
* a fresh customer: `Z_{t+1}` is independent of `σ(Z_1, …, Z_t, ε_1, …, ε_t)`;
* the shocks form a martingale difference sequence for `𝒢_{t-1}` with conditional variance
  at most `σ₀²` and conditionally finite exponential moments `E[e^{η ε_t} | 𝒢_{t-1}] < ∞` for
  `|η| < η₀`. -/
structure Model.Setting (M : Model d) (P : Measure Ω) (Z : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (σ0 η0 : ℝ) : Prop where
  Z_meas : ∀ t, 1 ≤ t → Measurable (Z t)
  Z_iIndep : iIndepFun (fun t : {t : ℕ // 1 ≤ t} => Z t) P
  Z_identDistrib : ∀ t, 1 ≤ t → IdentDistrib (Z t) (Z 1) P P
  Z_mem : ∀ t, 1 ≤ t → ∀ ω, Z t ω ∈ M.Zset
  Z_integrable : Integrable (Z 1) P
  Z_mean_zero : ∫ ω, Z 1 ω ∂P = 0
  Z_cov_posDef : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < ∫ ω, (v ⬝ᵥ Z 1 ω) ^ 2 ∂P
  fresh : ∀ t, Indep (MeasurableSpace.comap (Z (t + 1)) inferInstance) (pastSigma Z ε t) P
  ε_meas : ∀ t, 1 ≤ t → Measurable (ε t)
  ε_integrable : ∀ t, 1 ≤ t → Integrable (ε t) P
  σ0_pos : 0 < σ0
  η0_pos : 0 < η0
  ε_mds : ∀ t, 1 ≤ t → condExp (infoSigma Z ε (t - 1)) P (ε t) =ᵐ[P] 0
  ε_var : ∀ t, 1 ≤ t →
    condLExp (infoSigma Z ε (t - 1)) P (fun ω => ENNReal.ofReal (ε t ω ^ 2))
      ≤ᵐ[P] fun _ => ENNReal.ofReal (σ0 ^ 2)
  ε_mgf : ∀ t, 1 ≤ t → ∀ η : ℝ, |η| < η0 → ∀ᵐ ω ∂P,
    condLExp (infoSigma Z ε (t - 1)) P (fun ω => ENNReal.ofReal (Real.exp (η * ε t ω))) ω < ⊤

/-- An estimator `est n h ∈ ℝ^{2(d+1)}` computed from the history `h` of the first `n`
periods (entries `(x_k, p_k, D_k)`, entry `k` of `Fin n` being period `k + 1`) is a
maximum quasi-likelihood lasso estimate (18) for the schedule `λ_{n+1} = c̃ n^{1/4}
√(log d + log n)`: each `est n` is measurable, and for `n ≥ 2`, whenever the objective `Qbar`
with `λ̃ = λ_{n+1}` has a maximizer, `est n h` is one of them. -/
def Model.IsLassoMQLE (M : Model d) (c : ℝ)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) : Prop :=
  (∀ n, Measurable (est n)) ∧
    ∀ n, 2 ≤ n → ∀ h : Fin n → Feat d × ℝ × ℝ,
      (∃ θ' : Param d, ∀ θ'' : Param d, Qbar M.g n h θ'' (lam c d n) ≤ Qbar M.g n h θ' (lam c d n)) →
        ∀ θ'' : Param d, Qbar M.g n h θ'' (lam c d n) ≤ Qbar M.g n h (est n h) (lam c d n)

open Classical in
/-- The price charged in period `t` (1-based) by ILQX(m₁, m₂, λ) (19) when the true parameter
is `θ`: `m₁` on `M₁`, `m₂` on `M₂`, and otherwise `φ(𝒫_Θ(θ̂_t), X_t)`, where the estimate
`θ̂_t = est (t-1) H_{t-1}` is computed from the realized history of periods `1, …, t-1`, whose
demands are `D_k = g(θ · u(p_k, X_k)) + ε_k` (1). -/
noncomputable def Model.price (M : Model d) (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (θ : Param d) (t : ℕ) (ω : Ω) : ℝ :=
  if BanKeskin.KnownSparsity.inM1 t then M.m1 else if BanKeskin.KnownSparsity.inM2 t then M.m2 else
    M.φ (clamp M.lo M.hi (est (t - 1) (fun k : Fin (t - 1) =>
      (featProc Z (k.val + 1) ω, M.price Z ε est θ (k.val + 1) ω,
        M.g (θ ⬝ᵥ regr (M.price Z ε est θ (k.val + 1) ω) (featProc Z (k.val + 1) ω)) +
          ε (k.val + 1) ω)))) (featProc Z t ω)
termination_by t
decreasing_by all_goals (have := k.isLt; omega)

/-- The demand `D_t = g(θ · u(p_t, X_t)) + ε_t` (1) realized in period `t` under ILQX. -/
noncomputable def Model.demand (M : Model d) (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (θ : Param d) (t : ℕ) (ω : Ω) : ℝ :=
  M.g (θ ⬝ᵥ regr (M.price Z ε est θ t ω) (featProc Z t ω)) + ε t ω

/-- The history `H_n = (x_k, p_k, D_k)_{k = 1, …, n}` of the first `n` periods under ILQX
(entry `k` of `Fin n` is period `k + 1`). -/
noncomputable def Model.hist (M : Model d) (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (θ : Param d) (n : ℕ) (ω : Ω) :
    Fin n → Feat d × ℝ × ℝ :=
  fun k => (featProc Z (k.val + 1) ω, M.price Z ε est θ (k.val + 1) ω,
    M.demand Z ε est θ (k.val + 1) ω)

/-- The `T`-period expected regret (3)–(4) of ILQX:
`Δ_θ(T) = E[Σ_{t=1}^T (r*(θ, X_t) - r(p_t, θ, X_t))]`, as a lower Lebesgue integral of the
(nonnegative) per-period revenue losses. -/
noncomputable def Model.regret (M : Model d) (P : Measure Ω) (Z : ℕ → Ω → Fin d → ℝ)
    (ε : ℕ → Ω → ℝ) (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (θ : Param d)
    (T : ℕ) : ENNReal :=
  ∫⁻ ω, ∑ t ∈ Finset.Icc 1 T,
    ENNReal.ofReal (M.rstar θ (featProc Z t ω) -
      revenue M.g (M.price Z ε est θ t ω) θ (featProc Z t ω)) ∂P

end BanKeskin.UnknownSparsity


