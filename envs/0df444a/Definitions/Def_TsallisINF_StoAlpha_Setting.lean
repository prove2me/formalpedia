-- Prove2me | Definitions.Def_TsallisINF_StoAlpha_Setting
-- name    : TsallisINF_StoAlpha_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:38:34.564724+00:00
-- url     : https://prove2.me/theorems/406c1dd2-68c6-4fb6-b91d-0ff32e1dc809
-- title:
--   §2–§3, §4.2.2, App. C–D, pp. 5–8, 12, 34, 43–44 — randomized adaptive adversaries, the law of a run, pseudo-regret, α-Tsallis-INF with IW estimators, Φ_t, and the parameters of Theorem 4
-- statement:
--   This file fixes the model and the algorithm of Zimmert and Seldin's *Tsallis-INF* paper, as used for the stochastically constrained analysis (Theorem 4).
--
--   1. **Protocol and adversary (§2, p. 5).** There are $K$ arms and rounds $t=1,2,\dots$. In round $t$ the learner draws an arm $I_t$, the environment fixes a loss vector $\ell_t\in[0,1]^K$, and only $\ell_{t,I_t}$ is observed. The adversary may adapt to the past actions $I_1,\dots,I_{t-1}$ and use internal randomization: its randomness is a seed $\omega$ drawn from a probability measure $\mu$, and given $\omega$ the losses $\ell_{t,i}=\ell_{t,i}(\omega; I_1,\dots,I_{t-1})$ are those of a deterministic adaptive adversary (the published `RegretBandits.Adversarial.Adversary`).
--   2. **Law of a run.** Given the learner's weight vectors $w_t=w_t(\omega;I_1,\dots,I_{t-1})$ in the probability simplex $\Delta^{K-1}$, the expectation of a quantity $F$ over the first $T$ rounds is
--   $$\mathbb E[F]=\int \sum_{a\in[K]^T}\Big(\prod_{t=1}^T w_{t,a_t}\Big)\,F(\omega,a)\,d\mu(\omega),$$
--   i.e. $\omega\sim\mu$, then $I_t\sim w_t$ successively. $\mathbb E[w_{t,i}]$ is the expectation of $w_{t,i}$ under this law (for any horizon $T\ge t$).
--   3. **Pseudo-regret (p. 5).** $\overline{Reg}_T=\mathbb E\big[\sum_{t=1}^T\ell_{t,I_t}\big]-\min_i\mathbb E\big[\sum_{t=1}^T\ell_{t,i}\big]$; an arm attaining the minimum is a *best arm in hindsight* $i^*_T$.
--   4. **Self-bounding property (4), p. 10.** For a gap vector $\Delta$ with a unique zero $i^*$ and $C\ge 0$: $\overline{Reg}_T\ge\mathbb E\big[\sum_{t=1}^T\sum_{i\ne i^*}w_{t,i}\Delta_i\big]-C$.
--   5. **α-Tsallis-INF (Algorithm 1, p. 7, and §3.2, p. 8).** With regularization parameters $\xi_i>0$ and learning rates $\eta_t>0$, the regularizer is
--   $$\Psi(w)=-\sum_i\frac{w_i^\alpha-\alpha w_i}{\alpha(1-\alpha)\xi_i},\qquad \Psi_t=\Psi/\eta_t,$$
--   the importance-weighted estimator (IW) is $\hat\ell_{t,i}=\mathbb 1(I_t=i)\,\ell_{t,i}/w_{t,i}$, $\hat L_{t}=\sum_{s\le t}\hat\ell_s$, and the algorithm plays
--   $$w_t=\arg\max_{w\in\Delta^{K-1}}\ \langle w,-\hat L_{t-1}\rangle-\Psi_t(w).$$
--   The potential is $\Phi_t(Y)=\max_{w\in\Delta^{K-1}}\langle w,Y\rangle-\Psi_t(w)$. The *stability* and *penalty* terms (6) are $\mathbb E\big[\sum_t\ell_{t,I_t}+\Phi_t(-\hat L_t)-\Phi_t(-\hat L_{t-1})\big]$ and $\mathbb E\big[\sum_t\Phi_t(-\hat L_{t-1})-\Phi_t(-\hat L_t)-\ell_{t,i^*_T}\big]$.
--   6. **Parameters of Theorem 4 (§4.2.2, p. 12).** $\bar t=\max\{e,t\}$, $\eta_t=\frac{16^\alpha}{4}\,\frac{1-\bar t^{-1+\alpha}}{(1-\alpha)t^\alpha}$, $\Delta_{\min}=\min_{i\ne i^*}\Delta_i$, $\xi_i=\Delta_i^{1-2\alpha}$ for $i\ne i^*$ and $\xi_{i^*}=\Delta_{\min}^{1-2\alpha}$; and $T_0=\frac{16}{\Delta_{\min}^2}\log^2\frac{16}{\Delta_{\min}^2}$ (App. D, p. 44).
--   7. **Gradients (App. C, p. 34).** $\nabla\Psi_t(w)_i=-\frac{w_i^{\alpha-1}-1}{(1-\alpha)\eta_t\xi_i}$ and, from (9), $\nabla\Psi_t^*(Y)_i=\big(-\eta_t(1-\alpha)\xi_iY_i+1\big)^{1/(\alpha-1)}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Arms are `Fin K` (index base 0). An action sequence is `h : ℕ → Fin K` with `h t` $=I_t$ and `h 0` unused; `expect` sums over the action paths `Fin T → Fin K`, extended to `ℕ → Fin K` by a filler arm that never matters. The algorithm is the predicate `IsAlphaTsallisINF`, with the objective multiplied through by $\eta_t$; for positive $\eta_t$ this is exactly the argmax, which is unique (strictly concave objective), so the predicate determines $w_t$. `Lhat est t` is $\hat L_{t-1}$. `Phi` is a real supremum over the simplex subtype, which is nonempty and on which the objective is continuous, hence bounded. $\Delta_{\min}$ is a finite minimum over $i\ne i^*$ and needs $K\ge 2$. Real powers are `Real.rpow`, with nonnegative bases wherever they are used.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 5–8 (Section 2, Algorithm 1, (IW), §3.2), p. 10 (4), p. 12 (§4.2.2), p. 34 (App. C, (9)), p. 44 (T_0)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_TsallisINF_AdvAlpha_Setting
import Definitions.Def_TsallisINF_Half_Setting

namespace TsallisINF.StoAlpha

open MeasureTheory

/-- The adversary of Section 2 (p. 5), given the outcome of its internal randomization: losses
`val t h i ∈ [0,1]` that depend on the actions `h 1, …, h (t-1)` only. -/
abbrev Adversary (K : ℕ) := RegretBandits.Adversarial.Adversary K

/-- `E[w_{t,i}]` computed with the law of the first `T` rounds (any `T ≥ t` gives the same
value). -/
noncomputable def meanW {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T t : ℕ) (i : Fin K) : ℝ :=
  TsallisINF.Half.expect μ W i₀ T (fun ω h => W t ω h i)

/-- Pseudo-regret (p. 5): `Reg_T = E[∑_{t=1}^T ℓ_{t,I_t}] - min_i E[∑_{t=1}^T ℓ_{t,i}]`. -/
noncomputable def pseudoRegret {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ) : ℝ :=
  TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h (h t)) -
    ⨅ i : Fin K, TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h i)

/-- `j` is a best arm in expectation in hindsight at horizon `T` (p. 5):
`j ∈ argmin_i E[∑_{t=1}^T ℓ_{t,i}]`. -/
def IsBestInHindsight {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (j : Fin K) : Prop :=
  ∀ i : Fin K,
    TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h j) ≤
      TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h i)

/-- The self-bounding property (4), p. 10:
`Reg_T ≥ E[∑_{t=1}^T ∑_{i ≠ i*} w_{t,i} Δ_i] - C`. -/
def SelfBounding {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K) (T : ℕ)
    (Δ : Fin K → ℝ) (istar : Fin K) (C : ℝ) : Prop :=
  TsallisINF.Half.expect μ W i₀ T (fun ω h =>
      ∑ t ∈ Finset.Icc 1 T, ∑ i ∈ Finset.univ.erase istar, W t ω h i * Δ i) - C ≤
    pseudoRegret μ adv W i₀ T

/-- The importance-weighted loss estimator (IW), p. 7:
`ℓ̂_{t,i} = 1(I_t = i) ℓ_{t,i} / w_{t,i}`. -/
noncomputable def estIW {K : ℕ} {Ω : Type*} (adv : Ω → Adversary K)
    (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (t : ℕ) (ω : Ω) (h : ℕ → Fin K) (i : Fin K) : ℝ :=
  if h t = i then (adv ω).val t h i / W t ω h i else 0

/-- An estimator at round `t` uses only the actions through round `t`, as required by the
bandit feedback protocol of §3.1 (p. 7). -/
def IsCausalEstimator {K : ℕ} {Ω : Type*}
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ (ω : Ω) (h h' : ℕ → Fin K),
    RegretBandits.Adversarial.AgreeBefore (t + 1) h h' →
      est t ω h = est t ω h'

/-- α-Tsallis-INF (Algorithm 1, p. 7, with the regularizer of §3.2): for every round `t ≥ 1`,
seed `ω` and action sequence `h`, the weight vector `w_t = W t ω h` lies in the probability
simplex and maximizes `⟨w, -L̂_{t-1}⟩ - Ψ(w)/η_t` over the simplex (the objective is multiplied
through by `η_t`, which is positive wherever the predicate is used). `est` is the loss
estimator, computed from `W` itself. -/
def IsAlphaTsallisINF {K : ℕ} {Ω : Type*} (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ (ω : Ω) (h : ℕ → Fin K),
    W t ω h ∈ stdSimplex ℝ (Fin K) ∧
      ∀ v ∈ stdSimplex ℝ (Fin K),
        η t * (∑ i, v i * -TsallisINF.Half.Lhat est t ω h i) - TsallisINF.AdvAlpha.tsallisPsi α ξ v ≤
          η t * (∑ i, W t ω h i * -TsallisINF.Half.Lhat est t ω h i) - TsallisINF.AdvAlpha.tsallisPsi α ξ (W t ω h)

/-- The instantaneous stability at round `t` with IW estimators (Lemma 11, p. 20):
`E[ℓ_{t,I_t} + Φ_t(-L̂_t) - Φ_t(-L̂_{t-1})]`, taken with the law of the first `t` rounds. -/
noncomputable def instStability {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ) (t : ℕ) : ℝ :=
  TsallisINF.Half.expect μ W i₀ t (fun ω h =>
    (adv ω).val t h (h t) + TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (estIW adv W) (t + 1) ω h i) -
      TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (estIW adv W) t ω h i))

/-- The stability term (6), p. 18, with IW estimators:
`E[∑_{t=1}^T ℓ_{t,I_t} + Φ_t(-L̂_t) - Φ_t(-L̂_{t-1})]`. -/
noncomputable def stability {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ) (T : ℕ) : ℝ :=
  TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T,
    ((adv ω).val t h (h t) + TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (estIW adv W) (t + 1) ω h i) -
      TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat (estIW adv W) t ω h i)))

/-- The penalty term (6), p. 18, with an estimator and comparator arm `j` (the paper's
`i*_T`): `E[∑_{t=1}^T Φ_t(-L̂_{t-1}) - Φ_t(-L̂_t) - ℓ_{t,j}]`. -/
noncomputable def penaltyWith {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (T : ℕ) (j : Fin K) : ℝ :=
  TsallisINF.Half.expect μ W i₀ T (fun ω h => ∑ t ∈ Finset.Icc 1 T,
    (TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat est t ω h i) -
      TsallisINF.AdvAlpha.Phi α ξ (η t) (fun i => -TsallisINF.Half.Lhat est (t + 1) ω h i) - (adv ω).val t h j))

/-- The penalty term specialized to the importance-weighted estimator (IW), p. 7. -/
noncomputable def penalty {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (adv : Ω → Adversary K) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (i₀ : Fin K)
    (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ) (T : ℕ) (j : Fin K) : ℝ :=
  penaltyWith μ adv W i₀ α ξ η (estIW adv W) T j

/-- `Δ_min = min_{i ≠ i*} Δ_i` (p. 12); the minimum is over a nonempty set because `1 < K`. -/
noncomputable def deltaMin {K : ℕ} (hK : 1 < K) (Δ : Fin K → ℝ) (istar : Fin K) : ℝ :=
  (Finset.univ.erase istar).inf'
    (Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega)) Δ

/-- `t̄ = max{e, t}` (§4.2.2, p. 12). -/
noncomputable def tbar (t : ℕ) : ℝ := max (Real.exp 1) (t : ℝ)

/-- The learning rate of Theorem 4 (p. 12):
`η_t = (16^α / 4) · (1 - t̄^{-1+α}) / ((1 - α) t^α)`. -/
noncomputable def etaThm4 (α : ℝ) (t : ℕ) : ℝ :=
  16 ^ α / 4 * (1 - tbar t ^ (-1 + α)) / ((1 - α) * (t : ℝ) ^ α)

/-- The asymmetric regularization parameters of Theorem 4 (p. 12): `ξ_i = Δ_i^{1-2α}` for
`i ≠ i*` and `ξ_{i*} = Δ_min^{1-2α}`. -/
noncomputable def xiThm4 {K : ℕ} (hK : 1 < K) (α : ℝ) (Δ : Fin K → ℝ) (istar : Fin K)
    (i : Fin K) : ℝ :=
  if i = istar then deltaMin hK Δ istar ^ (1 - 2 * α) else Δ i ^ (1 - 2 * α)

/-- `T₀ = (16/Δ_min²) log²(16/Δ_min²)` (App. D, p. 44). -/
noncomputable def T0 {K : ℕ} (hK : 1 < K) (Δ : Fin K → ℝ) (istar : Fin K) : ℝ :=
  16 / deltaMin hK Δ istar ^ 2 * Real.log (16 / deltaMin hK Δ istar ^ 2) ^ 2

/-- The gradient of `Ψ_t` (App. C, p. 34):
`∇Ψ_t(w)_i = -(w_i^{α-1} - 1) / ((1 - α) η_t ξ_i)`, with `η = η_t`. -/
noncomputable def gradPsi {K : ℕ} (α : ℝ) (ξ : Fin K → ℝ) (η : ℝ) (w : Fin K → ℝ)
    (i : Fin K) : ℝ :=
  -(w i ^ (α - 1) - 1) / ((1 - α) * η * ξ i)

/-- The gradient of the conjugate `Ψ_t^*`, coordinatewise from (9), p. 34:
`∇Ψ_t^*(Y)_i = (-η_t (1 - α) ξ_i Y_i + 1)^{1/(α-1)}`, with `η = η_t`. -/
noncomputable def gradPsiConj {K : ℕ} (α : ℝ) (ξ : Fin K → ℝ) (η : ℝ) (Y : Fin K → ℝ)
    (i : Fin K) : ℝ :=
  (-η * (1 - α) * ξ i * Y i + 1) ^ (1 / (α - 1))

end TsallisINF.StoAlpha


