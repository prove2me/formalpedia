-- Prove2me | Definitions.Def_TsallisINF_AdvAlpha_Setting
-- name    : TsallisINF_AdvAlpha_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:57.913669+00:00
-- url     : https://prove2.me/theorems/41fd9dce-c18f-425b-a3c1-cf571fa5607d
-- title:
--   §3.1–§3.2, pp. 6–8, 11–12 — the α-Tsallis regularizer and its α→0, α→1 limits, OMD for bandits, α-Tsallis-INF, its potential Φ_t and the learning rates of Theorem 3
-- statement:
--   This file fixes the α-Tsallis objects of Zimmert and Seldin's general analysis (Sections 3.1–3.2 and Theorem 3). The protocol, the law of a run, the pseudo-regret and the cumulative estimates $\hat L_{t-1}=\sum_{s=1}^{t-1}\hat\ell_s$ are those of the imported setting `TsallisINF.Half.Setting`.
--
--   1. **Cumulative loss.** $L_{T,i}=\sum_{t=1}^T\ell_{t,i}$.
--
--   2. **Regularizer.** For $\alpha\in(0,1)$ and parameters $\xi_i>0$,
--   $$
--   \Psi(w)=-\sum_i\frac{w_i^\alpha-\alpha w_i}{\alpha(1-\alpha)\xi_i},\qquad \Psi_t=\Psi/\eta_t .
--   $$
--   Symmetric regularization is $\xi_i=1$. The limits $\alpha\to1$ and $\alpha\to0$ (with $\xi_i=1$, up to linear and constant terms) are the negative Shannon entropy $\sum_i(w_i\log w_i-w_i+1)$ and the log-barrier $-\sum_i(\log w_i-w_i+1)$.
--
--   3. **Online mirror descent (Algorithm 1).** At every round $t\ge1$,
--   $$
--   w_t\in\Delta^{K-1}\ \text{maximizes}\ \ \eta_t\langle w,-\hat L_{t-1}\rangle-\Psi(w)\ \ \text{over the simplex }\Delta^{K-1},
--   $$
--   which for $\eta_t>0$ is $w_t=\arg\max_{w}\langle w,-\hat L_{t-1}\rangle-\Psi_t(w)$ and for $\eta_t=0$ is $w_1=\arg\min_\Delta\Psi$, the initialisation of online mirror descent (p. 6). With the α-Tsallis regularizer this is **α-Tsallis-INF**. For the log-barrier the weights and competitors range over the open simplex.
--
--   4. **Potential.** $\Phi_t(Y)=(\Psi_t+\mathcal I_{\Delta^{K-1}})^*(Y)=\max_{w\in\Delta^{K-1}}\langle w,Y\rangle-\Psi(w)/\eta_t$.
--
--   5. **Learning rates of Theorem 3.** $\eta_t=\sqrt{\frac{K^{1-2\alpha}-K^{-\alpha}}{1-\alpha}\cdot\frac{1-t^{-\alpha}}{\alpha t}}$, and at the boundaries $\sqrt{\log(K)(1-t^{-1})/t}$ ($\alpha\to1$) and $\sqrt{(K-1)\log(t)/t}$ ($\alpha\to0$).
--
--   These objects are shared by the missions on the adversarial and the stochastic analysis of α-Tsallis-INF.
--
--   **Formalization Note** Arms are `Fin K` (index base $0$). The weights are given by an argmax **predicate** on a function `W`, never by a choice function; the objective is multiplied by $\eta_t$, so that at $\eta_1=0$ (Theorem 3's rate vanishes at $t=1$) the predicate pins $w_1=\arg\min_\Delta\Psi$, the uniform vector for symmetric regularization. The maximizer is unique (strictly concave objective), so the predicate determines `W`. $\Phi_t$ is a real supremum over the simplex, which is nonempty and on which the objective is continuous, so the supremum is attained; it is meant for $\eta>0$. Powers are `Real.rpow`, and $\log$ is the natural logarithm.
-- source:
--   Zimmert & Seldin, Tsallis-INF: An Optimal Algorithm for Stochastic and Adversarial Bandits, arXiv:1807.07623v6, pp. 5–8, Section 2, §3.1, Algorithm 1, (IW), §3.2; pp. 11–12, Theorem 3 (learning rates)

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_TsallisINF_Half_Setting

namespace TsallisINF.AdvAlpha

open MeasureTheory RegretBandits.Adversarial

/-- Cumulative true loss of arm `i` up to round `T`: `L_{T,i} = ∑_{t=1}^T ℓ_{t,i}`. -/
def cumLoss {K : ℕ} {Ω : Type*} (adv : Ω → Adversary K) (T : ℕ) (ω : Ω) (h : ℕ → Fin K)
    (i : Fin K) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (adv ω).val t h i

/-- The α-Tsallis regularizer of §3.2, p. 8 (`Real.rpow`):
`Ψ(w) = −∑_i (w_i^α − α w_i) / (α (1 − α) ξ_i)`. Used for `α ∈ (0, 1)`. -/
noncomputable def tsallisPsi {K : ℕ} (α : ℝ) (ξ : Fin K → ℝ) (w : Fin K → ℝ) : ℝ :=
  -∑ i, (w i ^ α - α * w i) / (α * (1 - α) * ξ i)

/-- The `α → 1` limit regularizer of §3.2, p. 8, with `ξ_i = 1` (negative Shannon entropy up to
linear and constant terms): `∑_i (w_i log w_i − w_i + 1)`. -/
noncomputable def shannonPsi {K : ℕ} (w : Fin K → ℝ) : ℝ :=
  ∑ i, (w i * Real.log (w i) - w i + 1)

/-- The `α → 0` limit regularizer of §3.2, p. 8, with `ξ_i = 1` (log-barrier up to linear and
constant terms): `−∑_i (log w_i − w_i + 1)`. Only meaningful for `w_i > 0`. -/
noncomputable def logBarrierPsi {K : ℕ} (w : Fin K → ℝ) : ℝ :=
  -∑ i, (Real.log (w i) - w i + 1)

/-- Online mirror descent for bandits (Algorithm 1, p. 7) with regularizer `Ψ_t = Ψ / η_t`:
for every round `t ≥ 1`, `w_t ∈ Δ^{K−1}` maximizes `⟨w, −L̂_{t−1}⟩ − Ψ(w)/η_t` over the
simplex. The objective is multiplied by `η_t ≥ 0`; for `η_t = 0` this is `argmin_{Δ} Ψ`, the
OMD initialisation of §3.1, p. 6. -/
def IsOMDBandit {K : ℕ} {Ω : Type*} (Ψ : (Fin K → ℝ) → ℝ) (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ ω h, W t ω h ∈ stdSimplex ℝ (Fin K) ∧
    ∀ v ∈ stdSimplex ℝ (Fin K),
      η t * (∑ i, v i * -TsallisINF.Half.Lhat est t ω h i) - Ψ v ≤
        η t * (∑ i, W t ω h i * -TsallisINF.Half.Lhat est t ω h i) - Ψ (W t ω h)

/-- Same as `IsOMDBandit`, but for a regularizer that is `+∞` on the boundary of the simplex
(the log-barrier): the weights lie in the open simplex and maximize over it. -/
def IsOMDBanditInterior {K : ℕ} {Ω : Type*} (Ψ : (Fin K → ℝ) → ℝ) (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  ∀ t, 1 ≤ t → ∀ ω h, W t ω h ∈ stdSimplex ℝ (Fin K) ∧ (∀ i, 0 < W t ω h i) ∧
    ∀ v ∈ stdSimplex ℝ (Fin K), (∀ i, 0 < v i) →
      η t * (∑ i, v i * -TsallisINF.Half.Lhat est t ω h i) - Ψ v ≤
        η t * (∑ i, W t ω h i * -TsallisINF.Half.Lhat est t ω h i) - Ψ (W t ω h)

/-- α-Tsallis-INF (§3.2, p. 8): OMD with the α-Tsallis regularizer with parameters `ξ`,
learning rates `η` and loss estimators `est`. -/
def IsAlphaTsallisINF {K : ℕ} {Ω : Type*} (α : ℝ) (ξ : Fin K → ℝ) (η : ℕ → ℝ)
    (est : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) (W : ℕ → Ω → (ℕ → Fin K) → Fin K → ℝ) : Prop :=
  IsOMDBandit (tsallisPsi α ξ) η est W

/-- The potential `Φ_t(Y) = (Ψ_t + I_Δ)^*(Y) = max_{w ∈ Δ^{K−1}} ⟨w, Y⟩ − Ψ(w)/η_t` (p. 7),
for the α-Tsallis regularizer and a learning rate `η > 0`. -/
noncomputable def Phi {K : ℕ} (α : ℝ) (ξ : Fin K → ℝ) (η : ℝ) (Y : Fin K → ℝ) : ℝ :=
  ⨆ w : stdSimplex ℝ (Fin K), (∑ i, (w : Fin K → ℝ) i * Y i) - η⁻¹ * tsallisPsi α ξ w

/-- The learning rate of Theorem 3, p. 11:
`η_t = √( (K^{1−2α} − K^{−α})/(1 − α) · (1 − t^{−α})/(α t) )` (`η_1 = 0`). -/
noncomputable def etaThm3 (α : ℝ) (K : ℕ) (t : ℕ) : ℝ :=
  Real.sqrt (((K : ℝ) ^ (1 - 2 * α) - (K : ℝ) ^ (-α)) / (1 - α) *
    ((1 - (t : ℝ) ^ (-α)) / (α * t)))

/-- The `α → 1` learning rate of Theorem 3, p. 12: `η_t = √(log(K)(1 − t^{−1})/t)`. -/
noncomputable def etaThm3One (K : ℕ) (t : ℕ) : ℝ :=
  Real.sqrt (Real.log K * (1 - (t : ℝ)⁻¹) / t)

/-- The `α → 0` learning rate of Theorem 3, p. 12: `η_t = √((K − 1) log(t)/t)`. -/
noncomputable def etaThm3Zero (K : ℕ) (t : ℕ) : ℝ :=
  Real.sqrt (((K : ℝ) - 1) * Real.log t / t)

end TsallisINF.AdvAlpha


