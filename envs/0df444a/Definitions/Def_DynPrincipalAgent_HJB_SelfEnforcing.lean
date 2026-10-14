-- Prove2me | Definitions.Def_DynPrincipalAgent_HJB_SelfEnforcing
-- name    : DynPrincipalAgent_HJB_SelfEnforcing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:54.630021+00:00
-- url     : https://prove2.me/theorems/d97a47a6-b2f7-450f-8512-8cec2a96918c
-- title:
--   (2.25), (3.7), (3.9), (5.1), (4.4) — V^P_0, ū_0, u_1, the recursion u_n, ū_n and the boundary conditions (4.4)
-- statement:
--   This file defines the principal's values when only finitely many quittings are tolerated.
--
--   **Self-enforcing contracts (2.25).**
--   $$V^P_0(\theta;t)=\sup_{\eta\in\mathcal A^P_t}\mathbb E^{\theta,Z^{\theta;\eta}}\Big[\int_t^T\big[I^h(\theta;s,Z^{\theta;\eta}_s)-\eta_s\big]ds\Big]\quad\text{subject to}\quad Y^{\theta,\eta}_s\ge R^\theta_s,\ t\le s\le T,$$
--   and $\overline u_0(t)=\sup_{\tilde\theta\in\Theta}V^P_0(\tilde\theta;t)-c^P_t$ (3.7).
--
--   **At most $n$ quittings (3.9), (5.1).** For a new-hire value $g$, let
--   $$u^g(\theta;t,x)=\sup_{(\eta,Z)\in\mathcal A^\theta_{t,x}}\mathbb E^{\theta,Z}\Big[\int_t^{\tau}\big[I^h(\theta;s,Z_s)-\eta_s\big]ds+g(\tau)\mathbf 1_{\{\tau<T\}}\Big],\qquad\tau=\tau^{\theta;t,x,\eta,Z}.$$
--   Then $u_1=u^{\overline u_0}$ (3.9), and recursively $u_n=u^{\overline u_{n-1}}$ and $\overline u_n(t)=\sup_\theta u_n(\theta;t,R^\theta_t)-c^P_t$ (5.1).
--
--   **Boundary conditions (4.4)** for a function $u(t,x)$ of type $\theta$ and a boundary function $g$:
--   $$u(t,\overline L^\theta_t)=-C_0(T-t),\qquad u(T-,x)=0\ \ (x\in(\underline L^\theta_T,0)),\qquad u(t,\underline L^\theta_t+)\ge g(t),$$
--   with $g=\overline u_0$ in (4.4).
--
--   **Formalization Note.** The BSDE (2.13) is used in forward form (Remark 7.3): $\eta$ is feasible in (2.25) when for some $x$ and $Z$, $(\eta,Z)\in\mathcal A^\theta_{t,x}$ and $\mathcal X^{\theta;t,x,\eta,Z}_s\ge R^\theta_s$ on $[t,T]$ almost surely; then $x=Y^{\theta,\eta}_t$ and $Z=Z^{\theta,\eta}$ by uniqueness for (2.13). Expectations are recorded only when they are genuine (integrable payoffs, almost surely integrable running rewards). In (4.4) the right limit at $\underline L^\theta_t$ is required to exist as a real number.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, (2.25), p. 12; (3.7) and (3.9), p. 15; (4.4), p. 18; (5.1), p. 27; Remark 7.3, p. 35

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Controls

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DynPrincipalAgent.HJB

open Peng1990.SMP

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

namespace Model

variable {Θ : Type} (M : Model Θ) (S : Setting Ω)

/-- The set of values `J_P(θ; t, η)` of (2.25) over self-enforcing contracts, in forward form
(Remark 7.3): `η ∈ 𝒜^P_t` such that for some `x` and `Z`, `(η, Z) ∈ 𝒜^θ_{t,x}` (so that `x = Y^{θ,η}_t`,
`Z = Z^{θ,η}`) and `𝒳^{θ;t,x,η,Z}_s ≥ R^θ_s` for all `s ∈ [t, T]`, almost surely.
`J_P(θ; t, η) = E^{θ,Z}[∫_t^T [I^h(θ; s, Z_s) − η_s] ds]`, recorded only when it is a genuine expectation
(the running reward is a.s. integrable on `[t, T]` and the payoff is `ℙ^{θ,Z}`-integrable). -/
def valSet0 (θ : Θ) (t : ℝ≥0) : Set ℝ :=
  {v | ∃ (x : ℝ) (η Z J I : ℝ≥0 → Ω → ℝ),
    M.InAWith S θ t x η Z J ∧
    (∀ᵐ ω ∂S.P, ∀ s : ℝ≥0, t ≤ s → s ≤ M.T → M.R θ s ≤ M.fwd θ t x η Z J s ω) ∧
    IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha (fun _ _ => θ) Z)) I ∧
    (∀ᵐ ω ∂S.P, IntegrableOn (fun r : ℝ => M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω)
      (Icc (t : ℝ) M.T)) ∧
    Integrable (fun ω => ∫ r in Icc (t : ℝ) M.T, (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
      (M.girsanov S t (M.alpha (fun _ _ => θ) Z) I) ∧
    v = ∫ ω, (∫ r in Icc (t : ℝ) M.T, (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
      ∂(M.girsanov S t (M.alpha (fun _ _ => θ) Z) I)}

/-- `V^P_0(θ; t)` of (2.25): the principal's value over self-enforcing contracts. -/
noncomputable def V0P (θ : Θ) (t : ℝ) : ℝ :=
  sSup (M.valSet0 S θ t.toNNReal)

/-- `ū₀(t) = sup_{θ̃ ∈ Θ} V^P_0(θ̃; t) − c^P_t` ((3.7)). -/
noncomputable def u0bar (t : ℝ) : ℝ :=
  (⨆ θ : Θ, M.V0P S θ t) - M.cP t

/-- The set of values, over `(η, Z) ∈ 𝒜^θ_{t,x}`, of
`E^{θ,Z}[∫_t^{τ} [I^h(θ; s, Z_s) − η_s] ds + g(τ) 1_{τ < T}]` with `τ = τ^{θ;t,x,η,Z}` the quitting time
(3.9) and `g` the value of a new hire. With `g = ū₀` this is `J₁` of (3.9); with `g = ū_{n−1}` it is the
objective of (5.1). Values are recorded only when they are genuine expectations. -/
def valSetWith (g : ℝ → ℝ) (θ : Θ) (t : ℝ≥0) (x : ℝ) : Set ℝ :=
  {v | ∃ (η Z J I : ℝ≥0 → Ω → ℝ),
    M.InAWith S θ t x η Z J ∧
    IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha (fun _ _ => θ) Z)) I ∧
    (∀ᵐ ω ∂S.P, IntegrableOn (fun r : ℝ => M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω)
      (Icc (t : ℝ) M.T)) ∧
    Integrable (fun ω =>
        (∫ r in Icc (t : ℝ) (M.hitTime θ t x η Z J ω),
          (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
        + (if M.hitTime θ t x η Z J ω < M.T then g (M.hitTime θ t x η Z J ω) else 0))
      (M.girsanov S t (M.alpha (fun _ _ => θ) Z) I) ∧
    v = ∫ ω, ((∫ r in Icc (t : ℝ) (M.hitTime θ t x η Z J ω),
          (M.Ih θ r (Z r.toNNReal ω) - η r.toNNReal ω))
        + (if M.hitTime θ t x η Z J ω < M.T then g (M.hitTime θ t x η Z J ω) else 0))
      ∂(M.girsanov S t (M.alpha (fun _ _ => θ) Z) I)}

/-- The value function with at most one quitting and new-hire value `g`:
`sup_{(η,Z) ∈ 𝒜^θ_{t,x}} E^{θ,Z}[∫_t^τ [I^h − η] ds + g(τ) 1_{τ < T}]`. -/
noncomputable def uWith (g : ℝ → ℝ) (θ : Θ) (t x : ℝ) : ℝ :=
  sSup (M.valSetWith S g θ t.toNNReal x)

/-- `u₁(θ; t, x)` of (3.9). -/
noncomputable def u1 (θ : Θ) (t x : ℝ) : ℝ :=
  M.uWith S (M.u0bar S) θ t x

/-- `ū_n` of (3.7) and (5.1): `ū_0` as in (3.7), and
`ū_{n+1}(t) = sup_{θ ∈ Θ} u_{n+1}(θ; t, R^θ_t) − c^P_t` with `u_{n+1} = uWith ū_n`. -/
noncomputable def ubarN : ℕ → ℝ → ℝ
  | 0 => M.u0bar S
  | n + 1 => fun t => (⨆ θ : Θ, M.uWith S (ubarN n) θ t (M.R θ t)) - M.cP t

/-- `u_n(θ; t, x)` of (5.1), for `n ≥ 1`: the value with new-hire value `ū_{n−1}` (`u_1` is (3.9)). -/
noncomputable def uN (n : ℕ) (θ : Θ) (t x : ℝ) : ℝ :=
  M.uWith S (M.ubarN S (n - 1)) θ t x

/-- The boundary conditions (4.4) for a single function `u(t, x)` of type `θ`, with a given boundary
function `g` at the lower barrier (`g = ū₀` in (4.4)):
* `u(t, L̄^θ_t) = −C₀ (T − t)` for `t ∈ [0, T)`;
* `u(T−, x) = 0` for `x ∈ (L̲^θ_T, 0)`;
* `u(t, L̲^θ_t +) ≥ g(t)` for `t ∈ [0, T)`: the right limit in `x` exists and is `≥ g(t)`. -/
def BCwith (θ : Θ) (g : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) → u t (M.Lbar θ t) = -M.C₀ * ((M.T : ℝ) - t)) ∧
  (∀ x : ℝ, M.Lund θ M.T < x → x < 0 → Tendsto (fun s => u s x) (𝓝[<] (M.T : ℝ)) (𝓝 0)) ∧
  (∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) → ∃ ℓ : ℝ,
    Tendsto (u t) (𝓝[>] (M.Lund θ t)) (𝓝 ℓ) ∧ g t ≤ ℓ)

end Model

end DynPrincipalAgent.HJB


