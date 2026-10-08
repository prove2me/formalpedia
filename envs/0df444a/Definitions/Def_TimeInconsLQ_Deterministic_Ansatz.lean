-- Prove2me | Definitions.Def_TimeInconsLQ_Deterministic_Ansatz
-- name    : TimeInconsLQ_Deterministic_Ansatz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:31.633756+00:00
-- url     : https://prove2.me/theorems/b0764608-4a12-4188-80af-8da278a6cd3a
-- title:
--   §3–§4 — BSDE on [t, T], the ansatz (4.1), (4.3) for the adjoint flow, Λ(s; t) and condition (3.4)
-- statement:
--   This module collects the objects used in the proof of Theorem 4.4 of Hu, Jin and Zhou to verify the sufficient condition of Theorem 3.3.
--
--   1. **Backward SDE on $[t,T]$.** $(p,k)$ solves $-dp(s)=F(s,p(s),k(s))\,ds-\sum_jk_j(s)\,dW^j_s$, $p(T)=\xi$, on $[t,T]$: $p$ and the $k_j$ are progressive and square integrable on $[t,T]$, and for every $r\in[t,T]$, almost surely, $p(r)=\xi+\int_r^TF(s,p(s),k(s))\,ds-\sum_j\int_r^Tk_j\,dW^j$.
--   2. **Version of $s\mapsto\mathbb E_t[X^*_s]$.** A progressive process $Y$ with $Y_s=\mathbb E[X^*_s\mid\mathcal F_t]$ a.s. for every $s\in[t,T]$.
--   3. **The ansatz.** With $u^*_s=\alpha_sX^*_s+\beta_s$ (4.4),
--   $$p(s;t)=M_sX^*_s-N_s\mathbb E_t[X^*_s]-\Gamma^{(1)}_sX^*_t+\Phi_s,\qquad k(s;t)=M_s[C_sX^*_s+D_su^*_s+\sigma_s],\tag{4.1, 4.3}$$
--   the driver $A_sp+C_s'k+Q_sX^*_s$ and the terminal value $GX^*_T-h\mathbb E_t[X^*_T]-\mu_1X^*_t-\mu_2$ of (3.10).
--   4. $\Lambda(s;t)=R_su^*_s+p(s;t)B_s+D_s'k(s;t)\in\mathbb R^l$.
--   5. **Condition (3.4)**: for every $t\in[0,T)$,
--   $$\mathbb E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty,\qquad\lim_{s\downarrow t}\mathbb E_t[\Lambda(s;t)]=0\quad\text{a.s.}$$
--
--   **Formalization Note.** The first part of (3.4) is a conditional expectation of a nonnegative, possibly non-integrable variable; it is stated exactly, as the existence of $\mathcal F_t$-measurable sets $\Omega_m$ covering almost all of $\Omega$ with $\mathbb E[\mathbf 1_{\Omega_m}\int_t^T|\Lambda(s;t)|ds]<\infty$. The second part concerns uncountably many conditional expectations and is stated version-robustly: $\Lambda(s;t)$ is integrable for a.e. $s\in(t,T]$, and some jointly measurable $\hat\Lambda$ with $\hat\Lambda_s=\mathbb E_t[\Lambda(s;t)]$ a.s. for a.e. $s\in(t,T]$ satisfies $\hat\Lambda_s(\omega)\to0$ as $s\downarrow t$ for a.e. $\omega$ (processes in $L^2_{\mathcal F}$ are determined only $d\mathbb P\otimes ds$-a.e., so "a.e. $s$" is the faithful reading). The BSDE on $[t,T]$ follows Peng's `SolvesBSDE`, with the stochastic integrals taken of $\mathbf 1_{s\ge t}k_j$ on $[0,T]$.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 6 (3.4), p. 8 (3.10), (4.1), (4.3), p. 14 (proof of Theorem 4.4)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

namespace TimeInconsLQ.Deterministic

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `(p, k)` solves the backward SDE `−dp(s) = F(s, p(s), k(s)) ds − Σⱼ kⱼ(s) dWʲ(s)`,
`p(T) = ξ`, on `[t, T]` (Peng's sign convention). The processes `1_{s ≥ t} p(s)` and
`1_{s ≥ t} kⱼ(s)` are progressive, `E∫ₜᵀ|p|² < ∞` and `E∫ₜᵀ|kⱼ|² < ∞`; `Jᵢⱼ` is an Itô integral
process of `1_{s ≥ t} kⱼ(s)ᵢ` against `Wʲ` (so `∫ᵣᵀ kⱼ dWʲ = Jⱼ(T) − Jⱼ(r)` for `r ≥ t`); and for
every `r ∈ [t, T]`, almost surely, the drift is integrable on `[r, T]` and
`p(r) = ξ + ∫ᵣᵀ F(s, p(s), k(s)) ds − Σⱼ (Jⱼ(T) − Jⱼ(r))`. -/
def SolvesBSDEOn {ι : Type*} [Fintype ι] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (t T : ℝ≥0) (W : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ι → ℝ)
    (F : ℝ≥0 → Ω → (ι → ℝ) → (Fin d → ι → ℝ) → (ι → ℝ))
    (p : ℝ≥0 → Ω → ι → ℝ) (k : Fin d → ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 (fun s ω => if t ≤ s then p s ω else 0) ∧
  (∀ j, IsStronglyProgressive 𝓕 (fun s ω => if t ≤ s then k j s ω else 0)) ∧
  ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) T, ‖p s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤ ∧
  (∀ j, ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) T, ‖k j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤) ∧
  ∃ J : ι → Fin d → ℝ≥0 → Ω → ℝ,
    (∀ i j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun s ω => W s ω j)
      (fun s ω => if t ≤ s then k j s ω i else 0) (J i j)) ∧
    ∀ r, t ≤ r → r ≤ T → ∀ᵐ ω ∂P,
      IntegrableOn (fun s : ℝ => F s.toNNReal ω (p s.toNNReal ω) (fun j => k j s.toNNReal ω))
        (Set.Icc (r : ℝ) T) ∧
      ∀ i, p r ω i = ξ ω i
        + (∫ s in Set.Icc (r : ℝ) T,
            F s.toNNReal ω (p s.toNNReal ω) (fun j => k j s.toNNReal ω)) i
        - ∑ j, (J i j T ω - J i j r ω)

variable {l d : ℕ}

/-- `Y` is a version of the family of conditional expectations `s ↦ E_t[X_s]`, `s ∈ [t, T]`:
`1_{s ≥ t} Y_s` is progressive and `Y_s = E[X_s | 𝓕_t]` almost surely for every `s ∈ [t, T]`. -/
def IsCondMeanVersion (M : TimeInconsLQ.Sufficient.Data Ω 1 l d) (t : ℝ≥0) (X : ℝ≥0 → Ω → Fin 1 → ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive (TimeInconsLQ.Sufficient.filt M) (fun s ω => if t ≤ s then Y s ω else 0) ∧
  ∀ s, t ≤ s → s ≤ M.T → Y s =ᵐ[M.P] M.P[fun ω => X s ω 0 | TimeInconsLQ.Sufficient.filt M t]

/-- The feedback control (4.4), `u*_s = α_sX*_s + β_s`, along a state process `X`. -/
noncomputable def fbControl (c : Coeffs l d) (T : ℝ≥0) (M N Φ : ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) : ℝ≥0 → Ω → Fin l → ℝ :=
  fun s ω => X s ω 0 • alpha c T M N s + beta c M Φ s

/-- The ansatz (4.1) for the flow at time `t`, with `Y_s` standing for `E_t[X*_s]`:
`p(s; t) = M_sX*_s − N_sE_t[X*_s] − Γ⁽¹⁾_sX*_t + Φ_s`. -/
noncomputable def pAnsatz (c : Coeffs l d) (T : ℝ≥0) (M N Φ : ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun s ω _ => M s * X s ω 0 - N s * Y s ω - Gam1 c T s * X t ω 0 + Φ s

/-- (4.3): `k(s; t) = M_s[C_sX*_s + D_su*_s + σ_s] ∈ ℝᵈ` (independent of `t`), component `j`. -/
noncomputable def kAnsatz (c : Coeffs l d) (M : ℝ≥0 → ℝ) (X : ℝ≥0 → Ω → Fin 1 → ℝ)
    (u : ℝ≥0 → Ω → Fin l → ℝ) : Fin d → ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun j s ω _ => M s * (c.C s j * X s ω 0 + (c.D s *ᵥ u s ω) j + c.σ s j)

/-- The driver of the backward equation in (3.10):
`A_sp + C′_sk + Q_sX*_s` (with `p ∈ ℝ`, `k ∈ ℝᵈ`). -/
noncomputable def driver310 (c : Coeffs l d) (X : ℝ≥0 → Ω → Fin 1 → ℝ) :
    ℝ≥0 → Ω → (Fin 1 → ℝ) → (Fin d → Fin 1 → ℝ) → (Fin 1 → ℝ) :=
  fun s ω p k _ => c.A s * p 0 + ∑ j, c.C s j * k j 0 + c.Q s * X s ω 0

/-- The terminal value in (3.10) at time `t`:
`p(T; t) = GX*_T − hE_t[X*_T] − μ₁X*_t − μ₂`. -/
noncomputable def terminal310 (c : Coeffs l d) (M : TimeInconsLQ.Sufficient.Data Ω 1 l d) (X : ℝ≥0 → Ω → Fin 1 → ℝ)
    (t : ℝ≥0) : Ω → Fin 1 → ℝ :=
  fun ω _ => c.G * X M.T ω 0 - c.h * (M.P[fun ω' => X M.T ω' 0 | TimeInconsLQ.Sufficient.filt M t]) ω
    - c.μ₁ * X t ω 0 - c.μ₂

/-- `Λ(s; t) = R_su*_s + p(s; t)B_s + D′_sk(s; t) ∈ ℝˡ` (the `n = 1` form of `Λ` in Theorem 3.3
and in the proof of Theorem 4.4), for the flow `p(·; t)`, `k` and the control `u`. -/
noncomputable def Lam (c : Coeffs l d) (p : ℝ≥0 → Ω → Fin 1 → ℝ)
    (k : Fin d → ℝ≥0 → Ω → Fin 1 → ℝ) (u : ℝ≥0 → Ω → Fin l → ℝ) : ℝ≥0 → Ω → Fin l → ℝ :=
  fun s ω => c.R s *ᵥ u s ω + p s ω 0 • c.B s + (c.D s)ᵀ *ᵥ (fun j => k j s ω 0)

/-- Condition (3.4) for the family `Λ(s; t)` (`Λ t s ω`), for every `t ∈ [0, T)`:
(a) `E_t∫ₜᵀ|Λ(s; t)| ds < +∞` a.s.: there are `𝓕_t`-measurable sets `Ωₘ` covering almost all
of `Ω` with `E[1_{Ωₘ}∫ₜᵀ|Λ(s; t)| ds] < ∞`;
(b) `lim_{s↓t} E_t[Λ(s; t)] = 0` a.s.: `Λ(s; t)` is integrable for a.e. `s ∈ (t, T]`, and some
jointly measurable `Λ̂` with `Λ̂_s = E_t[Λ(s; t)]` a.s. for a.e. `s ∈ (t, T]` satisfies
`Λ̂_s(ω) → 0` as `s ↓ t` for a.e. `ω`. -/
def Cond34 {n : ℕ} (M : TimeInconsLQ.Sufficient.Data Ω n l d) (Λ : ℝ≥0 → ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  ∀ t : ℝ≥0, t < M.T →
    (∃ Ωm : ℕ → Set Ω, (∀ m, MeasurableSet[TimeInconsLQ.Sufficient.filt M t] (Ωm m)) ∧ (∀ᵐ ω ∂M.P, ∃ m, ω ∈ Ωm m) ∧
      ∀ m, ∫⁻ ω in Ωm m, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖Λ t s.toNNReal ω‖ₑ ∂volume ∂M.P < ⊤) ∧
    ∃ Λh : ℝ≥0 → Ω → Fin l → ℝ, Measurable (Function.uncurry Λh) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Ioc (t : ℝ) M.T)),
        Integrable (Λ t s.toNNReal) M.P ∧
        Λh s.toNNReal =ᵐ[M.P] condVec M t (Λ t s.toNNReal)) ∧
      ∀ᵐ ω ∂M.P, Tendsto (fun s => Λh s ω) (𝓝[>] t) (𝓝 0)

end TimeInconsLQ.Deterministic


