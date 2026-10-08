-- Prove2me | Definitions.Def_TimeInconsLQ_MeanVariance_Adjoint
-- name    : TimeInconsLQ_MeanVariance_Adjoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:00.605624+00:00
-- url     : https://prove2.me/theorems/affec9d3-33dc-4ce3-9931-9037ebc58956
-- title:
--   §3 — BSDEs on [t, T], the first-order adjoint equation (3.1), Λ(s; t) and condition (3.4)
-- statement:
--   This module defines the objects of §3 of Hu, Jin and Zhou that the sufficient condition for an equilibrium is stated in, for one fixed $t\in[0,T)$.
--
--   **BSDE on $[t,T]$.** A pair $(p,K)$, $p$ with values in $\mathbb R^m$ and $K=(K_1,\dots,K_d)$, solves
--   $$-dp(s)=F(s,p(s),K(s))\,ds-\sum_{j=1}^dK_j(s)\,dW^j_s,\qquad p(T)=\xi,\qquad s\in[t,T],$$
--   if $p$ and each $K_j$ are progressively measurable with $E\int_t^T|p|^2ds<\infty$, $E\int_t^T|K_j|^2ds<\infty$, and for every $r\in[t,T]$, almost surely, $s\mapsto F(s,p(s),K(s))$ is integrable on $[r,T]$ and $p(r)=\xi+\int_r^TF(s,p(s),K(s))\,ds-\sum_j\int_r^TK_j(s)\,dW^j_s$.
--
--   **First-order adjoint equation** (3.1). Given a control with state process $X^*$ and $t\in[0,T)$, $(p(\cdot;t),k(\cdot;t))$ solves on $[t,T]$
--   $$dp(s;t)=-\Big[A_s'p(s;t)+\sum_{j=1}^d(C^j_s)'k^j(s;t)+Q_sX^*_s\Big]ds+\sum_{j=1}^dk^j(s;t)\,dW^j_s,\qquad p(T;t)=GX^*_T-hE_t[X^*_T]-\mu_1X^*_t-\mu_2 .$$
--
--   **The process** $\Lambda(s;t)=B_sp(s;t)+\sum_j(D^j_s)'k^j(s;t)+R_su^*_s$ (p. 6).
--
--   **Condition (3.4)** at $t$: $E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty$ a.s., and $\lim_{s\downarrow t}E_t[\Lambda(s;t)]=0$ a.s.
--
--   For the mean–variance problem ($n=1$, $C=0$, $Q=0$, $B=\theta$, $D^j=e_j'$, $R=0$, $G=h=1$) the adjoint equation becomes the second line of (5.4) and $\Lambda(s;t)=p(s;t)\theta_s+k(s;t)$.
--
--   **Formalization Note.** The stochastic integral on $[t,T]$ is $J(T)-J(r)$ for an Itô integral process $J$ (Peng's `IsItoIntegral`) of $\mathbf 1_{s\ge t}K_j$. The first half of (3.4), a conditional expectation of a nonnegative and possibly non-integrable variable, is written as: there are $\mathcal F_t$-sets $\Omega_0\subseteq\Omega_1\subseteq\cdots$ covering almost all of $\Omega$ with $E[\mathbf 1_{\Omega_m}\int_t^T|\Lambda|ds]<\infty$. The second half concerns uncountably many conditional expectations, so it is written version-robustly: $\Lambda(s;t)$ is integrable for a.e. $s\in(t,T]$, and some jointly measurable process $\hat\Lambda$, equal a.s. to $E_t[\Lambda(s;t)]$ for a.e. $s\in(t,T]$, satisfies $\hat\Lambda_s(\omega)\to0$ as $s\downarrow t$ for a.e. $\omega$ ("a.e. $s$" because $\Lambda$, built from $L^2$ processes, is itself only defined $ds\otimes dP$-a.e.).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, pp. 4–6, (3.1), (3.4) and the definition of Λ(s; t); specialization (5.4), p. 15

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `(p, K)` solves the backward SDE `−dp(s) = F(s, p(s), K(s)) ds − Σⱼ Kⱼ(s) dWʲ(s)`,
`p(T) = ξ`, on the interval `[t, T]` (Peng's sign convention): `p` and every `Kⱼ` are progressively
measurable with `E ∫ₜᵀ |p|² ds < ∞`, `E ∫ₜᵀ |Kⱼ|² ds < ∞`, and for every `r ∈ [t, T]`, almost
surely, `s ↦ F(s, p(s), K(s))` is integrable on `[r, T]` and
`p(r) = ξ + ∫ᵣᵀ F(s, p(s), K(s)) ds − Σⱼ (Jⱼ(T) − Jⱼ(r))`, where `Jⱼ` is an Itô integral process of
`1_{s ≥ t} Kⱼ(s)` against `Wʲ`. -/
def SolvesBSDEOn {ι : Type*} [Fintype ι] {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (T t : ℝ≥0) (W : ℝ≥0 → Ω → Fin d → ℝ) (ξ : Ω → ι → ℝ)
    (F : ℝ≥0 → Ω → (ι → ℝ) → (Fin d → ι → ℝ) → (ι → ℝ))
    (p : ℝ≥0 → Ω → ι → ℝ) (K : Fin d → ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 p ∧ (∀ j, IsStronglyProgressive 𝓕 (K j)) ∧
  ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) T, ‖p s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤ ∧
  (∀ j, ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) T, ‖K j s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P < ⊤) ∧
  ∃ J : ι → Fin d → ℝ≥0 → Ω → ℝ,
    (∀ i j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun s ω => W s ω j)
      (fun s ω => if t ≤ s then K j s ω i else 0) (J i j)) ∧
    ∀ r, t ≤ r → r ≤ T → ∀ᵐ ω ∂P,
      MeasureTheory.IntegrableOn
        (fun s : ℝ => F s.toNNReal ω (p s.toNNReal ω) (fun j => K j s.toNNReal ω))
        (Set.Icc (r : ℝ) T) ∧
      ∀ i, p r ω i = ξ ω i
        + (∫ s in Set.Icc (r : ℝ) T,
            F s.toNNReal ω (p s.toNNReal ω) (fun j => K j s.toNNReal ω)) i
        - ∑ j, (J i j T ω - J i j r ω)

namespace Data

variable {n l d : ℕ} (M : Data Ω n l d)

/-- The first-order adjoint equation (3.1) at a fixed `t ∈ [0, T)`, for a control `u` with state
process `X`: `(p(·; t), k(·; t))` solves, on `[t, T]`,
`dp(s; t) = −[A′_s p(s; t) + Σⱼ (Cʲ_s)′ kʲ(s; t) + Q_s X_s] ds + Σⱼ kʲ(s; t) dWʲ_s`,
`p(T; t) = G X_T − h E_t[X_T] − μ₁ X_t − μ₂`. -/
def IsFirstAdjointAt (X : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ≥0)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesBSDEOn M.filt M.P M.T t M.W
    (fun ω => M.G *ᵥ X M.T ω - M.h *ᵥ M.condVec t (X M.T) ω - M.μ₁ *ᵥ X t ω - M.μ₂)
    (fun s ω y z => (M.A s)ᵀ *ᵥ y + ∑ j, (M.C j s ω)ᵀ *ᵥ z j + M.Q s ω *ᵥ X s ω)
    p k

/-- `Λ(s; t) = B_s p(s; t) + Σⱼ (Dʲ_s)′ kʲ(s; t) + R_s u_s` (p. 6), for one `t`. -/
noncomputable def Lam (u : ℝ≥0 → Ω → Fin l → ℝ) (p : ℝ≥0 → Ω → Fin n → ℝ)
    (k : Fin d → ℝ≥0 → Ω → Fin n → ℝ) : ℝ≥0 → Ω → Fin l → ℝ :=
  fun s ω => M.B s ω *ᵥ p s ω + ∑ j, (M.D j s ω)ᵀ *ᵥ k j s ω + M.R s ω *ᵥ u s ω

/-- Condition (3.4) at a fixed `t ∈ [0, T)` for a process `Λ = Λ(·; t)`:
(a) `E_t ∫ₜᵀ |Λ(s; t)| ds < +∞` a.s. — there are `𝓕_t`-measurable sets `Ω₀ ⊆ Ω₁ ⊆ ⋯` covering
almost all of `Ω` with `E[1_{Ωₘ} ∫ₜᵀ |Λ(s; t)| ds] < ∞` for every `m`;
(b) `lim_{s↓t} E_t[Λ(s; t)] = 0` a.s. — for a.e. `s ∈ (t, T]`, `Λ(s; t)` is integrable, and some
jointly measurable process `Λ̂` is a version of `s ↦ E_t[Λ(s; t)]` for a.e. `s ∈ (t, T]` and
satisfies `Λ̂_s(ω) → 0` as `s ↓ t` for a.e. `ω`. -/
def Cond34At (t : ℝ≥0) (Λ : ℝ≥0 → Ω → Fin l → ℝ) : Prop :=
  (∃ Ωs : ℕ → Set Ω, (∀ m, MeasurableSet[M.filt t] (Ωs m)) ∧ Monotone Ωs ∧
    (∀ᵐ ω ∂M.P, ∃ m, ω ∈ Ωs m) ∧
    ∀ m, ∫⁻ ω in Ωs m, ∫⁻ s in Set.Icc (t : ℝ) M.T, ‖Λ s.toNNReal ω‖ₑ ∂volume ∂M.P < ⊤) ∧
  ∃ Λh : ℝ≥0 → Ω → Fin l → ℝ, Measurable (Function.uncurry Λh) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Ioc (t : ℝ) M.T)),
      Integrable (Λ s.toNNReal) M.P ∧
      ∀ i, (fun ω => Λh s.toNNReal ω i) =ᵐ[M.P] M.P[fun ω => Λ s.toNNReal ω i | M.filt t]) ∧
    ∀ᵐ ω ∂M.P, Tendsto (fun s => Λh s ω) (𝓝[>] t) (𝓝 0)

end Data

end TimeInconsLQ.MeanVariance


