-- Prove2me | Definitions.Def_SigRoute_SignalSystem
-- name    : SigRoute_SignalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:07.091735+00:00
-- url     : https://prove2.me/theorems/59e2b08f-0fa9-471d-9d68-e44a668ee7fd
-- title:
--   Signal system $(\sigma,w,\theta)$, score and route
-- statement:
--   A **signal system** $\mathcal S=(\sigma,w,\theta)$ consists of signals $\sigma_1,\dots,\sigma_k$ mapping the verifier's view into $[0,1]$, a weight vector $w$ in the probability simplex $\Delta_k=\{w\in\mathbb R^k_{\ge0}:\sum_iw_i=1\}$ and a cut-off $\theta\in[0,1]$. The **score** of a view $\nu$ and its **route** are
--
--   $$
--   s(\nu)=\sum_iw_i\sigma_i(\nu),\qquad \rho(\nu)=\begin{cases}A & s(\nu)\ge\theta,\\ B & \text{otherwise.}\end{cases}
--   $$
--
--   By convention $\sigma_1(\nu)=1[V_0\text{ accepts in }\nu]$ is the correctness signal of the base stage.
--
--   The gating condition of Lemma 11 is a condition on this data.
--
--   **Formalization Note** Signals are indexed by `Fin (k+1)`, index `0` being the paper's $\sigma_1$ (weight $w_1$). Views range over an arbitrary type and "efficiently computable" is not modelled. The convention on $\sigma_1$ is the predicate `IsCorrectnessSignal S acc₀`: $\sigma_1$ is the indicator of the set $\mathrm{acc}_0$ of views in which the base verifier accepts.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 4 and the convention after it, p.5

import Mathlib
import Definitions.Def_SigRoute_Arm

namespace SigRoute

/-- A signal system `S = (σ, w, θ)` (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 4, p.5): signals `σ_i` mapping the
verifier's view into `[0, 1]`, a weight vector `w` in the probability simplex `Δ_k` and a cut-off
`θ ∈ [0, 1]`.

**Formalization Note** Signals are indexed by `Fin (k+1)`; index `0` is the paper's correctness signal
`σ_1` (with weight `w_1`), so a signal system has at least one signal. Views range over an arbitrary type
`W` instead of `{0,1}*`, and "efficiently computable" is not modelled; the paper uses only that each
`σ_i` maps into `[0, 1]` (p.5). -/
structure SignalSystem (W : Type*) (k : ℕ) where
  /-- The signals: `sig ν i` is `σ_{i+1}(ν)`. -/
  sig : W → Fin (k + 1) → ℝ
  /-- The weights: `w i` is `w_{i+1}`. -/
  w : Fin (k + 1) → ℝ
  /-- The cut-off. -/
  θ : ℝ
  sig_mem : ∀ ν i, sig ν i ∈ Set.Icc (0 : ℝ) 1
  w_nonneg : ∀ i, 0 ≤ w i
  w_sum : ∑ i, w i = 1
  θ_mem : θ ∈ Set.Icc (0 : ℝ) 1

namespace SignalSystem

variable {W : Type*} {k : ℕ}

/-- The score `s(ν) = ⟨w, σ(ν)⟩ = ∑_i w_i σ_i(ν)` of a view (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 4, p.5). -/
def score (S : SignalSystem W k) (ν : W) : ℝ := ∑ i, S.w i * S.sig ν i

/-- The route `ρ(ν) = A` if `s(ν) ≥ θ` and `ρ(ν) = B` otherwise (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 4, p.5). -/
noncomputable def route (S : SignalSystem W k) (ν : W) : Arm :=
  if S.θ ≤ S.score ν then Arm.A else Arm.B

/-- The convention `σ_1(ν) = 1[V_0 accepts in ν]` (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), p.5, after Definition 4): the correctness
signal is the indicator of the set `acc₀` of views in which the base verifier accepts. -/
def IsCorrectnessSignal (S : SignalSystem W k) (acc₀ : Set W) : Prop :=
  ∀ ν, S.sig ν 0 = acc₀.indicator (fun _ => (1 : ℝ)) ν

end SignalSystem

end SigRoute


