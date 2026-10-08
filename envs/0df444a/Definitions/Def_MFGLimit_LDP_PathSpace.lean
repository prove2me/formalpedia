-- Prove2me | Definitions.Def_MFGLimit_LDP_PathSpace
-- name    : MFGLimit_LDP_PathSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:01.25554+00:00
-- url     : https://prove2.me/theorems/319ad82c-cf69-49fa-bdff-32d5558b6f76
-- title:
--   §3.2, p. 13 — C([0,T]; P¹(ℝ^d)) with sup_t W₁, empirical-measure flows m^n_{X_·}, translated flows, mean path (6.10)
-- statement:
--   The state space of the large deviation principles (§3.2).
--
--   $C([0,T];\mathcal P^1(\mathbb R^d))$ is the space of flows $\nu=(\nu_t)_{t\in[0,T]}$ of probability measures with finite first moment that are continuous for the 1-Wasserstein distance, with the uniform metric
--
--   $$D(\nu,\nu')=\sup_{t\in[0,T]}\mathcal W_1(\nu_t,\nu'_t).$$
--
--   For $n$ continuous paths $X^1,\dots,X^n$ the flow of empirical measures is $m^n_{\boldsymbol X_\cdot}=(m^n_{\boldsymbol X_t})_{t\in[0,T]}$, $m^n_{\boldsymbol X_t}=\frac1n\sum_i\delta_{X^i_t}$. With the translations $\tau_x(z)=z-x$, the translated flow of $\nu$ by a path $\phi$ is $(\nu_t\circ\tau_{\phi_t}^{-1})_t$, i.e. the law of $Z-\phi_t$ for $Z\sim\nu_t$. The mean path is $\mathbb M^\nu_t=\int x\,d\nu_t(x)$ (6.10).
--
--   **Formalization Note** An element of the space is a structure carrying the flow, the $\mathcal P^1$ membership of each $\nu_t$ and its $\mathcal W_1$-continuity; $D$ takes values in $[0,\infty]$. The event $\{m^n_{\boldsymbol X_\cdot}\in O\}$ is "some $\nu\in O$ has flow equal to $(m^n_{\boldsymbol X_t(\omega)})_t$" (the empirical flow of continuous paths is $\mathcal W_1$-continuous, so this is the paper's event). A flow at a real time $r$ is read at the projection of $r$ onto $[0,T]$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, p. 13, §3.2; p. 26; p. 27, (6.10)

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {d : ℕ} {T : ℝ≥0}

/-- A flow of measures `(ν_t)_{t ∈ [0, T]}` on `ℝ^d`. -/
abbrev Flow (d : ℕ) (T : ℝ≥0) := Set.Icc (0 : ℝ≥0) T → Measure (MFGLimit.Conc.E d)

/-- The measure `ν_r` of a flow at a real time `r ∈ [0, T]`. -/
noncomputable def flowAt (ν : Flow d T) (r : ℝ) : Measure (MFGLimit.Conc.E d) := ν (toIcc T r)

/-- An element of `C([0, T]; P_1(ℝ^d))` (§3.2, p. 13): a flow `t ↦ ν_t ∈ P_1(ℝ^d)` continuous for
the 1-Wasserstein distance. -/
structure PathP1 (d : ℕ) (T : ℝ≥0) where
  ν : Flow d T
  isP1 : ∀ t, MFGLimit.Conc.IsPp 1 (ν t)
  cont : ∀ t, Tendsto (fun s => Wp 1 (ν s) (ν t)) (𝓝 t) (𝓝 0)

/-- The uniform metric `D(ν, ν') = sup_{t ∈ [0, T]} W_1(ν_t, ν'_t)` on `C([0, T]; P_1(ℝ^d))`. -/
noncomputable def Dpath (ν ν' : PathP1 d T) : ℝ≥0∞ := ⨆ t, Wp 1 (ν.ν t) (ν'.ν t)

/-- The flow of empirical measures `t ↦ m^n_{X_t(ω)} = (1/n) Σ_i δ_{X^i_t(ω)}` of `n` paths. -/
noncomputable def empFlow {Ω : Type*} {n : ℕ} (X : Fin n → Ω → CPath d T) (ω : Ω) : Flow d T :=
  fun t => empMeas (fun i => X i ω t)

/-- The event `{m^n_{X_·} ∈ O}` for a set `O ⊆ C([0, T]; P_1(ℝ^d))`. -/
def flowEvent {Ω : Type*} (X : ∀ n, Fin n → Ω → CPath d T) (n : ℕ) (O : Set (PathP1 d T)) :
    Set Ω :=
  {ω | ∃ ν ∈ O, ν.ν = empFlow (X n) ω}

/-- The translated flow `(ν_t ∘ τ_{φ_t}^{-1})_t`, `τ_x(z) = z − x`, for a path `φ`. -/
noncomputable def shiftFlow (ν : Flow d T) (φ : ℝ → MFGLimit.Conc.E d) : Flow d T :=
  fun t => (ν t).map (fun z => z - φ t)

/-- The mean path `𝕄^ν_r = ∫ x dν_r(x)` (6.10). -/
noncomputable def meanPath (ν : Flow d T) (r : ℝ) : MFGLimit.Conc.E d := ∫ x, x ∂(flowAt ν r)

end MFGLimit.LDP


