-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_SRBM
-- name    : ForkJoinCtrl_Tracking_SRBM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:30.928446+00:00
-- url     : https://prove2.me/theorems/d2b495d7-a8f9-4778-ada5-785b2d65a741
-- title:
--   §3.2, p. 10 — Θ, Σ, the diagonal reflection matrix R and the SRBM with data (ℝ^{a1}_+, Θ, Σ, R, 0)
-- statement:
--   Let $a_1=I+\sum_j|\mathcal K^H_j|$, with coordinates indexed by the heavy-traffic dedicated servers and the shared servers. The **drift** is $\Theta=(\theta_k, k\in\mathcal K^H;\ \theta_i, i\in\mathcal I)$ and the **covariance** $\Sigma$ has entries
--
--   $$\Sigma_{kl}=\lambda_j(\beta_j^2+\sigma_k^2\mathbb I(k=l))\ (k,l\in\mathcal K^H_j),\quad \Sigma_{ki}=\Sigma_{ik}=\frac{\lambda_j\beta_j^2}{\mu_{ij}}\ (k\in\mathcal K^H_j, i\in\mathcal I_j),\quad \Sigma_{in}=\sum_{j\in\mathcal J_i\cap\mathcal J_n}\frac{\lambda_j(\beta_j^2+\sigma_{ij}^2\mathbb I(i=n))}{\mu_{ij}\mu_{nj}},$$
--
--   all other entries being $0$. The reflection matrix $R$ is diagonal with $R_{kk}=\mu_k$, $R_{ii}=1$.
--
--   A process $Z$ is an **SRBM** with data $(\mathbb R^{a_1}_+,\Theta,\Sigma,R,0)$ if there are a Brownian motion $X$ with drift $\Theta$, covariance $\Sigma$ and $X(0)=0$, and a regulator $Y$, such that pathwise $Z=X+Y$, $Z\ge 0$, and each $Y_c$ is continuous, nondecreasing, starts at $0$ and increases only when $Z_c=0$. The **limit vector** at time $t$ is $(\tilde Q_k(t), k\in\mathcal K;\ \tilde W_i(t), i\in\mathcal I)$ with $\tilde Q_k=Z_k$ for $k\in\mathcal K^H$, $\tilde Q_k=0$ for $k\in\mathcal K^L$ and $\tilde W_i=Z_i$.
--
--   This is the common diffusion limit of the dedicated queues and shared workloads under every admissible policy (Proposition 2).
--
--   **Formalization Note** The Brownian motion and the reflection are the published definitions `Reiman84.QueueLength.IsDriftedBM` and `IsReflectionPair` (with routing matrix $0$). Because $R$ is diagonal with positive entries, Williams' form $Z=X+RY'$ is the same as $Z=X+Y$ with $Y=RY'$, so $R$ is absorbed into the regulator and does not appear in Lean. The coordinates are enumerated by `Fin a₁` through `Fintype.equivFin`; positive definiteness of $\Sigma$, which the paper asserts, is a hypothesis of the theorems that use it.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 10, §3.2, Θ, Σ, R, Proposition 2

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Model
import Definitions.Def_Reiman84_QueueLength_Paths

namespace ForkJoinCtrl.Tracking

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Topology

/-!
Özkan, arXiv:2002.01496v1, §3.2, p. 10: the drift vector `Θ`, the covariance matrix `Σ`, the
diagonal reflection matrix `R`, and the SRBM with data `(ℝ^{a₁}_+, Θ, Σ, R, 0^{(a₁)})` of
Proposition 2, built on the published definitions `Reiman84.QueueLength.IsDriftedBM` (Brownian
motion with drift and covariance, started at `0`) and `Reiman84.QueueLength.IsReflectionPair`.
-/

variable {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The `a₁ = I + ∑_j |𝒦^H_j|` coordinates of the SRBM: the heavy-traffic dedicated servers
`k ∈ 𝒦^H` and the shared servers `i ∈ ℐ`. -/
abbrev Model.Coord (M : Model N Ω P) : Type := {k : Fin N.K // M.heavy k = true} ⊕ Fin N.I

/-- `a₁ = I + ∑_{j} |𝒦^H_j|`. -/
abbrev Model.a1 (M : Model N Ω P) : ℕ := Fintype.card M.Coord

/-- The enumeration of the coordinates by `Fin a₁` used to state the Brownian motion on
`ℝ^{a₁}`. -/
noncomputable def Model.coordEquiv (M : Model N Ω P) : M.Coord ≃ Fin M.a1 :=
  Fintype.equivFin M.Coord

/-- `Θ := (θ_k, j ∈ 𝒥, k ∈ 𝒦^H_j, θ_i, i ∈ ℐ)` on the coordinates. -/
def Model.ThetaC (M : Model N Ω P) : M.Coord → ℝ
  | .inl k => M.thetaK k.1
  | .inr i => M.thetaI i

/-- `Σ` on the coordinates (p. 10), symmetric:
* `Σ_kl := λ_j (β_j² + σ_k² 𝕀(k = l))` for `j ∈ 𝒥` and `k, l ∈ 𝒦^H_j`;
* `Σ_ki = Σ_ik := λ_j β_j² / µ_ij` for `j ∈ 𝒥`, `k ∈ 𝒦^H_j` and `i ∈ ℐ_j`;
* `Σ_in := ∑_{j ∈ 𝒥_i ∩ 𝒥_n} λ_j (β_j² + σ_ij² 𝕀(i = n)) / (µ_ij µ_nj)` for `i, n ∈ ℐ`;
* all remaining components are `0`. -/
noncomputable def Model.SigmaC (M : Model N Ω P) : Matrix M.Coord M.Coord ℝ
  | .inl k, .inl l =>
      if N.own k.1 = N.own l.1 then
        N.lam (N.own k.1) * (N.beta2 (N.own k.1) + N.sig2K k.1 * (if k = l then 1 else 0))
      else 0
  | .inl k, .inr i =>
      if N.P i (N.own k.1) = true then
        N.lam (N.own k.1) * N.beta2 (N.own k.1) / N.mu i (N.own k.1)
      else 0
  | .inr i, .inl k =>
      if N.P i (N.own k.1) = true then
        N.lam (N.own k.1) * N.beta2 (N.own k.1) / N.mu i (N.own k.1)
      else 0
  | .inr i, .inr n =>
      ∑ j ∈ N.Ji i ∩ N.Ji n,
        N.lam j * (N.beta2 j + N.sig2 i j * (if i = n then 1 else 0)) / (N.mu i j * N.mu n j)

/-- `Θ ∈ ℝ^{a₁}`. -/
noncomputable def Model.Theta (M : Model N Ω P) : Fin M.a1 → ℝ :=
  fun c => M.ThetaC (M.coordEquiv.symm c)

/-- `Σ ∈ ℝ^{a₁ × a₁}`. -/
noncomputable def Model.Sigma (M : Model N Ω P) : Matrix (Fin M.a1) (Fin M.a1) ℝ :=
  Matrix.reindex M.coordEquiv M.coordEquiv M.SigmaC

/-- `Z` is a semimartingale reflected Brownian motion (SRBM) associated with the data
`(ℝ^{a}_+, Θ, Σ, R, 0^{(a)})` (Williams 1998, Definition 3.1), where `Σ = Sig` and `R` is a diagonal
matrix with positive diagonal (p. 10: `R_kk := µ_k` for `k ∈ 𝒦^H`, `R_ii := 1` for `i ∈ ℐ`): there are a Brownian motion `X` with drift `Θ`, covariance `Σ` and `X(0) = 0`,
and a regulator `Y` such that pathwise `Z = X + Y` on `[0, ∞)`, `Z ≥ 0`, each `Y_c` is continuous,
nondecreasing, `Y_c(0) = 0`, and `Y_c` increases only when `Z_c = 0`. For a positive diagonal `R`
this is Williams' `Z = X + R Y'` with `Y' = R⁻¹ Y`, which has the same three properties as `Y`; the
diagonal entries of `R` are absorbed into the regulator. -/
def IsSRBM {a : ℕ} {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Θ : Fin a → ℝ)
    (Sig : Matrix (Fin a) (Fin a) ℝ) (Z : Ω' → ℝ → Fin a → ℝ) : Prop :=
  ∃ X Y : Ω' → ℝ → Fin a → ℝ,
    Reiman84.QueueLength.IsDriftedBM Θ Sig P' X ∧
    ∀ ω, Reiman84.QueueLength.IsReflectionPair 0 (X ω) (Y ω) (Z ω)

/-- The limit vector `(Q̃_k(t), j ∈ 𝒥, k ∈ 𝒦_j; W̃_i(t), i ∈ ℐ)` of Proposition 2 at time `t`, read
off an SRBM `Z` on the coordinates `Fin a₁`: `Q̃_k(t)` is the `k`-coordinate of `Z(t)` for
`k ∈ 𝒦^H`, `Q̃_k(t) = 0` for `k ∈ 𝒦^L`, and `W̃_i(t)` is the `i`-coordinate of `Z(t)`. -/
noncomputable def Model.limitVec (M : Model N Ω P) {Ω' : Type} (Z : Ω' → ℝ → Fin M.a1 → ℝ)
    (ω' : Ω') (t : ℝ) : LPParam N :=
  (fun k => if hk : M.heavy k = true then Z ω' t (M.coordEquiv (.inl ⟨k, hk⟩)) else 0,
   fun i => Z ω' t (M.coordEquiv (.inr i)))

end ForkJoinCtrl.Tracking


