-- Prove2me | Definitions.Def_FasterSFM_Recenter
-- name    : FasterSFM_Recenter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:39.168561+00:00
-- url     : https://prove2.me/theorems/e9da98e9-1e1d-4458-b582-580632b76fdb
-- title:
--   Recentering after a contraction: $\Psi_\kappa$, RecenterPhase, ProjectAndCheck and Recenter
-- statement:
--   After a contraction the subspace $S$ (basis $J$) shrinks to $S'=J\ker\Gamma$, where $\Gamma\in\mathbb R^{r\times N}$ has orthonormal rows. In the old coordinates the algorithm follows the penalty path
--
--   $$\Psi_\kappa(x)=\Psi_{\mathrm{fl}}(Jx)+\frac{e^\kappa}{2}\|\Gamma x\|_2^2 .$$
--
--   With $f_\kappa=c\Psi_\kappa$, $c=400/\lambda$, its Newton decrement is $d_\kappa(x)=\sqrt{c\,\nabla\Psi_\kappa^\top(\nabla^2\Psi_\kappa)^{-1}\nabla\Psi_\kappa}$, and $K_\kappa(x)=H_S(x)+(e^\kappa/\lambda)\Gamma^\top\Gamma$.
--
--   1. **RecenterPhase**$(\kappa,x)$ (Algorithm 2) takes full Newton steps on $\Psi_\kappa$ until $\|\nabla\Psi_\kappa(x)\|^2_{K_\kappa(x)^{-1}}\le\bar\tau^2$ and returns that point.
--   2. **ProjectAndCheck**$(x)$ (Algorithm 3) sets $u=-\Gamma^\top\Gamma x$, $\bar x=x+u$ and $q=\sum_i(v_i^\top Ju/s_i(Jx))^2$, and returns $(\mathrm{false},\bar x)$ if $q>\tilde\tau^2$, otherwise $(\mathrm{true},\bar x)$.
--   3. **Recenter**$(x_{\mathrm{in}})$ (Algorithm 1) starts at $\kappa=\kappa_0$ and repeats: run a phase; if the projection test passes, stop with $\bar x$; otherwise set $\mu=e^{\kappa/2}\|\Gamma x\|_2$, $\vartheta=\vartheta_0/\max\{1,\mu\}$ and $\kappa\leftarrow\kappa+\log(1+\vartheta)$.
--
--   The exact minimizer of $\Psi_\kappa$ over $\{x:s_i(Jx)>0\}$ is $z_\kappa$. For the projection test, $J'$ has orthonormal columns spanning $\ker\Gamma$, $G(y)=J'^\top J^\top\nabla\Psi_{\mathrm{fl}}(Jy)$ and $H'(y)=J'^\top H_S(y)J'$ (p.35).
--
--   **Formalization Note** RecenterPhase is modelled as the sequence of Newton iterates and its first iterate passing the test; if none passes, the junk value is the input point. Recenter is an iteration of its loop body on the state $(\kappa,x,\text{done},\text{phases},\text{Newton steps})$, so the number of phases and Newton steps of a run can be read off. The final change of basis $x_{\mathrm{new}}=J'^\top\bar x$ (line 13) is not modelled.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §7, pp.29–31 and 35; Algorithms 1–3, p.30

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix

/-!
# Recentering after a contraction: `Ψ_κ`, RecenterPhase, ProjectAndCheck and Recenter

Ene & Nguyen, arXiv:2610.25403v1, §7, pp.29–31 and 35: the contraction matrix `Γ` and
`S' = J ker Γ` (p.29), `Ψ_κ` (p.29), Algorithms 1–3 (p.30), `f_κ = cΨ_κ`, its Newton decrement
`d_κ` and `K_κ` (p.31), `G` and `H'` (p.35), and the exact penalty minimizers `z_κ` (p.31).

**Formalization Note.**
* Coordinates are those before the contraction: `x ∈ ℝ^N`, `J ∈ ℝ^{n×N}` with orthonormal columns,
  `Γ ∈ ℝ^{r×N}` with orthonormal rows (`Γ Γᵀ = I_r`). `‖Γx‖₂² = (Γx) ⬝ᵥ (Γx)`.
* RecenterPhase (Algorithm 2) is the sequence of full Newton iterates of `Ψ_κ` from `x`; it returns the
  first iterate passing the test `‖∇Ψ_κ(x)‖²_{K_κ(x)⁻¹} ≤ τ̄²` of line 3. When no iterate passes, the
  loop does not terminate; `phaseOut` then returns its input as a junk value, and `phaseSteps` is `0`.
  Every lemma that uses `phaseOut` assumes, or proves, termination.
* Recenter (Algorithm 1) is run as an iteration of the loop body on the state
  `(κ, x, done, phases, newtonSteps)`; a `done` state is fixed. The returned center is `x̄` in the
  old coordinates; line 13's change of basis to `J' ᵀ x̄` is not modelled.
-/

variable {n N r : ℕ}

/-- The squared Euclidean norm `‖w‖₂²`. -/
noncomputable def sqNorm {m : ℕ} (w : Fin m → ℝ) : ℝ := w ⬝ᵥ w

/-- The section after the contraction, `S' = J ker Γ` (p.29). -/
noncomputable def contractedSpace (J : Matrix (Fin n) (Fin N) ℝ) (Γ : Matrix (Fin r) (Fin N) ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  (LinearMap.ker (Matrix.toLin' Γ)).map (Matrix.toLin' J)

namespace Body

variable (P : Body n) (J : Matrix (Fin n) (Fin N) ℝ) (Γ : Matrix (Fin r) (Fin N) ℝ)

/-- `Ψ_κ(x) = Ψ_fl(J x) + (e^κ/2) ‖Γ x‖₂²` (p.29). -/
noncomputable def Psik (κ : ℝ) (x : Fin N → ℝ) : ℝ :=
  P.Psi (J *ᵥ x) + Real.exp κ / 2 * sqNorm (Γ *ᵥ x)

/-- `K_κ(x) = H_S(x) + (e^κ/λ) Γᵀ Γ` (p.31; Algorithm 2, line 2). -/
noncomputable def Kk (κ : ℝ) (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  P.HS J x + (Real.exp κ / lam) • (Γᵀ * Γ)

/-- The Newton decrement of `f_κ = cΨ_κ`: `d_κ(x) = (c ∇Ψ_κᵀ (∇²Ψ_κ)⁻¹ ∇Ψ_κ)^{1/2}` (p.31). -/
noncomputable def dk (κ : ℝ) (x : Fin N → ℝ) : ℝ :=
  Real.sqrt (cSC * invNormSq (hess (P.Psik J Γ κ) x) (grad (P.Psik J Γ κ) x))

/-- The stopping test of RecenterPhase (Algorithm 2, line 3): `‖∇Ψ_κ(x)‖²_{K_κ(x)⁻¹} ≤ τ̄²`. -/
def phaseTest (κ : ℝ) (x : Fin N → ℝ) : Prop :=
  invNormSq (P.Kk J Γ κ x) (grad (P.Psik J Γ κ) x) ≤ taubar ^ 2

/-- The `k`-th Newton iterate of RecenterPhase from `x₀` (Algorithm 2, line 6). -/
noncomputable def phaseIter (κ : ℝ) (x₀ : Fin N → ℝ) (k : ℕ) : Fin N → ℝ :=
  (newtonStep (P.Psik J Γ κ))^[k] x₀

/-- The number of Newton steps RecenterPhase executes (the index of the first iterate passing the
test; `0` if none passes). -/
noncomputable def phaseSteps (κ : ℝ) (x₀ : Fin N → ℝ) : ℕ :=
  if h : ∃ k, P.phaseTest J Γ κ (P.phaseIter J Γ κ x₀ k) then Nat.find h else 0

/-- The vector returned by RecenterPhase(`κ`, `x₀`) (Algorithm 2). -/
noncomputable def phaseOut (κ : ℝ) (x₀ : Fin N → ℝ) : Fin N → ℝ :=
  P.phaseIter J Γ κ x₀ (P.phaseSteps J Γ κ x₀)

/-- ProjectAndCheck(`x`) (Algorithm 3): `u = −ΓᵀΓx`, `x̄ = x + u`,
`q = Σ_i (v_iᵀ J u / s_i(J x))²`; returns `(false, x̄)` if `q > τ̃²`, else `(true, x̄)`. -/
noncomputable def projectAndCheck (x : Fin N → ℝ) : Bool × (Fin N → ℝ) :=
  let u := -((Γᵀ * Γ) *ᵥ x)
  let q := ∑ i, (P.rowV i ⬝ᵥ (J *ᵥ u) / P.slack i (J *ᵥ x)) ^ 2
  if tautilde ^ 2 < q then (false, x + u) else (true, x + u)

/-- `z` is the exact minimizer `z_κ` of `Ψ_κ` over the domain `{x : s_i(Jx) > 0 ∀ i}` (p.31). -/
def IsPenaltyMin (κ : ℝ) (z : Fin N → ℝ) : Prop :=
  P.Interior (J *ᵥ z) ∧ ∀ x, P.Interior (J *ᵥ x) → P.Psik J Γ κ z ≤ P.Psik J Γ κ x

/-- The state of Recenter: `(κ, x, done, phases, newtonSteps)`. -/
abbrev RecState (N : ℕ) := ℝ × (Fin N → ℝ) × Bool × ℕ × ℕ

/-- One pass of the outer loop of Recenter (Algorithm 1, lines 5–11): run RecenterPhase, run
ProjectAndCheck; on success stop with `x̄`, otherwise set `µ = e^{κ/2}‖Γx‖₂`,
`ϑ = ϑ₀/max{1, µ}`, `κ ← κ + log(1 + ϑ)`. A `done` state is fixed. -/
noncomputable def recenterStep (s : RecState N) : RecState N :=
  match s with
  | (κ, x, done, ph, nw) =>
    if done then s else
      let x' := P.phaseOut J Γ κ x
      let pc := P.projectAndCheck J Γ x'
      if pc.1 then (κ, pc.2, true, ph + 1, nw + P.phaseSteps J Γ κ x)
      else
        let μ := Real.exp (κ / 2) * Real.sqrt (sqNorm (Γ *ᵥ x'))
        let ϑ := theta0 / max 1 μ
        (κ + Real.log (1 + ϑ), x', false, ph + 1, nw + P.phaseSteps J Γ κ x)

/-- The state of Recenter(`x_in`) after `j` passes of the outer loop, from `κ = κ₀ = log(τ/(8n))`
(Algorithm 1, lines 2–3). -/
noncomputable def recenterRun (xin : Fin N → ℝ) (j : ℕ) : RecState N :=
  (P.recenterStep J Γ)^[j] (kappa0 n, xin, false, 0, 0)

/-- The full-space gradient `∇Ψ_fl(x)`. -/
noncomputable def gradFl (x : Fin n → ℝ) : Fin n → ℝ := grad P.Psi x

/-- `G(y) = J'ᵀ Jᵀ ∇Ψ_fl(J y)` (p.35). -/
noncomputable def Gnew {N' : ℕ} (J' : Matrix (Fin N) (Fin N') ℝ) (y : Fin N → ℝ) : Fin N' → ℝ :=
  J'ᵀ *ᵥ (Jᵀ *ᵥ P.gradFl (J *ᵥ y))

/-- `H'(y) = J'ᵀ H_S(y) J'` (p.35). -/
noncomputable def Hnew {N' : ℕ} (J' : Matrix (Fin N) (Fin N') ℝ) (y : Fin N → ℝ) :
    Matrix (Fin N') (Fin N') ℝ :=
  J'ᵀ * P.HS J y * J'

end Body

end FasterSFM


