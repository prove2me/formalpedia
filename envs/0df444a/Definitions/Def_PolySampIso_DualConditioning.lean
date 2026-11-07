-- Prove2me | Definitions.Def_PolySampIso_DualConditioning
-- name    : PolySampIso_DualConditioning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:23.818578+00:00
-- url     : https://prove2.me/theorems/0131844a-34ad-4f5a-9bb0-6c07c914425d
-- title:
--   Dual conditioning (§5.1): the backwards measure π^{X|Γ=γ}, H_γ, r_τ and the stable set B_τ(γ, ρ)
-- statement:
--   For $\gamma\in\mathbb R^m_{>0}$, $\tau\in\mathbb N$ and $t\ge0$, the **backwards conditional measure** on $X$ is
--
--   $$\pi^{X|\Gamma=\gamma}_{t,\tau}(x)\propto\exp\big(\langle A^\top\gamma,x\rangle-\tau\psi(x)\big)\pi_t(x)\propto\exp\big(\langle A^\top\gamma,x\rangle-(\tau+t)\psi(x)\big),$$
--
--   and $H_\gamma=A^\top\mathrm{diag}(\gamma)^2A$ plays the role of a Hessian at a point with inverse slacks $\gamma$. The **normalized relative slacks** are $r_\tau(x;\gamma)=\mathbf 1_m-\gamma\circ s(x)/\tau$, and the **dual-stable set** is
--
--   $$B_\tau(\gamma,\rho)=\{x\in X:\|r_\tau(x;\gamma)\|_\infty\le\rho\}.$$
--
--   On $B_\tau(\gamma,\tfrac12)$ the potential of $\pi^{X|\Gamma=\gamma}_{t,\tau}$ is well conditioned in the $H_\gamma$ geometry, which is what Algorithm 6 exploits.
--
--   **Formalization Note** The backwards measure is defined by its density on $X$, normalized; it is not a disintegration.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), §5.1, pp.41–42 (PDF pp.43–44), eqs. (55)–(57)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Dual conditioning: `π^{X|Γ=γ}_{t,τ}`, `H_γ`, `r_τ` and `B_τ(γ, ρ)` (§5.1)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §5.1, pp.41–42 (PDF pp.43–44):
"πX|Γ=γ t,τ (x) ∝ exp(⟨A⊤γ, x⟩ − τψ(x)) πt(x) ∝ exp(⟨A⊤γ, x⟩ − (τ + t)ψ(x)), (55)"
"Hγ := A⊤diag (γ)2 A"; "rτ(x; γ) := 1m − γ ◦ s(x)/τ, (56)";
"Bτ(γ, ρ) := {x ∈ X : ∥rτ(x; γ)∥∞ ≤ ρ} , for all ρ ∈ (0, 1). (57)"

**Formalization Note.** `condX A b t τ γ` is defined by its density (55): Lebesgue measure on `X`
with density `exp(⟨A⊤γ, x⟩ − (τ + t)ψ(x))`, normalized (`⟨A⊤γ, x⟩ = Σᵢ γᵢ⟨aᵢ, x⟩`). For `γ > 0`,
`τ ≥ 1`, `t ≥ 0` and a nonempty bounded `X` the normalizer is finite and positive. It is not a
disintegration, so it has no a.e. ambiguity.
-/

/-- `π^{X|Γ=γ}_{t,τ}` (55). -/
noncomputable def condX {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (t : ℝ)
    (τ : ℕ) (γ : Fin m → ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  normalize ((volume.restrict (polytope A b)).withDensity fun x =>
    ENNReal.ofReal (Real.exp (∑ i, γ i * ∑ j, A i j * x j - ((τ : ℝ) + t) * logBarrier A b x)))

/-- `H_γ = A⊤ diag(γ)² A`. -/
noncomputable def hGamma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (γ : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A.transpose * Matrix.diagonal (fun i => γ i ^ 2) * A

/-- The normalized relative slacks `r_τ(x; γ) = 1_m − γ ∘ s(x)/τ` (56). -/
noncomputable def relSlack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (τ : ℕ)
    (γ : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin m → ℝ :=
  fun i => 1 - γ i * slack A b x i / τ

/-- The dual-stable set `B_τ(γ, ρ) = {x ∈ X : ‖r_τ(x; γ)‖_∞ ≤ ρ}` (57). -/
def stableSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (τ : ℕ)
    (γ : Fin m → ℝ) (ρ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ polytope A b ∧ ∀ i, |relSlack A b τ γ x i| ≤ ρ}

end PolySampIso


