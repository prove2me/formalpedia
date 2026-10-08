-- Prove2me | Definitions.Def_ViscosityPPDE_Comparison_Approx
-- name    : ViscosityPPDE_Comparison_Approx
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:42.47107+00:00
-- url     : https://prove2.me/theorems/a79c109c-d104-4b6a-a89a-897acafeacb7
-- title:
--   (6.5), (6.7), and $\omega\otimes_t\hat\omega$ — the data of Lemma 6.3
-- statement:
--   Let $t<T$.
--
--   1. (6.5) $\theta \in (C^0_b(\Lambda^t))^d$ satisfies (6.5) if there exists $\hat\theta\in(C^0_b(\hat\Lambda^t))^d$ such that $\theta = \hat\theta$ on $\Lambda^t$ and $\hat\theta$ is uniformly continuous in $\hat\omega$ under the uniform norm $\|\cdot\|^t_T$.
--   2. (6.7) For $z\in\mathbb R^d$,
--   $$\hat Z_s(\hat\omega) = z + \int_t^s\hat\theta_r(\hat\omega)\,dr,\qquad \hat v(s,\hat\omega) = \hat Z_s(\hat\omega)\,\hat\omega_s - \int_t^s\hat\theta_r(\hat\omega)\,\hat\omega_r\,dr,\qquad\hat\omega\in\hat\Omega^t.$$
--   3. For $\omega\in\Omega$ and $\hat\omega\in\hat\Omega^t$, the concatenation is $(\omega\otimes_t\hat\omega)_r = \omega_r$ for $r<t$ and $\omega_t + \hat\omega_r$ for $r\ge t$ (here $\omega_{t-} = \omega_t$ since $\omega$ is continuous).
--
--   These are the ingredients of the ODE (6.8) with random coefficients whose solution, restricted to $\Lambda^t$, is the classical solution of Lemma 6.3; they are the building block of the approximation in the proof of Theorem 6.1.
--
--   **Formalization Note** The page writes "$\theta = \hat\theta$ in $\Lambda$"; on the shifted space this is $\Lambda^t$, which is how it is encoded. "Uniformly continuous in $\hat\omega$" is read as one modulus, uniform in $s\in[t,T]$, the same reading as for Assumption 4.2. The products $\hat Z_s\hat\omega_s$ and $\hat\theta_r\hat\omega_r$ (row vector times column vector) are Euclidean inner products.
-- source:
--   Ekren, Keller, Touzi, Zhang, On viscosity solutions of path dependent PDEs, arXiv:1109.5971v2, (6.5), p. 25; (6.6)–(6.7), p. 26; concatenation, p. 7

import Mathlib
import Definitions.Def_ViscosityPPDE_Comparison_Calculus

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace ViscosityPPDE.Comparison

variable {d : ℕ} {T : ℝ≥0}

/-- Condition (6.5) on `θ ∈ (C^0_b(Λ^t))^d`: there is `θ̂ ∈ (C^0_b(Λ̂^t))^d` with `θ = θ̂` on `Λ^t`
and `θ̂` uniformly continuous in `ω̂` under `‖·‖^t_T` (one modulus, uniform in `s ∈ [t,T]`). -/
def Cond65 (T t : ℝ≥0) (θ : ℝ≥0 → Omega d T t → Rd d) (θhat : ℝ≥0 → (ℝ≥0 → Rd d) → Rd d) :
    Prop :=
  (∀ i, IsC0b T t (fun s ω => θ s ω i)) ∧ (∀ i, IsC0bHat T t (fun s ω => θhat s ω i)) ∧
    (∀ s (ω : Omega d T t), t ≤ s → s ≤ T → θhat s ω.1 = θ s ω) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ s ω ω', t ≤ s → s ≤ T → ω ∈ OmegaHatSet d T t →
      ω' ∈ OmegaHatSet d T t → SupNormLt T (ω - ω') δ → ‖θhat s ω - θhat s ω'‖ < ε

/-- `Ẑ_s(ω̂) = z + ∫_t^s θ̂_r(ω̂) dr` (6.7). -/
noncomputable def Zhat (t : ℝ≥0) (z : Rd d) (θhat : ℝ≥0 → (ℝ≥0 → Rd d) → Rd d) (s : ℝ≥0)
    (ω : ℝ≥0 → Rd d) : Rd d :=
  z + ∫ r in Set.Icc (t : ℝ) s, θhat r.toNNReal ω

/-- `v̂(s, ω̂) = Ẑ_s(ω̂) ω̂_s − ∫_t^s θ̂_r(ω̂) ω̂_r dr` (6.7); the row-times-column products are inner
products in `ℝ^d`. -/
noncomputable def vhat (t : ℝ≥0) (z : Rd d) (θhat : ℝ≥0 → (ℝ≥0 → Rd d) → Rd d) (s : ℝ≥0)
    (ω : ℝ≥0 → Rd d) : ℝ :=
  inner ℝ (Zhat t z θhat s ω) (ω s) - ∫ r in Set.Icc (t : ℝ) s, inner ℝ (θhat r.toNNReal ω) (ω r.toNNReal)

/-- The concatenation `ω ⊗_t ω̂` of `ω ∈ Ω` with a càdlàg path `ω̂ ∈ Ω̂^t`:
`ω_r` for `r < t` and `ω_{t−} + ω̂_r = ω_t + ω̂_r` for `r ≥ t`. -/
noncomputable def concatHat (ω : Omega d T 0) (t : ℝ≥0) (ω' : ℝ≥0 → Rd d) : ℝ≥0 → Rd d :=
  fun r => if r < t then ω.1 r else ω.1 t + ω' r

end ViscosityPPDE.Comparison


