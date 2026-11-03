-- Prove2me | Definitions.Def_QuantumNoise_IsState
-- name    : QuantumNoise_IsState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:27.22048+00:00
-- url     : https://prove2.me/theorems/3b98fe96-10e4-4ae4-acf7-582db84c9490
-- title:
--   State on a unital $\ast$-algebra
-- statement:
--   Let $\mathcal A$ be a unital $\ast$-algebra over $\mathbb C$. A **state** on $\mathcal A$ is a $\mathbb C$-linear functional $\rho:\mathcal A\to\mathbb C$ such that
--   $$
--   \rho(1)=1,\qquad \rho(x^\ast x)\in[0,\infty)\quad\text{for every }x\in\mathcal A .
--   $$
--   It is the expectation value $\langle\,\cdot\,\rangle_0$ of the paper, $\langle x\rangle_0=\operatorname{Tr}(\hat\rho_0 x)$ for a density matrix $\hat\rho_0$, and the expectation in the uncertainty relation (4.13).
--
--   **Formalization Note** No norm and no C$^\ast$ condition is imposed, so unbounded observables are allowed. Positivity is stated as $\operatorname{Im}\rho(x^\ast x)=0$ and $\operatorname{Re}\rho(x^\ast x)\ge 0$; hermiticity $\rho(x^\ast)=\overline{\rho(x)}$ is a consequence and is not assumed.
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.2, p.21 (density matrix ρ̂0) and Sec. IV.A.3, Eq. (4.13), p.23

import Mathlib

namespace QuantumNoise

/-- A **state** on a unital ∗-algebra `𝒜` over `ℂ`: a `ℂ`-linear functional `ρ` with `ρ 1 = 1`
that is positive, `ρ (x⋆ x) ≥ 0` (real and non-negative) for every `x`.

This is the expectation `⟨·⟩₀ = Tr(ρ̂₀ ·)` of Clerk et al., *Introduction to Quantum Noise,
Measurement and Amplification*, arXiv:0810.4729v2, Sec. IV.A.2, p.21 (printed p.21, PDF p.21),
"some unspecified density matrix ρ̂₀", and the expectation in the uncertainty relation (4.13), p.23.

**Formalization Note** The algebra is any unital ∗-algebra over `ℂ`, with no norm and no C∗
axiom, so that unbounded observables such as the cavity photon number `F̂ = n̂` (Sec. III.B) are
covered; a density matrix with bounded observables is the special case `ρ x = Tr(ρ̂₀ x)`.
Positivity is written as `Im ρ(x⋆x) = 0` and `Re ρ(x⋆x) ≥ 0`. Hermiticity `ρ(x⋆) = conj ρ(x)`
follows from positivity and `ρ 1 = 1` and is not assumed separately. -/
def IsState {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (ρ : 𝒜 →ₗ[ℂ] ℂ) : Prop :=
  ρ 1 = 1 ∧ ∀ x : 𝒜, (ρ (star x * x)).im = 0 ∧ 0 ≤ (ρ (star x * x)).re

end QuantumNoise


