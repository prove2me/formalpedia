-- Prove2me | Definitions.Def_TeschlQM_Scattering_waveOperator
-- name    : TeschlQM_Scattering_waveOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:16:04.452159+00:00
-- url     : https://prove2.me/theorems/f50ef1f7-fa9a-4d13-9000-8d93de3b9998
-- title:
--   Wave operators Ω± = lim_{t→±∞} e^{itH} e^{−itH₀} and their domains (12.3)
-- statement:
--   Let $H_0$ and $H$ be self-adjoint operators on $\mathfrak H$. The **wave operators** are
--   $$\mathfrak D(\Omega_\pm) = \{\psi \in \mathfrak H \mid \exists \lim_{t\to\pm\infty} \mathrm e^{\mathrm itH}\mathrm e^{-\mathrm itH_0}\psi\},\qquad \Omega_\pm\psi = \lim_{t\to\pm\infty} \mathrm e^{\mathrm itH}\mathrm e^{-\mathrm itH_0}\psi .$$
--   $\mathfrak D(\Omega_\pm)$ is the set of incoming/outgoing asymptotic states and $\operatorname{Ran}(\Omega_\pm) = \Omega_\pm\mathfrak D(\Omega_\pm)$ the set of states that have an incoming/outgoing asymptotic state.
--
--   **Formalization Note.** With $H_0 = \int\lambda\,dP_0$ and $H = \int\lambda\,dP$, `waveDomain P₀ P s` and `waveOp P₀ P s` take a sign `s : ℤˣ`: `s = 1` is $\Omega_+$ and `s = −1` is $\Omega_-$, and the limit $\tau \to s\cdot\infty$ is written as $t \to +\infty$ with $\tau = st$. `waveOp` is Mathlib's `limUnder`; outside $\mathfrak D(\Omega_\pm)$ its value is unspecified, and every statement of the mission uses it only on $\mathfrak D(\Omega_\pm)$. The range is `waveOp P₀ P s '' waveDomain P₀ P s`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 247, Section 12.1, Eq. (12.3)

import Mathlib
import Definitions.Def_TeschlQM_Shared_timeEvolution

open Filter Topology

namespace TeschlQM.Scattering

/-- Teschl, p. 247, (12.3): the **domain of the wave operator** `Ω_±`,
`𝔇(Ω_±) = {ψ ∈ ℌ | ∃ lim_{t→±∞} e^{itH} e^{−itH₀} ψ}`, where `H₀ = ∫ λ dP₀(λ)` and
`H = ∫ λ dP(λ)`, so that `e^{−itH₀} = timeEvolution P₀ t` and `e^{itH} = timeEvolution P (−t)`.
The sign is `s : ℤˣ`: `s = 1` gives `Ω₊` (`t → +∞`) and `s = −1` gives `Ω₋` (`t → −∞`); the
limit `τ → s·∞` is written as `t → +∞` with `τ = s t`. -/
def waveDomain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P₀ P : Set ℝ → (H →L[ℂ] H)) (s : ℤˣ) : Set H :=
  {ψ | ∃ φ : H, Tendsto (fun t : ℝ =>
      TeschlQM.Shared.timeEvolution P (-(((s : ℤ) : ℝ) * t)) (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ))
    atTop (𝓝 φ)}

/-- Teschl, p. 247, (12.3): the **wave operator** `Ω_± ψ = lim_{t→±∞} e^{itH} e^{−itH₀} ψ`
(sign `s` as in `waveDomain`). The value is Mathlib's `limUnder`, which is the limit for
`ψ ∈ 𝔇(Ω_±) = waveDomain P₀ P s` and an unspecified vector otherwise; every statement of the
mission uses it only on `𝔇(Ω_±)`. Its range `Ran(Ω_±)` is `waveOp P₀ P s '' waveDomain P₀ P s`. -/
noncomputable def waveOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P₀ P : Set ℝ → (H →L[ℂ] H)) (s : ℤˣ) (ψ : H) : H :=
  limUnder atTop (fun t : ℝ =>
    TeschlQM.Shared.timeEvolution P (-(((s : ℤ) : ℝ) * t)) (TeschlQM.Shared.timeEvolution P₀ (((s : ℤ) : ℝ) * t) ψ))

end TeschlQM.Scattering


