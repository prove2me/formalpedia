-- Prove2me | Definitions.Def_OgawaNagaoka_holevoInfo
-- name    : OgawaNagaoka_holevoInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:41.427713+00:00
-- url     : https://prove2.me/theorems/ea9a8274-5f5d-4fbe-8260-6f33570b755b
-- title:
--   Quantum mutual information $I(\pi)=H(\bar\rho_\pi)-\sum_i\pi_iH(\rho_i)$
-- statement:
--   Let $\pi=\{\pi_i\}_{i=1}^a$ be a probability distribution on the input alphabet. The (formal) quantum mutual information is
--
--   $$
--   I(\pi)=H(\bar\rho_\pi)-\sum_{i=1}^a\pi_iH(\rho_i),\qquad \bar\rho_\pi=\sum_{i=1}^a\pi_i\rho_i ,
--   $$
--
--   with $H(\rho)=-\mathrm{Tr}\,\rho\log\rho$ the von Neumann entropy (natural logarithm). Its maximum over $\pi$ is the capacity of the channel.
--
--   **Formalization Note** $H$ is the published `ProjectiveMeasurementEquilibration.vonNeumannEntropy`, $-\mathrm{Re}\,\mathrm{Tr}(\rho\log\rho)$ with the matrix logarithm by functional calculus and $0\log0=0$: the natural logarithm, which is what makes (16) hold. Defined for every real vector $\pi$; statements take $\pi$ in the simplex `stdSimplex ℝ A`.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, p.2

import Mathlib
import Definitions.Def_pme_quantum_basics

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, p.2: the (formal) quantum mutual information of an input
distribution `π` on the alphabet,
`I(π) = H(ρ̄_π) − Σ_{i=1}^a π_i H(ρ_i)`, where `ρ̄_π = Σ_i π_i ρ_i` and `H(ρ) = −Tr ρ log ρ` is the
von Neumann entropy.

**Formalization Note.** `H` is the published
`ProjectiveMeasurementEquilibration.vonNeumannEntropy`, `−Re Tr(ρ · log ρ)` with the matrix
logarithm by functional calculus (`Real.log 0 = 0`, so `0 log 0 = 0`): the natural logarithm, as in
the paper. The function is defined for every real vector `π`; the statements that use it take
`π ∈ stdSimplex ℝ A` and density matrices `ρ_i`. -/
noncomputable def holevoInfo {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (π : A → ℝ) : ℝ :=
  ProjectiveMeasurementEquilibration.vonNeumannEntropy (∑ i, ((π i : ℝ) : ℂ) • ρ i) -
    ∑ i, π i * ProjectiveMeasurementEquilibration.vonNeumannEntropy (ρ i)

end OgawaNagaoka


