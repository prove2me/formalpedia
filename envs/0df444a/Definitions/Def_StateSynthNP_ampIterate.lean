-- Prove2me | Definitions.Def_StateSynthNP_ampIterate
-- name    : StateSynthNP_ampIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:39.407733+00:00
-- url     : https://prove2.me/theorems/08b3253f-fadf-4739-b6c6-a05bed1f266d
-- title:
--   Phase shifts $S_P(\varphi)$ and the amplitude-amplification iterate $Q$
-- statement:
--   For a projector $P$ and a phase $\varphi\in\mathbb R$, the selective phase shift is $S_P(\varphi)=I-(1-e^{i\varphi})P$; it multiplies the range of $P$ by $e^{i\varphi}$ and fixes its kernel. For a unitary $U$, an initial vector $v_0$ and a "good" projector $\Pi$, the generalized amplitude-amplification iterate of Brassard, Høyer, Mosca and Tapp is
--
--   $$
--   Q=-\,U\,S_{v_0}(\varphi)\,U^{\dagger}\,S_{\Pi}(\varphi),
--   $$
--
--   where $S_{v_0}$ uses the projector $v_0v_0^{\dagger}$. With $\varphi=\pi$ it is the standard Grover iterate.
--
--   **Formalization Note** Operators are complex square matrices; $U^{\dagger}$ is the conjugate transpose, which is $U^{-1}$ for unitary $U$.
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Theorem 2.1, p.4 ("exact amplitude amplification algorithm [BHMT00]")

import Mathlib

set_option autoImplicit false

namespace StateSynthNP

/-- The selective phase shift `S_P(φ) = I − (1 − e^{iφ}) P` by the phase `φ` on the range of a
projector `P` (it multiplies the range of `P` by `e^{iφ}` and fixes its kernel). -/
noncomputable def phaseShift {ι : Type} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) (φ : ℝ) :
    Matrix ι ι ℂ :=
  1 - (1 - Complex.exp ((φ : ℂ) * Complex.I)) • P

/-- The generalized amplitude-amplification iterate of Brassard–Høyer–Mosca–Tapp with phase `φ`:
`Q = − U S_{v₀}(φ) U† S_Π(φ)`, where `U` prepares `U v₀` from the initial vector `v₀`, `S_{v₀}` is the
phase shift on the line through `v₀` (projector `v₀ v₀†`) and `S_Π` the phase shift on the range of
the "good" projector `Π`. With `φ = π` it is the standard Grover iterate.

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Theorem 2.1, p.4: "we just run an exact amplitude amplification
algorithm [BHMT00] to boost the probability of the |1⟩ branch from ≈ 1/2 to ≈ 1".

**Formalization Note.** `U†` (`Matrix.conjTranspose`) is `U⁻¹` for unitary `U`. -/
noncomputable def ampIterate {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (v₀ : ι → ℂ) (P : Matrix ι ι ℂ) (φ : ℝ) : Matrix ι ι ℂ :=
  -(U * phaseShift (Matrix.vecMulVec v₀ (star v₀)) φ * U.conjTranspose * phaseShift P φ)

end StateSynthNP


