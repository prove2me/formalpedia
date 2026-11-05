-- Prove2me | Definitions.Def_MagnonCode_AQEDC_IsDetecting
-- name    : MagnonCode_AQEDC_IsDetecting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:31.375617+00:00
-- url     : https://prove2.me/theorems/8ac8c988-8cca-4afe-a209-f578c54e5582
-- title:
--   Definition 3.1: $(\epsilon,\delta)$-approximate error-detection code for $\mathcal N$
-- statement:
--   Let $\mathcal C$ be a subspace with orthogonal projection $P$, and let $\mathcal N$ be a map on operators. Then $\mathcal C$ is an **$(\epsilon,\delta)$-approximate error-detection code for $\mathcal N$** if for every pure state $|\Psi\rangle\in\mathcal C$:
--
--   $$
--   \operatorname{tr}\bigl(P\mathcal N(|\Psi\rangle\langle\Psi|)\bigr)\ge\delta \quad\Longrightarrow\quad \langle\Psi|\rho_{\mathcal N,P}|\Psi\rangle\ge 1-\epsilon,
--   $$
--
--   where $\rho_{\mathcal N,P}=\operatorname{tr}(P\mathcal N(|\Psi\rangle\langle\Psi|))^{-1}\,P\mathcal N(|\Psi\rangle\langle\Psi|)P$ is the post-measurement state.
--
--   So when the code outcome has probability at least $\delta$, the state after the measurement is close to the input.
--
--   **Formalization Note** Pure states are unit vectors fixed by $P$. Real parts are taken of the trace and of the fidelity, which are real for a CPTP map. The clause "the trace is non-zero" excludes the case where $\rho_{\mathcal N,P}$ does not exist; it follows from the trace bound whenever $\delta>0$, as in every result of this mission.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Definition 3.1, p. 10

import Mathlib

namespace MagnonCode.AQEDC

open scoped Matrix

/-- **Definition 3.1** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 10): the subspace with associated projection `P` is an
`(ε, δ)`-approximate error-detection code for `N`: for every pure state `Ψ` of the code, with
`t = tr(P N(|Ψ⟩⟨Ψ|))`, if `t ≥ δ` then `⟨Ψ|ρ|Ψ⟩ ≥ 1 − ε`, where `ρ = t⁻¹ · P N(|Ψ⟩⟨Ψ|) P`.

**Formalization Note** A pure state of the code is a unit vector with `P Ψ = Ψ`. Since `t` and the
fidelity are real for a CPTP map, real parts are taken. The clause `t ≠ 0` excludes the case where
the printed `ρ` does not exist (Lean's `0⁻¹ = 0` would otherwise force `ε ≥ 1`); it is implied by
`δ ≤ t` whenever `δ > 0`, which holds in every use in this mission, and it is what makes the
remark on p. 10 true that an exact code is a `(0, 0)`-code. -/
def IsDetecting {X : Type*} [Fintype X] [DecidableEq X] (ε δ : ℝ) (P : Matrix X X ℂ)
    (N : Matrix X X ℂ → Matrix X X ℂ) : Prop :=
  ∀ Ψ : X → ℂ, star Ψ ⬝ᵥ Ψ = 1 → P *ᵥ Ψ = Ψ →
    let ρ := N (Matrix.vecMulVec Ψ (star Ψ))
    let t := (P * ρ).trace.re
    δ ≤ t → t ≠ 0 → 1 - ε ≤ (star Ψ ⬝ᵥ (t⁻¹ • (P * ρ * P)) *ᵥ Ψ).re

end MagnonCode.AQEDC


