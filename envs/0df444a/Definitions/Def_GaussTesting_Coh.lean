-- Prove2me | Definitions.Def_GaussTesting_Coh
-- name    : GaussTesting_Coh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:56.510908+00:00
-- url     : https://prove2.me/theorems/cdd25b4a-4f37-4949-b266-65053620563c
-- title:
--   Coherent states $\mathrm{Coh}_n$
-- statement:
--   For $\alpha\in\mathbb C$, the single-mode coherent state is $|\alpha\rangle=e^{-|\alpha|^2/2}\sum_{m\ge0}\frac{\alpha^m}{\sqrt{m!}}|m\rangle$, and for $\alpha\in\mathbb C^n$ the $n$-mode coherent state is $|\alpha\rangle=|\alpha_1\rangle\otimes\cdots\otimes|\alpha_n\rangle$, with coefficients
--
--   $$
--   \langle x|\alpha\rangle=\prod_{j=1}^n e^{-|\alpha_j|^2/2}\frac{\alpha_j^{x_j}}{\sqrt{x_j!}} .
--   $$
--
--   $\mathrm{Coh}_n$ is the class of these states, up to global phase: $\{e^{i\theta}|\alpha\rangle:\theta\in\mathbb R,\ \alpha\in\mathbb C^n\}$.
--
--   **Formalization Note** The explicit phase $e^{i\theta}$ makes the class closed under global phase like the other classes; it changes no distance $\mathrm{dist}(\psi,\mathrm{Coh}_n)$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.19

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The coefficients of the `n`-mode coherent state `|α⟩ = |α₁⟩ ⊗ ⋯ ⊗ |α_n⟩`,
`⟨x|α⟩ = ∏ⱼ e^{−|αⱼ|²/2} αⱼ^{xⱼ}/√(xⱼ!)`. -/
noncomputable def cohCoeff {n : ℕ} (α : Fin n → ℂ) (x : Fin n → ℕ) : ℂ :=
  ∏ j, ((Real.exp (-‖α j‖ ^ 2 / 2) : ℂ) * α j ^ x j / (Real.sqrt (x j).factorial : ℂ))

/-- The coherent states `Coh_n`, up to global phase.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2.3, p.19 ("For a given `α ∈ ℂ`, there is a corresponding single-mode coherent
state `|α⟩ = e^{−|α|²/2} ∑^∞_{n=0} αⁿ/√(n!) |n⟩`"; "The class of all `n`-mode coherent states is then
`Coh_n`, which is given by the tensor product of `n` single-mode coherent states:
`|α⟩ = |α₁⟩ ⊗ ⋯ ⊗ |α_n⟩` where now `α ∈ ℂⁿ`").

**Formalization Note.** States are rays: `Coh_n` contains every `e^{iθ}|α⟩`, so that it is closed under
global phase like the other classes (this changes no distance `dist(ψ, Coh_n)`). `Real.sqrt` of a
factorial is positive, so there is no division by zero. -/
noncomputable def Coh (n : ℕ) : Set (Ell2 (Fin n → ℕ)) :=
  {ψ | ∃ θ : ℝ, ∃ α : Fin n → ℂ, ∀ x, ψ x = Complex.exp (θ * Complex.I) * cohCoeff α x}

end GaussTesting


