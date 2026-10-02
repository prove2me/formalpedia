-- Prove2me | Definitions.Def_TeschlQM_OneParticle_hydrogenHamiltonian
-- name    : TeschlQM_OneParticle_hydrogenHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:57:34.85217+00:00
-- url     : https://prove2.me/theorems/a1f1a7fc-d6f2-417e-91b5-1bbdc903cd25
-- title:
--   The hydrogen Hamiltonian H⁽¹⁾ = −Δ − γ/|x| (10.5)
-- statement:
--   For $\gamma \in \mathbb R$ the **hydrogen Hamiltonian** on $L^2(\mathbb R^3)$ is
--   $$H^{(1)} = -\Delta - \frac{\gamma}{|x|}, \qquad \mathfrak D(H^{(1)}) = \mathfrak D(H_0) \cap \mathfrak D\big(\tfrac{1}{|x|}\big),$$
--   the sum of the free Schrödinger operator and multiplication by the Coulomb potential $V^{(1)}(x) = -\gamma/|x|$. The book notes that this domain equals $H^2(\mathbb R^3)$.
--
--   For $\gamma > 0$ it models a single electron in the field of a fixed nucleus.
--
--   **Formalization Note.** The operator is the `LinearPMap` sum `freeHamiltonian 3 + multOp V⁽¹⁾`, whose domain is the intersection of the two domains. At the single point $x = 0$ Lean evaluates $-\gamma/0$ as $0$; a null set does not affect the operator on $L^2$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 222, Section 10.2, Eq. (10.5)

import Mathlib
import Definitions.Def_TeschlQM_OneParticle_freeHamiltonian

namespace TeschlQM.OneParticle

/-- Teschl (10.5), p. 222: the hydrogen Hamiltonian `H⁽¹⁾ = -Δ - γ/|x|` on `L²(ℝ³)`, the operator sum
of `H₀` and multiplication by the Coulomb potential `V⁽¹⁾(x) = -γ/|x|`, with domain
`𝔇(H⁽¹⁾) = 𝔇(H₀) ∩ 𝔇(1/|x|)` (which the book notes equals `H²(ℝ³)`). The value of the potential at
the single point `x = 0` (Lean's `γ/0 = 0`) is irrelevant on `L²`. -/
noncomputable def hydrogenHamiltonian (γ : ℝ) : L2 3 →ₗ.[ℂ] L2 3 :=
  freeHamiltonian 3 + multOp (fun x => ((-γ / ‖x‖ : ℝ) : ℂ))

end TeschlQM.OneParticle


