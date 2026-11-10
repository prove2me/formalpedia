-- Prove2me | Definitions.Def_QPSpinProfile_hamiltonian
-- name    : QPSpinProfile_hamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:03.230832+00:00
-- url     : https://prove2.me/theorems/67cbf4dc-7689-4d67-9e32-e7728b9295ae
-- title:
--   Dense quantum $p$-spin Hamiltonian $H_{n,p}$ and its Gaussian disorder
-- statement:
--   The **dense quantum $p$-spin Hamiltonian** on $n$ qubits is
--   $$
--   H_{n,p}=\binom np^{-1/2}\sum_{P\in\mathcal P_{n,p}} g_P\,P ,
--   $$
--   where the coefficients $g_P$, $P\in\mathcal P_{n,p}$, are independent standard Gaussian random variables. The disorder is the vector $g=(g_P)_{P}\in\mathbb R^{\mathcal P_{n,p}}$, with product law $\bigotimes_{P\in\mathcal P_{n,p}}N(0,1)$; probabilities and expectations in this mission are taken under this law.
--
--   This is the random Hamiltonian whose maximal energy over restricted classes of states the mission studies.
--
--   **Formalization Note** `hamiltonian n p g` is the matrix for a fixed disorder vector `g`; `gaussMeasure n p` is the law of `g` (`Measure.pi` of `gaussianReal 0 1`).
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.1, p.3 (PDF p.6)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace QPSpinProfile

open Matrix MeasureTheory

/-- The dense quantum `p`-spin Hamiltonian as a function of the disorder vector
(arXiv:2610.02166, held version sha256 a0a1ec89…, §1.1, p.3, PDF p.6):
`H_{n,p} = C(n,p)^{-1/2} ∑_{P ∈ 𝒫_{n,p}} g_P P`.

**Formalization Note** The Gaussian coefficients are the coordinates of `g : PauliString n p → ℝ`;
randomness enters only through the law `gaussMeasure n p` of `g`. -/
noncomputable def hamiltonian (n p : ℕ) (g : PauliString n p → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (((Real.sqrt (n.choose p : ℝ))⁻¹ : ℝ) : ℂ) • ∑ P : PauliString n p, ((g P : ℝ) : ℂ) • P.mat

/-- The law of the disorder (arXiv:2610.02166, §1.1, p.3, PDF p.6): the coefficients `g_P`,
`P ∈ 𝒫_{n,p}`, are independent standard Gaussian random variables, i.e. `g` has the product law
`⊗_P N(0,1)` on `ℝ^{𝒫_{n,p}}`. -/
noncomputable def gaussMeasure (n p : ℕ) : Measure (PauliString n p → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1

end QPSpinProfile


