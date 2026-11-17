-- Prove2me | Definitions.Def_GapAgnosticGS_Supplement_selectorReward
-- name    : GapAgnosticGS_Supplement_selectorReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:33.313172+00:00
-- url     : https://prove2.me/theorems/18c3500b-ccb4-4528-97a0-a9c46332e7d3
-- title:
--   Reward of a selector state, $\mathrm{reward}(\rho)$ (Problem 3.12)
-- statement:
--   Let $E$ be a hidden-basis environment on a selector register $I=\mathbb C^n$ and an arm register $A$, with the known arm state $|0\rangle_A$ and the known reward projector $\Pi$ on $A$. The **reward** of a state $\rho$ of the selector register is
--
--   $$
--   \mathrm{reward}(\rho)=\operatorname{tr}\big((I\otimes\Pi)\,E\,(\rho\otimes|0\rangle\langle0|_A)\,E^\dagger\big),
--   $$
--
--   the probability of the reward-one outcome when the environment is applied to $\rho$. For a density matrix $\rho$ it equals $\sum_j\langle\phi_j|\rho|\phi_j\rangle\,p_j$, the average of the arm rewards $p_j$ under the distribution of $\rho$ over the hidden basis $\{|\phi_j\rangle\}$.
--
--   It is the objective of the PAC version of the hidden-basis bandit problem (Problem 3.12, Problem 4.1, Theorem 4.4): output a state whose reward is at least $p_\star-\varepsilon$.
--
--   **Formalization Note** The tensor product is `Matrix.kronecker` with the selector register first, as in the base mission's `HidEnv`; the real part of the trace is taken.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Problem 3.12 (PAC for QMAB), p.13 (PDF p.14); Problem 4.1, p.17 (PDF p.18)

import Definitions.Def_GapAgnosticGS_HidEnv

namespace GapAgnosticGS.Supplement

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Problem 3.12 (PAC for QMAB), p.13 (PDF p.14): "output a state ρ_I on the input register
I such that reward(ρ) := tr((I ⊗ Π) E (ρ_I ⊗ |0⟩⟨0|) E†) ≥ max_j p_j − ϵ"; Problem 4.1, p.17
(PDF p.18), "in the PAC setting reward(ρ_I) ≥ max_j p_j − ϵ". The **reward of a selector state**
`ρ` (a matrix on the selector register `Fin n`) in the hidden-basis environment `Env`:
`Re tr((1 ⊗ Π) E (ρ ⊗ |a₀⟩⟨a₀|) E†)`.

**Formalization Note.** `|0⟩_A` is the environment's known arm-register state `a₀`, `Π` its known
projector `Prj`; the tensor product is `Matrix.kronecker` with the selector register first, as in
`HidEnv`. The trace is real for a density matrix `ρ`; the real part is taken. For a density matrix
it equals `Σ_j ⟨ϕ_j|ρ|ϕ_j⟩ p_j`. -/
noncomputable def selectorReward {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) Prj * Env.E *
    Matrix.kronecker ρ (Matrix.single a₀ a₀ (1 : ℂ)) * Env.E.conjTranspose)).re

end GapAgnosticGS.Supplement


