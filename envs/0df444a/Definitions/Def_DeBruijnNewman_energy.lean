-- Prove2me | Definitions.Def_DeBruijnNewman_energy
-- name    : DeBruijnNewman_energy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T13:15:40.358084+00:00
-- url     : https://prove2.me/theorems/88415b21-cfe1-4883-91a2-dae24b42214e
-- title:
--   Hamiltonian interaction, interaction energy and renormalized energy of the zeros
-- statement:
--   The interaction quantities attached to a zero enumeration $x$ and a family of classical locations $\xi$, following Sections 4 and 7 of the source.
--
--   **Hamiltonian interaction.** $H_{jk} := \log \frac{1}{|x_j - x_k|}$ (equation (57)).
--
--   **Interaction energy.** $E_{jk} := \frac{1}{|x_j - x_k|^2}$ (equation (58)).
--
--   **Modified potential.** $V(y) := \frac{1}{|y|^2} - 1 + 2(|y| - 1)$, that is $1/|y|^2$ minus its linearization at $|y| = 1$; it is nonnegative and vanishes to second order at $|y| = 1$.
--
--   **Renormalized interaction energy.** $\tilde E_{jk} := \frac{1}{|\xi_k - \xi_j|^2}\,V\!\left(\frac{x_k - x_j}{\xi_k - \xi_j}\right)$, which vanishes when the zeros sit exactly at the classical locations and therefore measures the deviation of the local configuration from an arithmetic progression.
--
--   **Energies of a finite index set.** For a finite set $I$ of indices, $\tilde E_I := \sum_{j,k \in I,\, j \ne k} \tilde E_{jk}$ and $E_I := \sum_{j,k \in I,\, j \ne k} E_{jk}$. Both sums are over ordered pairs of distinct indices, as in the source.
--
--   Lean's division convention makes $1/0 = 0$, so these expressions take the value $0$ at coincident points; the statements that use them always exclude that case.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Section 4, equations (57)-(58), p. 29, and Section 7, p. 40

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros

open MeasureTheory Set

namespace DeBruijnNewman

/-- The Hamiltonian interaction `H_{jk} = log (1 / |x_j − x_k|)` between two
zeros, Rodgers–Tao equation (57). -/
noncomputable def Hint (x : ℤ → ℝ) (j k : ℤ) : ℝ := Real.log (1 / |x j - x k|)

/-- The interaction energy `E_{jk} = 1 / |x_j − x_k|²`, Rodgers–Tao
equation (58). -/
noncomputable def Eint (x : ℤ → ℝ) (j k : ℤ) : ℝ := 1 / |x j - x k| ^ 2

/-- The modified potential `V(y) = 1/|y|² − 1 + 2(|y| − 1)` of Rodgers–Tao,
Section 7. -/
noncomputable def V (y : ℝ) : ℝ := 1 / |y| ^ 2 - 1 + 2 * (|y| - 1)

/-- The renormalized interaction energy
`Ẽ_{jk} = (1 / |ξ_k − ξ_j|²) V ((x_k − x_j) / (ξ_k − ξ_j))`
of Rodgers–Tao, Section 7. -/
noncomputable def EtildeInt (x xi : ℤ → ℝ) (j k : ℤ) : ℝ :=
  1 / |xi k - xi j| ^ 2 * V ((x k - x j) / (xi k - xi j))

/-- The renormalized energy `Ẽ_I = ∑_{j,k ∈ I, j ≠ k} Ẽ_{jk}` of a finite
index set `I`, Rodgers–Tao Section 7. -/
noncomputable def EtildeFinset (x xi : ℤ → ℝ) (I : Finset ℤ) : ℝ :=
  ∑ j ∈ I, ∑ k ∈ I, if j = k then 0 else EtildeInt x xi j k

/-- The (un-normalized) energy `E_I = ∑_{j,k ∈ I, j ≠ k} E_{jk}` of a finite
index set `I`, Rodgers–Tao Section 8. -/
noncomputable def EFinset (x : ℤ → ℝ) (I : Finset ℤ) : ℝ :=
  ∑ j ∈ I, ∑ k ∈ I, if j = k then 0 else Eint x j k

end DeBruijnNewman


