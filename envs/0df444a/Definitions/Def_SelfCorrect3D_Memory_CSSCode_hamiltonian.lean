-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_CSSCode_hamiltonian
-- name    : SelfCorrect3D_Memory_CSSCode_hamiltonian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:12.614717+00:00
-- url     : https://prove2.me/theorems/f026c26a-d4d6-42ef-936b-026850b4fcc2
-- title:
--   Stabilizer Hamiltonian $H=\sum_a\frac{1-S^X_a}{2}+\sum_b\frac{1-S^Z_b}{2}$
-- statement:
--   The **stabilizer Hamiltonian** of a CSS code is
--
--   $$H=\sum_{a=1}^{m_x}\frac{1-S^X_a}{2}+\sum_{b=1}^{m_z}\frac{1-S^Z_b}{2}.$$
--
--   Each violated check costs energy $1$, so on the syndrome-$\sigma$ subspace $H$ equals the syndrome weight $|\sigma|=|\sigma_Z|+|\sigma_X|$ ("$H'$ is diagonal in the syndrome basis with matrix elements equal to the size of the syndrome").
--
--   **Formalization Note** There is one term per row of $H_x$ and of $H_z$, including dependent or repeated rows, each with coefficient $1/2$; no normalization.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, §2.5, p. 21; Theorem 1.1, p. 4

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode

namespace SelfCorrect3D.Memory

/-- **Stabilizer Hamiltonian** `H = Σ_a (1 − S^X_a)/2 + Σ_b (1 − S^Z_b)/2`.
Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943, §2.5, p. 21 (after Theorem 2.6): "H′ is diagonal in the
syndrome basis with matrix elements equal to the size of the syndrome"; the Hamiltonian of the
code (Theorem 1.1, p. 4; Theorem 3.16 (3), p. 40).

**Formalization Note.** One term per row of `H_x` and of `H_z`, including dependent or repeated
rows, each with coefficient `1/2` (energy `1` per violated check); no normalization. -/
noncomputable def CSSCode.hamiltonian {n mX mZ : ℕ} (C : CSSCode n mX mZ) : Op n :=
  (1 / 2 : ℂ) • ((∑ a, (1 - C.stabX a)) + ∑ b, (1 - C.stabZ b))

end SelfCorrect3D.Memory


