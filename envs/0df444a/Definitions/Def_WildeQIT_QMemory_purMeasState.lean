-- Prove2me | Definitions.Def_WildeQIT_QMemory_purMeasState
-- name    : WildeQIT_QMemory_purMeasState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:30.969882+00:00
-- url     : https://prove2.me/theorems/0e9a8e8f-a022-4202-9750-3ec92633933e
-- title:
--   Measured purifying system $\omega_{ZE}=\sum_z|z\rangle\langle z|_Z\otimes\mathrm{Tr}_{AB}\{(\Gamma^z_A\otimes I_{BE})\varphi_{ABE}\}$
-- statement:
--   Let $\varphi_{ABE}$ be an operator on $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_E$ (in the book, the projector $\varphi^\rho_{ABE}$ onto a purification of $\rho_{AB}$) and $\{\Gamma^z_A\}$ a POVM on $A$. The classical–quantum state of the outcome register $Z$ and the purifying system $E$ is
--
--   $$
--   \omega_{ZE}\equiv\sum_z|z\rangle\langle z|_Z\otimes\mathrm{Tr}_{AB}\{(\Gamma^z_A\otimes I_{BE})\varphi_{ABE}\}.
--   $$
--
--   It enters the intermediate uncertainty relation (11.212) from which the book derives the uncertainty principle with quantum memory.
--
--   **Formalization Note** $\mathcal H_A\otimes\mathcal H_B\otimes\mathcal H_E$ is indexed by `(a × b) × e`; $\Gamma\otimes I_{BE}$ is $(\Gamma\otimes I_B)\otimes I_E$; $\mathrm{Tr}_{AB}$ is the published `WildeQIT.partialTraceLeft` over the factor `a × b`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (11.213), p. 355

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace WildeQIT.QMemory

/-- **Measured state of the purifying system** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, eq. (11.213), p. 355): for a POVM `{Γ^z_A}` and an operator
`φ_ABE` (in the book, a purification of `ρ_AB`),
`ω_ZE ≡ ∑_z |z⟩⟨z|_Z ⊗ Tr_AB{(Γ^z_A ⊗ I_BE) φ_ABE}`.

**Formalization Note** `H_A ⊗ H_B ⊗ H_E` is indexed by `(a × b) × e`, and `Γ ⊗ I_BE` is
`(Γ ⊗ I_B) ⊗ I_E`; `Tr_AB` is the published `WildeQIT.partialTraceLeft` over the factor
`a × b`. -/
noncomputable def purMeasState {a b e z : Type} [Fintype a] [Fintype b] [DecidableEq b]
    [Fintype e] [DecidableEq e] [Fintype z] [DecidableEq z] (Γ : z → Matrix a a ℂ)
    (φ : Matrix ((a × b) × e) ((a × b) × e) ℂ) : Matrix (z × e) (z × e) ℂ :=
  ∑ j, Matrix.kronecker (Matrix.single j j (1 : ℂ))
    (WildeQIT.partialTraceLeft
      (Matrix.kronecker (Matrix.kronecker (Γ j) (1 : Matrix b b ℂ)) (1 : Matrix e e ℂ) * φ))

end WildeQIT.QMemory


