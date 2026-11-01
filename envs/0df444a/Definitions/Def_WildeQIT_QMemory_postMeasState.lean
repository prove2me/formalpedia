-- Prove2me | Definitions.Def_WildeQIT_QMemory_postMeasState
-- name    : WildeQIT_QMemory_postMeasState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:33.438401+00:00
-- url     : https://prove2.me/theorems/3b42f307-1d64-4364-836e-83c452ea458d
-- title:
--   Post-measurement state $\sigma_{XB}=\sum_x|x\rangle\langle x|_X\otimes\mathrm{Tr}_A\{(\Lambda^x_A\otimes I_B)\rho_{AB}\}$
-- statement:
--   Let $\rho_{AB}$ be a state shared by Alice ($A$) and Bob ($B$), and let Alice measure a POVM $\{\Lambda^x_A\}$ on her system, recording the outcome in a classical register $X$ with orthonormal basis $\{|x\rangle\}$. The post-measurement classical–quantum state is
--
--   $$
--   \sigma_{XB}\equiv\sum_x|x\rangle\langle x|_X\otimes\mathrm{Tr}_A\{(\Lambda^x_A\otimes I_B)\rho_{AB}\}.
--   $$
--
--   Outcome $x$ occurs with probability $\mathrm{Tr}\{(\Lambda^x_A\otimes I_B)\rho_{AB}\}$, and $H(X|B)_\sigma$ is Bob's uncertainty about it. The same construction with a second POVM $\{\Gamma^z_A\}$ gives $\tau_{ZB}$ of (11.209).
--
--   **Formalization Note** $|x\rangle\langle x|$ is `Matrix.single x x 1`; $\mathcal H_A\otimes\mathcal H_B$ is indexed by `a × b`; $\mathrm{Tr}_A$ is the published `WildeQIT.partialTraceLeft`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eqs. (11.208)–(11.209), pp. 353–354

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace WildeQIT.QMemory

/-- **Post-measurement classical–quantum state** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, eqs. (11.208)–(11.209), pp. 353–354): when Alice measures the POVM
`{Λ^x_A}` on her share of `ρ_AB`,
`σ_XB ≡ ∑_x |x⟩⟨x|_X ⊗ Tr_A{(Λ^x_A ⊗ I_B) ρ_AB}`.

**Formalization Note** `|x⟩⟨x|` is `Matrix.single x x 1` on the standard basis of the outcome
type; `H_A ⊗ H_B` is indexed by `a × b`; `Tr_A` is the published `WildeQIT.partialTraceLeft`. -/
noncomputable def postMeasState {a b x : Type} [Fintype a] [Fintype b] [DecidableEq b]
    [Fintype x] [DecidableEq x] (Λ : x → Matrix a a ℂ) (ρ : Matrix (a × b) (a × b) ℂ) :
    Matrix (x × b) (x × b) ℂ :=
  ∑ i, Matrix.kronecker (Matrix.single i i (1 : ℂ))
    (WildeQIT.partialTraceLeft (Matrix.kronecker (Λ i) (1 : Matrix b b ℂ) * ρ))

end WildeQIT.QMemory


