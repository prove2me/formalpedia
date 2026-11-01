-- Prove2me | Definitions.Def_WildeQIT_AFW_cqState
-- name    : WildeQIT_AFW_cqState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:57.282993+00:00
-- url     : https://prove2.me/theorems/d70a6aab-eaf6-4eb0-9347-daadc08aff39
-- title:
--   Classical–quantum state $\sum_x p(x)\,|x\rangle\langle x|_X \otimes \rho^x_B$
-- statement:
--   Let $\mathcal X$ be a finite alphabet, $\{|x\rangle\}_{x\in\mathcal X}$ an orthonormal basis of $\mathcal H_X$ (so $\dim\mathcal H_X = |\mathcal X|$), $p$ a probability distribution on $\mathcal X$, and $\{\rho^x_B\}_{x\in\mathcal X}$ operators on $\mathcal H_B$. The associated **classical–quantum state** is
--
--   $$
--   \rho_{XB} = \sum_{x\in\mathcal X} p(x)\,|x\rangle\langle x|_X \otimes \rho^x_B .
--   $$
--
--   When every $\rho^x_B$ is a density operator, $\rho_{XB}$ is a density operator; the second part of the AFW inequality (Theorem 11.10.3) gives sharper continuity bounds for such states.
--
--   **Formalization Note** $\mathcal X$ is a finite type `X` that also indexes $\mathcal H_X$. The orthonormal basis is given by the columns of a matrix $U$ ($|x\rangle$ = column $x$ of $U$); the theorems require $U$ to be unitary, which is exactly the condition that its columns form an orthonormal basis, and $U = I$ gives the standard basis. $|x\rangle\langle x|$ is the outer product of the column with its conjugate, $\otimes$ is the Kronecker product on `X × B`, and $p$ is a published `WildeQIT.FinDist X`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.3, (11.254)–(11.255), p. 359

import Mathlib
import Definitions.Def_WildeQIT_FinDist

open scoped Kronecker

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.3,
(11.254), p. 359: the classical–quantum state
"ρ_XB = Σ_x p(x)|x⟩⟨x|_X ⊗ ρ^x_B, where p … [is a probability distribution] defined over a finite
alphabet 𝒳, {|x⟩} is an orthonormal basis, and ρ^x_B ∈ D(H_B) for all x ∈ 𝒳".

**Formalization Note.** The alphabet `𝒳` is a finite type `X` that also indexes `H_X`, so
`dim(H_X) = |𝒳|`. The orthonormal basis `{|x⟩}` is given by the columns of a matrix
`U : Matrix X X ℂ`: `|x⟩ = U.col x` (the statements require `U` unitary, i.e. the columns are an
orthonormal basis; the standard basis is `U = 1`). `|x⟩⟨x|` is `vecMulVec (U.col x) (star (U.col x))`,
and `⊗` is the Kronecker product on `X × B`. The distribution `p` is a published
`WildeQIT.FinDist X`; `ρ^x_B` is `ρx x`. -/
noncomputable def cqState {X B : Type} [Fintype X] (U : Matrix X X ℂ) (p : WildeQIT.FinDist X)
    (ρx : X → Matrix B B ℂ) : Matrix (X × B) (X × B) ℂ :=
  ∑ x, ((p.prob x : ℝ) : ℂ) • (Matrix.vecMulVec (U.col x) (star (U.col x)) ⊗ₖ ρx x)

end WildeQIT.AFW


