-- Prove2me | Definitions.Def_WildeQIT_QMemory_cqState
-- name    : WildeQIT_QMemory_cqState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:18.447226+00:00
-- url     : https://prove2.me/theorems/d907c931-84d0-4a75-a471-f12563861a92
-- title:
--   Classical–quantum state $\rho_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_B$
-- statement:
--   Let $p_X$ be a probability distribution on a finite alphabet $\mathcal X$ and $\{\rho^x_B\}_{x\in\mathcal X}$ a family of operators on $\mathcal H_B$. The **classical–quantum state** is
--
--   $$
--   \rho_{XB}\equiv\sum_x p_X(x)\,|x\rangle\langle x|_X\otimes\rho^x_B ,
--   $$
--
--   where $\{|x\rangle\}$ is an orthonormal basis of the classical register $X$. When every $\rho^x_B$ is a density operator, $\rho_{XB}$ is a state in which $X$ and $B$ are correlated only classically.
--
--   **Formalization Note** $|x\rangle\langle x|$ is `Matrix.single x x 1` on the standard basis of the finite type indexing $\mathcal X$; $\otimes$ is the Kronecker product, so $\mathcal H_X\otimes\mathcal H_B$ is indexed by `x × b`. The distribution is the published `WildeQIT.FinDist`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (11.32), p. 326 (Definition 4.3.5)

import Mathlib
import Definitions.Def_WildeQIT_FinDist

namespace WildeQIT.QMemory

/-- **Classical–quantum state** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, eq. (11.32), p. 326, after Definition 4.3.5):
`ρ_XB ≡ ∑_x p_X(x) |x⟩⟨x|_X ⊗ ρ^x_B`.

**Formalization Note** The classical register `X` has the standard basis of the finite type
`x`, so `|x⟩⟨x|` is `Matrix.single x x 1`; `⊗` is the Kronecker product and `H_X ⊗ H_B` is
indexed by `x × b`. The distribution is the published `WildeQIT.FinDist`. -/
noncomputable def cqState {x b : Type} [Fintype x] [DecidableEq x] [Fintype b]
    (p : WildeQIT.FinDist x) (ρ : x → Matrix b b ℂ) : Matrix (x × b) (x × b) ℂ :=
  ∑ i, ((p.prob i : ℝ) : ℂ) • Matrix.kronecker (Matrix.single i i (1 : ℂ)) (ρ i)

end WildeQIT.QMemory


