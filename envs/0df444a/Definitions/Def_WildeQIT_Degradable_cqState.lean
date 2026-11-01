-- Prove2me | Definitions.Def_WildeQIT_Degradable_cqState
-- name    : WildeQIT_Degradable_cqState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:10.360875+00:00
-- url     : https://prove2.me/theorems/0ceb24b9-77d4-49e5-b748-6f2bc324e21f
-- title:
--   Classical–quantum state $\sum_x p(x)|x\rangle\langle x|_X\otimes\rho_x$
-- statement:
--   Given a finite alphabet $\mathcal X$, weights $p(x)$ and operators $\rho_x$ on a system $B$, the **classical–quantum state** is
--
--   $$
--   \rho_{XB} \equiv \sum_x p(x)\,|x\rangle\langle x|_X\otimes\rho_x ,
--   $$
--
--   with $\{|x\rangle\}$ the standard basis of the classical register $X$. When $p$ is a probability distribution and each $\rho_x$ a density operator, $\rho_{XB}$ is a density operator, and its quantum mutual information $I(X;B)_\rho$ is the Holevo information of the ensemble.
--
--   **Formalization Note** $|x\rangle\langle x|$ is `Matrix.single x x 1`, the register $X$ is the left factor of `X × B`, and the weights are a real function, so the definition is total; every statement that uses it supplies a probability distribution (or a convex combination of two) and density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eqs. (13.82)–(13.83), pp. 400–401; also (13.110)–(13.112), p. 405, and (13.178), p. 416

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.3, pp. 400–401, eqs. (13.82)–(13.83) (classical–quantum states).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.Degradable

/-- **Classical–quantum state** `ρ_{XB} ≡ ∑ₓ p_X(x) |x⟩⟨x|_X ⊗ ρˣ_B`
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 400–401, eqs. (13.82)–(13.83), (13.110)–(13.112), (13.178)).

**Formalization Note.** `|x⟩⟨x|_X` is `Matrix.single x x 1` on the classical alphabet `X`, the
left factor of `X × B`. The weights are a real function `p`; every use in this mission supplies
a probability distribution (or a convex combination of two). -/
noncomputable def cqState {X B : Type} [Fintype X] [DecidableEq X] (p : X → ℝ)
    (ρ : X → Matrix B B ℂ) : Matrix (X × B) (X × B) ℂ :=
  ∑ x, Matrix.single x x ((p x : ℂ)) ⊗ₖ ρ x

end WildeQIT.Degradable


