-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_TransitionMatrices
-- name    : NCFactorClosure607_Circuits_TransitionMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:07.255013+00:00
-- url     : https://prove2.me/theorems/4fa93d9d-7c31-4e7f-92dc-4c5c27fe111f
-- title:
--   Transition matrices $A_x$, $M_x$ and the matrix substitution $P((M_x)_{x\in X})$
-- statement:
--   Fix cofactor data with word $v=v_1\cdots v_b$, coefficient $c$ and suffix coefficients $d_\ell$, and put $\alpha_\ell=d_\ell/c$.
--
--   For a letter $x\in X$, $A_x$ is the $(b+1)\times(b+1)$ scalar matrix on the erasing states $0,\dots,b$ whose $(i,j)$ entry is the sum of the replacement labels of the transitions from $i$ to $j$ reading $x$: for each $0\le i<b$ with $x=v_{i+1}$ it has $1$ at $(i,i+1)$ and $-\alpha_{i+1}$ at $(i,0)$, and all other entries are $0$.
--
--   Indexing an additional row and column by $*$, the matrix $M_x$ with entries in $F\langle X\rangle$ is
--   $$M_x=\begin{pmatrix}x & e_0^{\mathsf T}A_x\\ 0 & A_x\end{pmatrix},$$
--   where $e_0$ is the coordinate vector of state $0$. For a polynomial $P$, $P((M_x)_{x\in X})$ is the matrix obtained by substituting $M_x$ for each variable $x$, with additions and ordered products of matrices over the noncommutative ring $F\langle X\rangle$.
--
--   These matrices implement the automaton map $T$ on circuits.
--
--   **Formalization Note** $A_x$ is written as the sum, over the advance and reset transitions, of their labels when their source, target and letter match. The substitution is `FreeAlgebra.lift`, the unique $F$-algebra map from $F\langle X\rangle$ to matrices over $F\langle X\rangle$ sending $x$ to $M_x$.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.9, §4, definition of A_x and eq. (7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_CofactorNFA

/-!
# Transition matrices of the cofactor-removal automaton

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §4, eq. (7), p.9.
-/

namespace NCFactorClosure607.Circuits

namespace CofactorData

variable {F : Type*} [Field F] {X : Type*}

open scoped Classical in
/-- The scalar transition matrix `A_x` on the erasing states `0, …, b` (§4, p.9): its `(i, j)`
entry is the sum of the replacement labels of the transitions from `i` to `j` reading `x`,
i.e. of `1` for every advance `t → t+1` and of `-α_{t+1}` for every reset `t → 0`, where
`v_{t+1} = x`. -/
noncomputable def eraseMatrix (data : CofactorData F X) (x : X) :
    Matrix (Fin (data.b + 1)) (Fin (data.b + 1)) F :=
  Matrix.of fun i j =>
    ∑ t : Fin data.b,
      ((if t.castSucc = i ∧ t.succ = j ∧ data.letter t = x then (1 : F) else 0) +
        (if t.castSucc = i ∧ (0 : Fin (data.b + 1)) = j ∧ data.letter t = x then
          data.resetCoeff t else 0))

/-- The matrix `M_x` of eq. (7), indexed by the states `∗, 0, …, b` (`none` = `∗`), with
entries in `F⟨X⟩`: `(M_x)_{∗,∗} = x`, `(M_x)_{∗,j} = (e₀ᵀ A_x)_j = (A_x)_{0,j}`,
`(M_x)_{i,∗} = 0` and `(M_x)_{i,j} = (A_x)_{i,j}` for erasing states `i, j`. -/
noncomputable def transMatrix (data : CofactorData F X) (x : X) :
    Matrix (State data.b) (State data.b) (FreeAlgebra F X) :=
  Matrix.of fun p q =>
    match p, q with
    | none, none => FreeAlgebra.ι F x
    | none, some j => algebraMap F (FreeAlgebra F X) (data.eraseMatrix x 0 j)
    | some _, none => 0
    | some i, some j => algebraMap F (FreeAlgebra F X) (data.eraseMatrix x i j)

/-- `P((M_x)_{x ∈ X})`: the matrix obtained by substituting `M_x` for every variable `x` of
`P` (the unique `F`-algebra homomorphism from `F⟨X⟩` to matrices over `F⟨X⟩` sending `x` to
`M_x`). -/
noncomputable def substMatrix (data : CofactorData F X) (P : FreeAlgebra F X) :
    Matrix (State data.b) (State data.b) (FreeAlgebra F X) :=
  FreeAlgebra.lift F data.transMatrix P

end CofactorData

end NCFactorClosure607.Circuits


