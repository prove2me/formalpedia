-- Prove2me | Definitions.Def_symplectic_block_generators
-- name    : symplectic_block_generators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T15:40:48.921479+00:00
-- url     : https://prove2.me/theorems/000585b0-5958-4fcf-a556-c2e45f43b998
-- title:
--   Standard block generators of $\mathfrak{sp}_{2l}(R)$
-- statement:
--   Mathlib defines the symplectic Lie algebra $\mathfrak{sp}_{2l}(R)$ as the skew-adjoint matrices for the canonical alternating form $J$, and stops there. There is no membership criterion, no description of its elements in blocks, and no distinguished generating family. This file supplies the standard families, over an arbitrary commutative ring.
--
--   **Block picture.** Writing a $2l\times2l$ matrix in $l\times l$ blocks, membership in $\mathfrak{sp}_{2l}(R)$ amounts to
--
--   $$
--   A=\begin{pmatrix} a & b\\ c & -a^{\mathsf T}\end{pmatrix},
--   \qquad b^{\mathsf T}=b,\qquad c^{\mathsf T}=c .
--   $$
--
--   The diagonal blocks carry a copy of $\mathfrak{gl}_l$, and the two off-diagonal blocks carry the abelian nilradical of the Siegel parabolic subalgebra and its opposite.
--
--   **The families.** For indices $i,j$, the symmetric elementary matrix is
--
--   $$
--   \Sigma_{i,j}=\begin{cases} E_{i,i}, & i=j,\\ E_{i,j}+E_{j,i}, & i\ne j,\end{cases}
--   $$
--
--   the diagonal convention being $E_{i,i}$ rather than $2E_{i,i}$ so that the family stays a basis of the symmetric matrices over any commutative ring, including one in which $2$ is not invertible. The three generator families are then
--
--   $$
--   X_{i,j}=\begin{pmatrix} E_{i,j} & 0\\ 0 & -E_{i,j}^{\mathsf T}\end{pmatrix},\qquad
--   T_{i,j}=\begin{pmatrix} 0 & \Sigma_{i,j}\\ 0 & 0\end{pmatrix},\qquad
--   S_{i,j}=\begin{pmatrix} 0 & 0\\ \Sigma_{i,j} & 0\end{pmatrix},
--   $$
--
--   spanning respectively the $\mathfrak{gl}_l$ part, the upper-right nilradical and the lower-left one.
--
--   Two named sets accompany them. The *standard basis set* collects all three families and is the natural spanning family of $\mathfrak{sp}_{2l}(R)$. The *standard generator set* is smaller — all $X_{i,j}$, all $T_{i,j}$, but only the diagonal $S_{i,i}$ — and is what generates the algebra once brackets are allowed, since the off-diagonal $S_{i,j}$ arise as $[S_{i,i},X_{i,j}]$.
--
--   The only lemma included here is the symmetry of $\Sigma_{i,j}$, which is the structural fact that makes the membership statements typecheck as expected.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l), where sp_{2l} is described in exactly this block form with the three displayed families of elements. Mathlib provides only LieAlgebra.Symplectic.sp (Mathlib/Algebra/Lie/Classical.lean) with no membership criterion, block description, spanning family or generating set; this file supplies them.

import Mathlib

/-!
# Standard block generators of the symplectic Lie algebra

Mathlib defines `LieAlgebra.Symplectic.sp` as the skew-adjoint matrices for the
canonical form `J`, and stops there: there is no membership criterion, no
description of its elements in blocks, and no distinguished generating family.
This file supplies the standard families.

Writing a `2l x 2l` matrix in `l x l` blocks, the symplectic Lie algebra
consists of the matrices whose lower-right block is minus the transpose of the
upper-left one and whose off-diagonal blocks are symmetric.  The three families
below realize that description: `elemX` occupies the diagonal blocks and spans a
copy of `gl_l`, while `elemT` and `elemS` occupy the upper-right and lower-left
blocks and span the two abelian nilradicals.
-/

namespace SymplecticMatrix

variable {l : ℕ} {R : Type*} [CommRing R]

/-- The elementary symmetric matrix attached to an unordered pair: the matrix
unit `E i i` on the diagonal, and `E i j + E j i` off it.  Avoiding the factor
`2` on the diagonal keeps the family a basis of the symmetric matrices over any
commutative ring. -/
def symmMatrix (i j : Fin l) : Matrix (Fin l) (Fin l) R :=
  if i = j then Matrix.single i i 1
  else Matrix.single i j 1 + Matrix.single j i 1

/-- The generator occupying the diagonal blocks, `E i j - E (l+j) (l+i)`.  These
span the copy of `gl_l` inside the symplectic Lie algebra. -/
def elemX (i j : Fin l) : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
  Matrix.fromBlocks (Matrix.single i j 1) 0 0 (-(Matrix.single i j (1 : R)).transpose)

/-- The generator occupying the upper-right block.  These span the abelian
nilradical of the Siegel parabolic subalgebra. -/
def elemT (i j : Fin l) : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
  Matrix.fromBlocks 0 (symmMatrix i j) 0 0

/-- The generator occupying the lower-left block, the opposite nilradical. -/
def elemS (i j : Fin l) : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R :=
  Matrix.fromBlocks 0 0 (symmMatrix i j) 0

@[simp]
theorem symmMatrix_transpose (i j : Fin l) :
    (symmMatrix i j : Matrix (Fin l) (Fin l) R).transpose = symmMatrix i j := by
  unfold symmMatrix
  split_ifs with h
  · simp [Matrix.transpose_single]
  · rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]

/-- The full standard spanning family: every diagonal-block generator together
with every upper-right and every lower-left generator. -/
def standardBasisSet (l : ℕ) (R : Type*) [CommRing R] :
    Set (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) :=
  (Set.range fun p : Fin l × Fin l => elemX p.1 p.2) ∪
    (Set.range fun p : Fin l × Fin l => elemS p.1 p.2) ∪
    (Set.range fun p : Fin l × Fin l => elemT p.1 p.2)

/-- The set of standard generators used to generate the symplectic Lie algebra:
all diagonal-block generators, the diagonal lower-left generators, and all
upper-right generators. -/
def standardGenerators (l : ℕ) (R : Type*) [CommRing R] :
    Set (Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R) :=
  (Set.range fun p : Fin l × Fin l => elemX p.1 p.2) ∪
    (Set.range fun i : Fin l => elemS i i) ∪
    (Set.range fun p : Fin l × Fin l => elemT p.1 p.2)

end SymplecticMatrix


