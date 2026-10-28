-- Prove2me | Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
-- name    : CountingMatroid_Analysis_SlotBlockSignature
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:26.510185+00:00
-- url     : https://prove2.me/theorems/7f8f90b9-25c1-4426-8026-af9767b5a00f
-- title:
--   A slot block matrix and its extended vector
-- statement:
--   Let $\alpha$ be an index type, let $V:\alpha\times\alpha\to\mathbb R$ be a matrix, let $s_a,s_b:\alpha\to\mathbb R$ be two vectors, and let $u\in\mathbb R$. Add two new coordinates labeled $0,1$. In the order $\alpha,0,1$, the slot block matrix is
--   $$M=\begin{pmatrix}
--   V&s_b&s_a\\
--   s_b^{\mathsf T}&0&u\\
--   s_a^{\mathsf T}&u&0
--   \end{pmatrix}.$$
--   Thus each mixed block uses the opposite child total: coordinate $0$ couples to $s_b$ and coordinate $1$ to $s_a$. For $h:\alpha\to\mathbb R$ and real numbers $x,y$, the extended vector is
--   $$\widetilde h|_\alpha=h,\qquad \widetilde h(0)=x,\qquad\widetilde h(1)=y.$$
--   No symmetry condition on $V$, finiteness assumption on $\alpha$, or signature inequality is part of these two definitions.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/SlotBlockSignature.lean#L15-L23

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
section


set_option autoImplicit false

/-!
The block-matrix calculation for the transport Hessian. This module proves
the implication from a one-positive-direction bound to the balanced slot
inequality; it does not assert that operational weights satisfy that bound.
-/

namespace CountingMatroid.Analysis.SlotBlockSignature

open scoped BigOperators

/-- INTERNAL: The old-hole block and two new coordinates, with the opposite
child totals in the mixed blocks.
TEXLINE: main.tex:595-601 -/
def slotBlockMatrix {α : Type*} (V : α → α → ℝ) (sₐ sᵦ : α → ℝ)
    (u : ℝ) : Matrix (α ⊕ Bool) (α ⊕ Bool) ℝ
  | .inl i, .inl j => V i j
  | .inl i, .inr b => if b then sₐ i else sᵦ i
  | .inr b, .inl i => if b then sₐ i else sᵦ i
  | .inr b, .inr c => if b = c then 0 else u

/-- INTERNAL: Extend an old-hole vector by the two new coordinate values.
TEXLINE: main.tex:605-625 -/
def slotBlockVector {α : Type*} (h : α → ℝ) (x y : ℝ) : α ⊕ Bool → ℝ :=
  Sum.elim h (fun b => if b then y else x)





end CountingMatroid.Analysis.SlotBlockSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · expanded the opposite-child block matrix and proved the balanced slot inequality from its one-positive-direction signature, using the positive vector (0,1,1).
-/

end


