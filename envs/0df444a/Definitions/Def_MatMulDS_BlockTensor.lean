-- Prove2me | Definitions.Def_MatMulDS_BlockTensor
-- name    : MatMulDS_BlockTensor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:28.663688+00:00
-- url     : https://prove2.me/theorems/2913248e-d9fb-4f37-af29-c9206b6ebbbb
-- title:
--   Block tensors
-- statement:
--   Let $\mathcal I,\mathcal K,\mathcal J$ be finite sets and $\mathcal B$ a finite set of blocks. Each block $\beta$ has nonempty sets $I_\beta\subseteq\mathcal I$, $K_\beta\subseteq\mathcal K$, $J_\beta\subseteq\mathcal J$, and row sets of different blocks are disjoint. The **block tensor** is
--   $$T_{\mathrm{base}}=\sum_{\beta}\sum_{i\in I_\beta}\sum_{k\in K_\beta}\sum_{j\in J_\beta}x_{ik}y_{kj}z_{ij}.$$
--
--   Its outputs are $O=\bigsqcup_\beta I_\beta\times J_\beta$, and an output in block $\beta$ has length $|K_\beta|$. The tensor square has as blocks the pairs of blocks.
--
--   These tensors are those whose outputs split into matrix products, and the data structures of the source are built from their identities.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Definition 5.1, p.27 (PDF p.29); Definition A.1, p.65 (PDF p.67); §6, p.36 (PDF p.38)

import Mathlib

set_option autoImplicit false

namespace MatMulDS

variable {I K J B : Type} [Fintype I] [Fintype K] [Fintype J] [Fintype B]
  [DecidableEq I] [DecidableEq K] [DecidableEq J] [DecidableEq B]

/-- **Block tensor** (Definition 5.1, p.27; Definition A.1, p.65, STOC 2027 submission, held file sha256
6c5a1c16…). `I`, `K`, `J` are the finite sets of rows, middle indices and columns, and `B` the finite set of
blocks. Each block `β` has nonempty sets of rows `I_β`, middle indices `K_β` and columns `J_β`, and the row sets
of different blocks are disjoint. The tensor is `T_base = Σ_β Σ_{i∈I_β} Σ_{k∈K_β} Σ_{j∈J_β} x_ik y_kj z_ij`. -/
structure BlockTensor (I K J B : Type) [DecidableEq I] [DecidableEq K] [DecidableEq J] where
  rows : B → Finset I
  mids : B → Finset K
  cols : B → Finset J
  rows_nonempty : ∀ β, (rows β).Nonempty
  mids_nonempty : ∀ β, (mids β).Nonempty
  cols_nonempty : ∀ β, (cols β).Nonempty
  rows_disjoint : ∀ β β', β ≠ β' → Disjoint (rows β) (rows β')

namespace BlockTensor

variable (T : BlockTensor I K J B)

/-- The outputs `z_ij` of a block: `I_β × J_β`. -/
def blockOutputs (β : B) : Finset (I × J) := T.rows β ×ˢ T.cols β

/-- The set `O = ⊔_β I_β × J_β ⊆ I × J` of outputs (p.65). -/
def outputs : Finset (I × J) := Finset.univ.biUnion T.blockOutputs

/-- The outputs as a type. -/
abbrev Out : Type := {o : I × J // o ∈ T.outputs}

/-- The set `X` of left variables `x_ik`. -/
def leftVars : Finset (I × K) := Finset.univ.biUnion fun β => T.rows β ×ˢ T.mids β

/-- The set `Y` of right variables `y_kj`. -/
def rightVars : Finset (K × J) := Finset.univ.biUnion fun β => T.mids β ×ˢ T.cols β

/-- The monomial `x_a y_b z_o` occurs in the tensor. -/
def Incident (a : I × K) (b : K × J) (o : I × J) : Prop :=
  ∃ β, a.1 ∈ T.rows β ∧ a.2 ∈ T.mids β ∧ b.1 = a.2 ∧ b.2 ∈ T.cols β ∧ o = (a.1, b.2)

/-- The length `len(o) = |K_β|` of an output `o` in block `β` (p.65). Row sets are disjoint, so at most one
term of the sum is nonzero. -/
def len (o : I × J) : ℕ := ∑ β, if o ∈ T.blockOutputs β then (T.mids β).card else 0

/-- The block tensor of pairs of blocks (§6, p.36): its blocks are the pairs of blocks. -/
def square : BlockTensor (I × I) (K × K) (J × J) (B × B) where
  rows β := T.rows β.1 ×ˢ T.rows β.2
  mids β := T.mids β.1 ×ˢ T.mids β.2
  cols β := T.cols β.1 ×ˢ T.cols β.2
  rows_nonempty β := (T.rows_nonempty β.1).product (T.rows_nonempty β.2)
  mids_nonempty β := (T.mids_nonempty β.1).product (T.mids_nonempty β.2)
  cols_nonempty β := (T.cols_nonempty β.1).product (T.cols_nonempty β.2)
  rows_disjoint β β' h := by
    by_cases h1 : β.1 = β'.1
    · have h2 : β.2 ≠ β'.2 := fun h2 => h (Prod.ext h1 h2)
      exact Finset.disjoint_product.mpr (Or.inr (T.rows_disjoint _ _ h2))
    · exact Finset.disjoint_product.mpr (Or.inl (T.rows_disjoint _ _ h1))

/-- The output `(w, w)` of the tensor square. -/
def squareOut (w : I × J) : (I × I) × (J × J) := ((w.1, w.1), (w.2, w.2))

end BlockTensor

end MatMulDS


