-- Prove2me | Definitions.Def_SymTensorNet_FusionTree
-- name    : SymTensorNet_FusionTree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:19:16.631808+00:00
-- url     : https://prove2.me/theorems/47690218-4543-4c2b-93ed-1b7b68510219
-- title:
--   Fusion trees, their labellings by intermediate charges, and the fusion-tree maps $W(\tau,\ell)$
-- statement:
--   Fix fusion data for a catalogue of irreps of $G$ and a set $S$ of legs.
--
--   1. A **fusion tree** over $S$ is a leaf $s\in S$, the trivial leaf $\mathbf 1$, or a trivalent node joining two fusion trees. Its **leaves** are the legs at its leaf nodes. A tree $\tau$ is **valid for the root leg** $r$ when every leg other than $r$ is a leaf of $\tau$ exactly once and $r$ is not a leaf.
--   2. Given a charge $x_s$ for each leg, the **labellings** $\ell$ of a tree and their **top charges** are defined bottom-up: a leaf $s$ has one labelling, with top charge $x_s$; the trivial leaf has one labelling, with top charge $0$; a node has the labellings $(\ell_1,\ell_2,\kappa)$, with $\ell_i$ a labelling of the $i$-th subtree and $\kappa$ a fusion channel of the pair of their top charges, and top charge $\mathrm{out}(\kappa)$. The channels at the inner branches carry the **intermediate charges** $e_1,e_2,\dots$ of Eq. (15) (and their multiplicity indices).
--   3. The **fusion-tree map** $W(\tau,\ell)$ is the matrix with rows indexed by $m=(m_s)_s$, $m_s\in\{1,\dots,\dim x_s\}$, and columns by $o\in\{1,\dots,\dim(\text{top charge})\}$, defined by
--   $$W(s)(m,o)=\delta_{m_s,o},\qquad W(\mathbf 1)(m,o)=1,\qquad W(\tau_1\tau_2,(\ell_1,\ell_2,\kappa))(m,o)=\sum_{o_1,o_2}W(\tau_1,\ell_1)(m,o_1)\,W(\tau_2,\ell_2)(m,o_2)\,(\iota_\kappa)_{(o_1,o_2),o}.$$
--   It composes the Clebsch–Gordan isometries along the tree. More generally the **tree amplitude** uses arbitrary leaf matrices $B_s$ in place of $\delta$ at the leaves.
--
--   Trees are the "trivalent tree used to label a basis in the space of intertwining operators" of Eq. (15) and Fig. 2(iv).
--
--   **Formalization Note** Trees are not planar: leaves may appear in any order. The trivial leaf is needed for a tensor with a single leg, whose tree has no leg leaf.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (11) (coupled basis obtained "by fusing to the intermediate basis |eq_e⟩") and Eq. (15) with the paragraph after it, p.3; Fig. 2(iv), p.3; footnote [10], p.4

import Mathlib
import Definitions.Def_SymTensorNet_FusionData

namespace SymTensorNet

universe u v w

open Matrix

/-- A **fusion tree** over a set of legs `S`: a leaf carrying a leg, the trivial leaf `unit`
(charge `0`), or a trivalent node fusing two subtrees.

arXiv:0907.2994v2, p.3, Eq. (15): "a trivalent tree used to label a basis in the space of
intertwining operators"; Fig. 2(iv).

**Formalization Note** Trees are not planar: the leaves may appear in any order. The `unit` leaf is
needed for a tensor with one leg, whose only fusion tree has no leg leaf. -/
inductive Tree (S : Type w)
  | leaf (s : S)
  | unit
  | node (t₁ t₂ : Tree S)

namespace Tree

variable {S : Type w}

/-- The list of legs at the leaves of a tree, from left to right. -/
def leaves : Tree S → List S
  | .leaf s => [s]
  | .unit => []
  | .node t₁ t₂ => t₁.leaves ++ t₂.leaves

end Tree

/-- A tree `τ` is **valid for the root leg `r`** when every leg other than `r` occurs exactly once
among its leaves and `r` does not occur.

arXiv:0907.2994v2, p.3, Eq. (15) and Fig. 2(iv): the legs of `T` other than the root hang from the
tree, the root being the leg into which the tree fuses. -/
def IsValidTree {S : Type w} (τ : Tree S) (r : S) : Prop :=
  τ.leaves.Nodup ∧ ∀ s, s ∈ τ.leaves ↔ s ≠ r

variable {G : Type u} [Group G]

/-- The **labellings** of a tree with leaf charges `x`, together with the charge on the top edge of
each labelling, defined bottom-up: a leaf `s` has one labelling, with top charge `x s`; `unit` has
one labelling, with top charge `0`; a node has the labellings `(ℓ₁, ℓ₂, κ)` of its subtrees and a
fusion channel `κ ∈ Chan (top ℓ₁) (top ℓ₂)`, with top charge `out κ`.

arXiv:0907.2994v2, p.3, Eq. (15): "e₁, e₂, …, e_{t′} are intermediate charges that decorate the
inner branches of a trivalent tree"; footnote [10], p.4, for the multiplicity index.

**Formalization Note** A labelling of an inner branch is a fusion channel, which records the
intermediate charge `e_k = out κ` and, beyond multiplicity freeness, the multiplicity index. -/
def LabT (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) :
    Tree S → (Σ L : Type v, (L → F.Charge))
  | .leaf s => ⟨PUnit, fun _ => x s⟩
  | .unit => ⟨PUnit, fun _ => F.unit⟩
  | .node t₁ t₂ =>
    ⟨Σ (l₁ : (LabT F x t₁).1) (l₂ : (LabT F x t₂).1),
        F.Chan ((LabT F x t₁).2 l₁) ((LabT F x t₂).2 l₂),
      fun l => F.out l.2.2⟩

/-- The type of labellings of the tree `t` (see `LabT`). -/
abbrev Lab (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) (t : Tree S) : Type v :=
  (LabT F x t).1

/-- The charge on the top edge of a labelling (see `LabT`). -/
abbrev top (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) (t : Tree S) :
    Lab F x t → F.Charge :=
  (LabT F x t).2

/-- Labellings of a tree form a finite type. -/
instance instFintypeLab (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) :
    (t : Tree S) → Fintype (Lab F x t)
  | .leaf _ => inferInstanceAs (Fintype PUnit)
  | .unit => inferInstanceAs (Fintype PUnit)
  | .node t₁ t₂ =>
    letI := instFintypeLab F x t₁
    letI := instFintypeLab F x t₂
    inferInstanceAs (Fintype (Σ (l₁ : Lab F x t₁) (l₂ : Lab F x t₂),
      F.Chan (top F x t₁ l₁) (top F x t₂ l₂)))

/-- Labellings of a tree have decidable equality. -/
instance instDecEqLab (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) :
    (t : Tree S) → DecidableEq (Lab F x t)
  | .leaf _ => inferInstanceAs (DecidableEq PUnit)
  | .unit => inferInstanceAs (DecidableEq PUnit)
  | .node t₁ t₂ =>
    letI := instDecEqLab F x t₁
    letI := instDecEqLab F x t₂
    inferInstanceAs (DecidableEq (Σ (l₁ : Lab F x t₁) (l₂ : Lab F x t₂),
      F.Chan (top F x t₁ l₁) (top F x t₂ l₂)))

/-- The **amplitude of a labelled fusion tree**, with leaf matrices `B s` from the leaf irrep
`𝕍^{x s}` to an index set `ι s`. For a multi-index `m` (one entry `m s ∈ ι s` per leg) and a
basis index `o` of the top irrep:
- leaf `s`: `B s o (m s)`;
- `unit`: `1`;
- node `(ℓ₁, ℓ₂, κ)`: `Σ_{o₁, o₂} A(t₁, ℓ₁)(m, o₁) A(t₂, ℓ₂)(m, o₂) (ι_κ)_{(o₁, o₂), o}`.

arXiv:0907.2994v2, p.3, Eq. (11) (`Q^{abcd}_e` "obtained by fusing to the intermediate basis
|e q_e⟩") and Eq. (15). -/
def treeAmp (F : FusionData.{u, v} G) {S : Type w} {ι : S → Type*} (x : S → F.Charge)
    (B : (s : S) → Fin (F.dim (x s)) → ι s → ℂ) :
    (t : Tree S) → (ℓ : Lab F x t) → ((s : S) → ι s) → Fin (F.dim (top F x t ℓ)) → ℂ
  | .leaf s, _, m, o => B s o (m s)
  | .unit, _, _, _ => 1
  | .node t₁ t₂, ℓ, m, o =>
    ∑ o₁ : Fin (F.dim (top F x t₁ ℓ.1)), ∑ o₂ : Fin (F.dim (top F x t₂ ℓ.2.1)),
      treeAmp F x B t₁ ℓ.1 m o₁ * treeAmp F x B t₂ ℓ.2.1 m o₂ * F.iso ℓ.2.2 (o₁, o₂) o

/-- The **fusion-tree map** `W(τ, ℓ)`: the matrix from the top irrep `𝕍^{top ℓ}` into the tensor
product `⊗_s 𝕍^{x s}` of the leaf irreps, `W(τ, ℓ)(m, o)`, obtained by composing the
Clebsch–Gordan isometries along the tree (leaf matrices `δ`).

arXiv:0907.2994v2, p.3, Eq. (15): "a trivalent tree used to label a basis in the space of
intertwining operators". -/
def treeW (F : FusionData.{u, v} G) {S : Type w} (x : S → F.Charge) (t : Tree S)
    (ℓ : Lab F x t) (m : (s : S) → Fin (F.dim (x s))) (o : Fin (F.dim (top F x t ℓ))) : ℂ :=
  treeAmp F x (fun _ o n => if o = n then 1 else 0) t ℓ m o

end SymTensorNet


