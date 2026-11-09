-- Prove2me | Definitions.Def_ElimAgree_ComLabel
-- name    : ElimAgree_ComLabel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:17.946599+00:00
-- url     : https://prove2.me/theorems/e1702b17-e8dc-4736-9539-57478af18416
-- title:
--   Common-output, transcript-determined and designated-party output rules
-- statement:
--   Fix an answer function $F:\alpha\times\beta\to O$; the elimination problem asks for an output different from $F(x,y)$.
--
--   1. **Common output** (Definition 2.1): at a leaf Alice outputs $o_A(x)$ and Bob outputs $o_B(y)$, each from their own view. A run **fails** if $o_A(x)\ne o_B(y)$, or if $o_A(x)=o_B(y)=F(x,y)$.
--   2. **Transcript-determined output**: each leaf carries one output $o\in O$, known to both parties; the run fails iff $o=F(x,y)$.
--   3. **Designated-party output** (Theorem 3.1, last clause): each leaf names one party and an output function of that party's input; the run fails iff the designated party's output equals $F(x,y)$. The output at a leaf **takes at most $M$ values on that leaf** when, restricted to the inputs that reach the leaf, the output function takes at most $M$ distinct values.
--
--   The error of a protocol is its failure probability on an input; error bounds are imposed **pointwise**, on every input.
--
--   **Formalization Note** `LeafValuesLE M T A B` tracks the rectangle $A\times B$ of inputs reaching each subtree, starting from all inputs; `Set.ncard` counts the values, and all input types in use are finite.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Definition 2.1, p.6 (PDF p.8); Theorem 3.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_ElimAgree_CostLE

namespace ElimAgree

/-- The common-output leaf label of Definition 2.1 (Ben Daniel, *Can Many Instances Be Cheaper
Than One? The Price of Agreement in Elimination*, manuscript, STOC 2027 submission, p.6): at a
leaf, Alice outputs `outA x` and Bob outputs `outB y`, each from their own view (their input; the
coins and the transcript are fixed by the leaf). -/
structure ComLabel (α β O : Type) where
  outA : α → O
  outB : β → O

variable {α β O : Type}

/-- Failure of a common-output run (Definition 2.1, p.6): the run fails if the two output
vectors differ, or if both equal the true answer `t = F(x, y)`. -/
def comFails (l : ComLabel α β O) (x : α) (y : β) (t : O) : Prop :=
  l.outA x ≠ l.outB y ∨ (l.outA x = t ∧ l.outB y = t)

/-- Failure probability of a common-output protocol for `Elim(F)` on input `(x, y)`. -/
noncomputable def comErr (F : α → β → O)
    (μ : PMF (OneOfManyCC.Protocol α β (ComLabel α β O))) (x : α) (y : β) : ENNReal :=
  failProb μ x y (fun l => comFails l x y (F x y))

/-- Failure probability of a protocol whose output is determined by the transcript (each leaf
carries one output vector, known to both parties): the run fails iff the leaf's vector equals
`F(x, y)`. -/
noncomputable def tdErr (F : α → β → O) (μ : PMF (OneOfManyCC.Protocol α β O)) (x : α)
    (y : β) : ENNReal :=
  failProb μ x y (fun o => o = F x y)

/-- Failure of a designated-party leaf label (Theorem 3.1, last clause, p.7): `inl f` means
Alice is the output party at this leaf and outputs `f x`; `inr f` means Bob outputs `f y`. The
run fails iff the designated party's output equals `t = F(x, y)`. -/
def desFails : (α → O) ⊕ (β → O) → α → β → O → Prop
  | .inl f, x, _, t => f x = t
  | .inr f, _, y, t => f y = t

/-- Failure probability of a designated-party protocol for `Elim(F)` on input `(x, y)`. -/
noncomputable def desErr (F : α → β → O)
    (μ : PMF (OneOfManyCC.Protocol α β ((α → O) ⊕ (β → O)))) (x : α) (y : β) : ENNReal :=
  failProb μ x y (fun l => desFails l x y (F x y))

/-- "The output at each leaf takes at most `M` values on that leaf" (Theorem 3.1, p.7).
`LeafValuesLE M T A B` says this for the subtree `T` reached by the inputs in `A × B`; at a leaf
the designated party's output function, restricted to the inputs that reach the leaf, takes at
most `M` distinct values. Apply it with `A = B = univ` to the whole tree.

**Formalization Note.** `Set.ncard` is `0` on infinite sets; every use has finite input types, so
the images are finite. -/
def LeafValuesLE (M : ℕ) :
    OneOfManyCC.Protocol α β ((α → O) ⊕ (β → O)) → Set α → Set β → Prop
  | .leaf (.inl f), A, _ => (f '' A).ncard ≤ M
  | .leaf (.inr f), _, B => (f '' B).ncard ≤ M
  | .alice s t₀ t₁, A, B =>
      LeafValuesLE M t₀ (A ∩ {x | s x = false}) B ∧ LeafValuesLE M t₁ (A ∩ {x | s x = true}) B
  | .bob s t₀ t₁, A, B =>
      LeafValuesLE M t₀ A (B ∩ {y | s y = false}) ∧ LeafValuesLE M t₁ A (B ∩ {y | s y = true})

end ElimAgree


