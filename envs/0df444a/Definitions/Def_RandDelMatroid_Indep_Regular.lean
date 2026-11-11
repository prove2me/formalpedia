-- Prove2me | Definitions.Def_RandDelMatroid_Indep_Regular
-- name    : RandDelMatroid_Indep_Regular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:25.688116+00:00
-- url     : https://prove2.me/theorems/58df77dc-d111-4ff6-a98f-93efcbf9ba8b
-- title:
--   Representable, binary and regular matroids (Definition 8)
-- statement:
--   Let $M$ be a matroid with ground set $E$ and let $\mathbb F$ be a field. A matrix $A$ over $\mathbb F$ with $n$ rows whose columns are indexed by $E$ (the column of $e$ is a vector $v_e\in\mathbb F^n$) **represents** $M$ if, for every $S\subseteq E$,
--
--   $$S \text{ is independent in } M \iff (v_e)_{e\in S} \text{ is linearly independent over } \mathbb F .$$
--
--   The family is linearly independent as a family, so two elements with equal columns are dependent and an element with a zero column is a loop. $M$ is **binary** if it is representable over $\mathbb F_2$, and **regular** if it is representable over every field.
--
--   Regularity is the hypothesis of every result of the mission. It is the paper's own definition; the equivalent characterisation by totally unimodular matrices (Tutte) is a theorem and is not used here.
--
--   **Formalization Note** `IsRepresentableOver M F` asks for some number of rows `n` and columns `v : β → (Fin n → F)` with `M.Indep S ↔ LinearIndepOn F v S` for every `S ⊆ M.E`. `IsRegular M` quantifies over all fields `F : Type`.
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 10, Definition 8

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

/-- Definition 8 (p. 10). A matroid `M` on ground set `M.E` is *represented* over the field `F`
by a matrix with `n` rows whose columns are indexed by the elements: the column of `e` is
`v e : Fin n → F`, and a set `S ⊆ E` is independent in `M` if and only if the columns indexed by
`S` are linearly independent over `F` (as a family, so a repeated column is dependent). -/
def IsRepresentableOver {β : Type} (M : Matroid β) (F : Type) [Field F] : Prop :=
  ∃ (n : ℕ) (v : β → (Fin n → F)), ∀ S : Set β, S ⊆ M.E → (M.Indep S ↔ LinearIndepOn F v S)

/-- Definition 8 (p. 10). `M` is *binary* if it is representable over `𝔽₂`. -/
def IsBinary {β : Type} (M : Matroid β) : Prop :=
  IsRepresentableOver M (ZMod 2)

/-- Definition 8 (p. 10). `M` is *regular* if it is representable over every field. -/
def IsRegular {β : Type} (M : Matroid β) : Prop :=
  ∀ (F : Type) [Field F], IsRepresentableOver M F

end RandDelMatroid.Indep


