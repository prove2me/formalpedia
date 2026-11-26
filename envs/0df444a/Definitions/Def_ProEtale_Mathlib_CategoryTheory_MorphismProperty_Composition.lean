-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_Composition
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:57:51.684143+00:00
-- url     : https://prove2.me/theorems/dcf59341-6e6e-46d1-a79c-ff84f0905a63
-- title:
--   Transition maps of an inverse sequence of P-morphisms lie in P when P is multiplicative
-- statement:
--   Let $\mathcal C$ be a category and $P$ a multiplicative class of morphisms (containing identities and closed under composition). Let $(X_n)_{n \in \mathbb N}$ be objects with morphisms $f_n : X_{n+1} \to X_n$, and let $X : \mathbb N^{\mathrm{op}} \to \mathcal C$ be the associated inverse system. For $m \le n$ its transition map is the composite
--   $$X_n \xrightarrow{f_{n-1}} X_{n-1} \to \cdots \xrightarrow{f_m} X_m.$$
--
--   **Lemma.** If $f_n \in P$ for every $n$, then for all $m \le n$ the transition map $X_n \to X_m$ lies in $P$.
--
--   This lets one check properties of all transition maps of a sequential inverse system on its consecutive maps.
--
--   **Formalization Note** The lemma is `CategoryTheory.MorphismProperty.ofOpSequence_map_of_isMultiplicative`. The inverse system is `Functor.ofOpSequence f`, and the transition map is its image of `(homOfLE hle).op`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/Composition.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.MorphismProperty.Composition

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace MorphismProperty


lemma ofOpSequence_map_of_isMultiplicative {C : Type*} [Category C] {X : ℕ → C}
    (f : (n : ℕ) → X (n + 1) ⟶ X n) {m n : ℕ} (hle : m ≤ n) (P : MorphismProperty C)
    [P.IsMultiplicative] (H : ∀ n, P (f n)) :
    P ((Functor.ofOpSequence f).map (homOfLE hle).op) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using P.id_mem _
  | succ n ih =>
    rw [← homOfLE_comp (show m ≤ m + n by lia) (show m + n ≤ m + (n + 1) by lia),
      op_comp, Functor.map_comp]
    apply P.comp_mem
    · simp [H]
    · apply ih

end MorphismProperty
end CategoryTheory


