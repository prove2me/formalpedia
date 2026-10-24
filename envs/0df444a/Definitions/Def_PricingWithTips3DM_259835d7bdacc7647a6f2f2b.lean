-- Prove2me | Definitions.Def_PricingWithTips3DM_259835d7bdacc7647a6f2f2b
-- name    : PricingWithTips3DM_259835d7bdacc7647a6f2f2b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:18:49.302634+00:00
-- url     : https://prove2.me/theorems/da5801c4-7397-466e-b925-5046eb4a7341
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Sets.Matching3D
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_PricingWithTips3DM_06e60956ff918030951e5808
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# 3-dimensional matching

An instance of 3-DIMENSIONAL MATCHING is three finite element sets `W`, `X`,
`Y` together with a set of triples `M ⊆ W × X × Y`. A yes-instance is one
where some subset `M' ⊆ M` is a *matching*: every element of every coordinate
is used by exactly one triple of `M'`.

Two deliberate choices in the formulation:

* The triples are a `Finset`, not a list. In SET COVER positions name the
  items because the threshold *counts* them; here duplicates are meaningless
  (two identical triples agree in every coordinate, so no matching contains
  both), and Garey–Johnson's `M ⊆ W × X × Y` is genuinely a set.
* Garey–Johnson require `|W| = |X| = |Y| = q` and ask for a matching of size
  `q`. Demanding instead that the matching cover all three coordinates
  *exactly* says the same thing without a well-formedness promise: an
  instance with `|W| ≠ |X|` admits no exact cover and is simply a
  no-instance. This is the `Problem.restrict`-free discipline of the library
  applied to a cardinality side condition.

Hardness proof (in `Matching3D/`): from SAT (`FromSat.lean`, the
truth-setting / satisfaction-testing / garbage-collection construction;
certified in `FromSat/Code.lean` and `FromSat/Adequacy.lean`).
-/

namespace Hardness

/-- `M` covers `Z` exactly along the coordinate map `p`: every element of `Z`
is `p`-hit by exactly one member of `M`. This single condition packages both
halves of "is a matching": *covering* (some member hits `z`) and
*disjointness* (no two members hit the same `z`). -/
def IsExactCover {ι Z : Type*} (M : Finset ι) (p : ι → Z) : Prop :=
  ∀ z : Z, ∃! t, t ∈ M ∧ p t = z

namespace IsExactCover

variable {ι Z : Type*} {M : Finset ι} {p : ι → Z}

/-- Every element is hit. -/
theorem exists_mem (h : IsExactCover M p) (z : Z) : ∃ t ∈ M, p t = z := by
  obtain ⟨t, ⟨ht, hpt⟩, -⟩ := h z
  exact ⟨t, ht, hpt⟩

/-- No two members hit the same element. -/
theorem inj (h : IsExactCover M p) {t₁ t₂ : ι} (h₁ : t₁ ∈ M) (h₂ : t₂ ∈ M)
    (heq : p t₁ = p t₂) : t₁ = t₂ := by
  obtain ⟨t, -, huniq⟩ := h (p t₁)
  rw [huniq t₁ ⟨h₁, rfl⟩, huniq t₂ ⟨h₂, heq.symm⟩]

/-- The member hitting a given element is the only one: anything else in `M`
hitting it is equal to it. -/
theorem eq_of_mem (h : IsExactCover M p) {t₁ t₂ : ι} (h₁ : t₁ ∈ M) (h₂ : t₂ ∈ M)
    {z : Z} (hz₁ : p t₁ = z) (hz₂ : p t₂ = z) : t₁ = t₂ :=
  h.inj h₁ h₂ (hz₁.trans hz₂.symm)

/-- An exact cover is a bijection between the covering family and the covered
elements, so the two have equal cardinality. This is what pins `|M'| = q` for
a matching, and with it `|W| = |X| = |Y|` — a cardinality obstruction any
reduction *from* 3DM may branch on. -/
theorem card_eq [Fintype Z] (h : IsExactCover M p) : M.card = Fintype.card Z :=
  Finset.card_bij (fun t _ ↦ p t) (fun t _ ↦ Finset.mem_univ (p t))
    (fun t₁ h₁ t₂ h₂ heq ↦ h.inj h₁ h₂ heq)
    (fun z _ ↦ by
      obtain ⟨t, ht, hpt⟩ := h.exists_mem z
      exact ⟨t, ht, hpt⟩)

end IsExactCover

/-- Covering and disjointness, assembled: an exact cover is exactly a family
that hits every element and hits none of them twice. -/
theorem isExactCover_iff {ι Z : Type*} {M : Finset ι} {p : ι → Z} :
    IsExactCover M p ↔
      (∀ z : Z, ∃ t ∈ M, p t = z) ∧
        ∀ t₁ ∈ M, ∀ t₂ ∈ M, p t₁ = p t₂ → t₁ = t₂ := by
  constructor
  · exact fun h ↦ ⟨h.exists_mem, fun _ h₁ _ h₂ heq ↦ h.inj h₁ h₂ heq⟩
  · rintro ⟨hcov, hinj⟩ z
    obtain ⟨t, ht, hpt⟩ := hcov z
    exact ⟨t, ⟨ht, hpt⟩, fun u hu ↦ hinj u hu.1 t ht (hu.2.trans hpt.symm)⟩

/-- An instance of 3-DIMENSIONAL MATCHING: three finite element types with
decidable equality, and a set of triples over them. -/
structure Matching3DInstance : Type 1 where
  /-- The first coordinate's element set. -/
  W : Type
  [fintypeW : Fintype W]
  [decEqW : DecidableEq W]
  /-- The second coordinate's element set. -/
  X : Type
  [fintypeX : Fintype X]
  [decEqX : DecidableEq X]
  /-- The third coordinate's element set. -/
  Y : Type
  [fintypeY : Fintype Y]
  [decEqY : DecidableEq Y]
  /-- The available triples. -/
  triples : Finset (W × X × Y)

attribute [instance] Matching3DInstance.fintypeW Matching3DInstance.decEqW
attribute [instance] Matching3DInstance.fintypeX Matching3DInstance.decEqX
attribute [instance] Matching3DInstance.fintypeY Matching3DInstance.decEqY

/-- 3-DIMENSIONAL MATCHING: is there a sub-family of the available triples
using every element of every coordinate exactly once? -/
def MATCHING_3D : Problem Matching3DInstance := fun I ↦
  ∃ M ⊆ I.triples,
    IsExactCover M (fun t ↦ t.1) ∧
      IsExactCover M (fun t ↦ t.2.1) ∧ IsExactCover M (fun t ↦ t.2.2)

/-! ## Invariance under renaming

A 3-DIMENSIONAL MATCHING instance is only ever inspected through the
incidence between triples and elements, so renaming the three coordinate sets
along bijections changes nothing. This is the transport a *certificate* needs:
the mathematical layer names elements by tagged tuples (`Ext`, `Slot` in
`Matching3D/FromSat.lean`), while a concrete instance can only name them by
*positions* of an element list, and the passage between the two views is a
bijection on each coordinate — the 3DM analogue of `CNF.relabel` for SAT
gadgets. -/

/-- An exact cover transports along a bijection of the index type, provided
the coordinate map does too. Injectivity of `f` is not needed separately: it
comes with the equivalence, and it is `e`'s surjectivity that supplies a
witness above every element of the new coordinate set. -/
theorem IsExactCover.image {ι ι' Z Z' : Type*} [DecidableEq ι'] {M : Finset ι}
    {p : ι → Z} {p' : ι' → Z'} (f : ι ≃ ι') (e : Z ≃ Z')
    (hcomm : ∀ t, p' (f t) = e (p t)) (h : IsExactCover M p) :
    IsExactCover (M.image f) p' := by
  intro z'
  obtain ⟨t, ⟨htM, hpt⟩, huniq⟩ := h (e.symm z')
  refine ⟨f t, ⟨Finset.mem_image_of_mem _ htM, ?_⟩, ?_⟩
  · rw [hcomm, hpt, Equiv.apply_symm_apply]
  · rintro u ⟨hu, hpu⟩
    obtain ⟨t₀, ht₀M, rfl⟩ := Finset.mem_image.mp hu
    rw [hcomm] at hpu
    exact congrArg f (huniq t₀ ⟨ht₀M, by rw [← hpu, Equiv.symm_apply_apply]⟩)

/-- Renaming the three coordinate sets along bijections preserves
yes-instances. -/
theorem matching3D_of_equiv {I J : Matching3DInstance} (eW : I.W ≃ J.W)
    (eX : I.X ≃ J.X) (eY : I.Y ≃ J.Y)
    (h : ∀ t : I.W × I.X × I.Y, t ∈ I.triples →
      (eW t.1, eX t.2.1, eY t.2.2) ∈ J.triples) :
    MATCHING_3D I → MATCHING_3D J := by
  classical
  rintro ⟨M, hM, hW, hX, hY⟩
  refine ⟨M.image (eW.prodCongr (eX.prodCongr eY)), ?_,
    hW.image _ eW (fun _ ↦ rfl), hX.image _ eX (fun _ ↦ rfl),
    hY.image _ eY (fun _ ↦ rfl)⟩
  intro t ht
  obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
  exact h t₀ (hM ht₀)

/-- **Renaming invariance**: instances that agree up to bijections of the three
coordinate sets have the same answer. -/
theorem matching3D_iff_of_equiv {I J : Matching3DInstance} (eW : I.W ≃ J.W)
    (eX : I.X ≃ J.X) (eY : I.Y ≃ J.Y)
    (h : ∀ t : I.W × I.X × I.Y, t ∈ I.triples ↔
      (eW t.1, eX t.2.1, eY t.2.2) ∈ J.triples) :
    MATCHING_3D I ↔ MATCHING_3D J := by
  refine ⟨matching3D_of_equiv eW eX eY fun t ht ↦ (h t).mp ht,
    matching3D_of_equiv eW.symm eX.symm eY.symm fun t ht ↦ ?_⟩
  refine (h (eW.symm t.1, eX.symm t.2.1, eY.symm t.2.2)).mpr ?_
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Hardness


