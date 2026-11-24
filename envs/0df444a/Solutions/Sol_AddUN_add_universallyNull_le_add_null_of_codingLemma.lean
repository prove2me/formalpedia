-- Prove2me | solution 1 for AddUN.add_universallyNull_le_add_null_of_codingLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:37.310604+00:00
-- url     : https://prove2.me/submissions/85112481-d8d5-4cd1-90fc-cf5964875c83

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_TheoremB
public import Theorems.Thm_AddUN_exists_unlocalised_family
public import Theorems.Thm_AddUN_universallyNull_subset_null
public import Theorems.Thm_IdealInvariant_add_le
public import Theorems.Thm_IdealInvariant_exists_cofinal_mk_eq_cof
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn
public import Theorems.Thm_MeasureTheory_exists_isCompact_disjoint_of_null


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Cardinal MeasureTheory IdealInvariant
open AddUN
namespace AddUN
theorem _root_.solution (hC : CodingLemma)
    (A : Set (ℕ → Bool)) (hA : IsUniversallyNull A) (hcard : #A = cof 𝒩) :
    add 𝒰𝒩 ≤ add 𝒩 := by
  obtain ⟨h, φ, hφ, hcode⟩ := hC
  obtain ⟨F, hF, hloc⟩ := exists_unlocalised_family h
  obtain ⟨𝒞, h𝒞, hcof, h𝒞card⟩ := exists_cofinal_mk_eq_cof 𝒩
  obtain ⟨e⟩ : Nonempty (𝒞 ≃ A) := Cardinal.eq.1 (h𝒞card.trans hcard.symm)
  -- For each `G ∈ 𝒞` choose `f G ∈ F` and a point `w G ∉ G` that `φ (f G)` sends to `e G`.
  have key : ∀ G : 𝒞, ∃ f ∈ F, ∃ w : ℕ → Bool, w ∉ G.1 ∧ φ f w = e G := fun G ↦ by
    obtain ⟨K, hK, hKpos, hKG⟩ := exists_isCompact_disjoint_of_null (h𝒞 G.2)
    obtain ⟨S, hS, hSf⟩ := hcode K hK hKpos (e G)
    obtain ⟨f, hfF, hf⟩ := hloc S hS
    obtain ⟨w, hwK, hw⟩ := hSf f hf
    exact ⟨f, hfF, w, fun hwG ↦ disjoint_left.1 hKG hwK hwG, hw⟩
  choose f hfF w hwG hw using key
  -- The points chosen for a fixed `g ∈ F` form a universally null set.
  let Xf : (ℕ → ℕ) → Set (ℕ → Bool) := fun g ↦ {x | ∃ G : 𝒞, f G = g ∧ w G = x}
  have hX : ∀ g, IsUniversallyNull (Xf g) := fun g ↦ by
    refine hA.of_injOn (hφ g) ?_ ?_
    · rintro _ ⟨G, rfl, rfl⟩ _ ⟨G', hG', rfl⟩ heq
      have hee : (e G : ℕ → Bool) = e G' := by
        rw [← hw G, ← hw G', hG']
        exact heq
      rw [e.injective (Subtype.ext hee)]
    · rintro _ ⟨_, ⟨G, rfl, rfl⟩, rfl⟩
      rw [hw G]
      exact (e G).2
  -- Their union is not null, because it meets the complement of every member of `𝒞`.
  refine (add_le (I := 𝒰𝒩) (𝒜 := Xf '' F) ?_ fun hUN ↦ ?_).trans (mk_image_le.trans hF)
  · rintro _ ⟨g, -, rfl⟩
    exact hX g
  · obtain ⟨G, hG, hsub⟩ := hcof _ (universallyNull_subset_null hUN)
    exact hwG ⟨G, hG⟩ (hsub ⟨Xf (f ⟨G, hG⟩), ⟨_, hfF _, rfl⟩, ⟨G, hG⟩, rfl, rfl⟩)
end AddUN
