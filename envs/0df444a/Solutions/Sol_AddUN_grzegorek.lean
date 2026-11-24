-- Prove2me | solution 1 for AddUN.grzegorek
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:46:47.791458+00:00
-- url     : https://prove2.me/submissions/02bd84ce-5a52-4d38-95c9-30a8f8978c97

module
public import Definitions.Def_AddUN_Localisation
public import Definitions.Def_AddUN_Transfer
public import Definitions.Def_AddUN_Uniformity
public import Mathlib.MeasureTheory.Measure.Prod
public import Definitions.Def_AddUN_Grzegorek
public import Theorems.Thm_AddUN_isUniversallyNull_of_mk_lt_non_of_injective
public import Theorems.Thm_AddUN_measurableSet_universalNull
public import Theorems.Thm_AddUN_measure_section_universalNull
public import Theorems.Thm_AddUN_exists_code_of_null
public import Theorems.Thm_AddUN_aleph0_lt_add_null
public import Theorems.Thm_AddUN_univ_notMem_null
public import Theorems.Thm_IdealInvariant_add_le_non
public import Theorems.Thm_IdealInvariant_exists_notMem_mk_eq_non
public import Theorems.Thm_IdealInvariant_mem_of_lt_non
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_length_revPrefix
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip
attribute [local simp] MeasureTheory.length_revPrefix



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
namespace AddUN
theorem _root_.solution : Grzegorek := by
  -- A set that is not null, of cardinality `non 𝒩`, with a well-order of the least order type.
  obtain ⟨X, hX, hXcard⟩ := exists_notMem_mk_eq_non (I := 𝒩) ⟨univ, univ_notMem_null⟩
  have hXpos : cantorMeasure X ≠ 0 := hX
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq X
  have haleph : ℵ₀ ≤ non 𝒩 := aleph0_lt_add_null.le.trans
    (add_le_non (fun x ↦ measure_singleton x) ⟨univ, univ_notMem_null⟩)
  have hinit : ∀ a : X, #{b : X | r b a} < non 𝒩 := fun a ↦ by
    have h := Cardinal.card_typein_lt (r := r) a hr
    rwa [Ordinal.card_typein, hXcard] at h
  -- A code for a null set that contains the initial segment below `a`.
  have hI : ∀ a : X, cantorMeasure (Subtype.val '' {b : X | r b a}) = 0 := fun a ↦
    mem_of_lt_non (mk_image_le.trans_lt (hinit a))
  choose c hc using fun a : X ↦ exists_code_of_null (hI a)
  let y : X → (ℕ → Bool) × (ℕ → ℕ) := fun a ↦ (a, c a)
  have hy : Function.Injective y := fun a b hab ↦ Subtype.ext (congrArg Prod.fst hab)
  have hunc : ¬ Countable (ℕ → Bool) := fun h ↦ by
    have h0 := (Set.countable_univ (α := ℕ → Bool)).measure_zero cantorMeasure
    simp at h0
  have hunc' : ¬ Countable ((ℕ → Bool) × (ℕ → ℕ)) := fun h ↦
    hunc ((Prod.mk_left_injective (fun _ ↦ 0 : ℕ → ℕ)).countable)
  let e : (ℕ → Bool) × (ℕ → ℕ) ≃ᵐ (ℕ → Bool) :=
    PolishSpace.measurableEquivOfNotCountable hunc' hunc
  -- The set of the pairs `(a, c a)` is universally null.
  have hY : IsUniversallyNull (range y) := by
    intro μ _ _
    let U' : Set ((ℕ → Bool) × ((ℕ → Bool) × (ℕ → ℕ))) :=
      (fun q ↦ (q.1, q.2.2)) ⁻¹' universalNull
    have hU' : MeasurableSet U' :=
      measurableSet_universalNull.preimage
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have hprod : (cantorMeasure.prod μ) U' = 0 := by
      rw [Measure.prod_apply_symm hU']
      have hsec : ∀ p : (ℕ → Bool) × (ℕ → ℕ), cantorMeasure ((fun x ↦ (x, p)) ⁻¹' U') = 0 :=
        fun p ↦ measure_section_universalNull p.2
      simp [hsec]
    have hae := (Measure.measure_prod_null hU').1 hprod
    obtain ⟨a, ha⟩ : ∃ a : X, μ (Prod.mk (a : ℕ → Bool) ⁻¹' U') = 0 := by
      by_contra hno
      exact hXpos (measure_mono_null
        (show X ⊆ {x | ¬ (fun x ↦ μ (Prod.mk x ⁻¹' U')) x = (0 : (ℕ → Bool) → ℝ≥0∞) x} from
          fun x hx h0 ↦ hno ⟨⟨x, hx⟩, h0⟩) (ae_iff.1 hae))
    have hsmall : IsUniversallyNull (y '' {b : X | ¬ r a b}) := by
      refine isUniversallyNull_of_mk_lt_non_of_injective e.measurable e.injective
        (mk_image_le.trans_lt ?_)
      have hsub : {b : X | ¬ r a b} ⊆ {b | r b a} ∪ {a} := fun b hb ↦ by
        rcases trichotomous_of r a b with h | h | h
        · exact absurd h hb
        · exact Or.inr h.symm
        · exact Or.inl h
      calc #{b : X | ¬ r a b} ≤ #({b | r b a} ∪ {a} : Set X) := mk_le_mk_of_subset hsub
        _ ≤ #{b : X | r b a} + #({a} : Set X) := mk_union_le _ _
        _ < non 𝒩 := Cardinal.add_lt_of_lt haleph (hinit a)
            (by simpa using one_lt_aleph0.trans_le haleph)
    refine measure_mono_null (t := Prod.mk (a : ℕ → Bool) ⁻¹' U' ∪ y '' {b : X | ¬ r a b}) ?_
      (measure_union_null ha (hsmall μ))
    rintro _ ⟨b, rfl⟩
    by_cases hab : r a b
    · exact Or.inl (hc b a ⟨a, hab, rfl⟩)
    · exact Or.inr ⟨b, hab, rfl⟩
  -- Move the set into the Cantor space.
  refine ⟨e '' range y, hY.of_injOn e.symm.measurable e.symm.injective.injOn ?_, ?_⟩
  · rw [← image_comp]
    simp
  · rw [mk_image_eq e.injective, mk_range_eq y hy, hXcard]
end AddUN
