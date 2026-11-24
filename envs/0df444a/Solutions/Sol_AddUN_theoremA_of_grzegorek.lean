-- Prove2me | solution 1 for AddUN.theoremA_of_grzegorek
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:59.774747+00:00
-- url     : https://prove2.me/submissions/5b590b56-6f0b-49de-b6d1-4b762c92426a

module
public import Definitions.Def_AddUN_Grzegorek
public import Definitions.Def_AddUN_ZeroOne
public import Definitions.Def_AddUN_TheoremA
public import Theorems.Thm_AddUN_exists_levels
public import Theorems.Thm_AddUN_le_spread
public import Theorems.Thm_AddUN_overwrite_spread_apply
public import Theorems.Thm_AddUN_overwrite_of_notMem_range
public import Theorems.Thm_AddUN_aleph0_lt_add_universallyNull
public import Theorems.Thm_AddUN_univ_notMem_null
public import Theorems.Thm_AddUN_universallyNull_subset_null
public import Theorems.Thm_IdealInvariant_add_le
public import Theorems.Thm_IdealInvariant_exists_notMem_mk_eq_non
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_IsUniversallyNull_of_injOn
public import Theorems.Thm_MeasureTheory_exists_flipSet_mem
public import Theorems.Thm_MeasureTheory_exists_isCompact_disjoint_of_null
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_length_revPrefix
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip
attribute [local simp] MeasureTheory.length_revPrefix



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open AddUN
variable {U : Set (ℕ → Bool)}
namespace AddUN
theorem _root_.solution (hG : Grzegorek) : TheoremA := by
  obtain ⟨P, hP, hPcard⟩ := hG
  obtain ⟨X, hX, hXcard⟩ := exists_notMem_mk_eq_non (I := 𝒩) ⟨univ, univ_notMem_null⟩
  have hXpos : cantorMeasure X ≠ 0 := hX
  obtain ⟨e⟩ : Nonempty (X ≃ P) := Cardinal.eq.1 (hXcard.trans hPcard.symm)
  -- A dominating family of cardinality `𝔡`.
  have hne : Nonempty {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g} :=
    ⟨⟨univ, fun f ↦ ⟨f, mem_univ f, EventuallyLE.refl _ _⟩⟩⟩
  obtain ⟨⟨D, hD⟩, hDcard⟩ :=
    ciInf_mem fun D : {D : Set (ℕ → ℕ) // ∀ f, ∃ g ∈ D, f ≤ᶠ[atTop] g} ↦ #D.1
  let W : D × ℕ × Finset ℕ → Set (ℕ → Bool) := fun π ↦
    range fun x : X ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
  -- Each set is universally null: reading the code is injective on it.
  have hW : ∀ π, IsUniversallyNull (W π) := fun π ↦ by
    have hread : ∀ x : X, (fun n ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
        (spread π.1 π.2.1 n)) = e x := fun x ↦ funext fun n ↦ overwrite_spread_apply _ _ _ _ n
    refine hP.of_injOn (φ := fun w n ↦ w (spread π.1 π.2.1 n))
      (measurable_pi_lambda _ fun n ↦ measurable_pi_apply _) ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ heq
      have hee : (e x : ℕ → Bool) = e x' := by
        rw [← hread x, ← hread x']
        exact heq
      rw [e.injective (Subtype.ext hee)]
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change (fun n ↦ overwrite (spread π.1 π.2.1) (e x) (flipSet π.2.2 x)
        (spread π.1 π.2.1 n)) ∈ P
      rw [hread x]
      exact (e x).2
  -- The union is not null.
  have hUnion : ⋃₀ range W ∉ 𝒰𝒩 := by
    intro hUN
    obtain ⟨K, hK, hKpos, hKdisj⟩ :=
      exists_isCompact_disjoint_of_null (universallyNull_subset_null hUN)
    obtain ⟨M, hMmono, hM⟩ := exists_levels hK hKpos
    obtain ⟨g, hgD, hg⟩ := hD M
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hg
    obtain ⟨Good, hGm, hGpos, hGood⟩ := hM (spread g k₀) fun k ↦
      ((hMmono (Nat.le_add_right k k₀)).trans (hk₀ _ (Nat.le_add_left _ _))).trans
        (le_spread g k₀ k)
    obtain ⟨x, hx, s, hs⟩ := exists_flipSet_mem hXpos hGm hGpos
    have hmem : overwrite (spread g k₀) (e ⟨x, hx⟩) (flipSet s x) ∈ K :=
      hGood _ hs _ fun i hi ↦ overwrite_of_notMem_range _ _ hi
    exact disjoint_left.1 hKdisj hmem
      ⟨W (⟨g, hgD⟩, k₀, s), mem_range_self _, ⟨⟨x, hx⟩, rfl⟩⟩
  -- There are `𝔡` sets.
  have h1 : add 𝒰𝒩 ≤ #D * ℵ₀ := by
    refine ((add_le (by rintro _ ⟨π, rfl⟩; exact hW π) hUnion).trans mk_range_le).trans ?_
    simp [mk_eq_aleph0]
  have h3 : ℵ₀ ≤ #D := by
    by_contra hlt
    have h4 : #D * ℵ₀ ≤ ℵ₀ :=
      (mul_le_mul_left (not_le.1 hlt).le ℵ₀).trans aleph0_mul_aleph0.le
    exact (aleph0_lt_add_universallyNull.trans_le (h1.trans h4)).false
  rw [mul_aleph0_eq h3] at h1
  exact h1.trans hDcard.le
end AddUN
