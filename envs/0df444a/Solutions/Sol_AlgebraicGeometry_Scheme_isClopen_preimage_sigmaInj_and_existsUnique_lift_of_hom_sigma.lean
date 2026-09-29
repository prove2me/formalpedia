-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dc1bf92a-0128-5dd9-a37f-d61e1ca92e54

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace CoprodPtsA

variable {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H)

theorem range_sigmaι_eq (i : σ) :
    Set.range (Sigma.ι H i).base = sigmaMk H '' Set.range (Sigma.mk i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨i, x⟩, ⟨x, rfl⟩, sigmaMk_mk H i x⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (sigmaMk_mk H i x).symm⟩

theorem isClosed_opensRange (i : σ) : IsClosed ((Sigma.ι H i).opensRange : Set ↥(∐ H)) := by
  rw [Scheme.Hom.coe_opensRange, range_sigmaι_eq]
  exact (sigmaMk H).isClosed_image.mpr isClosed_range_sigmaMk

private theorem _root_.CoprodPtsA.iSup_opensRange : (⨆ i, (Sigma.ι H i).opensRange) = ⊤ := by
  have h := (sigmaOpenCover H).iSup_opensRange
  simp only [sigmaOpenCover_f] at h
  exact h

p2m_export "CoprodPtsA" "iSup_opensRange"
theorem closed (i : σ) : IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) :=
  (isClosed_opensRange H i).preimage u.continuous

theorem disjoint (i j : σ) (hij : i ≠ j) :
    Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange) :=
  Opens.coe_disjoint.mp ((Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι H i j hij)).preimage u.base)

theorem cover : (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_opensRange, Scheme.Hom.preimage_top]

theorem range_subset (i : σ) :
    Set.range ((u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u).base ⊆ Set.range (Sigma.ι H i).base := by
  rintro _ ⟨x, rfl⟩
  have hx : (x.1 : T) ∈ (u ⁻¹ᵁ (Sigma.ι H i).opensRange : Set T) := x.2
  have hx' : u.base x.1 ∈ Set.range (Sigma.ι H i).base := by
    rw [← Scheme.Hom.coe_opensRange]; exact hx
  simpa using hx'

private theorem _root_.CoprodPtsA.lift (i : σ) : ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u := by
  refine ⟨IsOpenImmersion.lift (Sigma.ι H i) _ (range_subset H u i), IsOpenImmersion.lift_fac _ _ _, fun v hv => ?_⟩
  rw [← cancel_mono (Sigma.ι H i), hv, IsOpenImmersion.lift_fac]

p2m_export "CoprodPtsA" "lift"
theorem finite [CompactSpace T] :
    {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) (fun i => (u ⁻¹ᵁ _).isOpen)
    (by
      intro x _
      have hx : x ∈ ((⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) := by rw [cover]; trivial
      simpa [Opens.coe_iSup] using hx)
  refine t.finite_toSet.subset ?_
  rintro j ⟨x, hx⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) := by
    simpa using ht (Set.mem_univ x)
  by_cases hij : i = j
  · exact hij ▸ hi
  · exact ((Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (disjoint H u i j hij))) ⟨hxi, hx⟩).elim

end CoprodPtsA

theorem solution
    {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    (∀ i, IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) ∧
    (∀ i j, i ≠ j → Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange)) ∧
    (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ ∧
    (∀ i, ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u) ∧
    (CompactSpace T → {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite) :=
  ⟨CoprodPtsA.closed H u, CoprodPtsA.disjoint H u, CoprodPtsA.cover H u, CoprodPtsA.lift H u,
    fun _ => CoprodPtsA.finite H u⟩

end S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma (solution)
