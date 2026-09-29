-- Prove2me | solution 1 for AlgebraicGeometry.isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/39fa6c6d-504f-5dae-920d-fd5a9689db4e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ThickeningTransferBody

variable {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X}

theorem isClosedImmersion_of_isPullback [IsClosedImmersion i] (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) hg.flip inferInstance

theorem surjective_of_isPullback [Surjective i] (hg : IsPullback g f₀ f i) : Surjective g :=
  MorphismProperty.of_isPullback (P := @Surjective) hg.flip inferInstance

variable [IsClosedImmersion i] [Surjective i]

theorem universallyClosed_of_isPullback (hg : IsPullback g f₀ f i) [UniversallyClosed f₀] :
    UniversallyClosed f := by
  haveI : Surjective g := surjective_of_isPullback i hg
  haveI : UniversallyClosed (g ≫ f) := by rw [hg.w]; infer_instance
  exact UniversallyClosed.of_comp_surjective g f

theorem isSeparated_of_isPullback (hg : IsPullback g f₀ f i) [IsSeparated f₀] : IsSeparated f := by
  haveI : Surjective g := surjective_of_isPullback i hg
  haveI : IsClosedImmersion g := isClosedImmersion_of_isPullback i hg

  have e₁ : f₀ ≫ i = g ≫ f := hg.w.symm
  let k : pullback (f₀ ≫ i) (f₀ ≫ i) ⟶ pullback f f :=
    pullback.map (f₀ ≫ i) (f₀ ≫ i) f f g g (𝟙 S) ((Category.comp_id _).trans e₁) ((Category.comp_id _).trans e₁)
  have hk : IsClosedImmersion k :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹IsClosedImmersion g› ‹IsClosedImmersion g› e₁ e₁
  have hΔ₀ : IsClosedImmersion (pullback.diagonal (f₀ ≫ i)) := inferInstance
  have hcomp : g ≫ pullback.diagonal f = pullback.diagonal (f₀ ≫ i) ≫ k := by
    apply pullback.hom_ext
    · simp only [k, Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc, pullback.diagonal_fst]
      rfl
    · simp only [k, Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc, pullback.diagonal_snd]
      rfl
  have hclosedcomp : IsClosedImmersion (pullback.diagonal (f₀ ≫ i) ≫ k) := inferInstance
  have hrange : Set.range (pullback.diagonal f).base = Set.range (pullback.diagonal (f₀ ≫ i) ≫ k).base := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨y₀, rfl⟩ := g.surjective y
      refine ⟨y₀, ?_⟩
      change (pullback.diagonal (f₀ ≫ i) ≫ k) y₀ = (g ≫ pullback.diagonal f) y₀
      rw [hcomp]
    · rintro ⟨y₀, rfl⟩
      refine ⟨g.base y₀, ?_⟩
      change (g ≫ pullback.diagonal f) y₀ = (pullback.diagonal (f₀ ≫ i) ≫ k) y₀
      rw [hcomp]
  have hclosed : IsClosed (Set.range (pullback.diagonal f).base) := by
    rw [hrange]
    exact hclosedcomp.isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isProper_of_isPullback (hg : IsPullback g f₀ f i) [IsProper f₀] [LocallyOfFiniteType f] :
    IsProper f := by
  haveI := isSeparated_of_isPullback i hg
  haveI := universallyClosed_of_isPullback i hg
  exact (isProper_iff f).mpr ⟨‹_›, ‹_›, ‹_›⟩

end ThickeningTransferBody

theorem solution
    {S S₀ X X₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i] [Surjective i]
    {f : X ⟶ S} {f₀ : X₀ ⟶ S₀} {g : X₀ ⟶ X} (hg : IsPullback g f₀ f i) :
    IsClosedImmersion g ∧ Surjective g ∧ (IsSeparated f₀ → IsSeparated f) ∧
      (UniversallyClosed f₀ → UniversallyClosed f) ∧
      (IsProper f₀ → LocallyOfFiniteType f → IsProper f) :=
  ⟨ThickeningTransferBody.isClosedImmersion_of_isPullback i hg,
    ThickeningTransferBody.surjective_of_isPullback i hg,
    fun _ => ThickeningTransferBody.isSeparated_of_isPullback i hg,
    fun _ => ThickeningTransferBody.universallyClosed_of_isPullback i hg,
    fun _ _ => ThickeningTransferBody.isProper_of_isPullback i hg⟩

end S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_isClosedImmersion_and_surjective_and_isProper_of_isPullback_of_surjective (solution)
