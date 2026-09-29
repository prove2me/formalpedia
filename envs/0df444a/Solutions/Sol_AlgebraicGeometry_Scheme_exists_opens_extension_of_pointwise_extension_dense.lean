-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_opens_extension_of_pointwise_extension_dense
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a39c6dcc-affb-5214-9aef-1f65ce1aec06

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_lift_schemeTheoreticImage_of_isDomain
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_extension_of_mem_image_graph
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G H : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
    [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]

    (η : G) (hη : g.base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
    [IsDiscreteValuationRing (G.presheaf.stalk η)]

    (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hφK : φK ≫ pullback.snd h (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R K))))

    (D : Set G) (hD : ∀ z ∈ D, g.base z = IsLocalRing.closedPoint R) (hDη : η ∈ closure D)
    (hpts : ∀ z ∈ D, ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
        (c : Spec (CommRingCat.of A) ⟶ pullback g h),
        (c ≫ pullback.fst g h).base (IsLocalRing.closedPoint A) = z ∧
        c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
          (pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base) :
    ∃ (V : G.Opens) (v : (V : Scheme.{u}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧
      (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      η ∈ V ∧

      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆
          Set.range V.ι.base,
        IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
          φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by

  let graph := pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])
  have hgraph_fst : graph ≫ pullback.fst g h = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))) := pullback.lift_fst _ _ _
  haveI : QuasiCompact graph := by
    have : QuasiCompact (graph ≫ pullback.fst g h) := by rw [hgraph_fst]; infer_instance
    exact QuasiCompact.of_comp graph (pullback.fst g h)

  have hDπ : D ⊆ Set.range (graph.imageι ≫ pullback.fst g h).base := by
    intro z hz
    obtain ⟨A, _, _, _, c, hcz, hcgen⟩ := hpts z hz
    obtain ⟨v, hv⟩ := AlgebraicGeometry.Scheme.Hom.exists_lift_schemeTheoreticImage_of_isDomain graph c hcgen
    refine ⟨v.base (IsLocalRing.closedPoint A), ?_⟩
    rw [← hcz, ← hv, Scheme.Hom.comp_base, Scheme.Hom.comp_base, Scheme.Hom.comp_base]
    rfl

  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian g
  have hS : IsClosed {x : G | g.base x = IsLocalRing.closedPoint R} :=
    (IsLocalRing.isClosed_singleton_closedPoint (R := R)).preimage g.base.hom.continuous
  obtain ⟨γ, hγ⟩ := AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure
    (graph.imageι ≫ pullback.fst g h) {x : G | g.base x = IsLocalRing.closedPoint R} hS η hη
    (fun x hx => hirr x hx) D (fun z hz => hD z hz) hDη hDπ

  exact AlgebraicGeometry.Scheme.exists_opens_extension_of_mem_image_graph K g h η hη hirr φK hφK γ hγ

end S_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_pointwise_extension_dense (solution)
