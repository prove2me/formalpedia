-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f0d83ae5-527c-53c2-9244-3e54f9bd89e1

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective

set_option autoImplicit false

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ Opens Cover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "algebraOfHom cover structureSheafSections toH0 toH0_apply_coe U1 U0 sup_eq_top"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafCondition

variable (X : Scheme.{u}) (U V : X.Opens)

private abbrev _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition.eqLocus : Subring (Γ(X, U) × Γ(X, V)) :=
  RingHom.eqLocus
    ((X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp (RingHom.fst Γ(X, U) Γ(X, V)))
    ((X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp (RingHom.snd Γ(X, U) Γ(X, V)))

p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition" "eqLocus"
theorem mem_eqLocus_iff (s : Γ(X, U) × Γ(X, V)) :
    s ∈ eqLocus X U V ↔
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom s.1
        = (X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom s.2 :=
  Iff.rfl

def gammaEquiv (h : U ⊔ V = ⊤) : Γ(X, ⊤) ≃+* eqLocus X U V :=
  ((X.presheaf.mapIso (eqToIso h).op).trans (X.sheaf.objSupIsoProdEqLocus U V)).commRingCatIsoToRingEquiv

private theorem map_comp_apply {W₁ W₂ W₃ : X.Opens} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) (a : Γ(X, W₃)) :
    (X.presheaf.map f.op).hom ((X.presheaf.map g.op).hom a) = (X.presheaf.map (f ≫ g).op).hom a := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

theorem gammaEquiv_apply_fst (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.1 = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.1
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1
      = (X.presheaf.map (homOfLE le_sup_left).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_fst U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_left) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_left : U ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : U ≤ ⊤))]

theorem gammaEquiv_apply_snd (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.2 = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.2
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2
      = (X.presheaf.map (homOfLE le_sup_right).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_snd U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_right) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_right : V ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : V ≤ ⊤))]

end SheafCondition

open SheafCondition

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

theorem toH0_bijective' : letI := algebraOfHom c ⊤; Function.Bijective (𝒱.toH0 c) := by
  letI := algebraOfHom c ⊤
  have hpair : ∀ s : Γ(X, ⊤),
      ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1))
        = (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top s).1 := fun s => by
    rw [toH0_apply_coe]
    exact Prod.ext (gammaEquiv_apply_fst X _ _ _ s).symm (gammaEquiv_apply_snd X _ _ _ s).symm
  constructor
  · intro s s' hss'
    apply (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).injective
    apply Subtype.ext
    rw [← hpair, ← hpair, hss']
  · rintro ⟨p, hp⟩
    have hp' : p ∈ eqLocus X 𝒱.U0 𝒱.U1 :=
      (mem_eqLocus_iff X 𝒱.U0 𝒱.U1 p).mpr ((TwoChartCech.Cover.mem_H0_structureSheaf_iff _ p).mp hp)
    refine ⟨(gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).symm ⟨p, hp'⟩, Subtype.ext ?_⟩
    rw [hpair, RingEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem solution {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R)) :
    letI := AlgebraicGeometry.Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (𝒱.toH0 c) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective' 𝒱 c

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective (solution)
