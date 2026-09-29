-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/bd0d4ea7-98bf-5d97-9dff-d8c8229eaf4b

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback mk Modules Opens TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap pullback mk sectionsOf exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial"
namespace H1Fibre
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

open TensorProduct

theorem subsingleton_of_forall_maximal {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], Subsingleton ((A ⧸ m) ⊗[A] M)) : Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  have hann : Module.annihilator A M ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ Module.annihilator A M := htop ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (by simpa using Module.mem_annihilator.mp h1 x)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
  have htop : (⊤ : Submodule A M) ≤ m • ⊤ := by
    intro x _
    haveI : Subsingleton (M ⧸ (m • ⊤ : Submodule A M)) :=
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.toEquiv.subsingleton
    have hx : Submodule.Quotient.mk x = (0 : M ⧸ (m • ⊤ : Submodule A M)) := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (⊤ : Submodule A M) Module.Finite.fg_top htop
  have hrann : r ∈ Module.annihilator A M := Module.mem_annihilator.mpr fun x => hr x Submodule.mem_top
  have h1 : (1 : A) ∈ m := by
    have := m.sub_mem (hle hrann) hr1
    rwa [sub_sub_cancel] at this
  exact hm.ne_top (m.eq_top_of_isUnit_mem h1 isUnit_one)

theorem main {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    Subsingleton (𝒱.sectionsOf π F).H1 := by
  haveI := hfin
  refine subsingleton_of_forall_maximal (A := A) _ fun m _ => ?_
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  obtain ⟨⟨e⟩, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 π F htriv (A ⧸ m)
  haveI := hfib (A ⧸ m)
  exact e.symm.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1Fibre

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    Subsingleton (𝒱.sectionsOf π F).H1 :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1Fibre.main π 𝒱 F htriv hfin hfib

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field (solution)
