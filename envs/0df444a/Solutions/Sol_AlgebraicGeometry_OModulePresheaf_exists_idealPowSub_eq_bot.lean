-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/964fbdff-a2bb-522d-936b-1e9bc8017d4c

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.preimage_basicOpen Spec Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal Scheme.basicOpen_zero IsLocallyNoetherian.component_noetherian IsNoetherian Scheme.IdealSheafData OModulePresheaf.idealPowSub OModulePresheaf OModulePresheaf.IsCoherent OModulePresheaf.IsQuasicoherent OModulePresheaf.SupportedIn Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "idealSections idealSections_eq_ideal idealPowSub IsCoherent IsQuasicoherent SupportedIn isScalarTower obj"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

theorem support_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

section Terminates

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem basicOpen_disjoint_of_mem_vanishingIdeal (Y : Closeds V)
    (U : V.affineOpens) (f : Γ(V, U.1))
    (hf : f ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U) :
    ((V.basicOpen f : V.Opens) : Set V) ∩ Y = ∅ := by
  set iY := (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι
  have hpre : iY ⁻¹ᵁ V.basicOpen f = ⊥ := by
    rw [Scheme.preimage_basicOpen,
      show (iY.app U.1).hom f = 0 from
        (idealSections_eq_ideal (Scheme.IdealSheafData.vanishingIdeal Y) U ▸ hf :
          f ∈ idealSections (Scheme.IdealSheafData.vanishingIdeal Y) U.1),
      Scheme.basicOpen_zero]
  have hrange : Set.range iY.base = (Y : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (congrArg SetLike.coe (support_vanishingIdeal Y))
  refine Set.eq_empty_of_forall_notMem fun x ⟨hxD, hxY⟩ => ?_
  obtain ⟨z, rfl⟩ := hrange ▸ hxY
  exact (congrArg (z ∈ ·) (congrArg SetLike.coe hpre)).mp hxD

theorem exists_idealPowSub_eq_bot [IsLocallyNoetherian V] (Y : Closeds V)
    (F : OModulePresheaf π) (hFc : OModulePresheaf.IsCoherent F)
    (hFq : OModulePresheaf.IsQuasicoherent F) (hFs : OModulePresheaf.SupportedIn F Y)
    (U : V.affineOpens) :
    ∃ N, idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  set ann : Ideal Γ(V, U.1) := Module.annihilator Γ(V, U.1) (F.obj U.1)

  have hrad : I.ideal U ≤ ann.radical := fun f hf => by
    have hDdisj := basicOpen_disjoint_of_mem_vanishingIdeal Y U f hf
    haveI := hFs ⟨V.basicOpen f, U.2.basicOpen f⟩ hDdisj
    have hann : ∀ y : F.obj U.1, ∃ n, (f ^ n : Γ(V, U.1)) • y = 0 :=
      fun y => (hFq U f).2 y (Subsingleton.elim _ _)
    obtain ⟨s, hs⟩ := Module.finite_def.mp (hFc U)
    choose ny hny using fun y : s => hann y
    refine ⟨s.attach.sup ny, Module.mem_annihilator.mpr fun y => ?_⟩
    have hy : y ∈ Submodule.span Γ(V, U.1) s := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      have hle : ny ⟨z, hz⟩ ≤ s.attach.sup ny := Finset.le_sup (Finset.mem_attach s ⟨z, hz⟩)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hny ⟨z, hz⟩, smul_zero]
    · exact smul_zero _
    · exact fun _ _ _ _ ha hb => by rw [smul_add, ha, hb, add_zero]
    · exact fun c z _ hz => by rw [smul_comm, hz, smul_zero]

  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, le_bot_iff.mp fun x hx => ?_⟩
  rw [idealPowSub, Submodule.restrictScalars_mem,
    idealSections_eq_ideal] at hx
  exact Submodule.smul_induction_on hx
    (fun a ha z _ => (Module.mem_annihilator.mp (hN ha) z) ▸ Submodule.zero_mem _)
    (fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂)

end Terminates

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (U : V.affineOpens) : ∃ N : ℕ, OModulePresheaf.idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ :=
  AlgebraicGeometry.OModulePresheaf.G4T.exists_idealPowSub_eq_bot π Y F hFc hFq hFs U

end S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot (solution)
