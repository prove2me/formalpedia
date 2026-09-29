-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f57f87b8-d5cd-5d1d-aeca-c8b9419cd3d1

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (V : X.Opens) (x : X) (hx : f.base x = IsLocalRing.closedPoint R) (hxV : x ∈ V) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : HenselianLocalRing R')
      (a : Spec (CommRingCat.of R') ⟶ X),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ∧
      a.base (IsLocalRing.closedPoint R') ∈ V := by
  classical

  let k : Type u := IsLocalRing.ResidueField R
  let ρ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let j : pullback f ρ ⟶ X := pullback.fst f ρ
  let fk : pullback f ρ ⟶ Spec (CommRingCat.of k) := pullback.snd f ρ
  haveI : Smooth fk := inferInstance

  have hρ : ρ.base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    show PrimeSpectrum.comap (IsLocalRing.residue R) _ = _
    exact IsLocalRing.PrimeSpectrum.comap_residue R _
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ρ) x (IsLocalRing.closedPoint k)
    (hx.trans hρ.symm)

  let O : (pullback f ρ).Opens := j ⁻¹ᵁ V
  have hzO : z ∈ O := show j.base z ∈ V by rw [hz]; exact hxV
  haveI : Nonempty (O : Scheme.{u}) := ⟨⟨z, hzO⟩⟩
  haveI : Smooth (O.ι ≫ fk) := inferInstance

  obtain ⟨k', instF, instA, instFin, instSep, P, hP⟩ :=
    AlgebraicGeometry.exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty k (O.ι ≫ fk)

  let x₁ : Spec (CommRingCat.of k') ⟶ pullback f ρ := P ≫ O.ι
  have hx₁ : x₁ ≫ fk = Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
    show (P ≫ O.ι) ≫ fk = _
    rw [Category.assoc, hP]
  let x₀ : Spec (CommRingCat.of k') ⟶ X := x₁ ≫ j
  have hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R) k').comp (IsLocalRing.residue R))) := by
    show (x₁ ≫ pullback.fst f ρ) ≫ f = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

  obtain ⟨R', instCR, instDom, instDVR, instAlg, instFinR, instEt, instFF, instLoc, instHens, φ, s, hmap, hs, hcl⟩ :=
    AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_of_isSeparable_of_henselianLocalRing
      f k' x₀ hx₀
  refine ⟨R', instCR, instDom, instDVR, instAlg, instFinR, instEt, instFF, instLoc, instHens, s, hmap, hs, ?_⟩

  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap R' (IsLocalRing.ResidueField R')))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R')) = IsLocalRing.closedPoint R' := by
    show PrimeSpectrum.comap (algebraMap R' (IsLocalRing.ResidueField R')) _ = _
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.PrimeSpectrum.comap_residue R' _
  have h2 : s.base (IsLocalRing.closedPoint R') =
      x₀.base ((Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom)).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R'))) := by
    rw [← h1, ← Scheme.Hom.comp_apply, hcl, Scheme.Hom.comp_apply]
  rw [h2]

  set pt := (Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom)).base
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField R')) with hpt
  have hO : x₁.base pt ∈ O := by
    show (P ≫ O.ι).base pt ∈ (O : Set ↥(pullback f ρ))
    rw [← Scheme.Opens.range_ι O, Scheme.Hom.comp_base]
    exact ⟨_, rfl⟩
  show (x₁ ≫ j).base pt ∈ V
  rw [Scheme.Hom.comp_apply]
  exact hO

end S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing (solution)
