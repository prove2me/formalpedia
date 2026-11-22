-- Prove2me | Definitions.Def_AlgebraicGeometry_SchematicImageLimitIdeal
-- name    : AlgebraicGeometry_SchematicImageLimitIdeal
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T07:13:18.499077+00:00
-- url     : https://prove2.me/theorems/a43e1716-662d-4798-bebb-c65859d1ac5f
-- title:
--   Kernel ideal in an affine-transition limit
-- statement:
--   The kernel ideal of a map into the limit is the sum of the pulled-back schematic image ideals.

import Mathlib.AlgebraicGeometry.AffineTransitionLimit

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.IdealSheafData

namespace PhilipponImageLimitIdeal

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} {c : Cone D}
    [∀ {j k : I} (v : j ⟶ k), IsAffineHom (D.map v)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]

private theorem exists_section_at_stage (hc : IsLimit c) (U : c.pt.Opens) (hU : IsAffineOpen U)
    (x : Γ(c.pt, U)) : ∃ (j : I) (V : (D.obj j).Opens) (_ : IsAffineOpen V)
      (e : U = c.π.app j ⁻¹ᵁ V) (t : Γ(D.obj j, V)), (c.π.app j).appLE V U e.le t = x := by
  obtain ⟨i, V₀, hV₀, rfl⟩ := exists_isAffineOpen_preimage_eq D c hc U hU
  let U := c.π.app i ⁻¹ᵁ V₀
  let : ∀ j, IsAffine ((opensDiagram D i V₀).obj j) := fun j => hV₀.preimage (D.map j.hom)
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit (opensDiagram D i V₀)
    (opensCone D c i V₀) (isLimitOpensCone D c hc i V₀) (U.topIso.inv x)
  let V := D.map j.hom ⁻¹ᵁ V₀
  have he : U = c.π.app j.left ⁻¹ᵁ V := by
    change c.π.app i ⁻¹ᵁ V₀ = c.π.app j.left ⁻¹ᵁ D.map j.hom ⁻¹ᵁ V₀
    rw [← Scheme.Hom.comp_preimage, c.w]
  refine ⟨j.left, V, hV₀.preimage (D.map j.hom), he, V.topIso.hom t, ?_⟩
  let e := arrowResLEAppIso (c.π.app j.left) V U he.le
  have hApp : ((opensCone D c i V₀).π.app j).appTop ≫ U.topIso.hom =
      V.topIso.hom ≫ (c.π.app j.left).appLE V U he.le := e.hom.w.symm
  calc
    _ = U.topIso.hom (((opensCone D c i V₀).π.app j).appTop t) :=
      (ConcreteCategory.congr_hom hApp t).symm
    _ = U.topIso.hom (U.topIso.inv x) := congrArg U.topIso.hom ht
    _ = x := ConcreteCategory.congr_hom U.topIso.inv_hom_id x

private theorem ker_mem_of_appLE {X Y Z : Scheme.{u}} (a : X ⟶ Y) (p : Y ⟶ Z)
    {U : Y.Opens} {V : Z.Opens} (e : U = p ⁻¹ᵁ V) (t : Γ(Z, V))
    (h : (a.app U).hom ((p.appLE V U e.le).hom t) = 0) :
    t ∈ RingHom.ker ((a ≫ p).app V).hom := by
  have e' : a ⁻¹ᵁ U = (a ≫ p) ⁻¹ᵁ V := by rw [Scheme.Hom.comp_preimage, e]
  have hz : ((a ≫ p).appLE V (a ⁻¹ᵁ U) e'.le).hom t = 0 := by
    have hComp := Scheme.Hom.appLE_comp_appLE a p V U (a ⁻¹ᵁ U) e.le le_rfl
    rw [← hComp, ← Scheme.Hom.app_eq_appLE]
    exact h
  change ((a ≫ p).app V).hom t = 0
  have hm : homOfLE e'.le = eqToHom e' := Subsingleton.elim _ _
  rw [Scheme.Hom.appLE, hm] at hz
  let r := X.presheaf.map (eqToHom e').op
  apply (ConcreteCategory.bijective_of_isIso r).1
  exact hz.trans (map_zero r.hom).symm

/-- The kernel of a quasi-compact map into an affine-transition limit is the sum
of the pullbacks of the kernels of its maps into the stages. -/
theorem iSup_kernels_eq (hc : IsLimit c) {X : Scheme.{u}} (a : X ⟶ c.pt) [QuasiCompact a] :
    (⨆ i, (a ≫ c.π.app i).ker.comap (c.π.app i)) = a.ker := by
  let : ∀ j, IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc
  let K := fun i => (a ≫ c.π.app i).ker
  let L := ⨆ i, (K i).comap (c.π.app i)
  change L = a.ker
  apply le_antisymm
  · refine iSup_le fun i => le_map_iff_comap_le.mp ?_
    rw [← Scheme.Hom.ker_comp]
  · apply le_def.mpr
    intro U x hx
    have hx0 : (a.app U).hom x = 0 := by
      rw [Scheme.Hom.ker_apply] at hx
      exact hx
    obtain ⟨j, V, hV, he, t, ht⟩ := exists_section_at_stage hc U U.2 x
    let p := c.π.app j
    have hv : t ∈ (K j).ideal ⟨V, hV⟩ := by
      change t ∈ (a ≫ p).ker.ideal ⟨V, hV⟩
      rw [Scheme.Hom.ker_apply]
      exact ker_mem_of_appLE a p he t (by rw [← ht] at hx0; exact hx0)
    have hle : K j ≤ L.map p := le_map_iff_comap_le.mpr (le_iSup (fun i => (K i).comap (c.π.app i)) j)
    have hmem := hle ⟨V, hV⟩ hv
    have hAff : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
    rw [ideal_map L p ⟨V, hV⟩ hAff] at hmem
    have hres := L.ideal_le_comap_ideal (U := U) (V := ⟨_, hAff⟩) he.le hmem
    rw [← ht]
    exact hres

end PhilipponImageLimitIdeal

end

end


