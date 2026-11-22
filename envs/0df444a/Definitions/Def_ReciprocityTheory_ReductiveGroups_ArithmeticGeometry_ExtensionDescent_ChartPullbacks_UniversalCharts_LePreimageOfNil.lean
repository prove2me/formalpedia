-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:10.470078+00:00
-- url     : https://prove2.me/theorems/ac23ccc6-2a66-41e0-a6f6-644042cd1ded
-- title:
--   Le Preimage Of Nil
-- statement:
--   Definitions and structural lemmas for Le Preimage Of Nil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R₀ : Type} [CommRing R₀]
abbrev sp (P : Type) [CommRing P] [Algebra R₀ P] : Over (Spec (CommRingCat.of R₀)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R₀ P)))
def spMap {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    sp (R₀ := R₀) P' ⟶ sp P :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact g.comp_algebraMap)
section Chart
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
structure Chart where
  U : G.left.Opens
  hU : IsAffineOpen U
  he : ⊤ ≤ (η[G]).left ⁻¹ᵁ U
variable {G}
def alg0 (C : Chart G) : R₀ →+* Γ(G.left, C.U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ G.hom.appLE ⊤ C.U le_top).hom
instance (C : Chart G) : Algebra R₀ Γ(G.left, C.U) := (alg0 C).toAlgebra
theorem fromSpec_over (C : Chart G) :
    C.hU.fromSpec ≫ G.hom = Spec.map (CommRingCat.ofHom (alg0 C)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) C.hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl
def pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) : sp P ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec) (by
    simp only [sp, Over.mk_hom]
    rw [Category.assoc, fromSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact h.comp_algebraMap)
theorem chart_eq (C : Chart G) {P : Type} [CommRing P] (x : Spec (CommRingCat.of P) ⟶ G.left)
    (hx : ⊤ ≤ x ⁻¹ᵁ C.U) :
    Spec.map (x.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x C.hU (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]
end Chart
section ChartB
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]
def epsHom (C : Chart G) : Γ(G.left, C.U) ⟶ CommRingCat.of R₀ :=
  Scheme.Hom.appLE (η[G]).left C.U ⊤ C.he ≫ (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom
theorem epsHom_spec (C : Chart G) : Spec.map (epsHom C) ≫ C.hU.fromSpec = (η[G]).left := chart_eq C (η[G]).left C.he
theorem epsHom_comp (C : Chart G) : (epsHom C).hom.comp (alg0 C) = RingHom.id R₀ := by
  have e : Spec.map (CommRingCat.ofHom ((epsHom C).hom.comp (alg0 C))) =
      Spec.map (CommRingCat.ofHom (RingHom.id R₀)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc,
      epsHom_spec, CommRingCat.ofHom_id, Spec.map_id]
    first
    | exact Over.w (η[G])
    | simpa using Over.w (η[G])
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
def eps (C : Chart G) : Γ(G.left, C.U) →ₐ[R₀] R₀ :=
  { (epsHom C).hom with commutes' := fun r => RingHom.congr_fun (epsHom_comp C) r }
end ChartB
section Smooth
variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] (C : Chart G)
end Smooth
end ReciprocityTheory.ChartRestriction.G.Chart


