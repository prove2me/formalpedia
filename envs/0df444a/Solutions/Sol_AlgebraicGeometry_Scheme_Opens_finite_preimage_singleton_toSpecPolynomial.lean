-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Opens.finite_preimage_singleton_toSpecPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dadfb87e-3fdd-5720-ae70-d22692ae783d

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension.smooth Scheme.Opens.topIso_inv Scheme.germToFunctionField SmoothOfRelativeDimension basicOpen_eq_bot_iff Scheme.Hom QuasiCompact Scheme.Hom.image_top_eq_opensRange LocallyOfFiniteType Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme Smooth Scheme.Hom.comp_appTop locallyOfFiniteType_of_comp toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Opens.mem_basicOpen_toScheme Scheme.Opens Scheme.Opens.ι_appTop Scheme.Opens.opensRange_ι toSpecΓ Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Opens.topIso_inv germToFunctionField Hom germToFunctionField_injective Γ topIso Hom.image_top_eq_opensRange toSpecΓ_naturality Hom.comp_appTop basicOpen Opens.mem_basicOpen_toScheme Opens toSpecΓ_preimage_basicOpen Opens.ι_appTop Opens.opensRange_ι ΓSpecIso toSpecΓ" namespace Opens p2m_export "AlgebraicGeometry.Scheme.Opens" "topIso_inv toSpecΓ toSpecΓ_preimage_basicOpen toSpecΓ_naturality topIso mem_basicOpen_toScheme ι ι_appTop opensRange_ι" end Scheme.Opens
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

noncomputable abbrev Scheme.Opens.baseRingHom (U : C.Opens) : k →+* Γ((U : Scheme.{u}), ⊤) :=
  (U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

noncomputable abbrev Scheme.Opens.toSpecPolynomial (U : C.Opens) (s : Γ(C, U)) :
    (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
  (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)))

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens" in

theorem Scheme.Opens.toSpecPolynomial_comp_C (U : C.Opens) (s : Γ(C, U)) :
    Scheme.Opens.toSpecPolynomial c U s ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) =
      U.ι ≫ c := by
  simp only [Scheme.Opens.toSpecPolynomial, Category.assoc, ← Spec.map_comp]
  have h1 : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ c).appTop := by
    ext a
    simp [Scheme.Opens.baseRingHom]
  refine (congrArg (fun m => (U : Scheme.{u}).toSpecΓ ≫ Spec.map m) h1).trans ?_
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

namespace QFin

theorem germToFunctionField_map [IsIntegral C] {U V : C.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (t : Γ(C, U)) :
    (C.germToFunctionField V).hom ((C.presheaf.map i.op).hom t) = (C.germToFunctionField U).hom t := by
  change (C.presheaf.map i.op ≫ C.germToFunctionField V).hom t = _
  rw [Scheme.germToFunctionField, C.presheaf.germ_res]

theorem mem_toSpecΓ_asIdeal_iff (X : Scheme.{u}) (x : X) (t : Γ(X, ⊤)) :
    t ∈ (X.toSpecΓ.base x).asIdeal ↔ x ∉ X.basicOpen t := by
  have h : x ∈ X.basicOpen t ↔ t ∉ (X.toSpecΓ.base x).asIdeal := by
    rw [← X.toSpecΓ_preimage_basicOpen t]; rfl
  rw [h, not_not]

theorem mem_fibre_iff (U : C.Opens) (s : Γ(C, U)) (x : (U : Scheme.{u})) (q : k[X]) :
    q ∈ ((Scheme.Opens.toSpecPolynomial c U s).base x).asIdeal ↔
      x.1 ∉ C.basicOpen
        (Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q) := by
  rw [← Scheme.Opens.mem_basicOpen_toScheme]
  exact mem_toSpecΓ_asIdeal_iff (U : Scheme.{u}) x _

variable [IsIntegral C]

theorem germToFunctionField_eval₂ (U : C.Opens) [Nonempty U] (s : Γ(C, U)) (q : k[X]) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    haveI : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance
    (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom
        (Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q) =
      Polynomial.aeval (C.germToFunctionField U s) q := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
  congr 1
  · ext a
    change (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom ((U.ι ≫ c).appTop.hom _) =
      AlgebraicCurve.baseToFunctionField c a
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Opens.ι_appTop]
    have hc : C.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        C.germToFunctionField (U.ι ''ᵁ ⊤) = C.presheaf.germ ⊤ (genericPoint C) trivial := by
      rw [Scheme.germToFunctionField, C.presheaf.germ_res]
    exact congrArg (fun φ => φ.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a))) hc
  · rw [Scheme.Opens.topIso_inv]
    exact germToFunctionField_map _ s

end QFin

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.AlgebraicGeometry AlgebraicGeometry.QFin in
theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s))
    (p : Spec (CommRingCat.of k[X])) :
    (((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))).base ⁻¹' {p}).Finite := by
  show ((Scheme.Opens.toSpecPolynomial c U s).base ⁻¹' {p}).Finite
  classical
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  haveI hne' : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance

  have hsec : ∀ q : k[X], q ≠ 0 →
      Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q ≠ 0 := by
    intro q hq h0
    apply hs
    refine ⟨q, hq, ?_⟩
    rw [← germToFunctionField_eval₂ c U s q]
    exact (map_eq_zero_iff (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom
      (C.germToFunctionField_injective _)).mpr h0
  by_cases hp : p.asIdeal = ⊥
  ·
    haveI : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
    haveI : LocallyOfFiniteType (Scheme.Opens.toSpecPolynomial c U s ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
      rw [Scheme.Opens.toSpecPolynomial_comp_C]; infer_instance
    haveI : LocallyOfFiniteType (Scheme.Opens.toSpecPolynomial c U s) :=
      locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
    apply Set.Subsingleton.finite
    intro x hx y hy
    have hx' : (Scheme.Opens.toSpecPolynomial c U s).base x = p := hx
    have hy' : (Scheme.Opens.toSpecPolynomial c U s).base y = p := hy

    have hgen : ∀ z : (U : Scheme.{u}), (Scheme.Opens.toSpecPolynomial c U s).base z = p →
        z.1 = genericPoint C := by
      intro z hz
      by_contra hzη
      have hzC : IsClosed ({z.1} : Set C) :=
        AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c z.1 hzη
      have hzU : IsClosed ({z} : Set (U : Scheme.{u})) := by
        have : ({z} : Set (U : Scheme.{u})) = Subtype.val ⁻¹' {z.1} := by
          ext w
          simp only [Set.mem_singleton_iff]
          exact Subtype.ext_iff
        rw [this]
        exact hzC.preimage continuous_subtype_val
      have hcl := (Scheme.Opens.toSpecPolynomial c U s).closePoints_subset_preimage_closedPoints hzU
      have hcl' : IsClosed ({p} : Set (PrimeSpectrum k[X])) := by rw [← hz]; exact hcl
      have hmax : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hcl'
      rw [hp] at hmax
      exact Polynomial.not_isField k (Ring.isField_iff_maximal_bot.mpr hmax)
    exact Subtype.ext ((hgen x hx').trans (hgen y hy').symm)
  ·
    obtain ⟨q, hqp, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    set r := Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q with hrdef
    have hr0 : r ≠ 0 := hsec q hq0

    have hopen : ((C.basicOpen r : C.Opens) : Set C).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, SetLike.coe_set_eq]
      intro hbot
      exact hr0 ((basicOpen_eq_bot_iff (X := C) (U := U.ι ''ᵁ ⊤) r).mp hbot)
    have hfin := AlgebraicCurve.finite_compl_of_isOpen c (C.basicOpen r) hopen

    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    have hx' : (Scheme.Opens.toSpecPolynomial c U s).base x = p := hx
    show x.1 ∈ ((C.basicOpen r : C.Opens) : Set C)ᶜ
    rw [Set.mem_compl_iff, SetLike.mem_coe]
    exact (mem_fibre_iff c U s x q).mp (hx' ▸ hqp)

end S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial (solution)
