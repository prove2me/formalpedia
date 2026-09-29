-- Prove2me | solution 1 for AlgebraicCurve.nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7f11c261-cd0e-5c2b-afe2-07da2dade986

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace TwoChartCech
p2m_export "TwoChartCech" "Sections Sections.cechDiff_apply kerMap cokerMap"
p2m_open "TwoChartCech"

universe uR uK

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective' (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective' (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Divisor baseToFunctionField placesOf placesOf_mono lSpaceOn cechDiff coe_cechDiff_apply cechH0 cechH1 H1 eq_of_range_stalk_eq"
p2m_open "AlgebraicCurve"
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

theorem placesOf_inf' [IsSeparated x] [SmoothOfRelativeDimension 1 x] (U V : X.Opens) :
    letI := (baseToFunctionField x).toAlgebra
    placesOf x (U ⊓ V) = placesOf x U ∩ placesOf x V := by
  letI := (baseToFunctionField x).toAlgebra
  apply Set.Subset.antisymm
  · exact fun v hv => ⟨placesOf_mono x inf_le_left hv, placesOf_mono x inf_le_right hv⟩
  · rintro v ⟨⟨y, hyU, hy, hvy⟩, ⟨z, hzV, -, hvz⟩⟩
    have hyz : y = z := eq_of_range_stalk_eq x y z (hvy.trans hvz.symm)
    subst hyz
    exact ⟨y, ⟨hyU, hzV⟩, hy, hvy⟩

theorem germToFunctionField_algebraMap' (U : X.Opens) [Nonempty U] (r : K) :
    (X.germToFunctionField U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom x U).algebraMap r)
      = baseToFunctionField x r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (x.appLE ⊤ U le_top ≫ X.germToFunctionField U).hom _
    = (x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom _
  congr 2
  rw [Scheme.Hom.appLE, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  try rfl

noncomputable def sectionsEquivLSpaceOn (M : X.Modules) (U : X.Opens) [Nonempty U]
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : Γ(M, U) →+ (X.functionField : Type u))
    (hsmul : ∀ (a : Γ(X, U)) (m : Γ(M, U)), φ (a • m) = algebraMap Γ(X, U) X.functionField a * φ m)
    (hinj : Function.Injective φ)
    (hrange : letI := (baseToFunctionField x).toAlgebra
      Set.range φ = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M U
    letI := (baseToFunctionField x).toAlgebra
    Γ(M, U) ≃ₗ[K] ↥(lSpaceOn (placesOf x U) D) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M U
  letI := (baseToFunctionField x).toAlgebra
  LinearEquiv.ofBijective
    ({ toFun := fun m => ⟨φ m, by
          have : φ m ∈ Set.range φ := ⟨m, rfl⟩
          rw [hrange] at this
          exact this⟩
       map_add' := fun m m' => Subtype.ext (map_add φ m m')
       map_smul' := fun r m => Subtype.ext (by
          show φ (((Scheme.TwoAffineOpenCover.algebraOfHom x U).algebraMap r) • m) = r • φ m
          rw [hsmul, Algebra.smul_def]
          exact congrArg (· * φ m) (germToFunctionField_algebraMap' x U r)) }
      : Γ(M, U) →ₗ[K] ↥(lSpaceOn (placesOf x U) D))
    ⟨fun m m' h => hinj (congrArg Subtype.val h),
     fun ⟨f, hf⟩ => by
      have : f ∈ Set.range φ := by rw [hrange]; exact hf
      obtain ⟨m, rfl⟩ := this
      exact ⟨m, rfl⟩⟩

theorem coe_sectionsEquivLSpaceOn_apply (M : X.Modules) (U : X.Opens) [Nonempty U]
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : Γ(M, U) →+ (X.functionField : Type u))
    (hsmul : ∀ (a : Γ(X, U)) (m : Γ(M, U)), φ (a • m) = algebraMap Γ(X, U) X.functionField a * φ m)
    (hinj : Function.Injective φ)
    (hrange : letI := (baseToFunctionField x).toAlgebra
      Set.range φ = (lSpaceOn (placesOf x U) D : Set X.functionField)) (m : Γ(M, U)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M U
    letI := (baseToFunctionField x).toAlgebra
    ((sectionsEquivLSpaceOn x M U D φ hsmul hinj hrange m : ↥(lSpaceOn (placesOf x U) D)) : X.functionField)
      = φ m := rfl

theorem nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq
    (𝒱 : X.TwoAffineOpenCover) [IsSeparated x] [SmoothOfRelativeDimension 1 x]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) (M : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := (baseToFunctionField x).toAlgebra
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[K] ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D)) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[K] cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) := by
  letI := (baseToFunctionField x).toAlgebra
  haveI := h0
  haveI := h1
  haveI h01 : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens) := by
    obtain ⟨⟨u, hu⟩⟩ := h0
    obtain ⟨⟨w, hw⟩⟩ := h1
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen ⟨u, hu⟩ ⟨w, hw⟩
    exact ⟨⟨z, hz⟩⟩
  have hS01 : placesOf x (𝒱.U0 ⊓ 𝒱.U1) = placesOf x 𝒱.U0 ∩ placesOf x 𝒱.U1 := placesOf_inf' x 𝒱.U0 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.algebraOfHom x (𝒱.U0 ⊓ 𝒱.U1)
  letI : Module K Γ(M, 𝒱.U0) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M 𝒱.U0
  letI : Module K Γ(M, 𝒱.U1) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M 𝒱.U1
  letI : Module K Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x M (𝒱.U0 ⊓ 𝒱.U1)

  let e0 := sectionsEquivLSpaceOn x M 𝒱.U0 D (φ 𝒱.U0) (fun a m => hsmul 𝒱.U0 a m) (hinj _ h0)
    (hrange _ 𝒱.isAffineOpen_U0 h0)
  let e1 := sectionsEquivLSpaceOn x M 𝒱.U1 D (φ 𝒱.U1) (fun a m => hsmul 𝒱.U1 a m) (hinj _ h1)
    (hrange _ 𝒱.isAffineOpen_U1 h1)
  let e01' := sectionsEquivLSpaceOn x M (𝒱.U0 ⊓ 𝒱.U1) D (φ (𝒱.U0 ⊓ 𝒱.U1)) (fun a m => hsmul _ a m)
    (hinj _ h01) (hrange _ 𝒱.isAffineOpen_inf h01)
  let e01 := e01'.trans (LinearEquiv.ofEq _ _ (by rw [hS01]))

  let ι0 : (𝒱.sectionsOf x M).M0 × (𝒱.sectionsOf x M).M1
      →ₗ[K] ↥(lSpaceOn (placesOf x 𝒱.U0) D) × ↥(lSpaceOn (placesOf x 𝒱.U1) D) :=
    LinearMap.prodMap e0.toLinearMap e1.toLinearMap
  let ι1 : (𝒱.sectionsOf x M).M01 →ₗ[K] ↥(lSpaceOn (placesOf x 𝒱.U0 ∩ placesOf x 𝒱.U1) D) :=
    e01.toLinearMap
  have comm : cechDiff (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D ∘ₗ ι0 = ι1 ∘ₗ (𝒱.sectionsOf x M).cechDiff := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    have lhs : ((cechDiff (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D ∘ₗ ι0) p : X.functionField)
        = φ 𝒱.U1 p.2 - φ 𝒱.U0 p.1 := by
      rw [LinearMap.comp_apply, coe_cechDiff_apply]
      rfl
    have rhs : ((ι1 ∘ₗ (𝒱.sectionsOf x M).cechDiff) p : X.functionField)
        = φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).cechDiff p) := rfl
    rw [lhs, rhs, TwoChartCech.Sections.cechDiff_apply]
    have e2 : φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).r1 p.2) = φ 𝒱.U1 p.2 := by
      rw [Scheme.TwoAffineOpenCover.sectionsOf_r1_apply]
      exact hnat 𝒱.U1 (𝒱.U0 ⊓ 𝒱.U1) inf_le_right h01 p.2
    have e1 : φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).r0 p.1) = φ 𝒱.U0 p.1 := by
      rw [Scheme.TwoAffineOpenCover.sectionsOf_r0_apply]
      exact hnat 𝒱.U0 (𝒱.U0 ⊓ 𝒱.U1) inf_le_left h01 p.1
    have e3 : φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).r1 p.2 - (𝒱.sectionsOf x M).r0 p.1)
        = φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).r1 p.2) - φ (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.sectionsOf x M).r0 p.1) :=
      map_sub (φ (𝒱.U0 ⊓ 𝒱.U1)) _ _
    rw [e3, e2, e1]
  have hι0 : Function.Bijective ι0 :=
    ⟨fun a b hab => Prod.ext (e0.injective (congrArg Prod.fst hab)) (e1.injective (congrArg Prod.snd hab)),
     fun q => ⟨(e0.symm q.1, e1.symm q.2), Prod.ext (e0.apply_symm_apply q.1) (e1.apply_symm_apply q.2)⟩⟩
  have hι1 : Function.Bijective ι1 := e01.bijective
  exact ⟨⟨LinearEquiv.ofBijective _
      (TwoChartCech.kerMap_bijective_of_bijective' ((𝒱.sectionsOf x M).cechDiff)
        (cechDiff (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) ι0 ι1 comm hι0 hι1.1)⟩,
    ⟨LinearEquiv.ofBijective _
      (TwoChartCech.cokerMap_bijective_of_bijective' ((𝒱.sectionsOf x M).cechDiff)
        (cechDiff (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) ι0 ι1 comm hι0.2 hι1)⟩⟩

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn.AlgebraicCurve in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x] [SmoothOfRelativeDimension 1 x]
    (h0 : Nonempty 𝒱.U0) (h1 : Nonempty 𝒱.U1) (M : X.Modules)
    (D : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[K]
        ↥(AlgebraicCurve.cechH0 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D)) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[K]
        AlgebraicCurve.cechH1 (AlgebraicCurve.placesOf x 𝒱.U0) (AlgebraicCurve.placesOf x 𝒱.U1) D) :=
  nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq x 𝒱 h0 h1 M D φ hnat
    (fun U _ a m => hsmul U a m) hinj hrange

end S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
end P2MW
export P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn (solution)
