-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fc855615-c7ee-557b-b4bb-43d1dfb66c30

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsTangentOfPair_exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp
import Theorems.Thm_AlgebraicGeometry_SmallExtension_tangentCoords_comp_map_add_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add.AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add.AlgebraicGeometry.SmallExtension NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Spec Spec.map Scheme Scheme.Hom.comp_appTop Flat IsAffineOpen Scheme.ΓSpecIso_naturality SquareZero.specMap SquareZero.specMap_toBase SquareZero.basePoint_specMap SquareZero.zeroSection SquareZero.zeroSection_fst SquareZero.zeroSection_snd RelTangentPoints SquareZero.zeroSection_snd_assoc RelTangentPoints.base RelTangentPoints.translate RelTangentPoints.existsUnique_comp_openInclusion_eq RelTangentPoints.comp_translate_eq_translate_comp"
namespace SmallExtension
p2m_export "AlgebraicGeometry.SmallExtension" "thickening IsTangentOfPair reductionBase thickeningFst thickeningSnd thickening_isPullback chartRingHom IsTangentCoordsOfPairAtVia existsUnique_isTangentOfPair_of_flat IsTangentOfPair.exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add tangentCoords_comp_map_add_eq_add"
namespace CoordsAddViaAux
p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry"

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

abbrev jmap (f : (V × V) →ₗ[ResidueField T'] V) :
    thickening T' (V × V) C →ₐ[ResidueField T'] thickening T' V C :=
  Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C)) (TrivSqZeroExt.map f)

variable (T') in

abbrev jSpec (f : (V × V) →ₗ[ResidueField T'] V) :
    Spec (CommRingCat.of (thickening T' V C)) ⟶ Spec (CommRingCat.of (thickening T' (V × V) C)) :=
  Spec.map (CommRingCat.ofHom (jmap T' V C f).toRingHom)

theorem jSpec_thickeningFst (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ thickeningFst T' (V × V) C = thickeningFst T' V C := by
  rw [jSpec, thickeningFst, thickeningFst, ← Spec.map_comp]
  congr 1
  all_goals
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change jmap T' V C f (Algebra.TensorProduct.includeLeftRingHom c) = Algebra.TensorProduct.includeLeftRingHom c
    simp [Algebra.TensorProduct.includeLeftRingHom_apply, jmap, Algebra.TensorProduct.map_tmul]

theorem jSpec_thickeningSnd (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ thickeningSnd T' (V × V) C = thickeningSnd T' V C ≫ SquareZero.specMap (ResidueField T') f := by
  rw [jSpec, thickeningSnd, thickeningSnd, SquareZero.specMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem jSpec_base (f : (V × V) →ₗ[ResidueField T'] V) :
    jSpec T' V C f ≫ RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) =
      RelTangentPoints.base V (thickeningSnd T' V C) := by
  rw [RelTangentPoints.base, RelTangentPoints.base, ← Category.assoc, jSpec_thickeningSnd, Category.assoc,
    SquareZero.specMap_toBase]

theorem zeroSection_jSpec (f : (V × V) →ₗ[ResidueField T'] V) :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫
        jSpec T' V C f =
      SquareZero.zeroSection (V × V) (reductionBase T' C) (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C)
        (thickening_isPullback (V × V) C) := by
  apply (thickening_isPullback (V × V) C).hom_ext
  · rw [Category.assoc, jSpec_thickeningFst, SquareZero.zeroSection_fst, SquareZero.zeroSection_fst]
  · rw [Category.assoc, jSpec_thickeningSnd, SquareZero.zeroSection_snd_assoc, SquareZero.zeroSection_snd,
      SquareZero.basePoint_specMap]

theorem chartRingHom_jSpec_comp {Ak : Scheme.{u}} (Ue : Ak.Opens) (f : (V × V) →ₗ[ResidueField T'] V)
    (w : Spec (CommRingCat.of (thickening T' (V × V) C)) ⟶ (Ue : Scheme.{u})) :
    chartRingHom V C Ue (jSpec T' V C f ≫ w) = (jmap T' V C f).toRingHom.comp (chartRingHom (V × V) C Ue w) := by
  simp only [chartRingHom, jSpec, Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.ΓSpecIso_naturality]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  rfl

end AlgebraicGeometry.SmallExtension.CoordsAddViaAux

end

open AlgebraicGeometry.SmallExtension.CoordsAddViaAux in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u v x : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hx : x ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (hvx : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ x)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (c₁ c₂ c₃ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h₁ : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c₁)
    (h₂ : IsTangentCoordsOfPairAtVia I V ι C v x xk Lk W aW Ue c₂)
    (h₃ : IsTangentCoordsOfPairAtVia I V ι C u x xk Lk W aW Ue c₃) :
    c₃ = c₁ + c₂  := by
  obtain ⟨a0, ha0, a1, hat, hatr, hac⟩ := h₁
  obtain ⟨b0, hb0, b1, hbt, hbtr, hbc⟩ := h₂
  obtain ⟨c0, hc0, c1, hct, hctr, hcc⟩ := h₃

  let k := ResidueField T'
  let fst : (V × V) →ₗ[k] V := LinearMap.fst k V V
  let snd : (V × V) →ₗ[k] V := LinearMap.snd k V V
  let add : (V × V) →ₗ[k] V := LinearMap.fst k V V + LinearMap.snd k V V

  obtain ⟨Wg, hWq, hW1, hW2, hW3⟩ :=
    IsTangentOfPair.exists_comp_map_fst_eq_and_isTangentOfPair_comp_map_add I hI hsmall V ι hιI C qY u v x hu hv hx
      (a0 ≫ aW) (b0 ≫ aW) hat hbt
  change jSpec T' V C fst ≫ Wg = a0 ≫ aW at hW1
  change jSpec T' V C snd ≫ Wg = b0 ≫ aW at hW2
  change IsTangentOfPair I V ι C u x (jSpec T' V C add ≫ Wg) at hW3

  have hux : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ x := huv.trans hvx
  have hW3' : jSpec T' V C add ≫ Wg = c0 ≫ aW :=
    (existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C qY u hu x hx hux).unique hW3 hct

  let W₀ : Spec (CommRingCat.of (thickening T' (V × V) C)) ⟶ (W : Scheme.{u}) :=
    haW.lift Wg (RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C)) hWq
  have hW₀a : W₀ ≫ aW = Wg := haW.lift_fst _ _ _
  have hW₀x : W₀ ≫ W.ι ≫ xk = RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) := haW.lift_snd _ _ _
  have hW₀x' : (W₀ ≫ W.ι) ≫ xk = RelTangentPoints.base (V × V) (thickeningSnd T' (V × V) C) := by
    rw [Category.assoc]; exact hW₀x
  have r1 : jSpec T' V C fst ≫ W₀ = a0 :=
    haW.hom_ext (by rw [Category.assoc, hW₀a, hW1]) (by rw [Category.assoc, hW₀x, jSpec_base, ← Category.assoc, ha0])
  have r2 : jSpec T' V C snd ≫ W₀ = b0 :=
    haW.hom_ext (by rw [Category.assoc, hW₀a, hW2]) (by rw [Category.assoc, hW₀x, jSpec_base, ← Category.assoc, hb0])
  have r3 : jSpec T' V C add ≫ W₀ = c0 :=
    haW.hom_ext (by rw [Category.assoc, hW₀a, hW3']) (by rw [Category.assoc, hW₀x, jSpec_base, ← Category.assoc, hc0])

  let T := RelTangentPoints.translate xk Lk (V × V) (reductionBase T' C) (thickeningFst T' (V × V) C)
    (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C) (W₀ ≫ W.ι) hW₀x'
  obtain ⟨T₁, hT₁⟩ := (RelTangentPoints.existsUnique_comp_openInclusion_eq xk (Lk.one (𝟙 _)).1 (V × V) (reductionBase T' C)
    (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C) T Ue e₁ he₁).exists

  have key : ∀ (f : (V × V) →ₗ[k] V) (w0 : Spec (CommRingCat.of (thickening T' V C)) ⟶ (W : Scheme.{u}))
      (hw0 : (w0 ≫ W.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
      (w1 : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
      jSpec T' V C f ≫ W₀ = w0 →
      w1 ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) (w0 ≫ W.ι) hw0).1 →
      jSpec T' V C f ≫ T₁ = w1 := by
    intro f w0 hw0 w1 hr hw1
    have htr : jSpec T' V C f ≫ T.1 = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C)
        (thickeningSnd T' V C) (thickening_isPullback V C) (w0 ≫ W.ι) hw0).1 :=
      RelTangentPoints.comp_translate_eq_translate_comp xk Lk V (V × V) (reductionBase T' C) (reductionBase T' C)
        (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
        (thickeningFst T' (V × V) C) (thickeningSnd T' (V × V) C) (thickening_isPullback (V × V) C)
        (𝟙 _) (Category.id_comp _) (jSpec T' V C f) (by rw [jSpec_thickeningFst, Category.comp_id])
        (by rw [zeroSection_jSpec, Category.id_comp]) (W₀ ≫ W.ι) hW₀x' (w0 ≫ W.ι) hw0 (by rw [← Category.assoc, hr])
    exact (RelTangentPoints.existsUnique_comp_openInclusion_eq xk (Lk.one (𝟙 _)).1 V (reductionBase T' C)
      (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) _ Ue e₁ he₁).unique
      (by rw [Category.assoc, hT₁, htr]) hw1
  have e1 : jSpec T' V C fst ≫ T₁ = a1 := key fst a0 ha0 a1 r1 hatr
  have e2 : jSpec T' V C snd ≫ T₁ = b1 := key snd b0 hb0 b1 r2 hbtr
  have e3 : jSpec T' V C add ≫ T₁ = c1 := key add c0 hc0 c1 r3 hctr

  rw [hac, hbc, hcc, ← e1, ← e2, ← e3, chartRingHom_jSpec_comp, chartRingHom_jSpec_comp, chartRingHom_jSpec_comp]
  exact tangentCoords_comp_map_add_eq_add V C (chartRingHom (V × V) C Ue T₁)

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_add (solution)
