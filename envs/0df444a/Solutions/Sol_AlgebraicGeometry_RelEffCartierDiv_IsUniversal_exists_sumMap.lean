-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_sumMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d8fa81e9-8f71-5754-b8d8-8a42a0135485

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom.finrank_comp_left_of_isIso SmoothOfRelativeDimension Scheme.Hom IsFinite Scheme Smooth Flat IsSeparated LocallyOfFinitePresentation fibrePowOver fibrePowOver.proj fibrePowOver.toBase fibrePowOver.proj_comp prodKerGraph fibrePowOver.tautIdeal RelEffCartierDiv mapOnProdOver RelEffCartierDiv.I RelEffCartierDiv.IsUniversal RelEffCartierDiv.exists_split RelEffCartierDiv.exists_I_eq_prodKerGraph prodKerGraph_comap_mapOnProdOver"
p2m_open "AlgebraicGeometry"

theorem prodKerGraph_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    {a a' : Fin r → (T ⟶ 𝒞)} (h : a = a') (ha : ∀ i, a i ≫ f = g) (ha' : ∀ i, a' i ≫ f = g) :
    prodKerGraph f a ha = prodKerGraph f a' ha' := by
  subst h; rfl

namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong pullbackAlong_comp I IsUniversal exists_split exists_I_eq_prodKerGraph"
namespace IsUniversal
p2m_export "AlgebraicGeometry.RelEffCartierDiv.IsUniversal" "lift lift_comp pullsBackOver_lift hom_ext"
p2m_open "AlgebraicGeometry.RelEffCartierDiv.IsUniversal AlgebraicGeometry.RelEffCartierDiv"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}

set_option backward.isDefEq.respectTransparency false in

private theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.exists_sumMap_aux (hU : Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial := by

  obtain ⟨Dt, hDt⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := f)
    (fibrePowOver.proj f r) (fibrePowOver.proj_comp f r)
  set σ : fibrePowOver f r ⟶ Y := hU.lift Dt with hσdef
  have hσ : σ ≫ y = fibrePowOver.toBase f r := hU.lift_comp Dt
  have hσI : Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r :=
    (hU.pullsBackOver_lift Dt).trans hDt
  clear_value σ

  obtain ⟨P, gP, p, hp, b, hb, hfin, hflat, hlfp, hsurj, hrank, hI, huniv⟩ :=
    RelEffCartierDiv.exists_split Duniv
  subst hp

  obtain ⟨u, ⟨hup, hub⟩, -⟩ := huniv (fibrePowOver.toBase f r) σ hσ (fibrePowOver.proj f r)
    (fibrePowOver.proj_comp f r) hσI

  let t : P ⟶ fibrePowOver f r := WidePullback.lift (p ≫ y) b hb
  have ht_proj : ∀ i, t ≫ fibrePowOver.proj f r i = b i := fun i => WidePullback.lift_π _ _ _ _ _
  have ht_base : t ≫ fibrePowOver.toBase f r = p ≫ y := WidePullback.lift_base _ _ _ _

  have hut : u ≫ t = 𝟙 _ := by
    apply WidePullback.hom_ext
    · intro i
      rw [Category.assoc, Category.id_comp]
      exact (ht_proj i).symm ▸ hub i
    · rw [Category.assoc, ht_base, Category.id_comp, ← Category.assoc, hup, hσ]

  have hty : (t ≫ σ) ≫ y = p ≫ y := by rw [Category.assoc, hσ, ht_base]
  have hcomp := congrArg RelEffCartierDiv.I (Duniv.pullbackAlong_comp σ hσ t ht_base)
  have htσ : p = t ≫ σ := by
    refine hU.hom_ext hty.symm ?_
    change (Duniv.pullbackAlong p rfl).I = (Duniv.pullbackAlong (t ≫ σ) hty).I
    rw [hI, ← hcomp]
    change prodKerGraph f b hb =
      ((Duniv.I.comap (mapOnProdOver f σ hσ)).comap (mapOnProdOver f t ht_base))
    rw [hσI, fibrePowOver.tautIdeal, prodKerGraph_comap_mapOnProdOver]
    exact prodKerGraph_congr f (funext fun i => (ht_proj i).symm) _ _

  have htu : t ≫ u = 𝟙 P := by
    obtain ⟨w, -, hwuniq⟩ := huniv (p ≫ y) p rfl b hb hI
    have h1 : t ≫ u = w :=
      hwuniq _ ⟨by rw [Category.assoc, hup, ← htσ], fun i => by rw [Category.assoc, hub, ht_proj]⟩
    have h2 : 𝟙 P = w := hwuniq _ ⟨Category.id_comp _, fun i => Category.id_comp _⟩
    exact h1.trans h2.symm
  have : IsIso u := ⟨⟨t, hut, htu⟩⟩
  subst hup
  exact ⟨u ≫ p, hσ, hσI, inferInstance, inferInstance, inferInstance, inferInstance,
    fun x => by rw [Scheme.Hom.finrank_comp_left_of_isIso]; exact hrank x⟩

p2m_export "AlgebraicGeometry.RelEffCartierDiv.IsUniversal" "exists_sumMap_aux"
end RelEffCartierDiv.IsUniversal

end AlgebraicGeometry

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S} {Duniv : RelEffCartierDiv f r y}
    (hU : Duniv.IsUniversal) :
    ∃ (σ : fibrePowOver f r ⟶ Y) (hσ : σ ≫ y = fibrePowOver.toBase f r),
      Duniv.I.comap (mapOnProdOver f σ hσ) = fibrePowOver.tautIdeal f r ∧
      IsFinite σ ∧ Flat σ ∧ LocallyOfFinitePresentation σ ∧ Surjective σ ∧
      ∀ x : Y, σ.finrank x = r.factorial :=
  hU.exists_sumMap_aux

end S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_sumMap (solution)
