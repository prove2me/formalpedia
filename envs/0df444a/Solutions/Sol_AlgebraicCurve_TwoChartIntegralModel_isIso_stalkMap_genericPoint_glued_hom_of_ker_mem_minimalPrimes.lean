-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/747ef89e-b4cf-543c-a3b8-83984bda8034

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct

namespace BirChart

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem germ_seam
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (φ : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(CurveModel.chartRing κ ({t} : Set L)))
    (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (g : Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ)) ⟶
        pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) [IsOpenImmersion g]
    (hψg : Spec.map (CommRingCat.ofHom φ) ≫ g = CurveModel.ι₀ κ t ≫ c)
    (hη : (CurveModel.ι₀ κ t).base (genericPoint (CurveModel.X₀ κ t)) = genericPoint (CurveModel.glued κ t))
    (hV : c.base (genericPoint (CurveModel.glued κ t)) ∈ g ''ᵁ ⊤)
    (s : ↥(chartAlgFin R F j) ⊗[R] κ) :
    ((CurveModel.ι₀ κ t).stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
      (((CurveModel.glued κ t).presheaf.stalkCongr (.of_eq hη.symm)).hom.hom
        (((CurveModel.glued κ t).presheaf.germ (c ⁻¹ᵁ (g ''ᵁ ⊤)) (genericPoint (CurveModel.glued κ t)) hV).hom
          ((c.app (g ''ᵁ ⊤)).hom ((g.appIso ⊤).inv.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s))))) =
    ((CurveModel.X₀ κ t).presheaf.germ ⊤ (genericPoint (CurveModel.X₀ κ t)) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(CurveModel.chartRing κ ({t} : Set L)))).inv.hom (φ s)) := by
  classical

  have hV' : c.base ((CurveModel.ι₀ κ t).base (genericPoint (CurveModel.X₀ κ t))) ∈ g ''ᵁ ⊤ := by
    rw [hη]; exact hV

  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_apply]

  rw [← Scheme.Hom.germ_stalkMap_apply c (g ''ᵁ ⊤) _ hV', ← CommRingCat.comp_apply, ← Scheme.Hom.stalkMap_comp]

  have key : ∀ (h h' : CurveModel.X₀ κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
      (e : h = h') (hm : h.base (genericPoint (CurveModel.X₀ κ t)) ∈ g ''ᵁ ⊤) (y),
      (h.stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
        (((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.germ (g ''ᵁ ⊤)
          (h.base (genericPoint (CurveModel.X₀ κ t))) hm).hom y) =
      (h'.stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
        (((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.germ (g ''ᵁ ⊤)
          (h'.base (genericPoint (CurveModel.X₀ κ t))) (e ▸ hm)).hom y) := by
    rintro h _ rfl hm y; rfl
  have hm' : (Spec.map (CommRingCat.ofHom φ) ≫ g).base (genericPoint (CurveModel.X₀ κ t)) ∈ g ''ᵁ ⊤ := by
    rw [hψg]; exact hV'
  change ((CurveModel.ι₀ κ t ≫ c).stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
      (((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.germ (g ''ᵁ ⊤)
        ((CurveModel.ι₀ κ t ≫ c).base (genericPoint (CurveModel.X₀ κ t))) hV').hom
        ((g.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s))) = _
  rw [key (CurveModel.ι₀ κ t ≫ c) (Spec.map (CommRingCat.ofHom φ) ≫ g) hψg.symm hV']

  rw [Scheme.Hom.stalkMap_comp]
  change ((Spec.map (CommRingCat.ofHom φ)).stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
      ((g.stalkMap ((Spec.map (CommRingCat.ofHom φ)).base (genericPoint (CurveModel.X₀ κ t)))).hom
        ((((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.germ (g ''ᵁ ⊤)
          ((Spec.map (CommRingCat.ofHom φ) ≫ g).base (genericPoint (CurveModel.X₀ κ t))) hm').hom
          ((g.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s))))) = _
  erw [Scheme.Hom.germ_stalkMap_apply g (g ''ᵁ ⊤) _ hm']

  have h5 : (g.app (g ''ᵁ ⊤)).hom ((g.appIso ⊤).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s)) =
      ((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).presheaf.map (eqToHom (g.preimage_image_eq ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s) := by
    change ((g.appIso ⊤).inv ≫ g.app (g ''ᵁ ⊤)).hom _ = _
    rw [Scheme.Hom.appIso_inv_app]
  rw [h5]
  erw [TopCat.Presheaf.germ_res_apply]

  change ((Spec.map (CommRingCat.ofHom φ)).stalkMap (genericPoint (CurveModel.X₀ κ t))).hom
      (((Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom φ)).base (genericPoint (CurveModel.X₀ κ t))) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s)) = _
  rw [Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) ⊤]
  change ((CurveModel.X₀ κ t).presheaf.germ ⊤ (genericPoint (CurveModel.X₀ κ t)) trivial).hom
      (((Spec.map (CommRingCat.ofHom φ)).app ⊤).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s)) = _
  congr 1
  have hnat := congrArg (fun k => k.hom s) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact hnat.symm

end BirChart

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (κ : Type u) [Field κ] [Algebra R κ] {L : Type u} [Field L] [Algebra κ L] (t : L) [Fact (t ≠ 0)]
    (m : ℕ) (hm : 0 < m)
    (θFin : κ ⊗[R] ↥(chartAlgFin R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t} : Set L)))
    (θInf : κ ⊗[R] ↥(chartAlgInf R F j) →ₐ[κ] ↥(CurveModel.chartRing κ ({t⁻¹} : Set L)))
    (hj : ((θFin ((1 : κ) ⊗ₜ[R] jChartFin R F j)) : L) = t ^ m)
    (hjInv : ((θInf ((1 : κ) ⊗ₜ[R] jInvChartInf R F j)) : L) = t⁻¹ ^ m)
    (c : CurveModel.glued κ t ⟶ pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hc_over : c ≫ pullback.snd (toBase R F j) _ = CurveModel.gluedToBase κ t)
    (hcFin : CurveModel.ι₀ κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θFin.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom)) ≫
          ιFin R F j)
    (hcInf : CurveModel.ιInf κ t ≫ c ≫ pullback.fst (toBase R F j) _ =
        Spec.map (CommRingCat.ofHom (θInf.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgInf R F j))).toRingHom)) ≫
          ιInf R F j)
    (hmatch : ∀ y : ↥(CurveModel.glued κ t),
        (c ≫ pullback.fst (toBase R F j) _).base y ∈ Set.range (ιFin R F j).base ↔
          y ∈ Set.range (CurveModel.ι₀ κ t).base)
    (hmin : RingHom.ker (θFin.toRingHom.comp
        (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom) ∈
      minimalPrimes (↥(chartAlgFin R F j) ⊗[R] κ))
    (hred : _root_.IsReduced ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).presheaf.stalk
      (c.base (genericPoint (CurveModel.glued κ t)))))
    (hfrac : ∀ x : L, ∃ a b : κ ⊗[R] ↥(chartAlgFin R F j),
      ((θFin b : ↥(CurveModel.chartRing κ ({t} : Set L))) : L) ≠ 0 ∧
        x * ((θFin b : ↥(CurveModel.chartRing κ ({t} : Set L))) : L) = ((θFin a : ↥(CurveModel.chartRing κ ({t} : Set L))) : L)) :
    IsIso (c.stalkMap (genericPoint (CurveModel.glued κ t))) := by

  obtain ⟨g, hgo, hg1, hg2, hrange⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_isOpenImmersion_spec_tensor_chartAlgFin R F j κ
  haveI := hgo

  let φ : ↥(chartAlgFin R F j) ⊗[R] κ →+* ↥(CurveModel.chartRing κ ({t} : Set L)) :=
    θFin.toRingHom.comp (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).toRingHom
  let ψ : CurveModel.X₀ κ t ⟶ Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ)) := Spec.map (CommRingCat.ofHom φ)

  have hφL : φ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(chartAlgFin R F j)) (B := κ)) =
      θFin.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom := by
    refine RingHom.ext fun b => ?_
    show θFin ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ) (b ⊗ₜ[R] (1 : κ))) = θFin ((1 : κ) ⊗ₜ[R] b)
    rw [Algebra.TensorProduct.comm_tmul]
  have hφR : φ.comp (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := κ)).toRingHom =
      algebraMap κ ↥(CurveModel.chartRing κ ({t} : Set L)) := by
    refine RingHom.ext fun x => ?_
    show θFin ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ) ((1 : ↥(chartAlgFin R F j)) ⊗ₜ[R] x)) = algebraMap κ ↥(CurveModel.chartRing κ ({t} : Set L)) x
    rw [Algebra.TensorProduct.comm_tmul]
    have : (x ⊗ₜ[R] (1 : ↥(chartAlgFin R F j)) : κ ⊗[R] ↥(chartAlgFin R F j)) = algebraMap κ (κ ⊗[R] ↥(chartAlgFin R F j)) x := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [this, AlgHom.commutes]
  have hψg : ψ ≫ g = CurveModel.ι₀ κ t ≫ c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hg1, ← Category.assoc, Category.assoc (CurveModel.ι₀ κ t), hcFin]
      show (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom _)) ≫ ιFin R F j = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφL]
    · rw [Category.assoc, hg2, Category.assoc, hc_over, CurveModel.ι₀_gluedToBase]
      show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom _) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφR]

  set ζ := c.base (genericPoint (CurveModel.glued κ t)) with hζdef
  let q₀ : ↥(Spec (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))) := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  have hψη : ψ.base (genericPoint (CurveModel.X₀ κ t)) = q₀ := by
    have hgen : genericPoint (CurveModel.X₀ κ t) = (⊥ : PrimeSpectrum ↥(CurveModel.chartRing κ ({t} : Set L))) :=
      genericPoint_eq_bot_of_affine (CommRingCat.of ↥(CurveModel.chartRing κ ({t} : Set L)))
    rw [hgen]
    apply PrimeSpectrum.ext
    show Ideal.comap φ ⊥ = RingHom.ker φ
    rw [← RingHom.ker_eq_comap_bot]
  have hζ : ζ = g.base q₀ := by
    rw [hζdef, ← genericPoint_eq_of_isOpenImmersion (CurveModel.ι₀ κ t)]
    show (CurveModel.ι₀ κ t ≫ c).base (genericPoint (CurveModel.X₀ κ t)) = g.base q₀
    rw [← hψg]
    show g.base (ψ.base (genericPoint (CurveModel.X₀ κ t))) = g.base q₀
    rw [hψη]

  have hmaxpt : ∀ z' : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))),
      z' ⤳ ζ → z' = ζ := by
    intro z' hz'
    have hopen : IsOpen (Set.range g.base) := g.isOpenEmbedding.isOpen_range
    have hζmem : ζ ∈ Set.range g.base := ⟨q₀, hζ.symm⟩
    obtain ⟨q', rfl⟩ : z' ∈ Set.range g.base := hz'.mem_open hopen hζmem
    rw [hζ] at hz' ⊢
    have hsp : q' ⤳ q₀ := (g.isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff).mp hz'
    have hle : q'.asIdeal ≤ q₀.asIdeal := (PrimeSpectrum.le_iff_specializes q' q₀).mpr hsp
    have hge : q₀.asIdeal ≤ q'.asIdeal := hmin.2 ⟨q'.isPrime, bot_le⟩ hle
    have heq : q' = q₀ := PrimeSpectrum.ext (le_antisymm hle hge)
    rw [heq]

  have hV : c.base (genericPoint (CurveModel.glued κ t)) ∈ g ''ᵁ ⊤ := by
    show ζ ∈ g ''ᵁ ⊤
    rw [hζ]
    exact ⟨q₀, trivial, rfl⟩
  have hη : (CurveModel.ι₀ κ t).base (genericPoint (CurveModel.X₀ κ t)) = genericPoint (CurveModel.glued κ t) :=
    genericPoint_eq_of_isOpenImmersion (CurveModel.ι₀ κ t)

  let A₀ := ↥(CurveModel.chartRing κ ({t} : Set L))
  letI algA : Algebra A₀ (CurveModel.X₀ κ t).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A₀)
  haveI : IsFractionRing A₀ (CurveModel.X₀ κ t).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of A₀)
  let Y := CurveModel.glued κ t
  let σ : ↥(chartAlgFin R F j) ⊗[R] κ → Γ(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))), g ''ᵁ ⊤) :=
    fun s => (g.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (↥(chartAlgFin R F j) ⊗[R] κ))).inv.hom s)
  let G : ↥(chartAlgFin R F j) ⊗[R] κ → Y.functionField := fun s =>
    (Y.presheaf.germ (c ⁻¹ᵁ (g ''ᵁ ⊤)) (genericPoint Y) hV).hom ((c.app (g ''ᵁ ⊤)).hom (σ s))
  let Ψ : Y.functionField →+* (CurveModel.X₀ κ t).functionField :=
    ((CurveModel.ι₀ κ t).stalkMap (genericPoint (CurveModel.X₀ κ t))).hom.comp
      (Y.presheaf.stalkCongr (.of_eq hη.symm)).hom.hom
  have hΨinj : Function.Injective Ψ := Ψ.injective
  have hΨG : ∀ s, Ψ (G s) = algebraMap A₀ (CurveModel.X₀ κ t).functionField (φ s) := by
    intro s
    have := BirChart.germ_seam R F j κ t φ c g hψg hη hV s
    exact this

  have hgen : ∀ x : Y.functionField, ∃ a b : Γ(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))), g ''ᵁ ⊤),
      Y.presheaf.germ (c ⁻¹ᵁ (g ''ᵁ ⊤)) (genericPoint Y) hV (c.app (g ''ᵁ ⊤) b) ≠ 0 ∧
        x * Y.presheaf.germ (c ⁻¹ᵁ (g ''ᵁ ⊤)) (genericPoint Y) hV (c.app (g ''ᵁ ⊤) b) =
          Y.presheaf.germ (c ⁻¹ᵁ (g ''ᵁ ⊤)) (genericPoint Y) hV (c.app (g ''ᵁ ⊤) a) := by
    intro x

    obtain ⟨r, s₀, hs₀, hrs⟩ := IsFractionRing.div_surjective (A := A₀) (Ψ x)
    have hs₀0 : (s₀ : L) ≠ 0 := fun h => nonZeroDivisors.ne_zero hs₀ (Subtype.ext h)
    obtain ⟨a, b, hb, hab⟩ := hfrac ((r : L) * ((s₀ : L))⁻¹)
    let a' := (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).symm a
    let b' := (Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).symm b
    have hφa : φ a' = θFin a := by
      show θFin ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ) ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).symm a)) = θFin a
      rw [AlgEquiv.apply_symm_apply]
    have hφb : φ b' = θFin b := by
      show θFin ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ) ((Algebra.TensorProduct.comm R ↥(chartAlgFin R F j) κ).symm b)) = θFin b
      rw [AlgEquiv.apply_symm_apply]

    have hA : r * θFin b = s₀ * θFin a := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, ← hab]
      field_simp
    refine ⟨σ a', σ b', ?_, ?_⟩
    · show G b' ≠ 0
      intro h0
      have := hΨG b'
      rw [h0, map_zero, hφb] at this
      exact hb (congrArg Subtype.val ((IsFractionRing.injective A₀ (CurveModel.X₀ κ t).functionField)
        (this.symm.trans (map_zero _).symm)))
    · show x * G b' = G a'
      apply hΨinj
      rw [map_mul, hΨG, hΨG, hφa, hφb]
      have halg0 : algebraMap A₀ (CurveModel.X₀ κ t).functionField s₀ ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs₀
      rw [← hrs, div_mul_eq_mul_div, div_eq_iff halg0, ← map_mul, ← map_mul, hA, mul_comm]
  exact AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div
    c hred hmaxpt (g ''ᵁ ⊤) hV hgen

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes (solution)
