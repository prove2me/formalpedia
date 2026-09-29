-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_structureSheafSections_eq_finrank_span_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7cf2e806-74ef-565e-9eeb-e6e77f2ffa99

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite

namespace CechInKAux

p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]

theorem germ_res_apply' {U V : C.Opens} (h : V ≤ U) (hV : genericPoint C ∈ V) (s : Γ(C, U)) :
    (C.presheaf.germ V (genericPoint C) hV).hom ((C.presheaf.map (homOfLE h).op).hom s) =
      (C.presheaf.germ U (genericPoint C) (h hV)).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]

theorem germ_appLE (U : C.Opens) (hU : genericPoint C ∈ U) (r : Γ(Spec (CommRingCat.of k), ⊤)) :
    (C.presheaf.germ U (genericPoint C) hU).hom ((c.appLE ⊤ U le_top).hom r) =
      (C.presheaf.germ ⊤ (genericPoint C) trivial).hom (c.appTop.hom r) := by
  have : c.appLE ⊤ U le_top = c.appTop ≫ C.presheaf.map (homOfLE le_top).op := rfl
  rw [this, CommRingCat.hom_comp, RingHom.comp_apply]
  exact germ_res_apply' le_top hU _

noncomputable def germLin (U : C.Opens) (hU : genericPoint C ∈ U) :
    letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
    Γ(C, U) →ₗ[k] C.functionField :=
  letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
  { toFun := (C.presheaf.germ U (genericPoint C) hU).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      change (C.presheaf.germ U (genericPoint C) hU).hom (a • x) = a • (C.presheaf.germ U (genericPoint C) hU).hom x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact germ_appLE c U hU _ }

theorem germLin_apply (U : C.Opens) (hU : genericPoint C ∈ U) (s : Γ(C, U)) :
    letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
    germLin c U hU s = (C.presheaf.germ U (genericPoint C) hU).hom s := rfl

theorem germLin_injective (U : C.Opens) (hU : genericPoint C ∈ U) :
    letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
    Function.Injective (germLin c U hU) :=
  germ_injective_of_isIntegral _ _ hU

theorem germLin_res {U V : C.Opens} (h : V ≤ U) (hV : genericPoint C ∈ V) (hU : genericPoint C ∈ U) (s : Γ(C, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom c V; letI := (baseToFunctionField c).toAlgebra
    germLin c V hV ((C.presheaf.map (homOfLE h).op).hom s) = germLin c U hU s :=
  germ_res_apply' h hV s

theorem span_range_germ (U : C.Opens) (hU : genericPoint C ∈ U) :
    letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
    Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom) = LinearMap.range (germLin c U hU) := by
  letI := algebraOfHom c U; letI := (baseToFunctionField c).toAlgebra
  have : Set.range (C.presheaf.germ U (genericPoint C) hU).hom = (LinearMap.range (germLin c U hU) : Set C.functionField) := by
    rw [LinearMap.coe_range]; rfl
  rw [this, Submodule.span_eq]

end CechInKAux

open CechInKAux _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in

theorem solution
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    (𝒱 : C.TwoAffineOpenCover) (h0 : genericPoint C ∈ 𝒱.U0) (h1 : genericPoint C ∈ 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.finrank k (𝒱.structureSheafSections c).H0 =
        Module.finrank k ↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊓
          Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)) ∧
      Module.finrank k (𝒱.structureSheafSections c).H1 =
        Module.finrank k (↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)) ⧸
          (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊔ Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)).comap
            (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)).subtype) := by
  letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have h01 : genericPoint C ∈ 𝒱.U0 ⊓ 𝒱.U1 := ⟨h0, h1⟩
  rw [span_range_germ c 𝒱.U0 h0, span_range_germ c 𝒱.U1 h1, span_range_germ c (𝒱.U0 ⊓ 𝒱.U1) ⟨h0, h1⟩]
  letI i0 := algebraOfHom c 𝒱.U0
  letI i1 := algebraOfHom c 𝒱.U1
  letI i01 := algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  set S := 𝒱.structureSheafSections c with hS
  set γ0 := germLin c 𝒱.U0 h0 with hγ0
  set γ1 := germLin c 𝒱.U1 h1 with hγ1
  set γ01 := germLin c (𝒱.U0 ⊓ 𝒱.U1) ⟨h0, h1⟩ with hγ01

  have hr0 : ∀ a : S.M0, γ01 (S.r0 a) = γ0 a := fun a => germLin_res c inf_le_left h01 h0 a
  have hr1 : ∀ b : S.M1, γ01 (S.r1 b) = γ1 b := fun b => by
    change γ01 (((1 : ((𝒱.cover c).A01)ˣ) : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 b) = γ1 b
    rw [Units.val_one, one_mul]
    exact germLin_res c inf_le_right h01 h1 b
  have hd : ∀ s : S.M0 × S.M1, γ01 (S.cechDiff s) = γ1 s.2 - γ0 s.1 := fun s => by
    rw [TwoChartCech.Sections.cechDiff_apply]
    exact (γ01.map_sub (S.r1 s.2) (S.r0 s.1)).trans (by rw [hr0, hr1])
  constructor
  ·
    have hmem : ∀ s : S.M0 × S.M1, s ∈ S.H0 → γ0 s.1 ∈ LinearMap.range γ0 ⊓ LinearMap.range γ1 := by
      intro s hs
      rw [TwoChartCech.Sections.mem_H0_iff] at hs
      refine ⟨LinearMap.mem_range_self _ _, s.2, ?_⟩
      rw [← hr1, ← hs, hr0]
    let φ : S.H0 →ₗ[k] ↥(LinearMap.range γ0 ⊓ LinearMap.range γ1) :=
      LinearMap.codRestrict _ ((γ0 ∘ₗ LinearMap.fst k S.M0 S.M1) ∘ₗ S.H0.subtype) (fun s => hmem s.1 s.2)
    have hφ : ∀ s : S.H0, (φ s : C.functionField) = γ0 s.1.1 := fun s => rfl
    have hinj : Function.Injective φ := by
      intro s t hst
      have e1 : γ0 s.1.1 = γ0 t.1.1 := by rw [← hφ, ← hφ, hst]
      have hs := (TwoChartCech.Sections.mem_H0_iff S s.1).mp s.2
      have ht := (TwoChartCech.Sections.mem_H0_iff S t.1).mp t.2
      have e2 : γ1 s.1.2 = γ1 t.1.2 := by rw [← hr1, ← hr1, ← hs, ← ht, hr0, hr0, e1]
      exact Subtype.ext (Prod.ext (germLin_injective c _ _ e1) (germLin_injective c _ _ e2))
    have hsurj : Function.Surjective φ := by
      rintro ⟨f, ⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hab : (a, b) ∈ S.H0 := by
        refine (TwoChartCech.Sections.mem_H0_iff S (a, b)).mpr ?_
        apply germLin_injective c _ h01
        change γ01 (S.r0 a) = γ01 (S.r1 b)
        rw [hr0, hr1, hb]
      exact ⟨⟨(a, b), hab⟩, Subtype.ext rfl⟩
    exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  ·
    let e01 : S.M01 ≃ₗ[k] ↥(LinearMap.range γ01) := LinearEquiv.ofInjective γ01 (germLin_injective c _ h01)
    have he01 : ∀ m : S.M01, (e01 m : C.functionField) = γ01 m := fun m => rfl
    refine (Submodule.Quotient.equiv (LinearMap.range S.cechDiff)
      ((LinearMap.range γ0 ⊔ LinearMap.range γ1).comap (LinearMap.range γ01).subtype) e01 ?_).finrank_eq
    ext ⟨f, hf⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, Submodule.mem_sup]
    constructor
    · rintro ⟨m, ⟨s, rfl⟩, hm⟩
      have hm' : γ01 (S.cechDiff s) = f := by rw [← he01]; exact congrArg Subtype.val hm
      refine ⟨-(γ0 s.1), ⟨-s.1, map_neg _ _⟩, γ1 s.2, ⟨s.2, rfl⟩, ?_⟩
      rw [← hm', hd]; abel
    · rintro ⟨y, ⟨a, rfl⟩, z, ⟨b, rfl⟩, hyz⟩
      refine ⟨S.cechDiff (-a, b), ⟨(-a, b), rfl⟩, ?_⟩
      apply Subtype.ext
      change γ01 (S.cechDiff (-a, b)) = f
      rw [hd, map_neg, ← hyz]; abel

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ (solution)
