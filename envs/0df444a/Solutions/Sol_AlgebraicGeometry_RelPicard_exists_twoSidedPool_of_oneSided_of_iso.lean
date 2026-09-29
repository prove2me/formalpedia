-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_twoSidedPool_of_oneSided_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d8a1517b-f008-5944-9bb8-df7847fa0e13

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct

noncomputable section

namespace E9PMerge

variable {R : Type} [CommRing R] {C : Scheme.{0}} {c : C ⟶ Spec (CommRingCat.of R)} {U : C.Opens}
  {ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {σ : C ≅ C} (hσ : σ.hom ≫ c = c)
  (hσε : ε.1 ≫ σ.hom = ε'.1) (hσU : σ.hom ⁻¹ᵁ U = U) [IsSeparated c]
  (hε'U : Set.range ε'.1.base ⊆ (U : Set C)) (f : R)

local notation "L" => Localization.Away f
local notation "XL" => pullback (c) (specMap R (Localization.Away f))
local notation "bcL" => baseChange R (c) (Localization.Away f)

private abbrev wL : XL ⟶ XL := curveChange σ.hom hσ (specMap R (Localization.Away f))

@[reassoc] private theorem wL_fst : wL hσ f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ σ.hom := by
  unfold wL curveChange; rw [pullback.lift_fst]

@[reassoc] private theorem wL_snd : wL hσ f ≫ bcL = bcL := curveChange_snd _ _ _

include hσ in
private theorem hσinv : σ.inv ≫ c = c := by rw [Iso.inv_comp_eq, hσ]

private abbrev wLinv : XL ⟶ XL := curveChange σ.inv (hσinv hσ) (specMap R (Localization.Away f))

@[reassoc] private theorem wLinv_fst : wLinv hσ f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ σ.inv := by
  unfold wLinv curveChange; rw [pullback.lift_fst]

@[reassoc] private theorem wLinv_snd : wLinv hσ f ≫ bcL = bcL := curveChange_snd _ _ _

@[reassoc] private theorem wL_wLinv : wL hσ f ≫ wLinv hσ f = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, wLinv_fst, wL_fst_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, wLinv_snd, wL_snd, Category.id_comp]

@[reassoc] private theorem wLinv_wL : wLinv hσ f ≫ wL hσ f = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, wL_fst, wLinv_fst_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, wL_snd, wLinv_snd, Category.id_comp]

private theorem wLinv_base_wL_base (x : ↥XL) : (wLinv hσ f).base ((wL hσ f).base x) = x := by
  rw [← Scheme.Hom.comp_apply, wL_wLinv]; rfl

private theorem wL_base_wLinv_base (x : ↥XL) : (wL hσ f).base ((wLinv hσ f).base x) = x := by
  rw [← Scheme.Hom.comp_apply, wLinv_wL]; rfl

private theorem wL_base_injective : Function.Injective (wL hσ f).base :=
  Function.LeftInverse.injective (wLinv_base_wL_base hσ f)

include hσε in

private theorem εinf_wL : (sectionBaseChange (Localization.Away f) ε).1 ≫ wL hσ f =
    (sectionBaseChange (Localization.Away f) ε').1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, wL_fst, ← Category.assoc, sectionBaseChange_coe_fst, sectionBaseChange_coe_fst, Category.assoc,
      hσε]
  · rw [Category.assoc, wL_snd]
    exact ((sectionBaseChange (Localization.Away f) ε).2).trans ((sectionBaseChange (Localization.Away f) ε').2).symm

include hσε in
private theorem range_εzero_eq : Set.range (sectionBaseChange (Localization.Away f) ε').1.base =
    (wL hσ f).base '' Set.range (sectionBaseChange (Localization.Away f) ε).1.base := by
  rw [← Set.range_comp, ← εinf_wL hσ hσε f]; rfl

include hσU in
private theorem w_base_mem_smoothLocus {x : ↥C} (hx : x ∈ (U : Set ↥C)) :
    σ.hom.base x ∈ (U : Set ↥C) := by
  have h : x ∈ σ.hom ⁻¹ᵁ U := by rw [hσU]; exact hx
  exact h

include hσU in
private theorem wL_base_mem_preimage_smoothLocus {x : ↥XL}
    (hx : x ∈ ((pullback.fst (c) (specMap R (Localization.Away f)) ⁻¹ᵁ U : (XL).Opens) : Set ↥XL)) :
    (wL hσ f).base x ∈ ((pullback.fst (c) (specMap R (Localization.Away f)) ⁻¹ᵁ U : (XL).Opens) : Set ↥XL) := by
  show (pullback.fst (c) (specMap R (Localization.Away f))).base ((wL hσ f).base x) ∈ (U : Set ↥C)
  rw [← Scheme.Hom.comp_apply, wL_fst, Scheme.Hom.comp_apply]
  exact w_base_mem_smoothLocus hσU hx

private theorem isClosedImmersion_εzero : IsClosedImmersion (sectionBaseChange (Localization.Away f) ε').1 := by
  have : IsClosedImmersion ((sectionBaseChange (Localization.Away f) ε').1 ≫ bcL) := by
    rw [(sectionBaseChange (Localization.Away f) ε').2]; infer_instance
  exact .of_comp _ (bcL)

include hε'U in
private theorem range_εzero_subset : Set.range (sectionBaseChange (Localization.Away f) ε').1.base ⊆
    ((pullback.fst (c) (specMap R (Localization.Away f)) ⁻¹ᵁ U : (XL).Opens) : Set ↥XL) := by
  rintro _ ⟨t, rfl⟩
  show (pullback.fst (c) (specMap R (Localization.Away f))).base ((sectionBaseChange (Localization.Away f) ε').1.base t) ∈ (U : Set ↥C)
  rw [← Scheme.Hom.comp_apply, sectionBaseChange_coe_fst, Scheme.Hom.comp_apply]
  exact hε'U ⟨_, rfl⟩

private theorem eq_sectionFibrePoint_of_mem {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) (bcL)) (y : ↥(pullback (bcL) s))
    (hy : (pullback.fst (bcL) s).base y ∈ Set.range γ.1.base) :
    y = (sectionFibrePoint γ s).1.base (IsLocalRing.closedPoint k) := by

  have hrange := Scheme.Pullback.range_map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1 (𝟙 _) (𝟙 _)
    (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  have hy' : y ∈ Set.range (pullback.map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1 (𝟙 _) (𝟙 _)
      (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])).base := by
    rw [hrange]
    exact ⟨hy, by simp⟩
  obtain ⟨t, rfl⟩ := hy'

  have ht : t = (pullback.lift s (𝟙 _) (by simp)).base (IsLocalRing.closedPoint k) := by
    have hid : pullback.snd (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s ≫ pullback.lift s (𝟙 _) (by simp) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← pullback.condition, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
    have h1 : t = (pullback.lift s (𝟙 _) (by simp)).base ((pullback.snd (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s).base t) := by
      rw [← Scheme.Hom.comp_apply, hid]; rfl
    rw [h1, Subsingleton.elim ((pullback.snd (𝟙 _) s).base t) (IsLocalRing.closedPoint k)]
  have hm : pullback.lift s (𝟙 _) (by simp) ≫ pullback.map (𝟙 (Spec (CommRingCat.of (Localization.Away f)))) s (bcL) s γ.1
      (𝟙 _) (𝟙 _) (by rw [γ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) = (sectionFibrePoint γ s).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp]
      exact (sectionFibrePoint γ s).2.symm
  rw [ht, ← Scheme.Hom.comp_apply, hm]

private abbrev wLs {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    pullback (bcL) s ⟶ pullback (bcL) s :=
  pullback.map (bcL) s (bcL) s (wL hσ f) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (curveChange_snd _ _ _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem wLs_fst {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    wLs hσ f s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ wL hσ f := pullback.lift_fst _ _ _

private abbrev wLsInv {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    pullback (bcL) s ⟶ pullback (bcL) s :=
  pullback.map (bcL) s (bcL) s (wLinv hσ f) (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (curveChange_snd _ _ _).symm) ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem wLsInv_fst {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    wLsInv hσ f s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ wLinv hσ f := pullback.lift_fst _ _ _

private theorem wLsInv_wLs {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))) :
    wLsInv hσ f s ≫ wLs hσ f s = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, wLs_fst, ← Category.assoc, wLsInv_fst, Category.assoc, wLinv_wL, Category.comp_id, Category.id_comp]
  · unfold wLs wLsInv
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.comp_id, Category.comp_id,
      Category.id_comp]

private theorem wLs_base_wLsInv_base {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (bcL) s)) : (wLs hσ f s).base ((wLsInv hσ f s).base y) = y := by
  rw [← Scheme.Hom.comp_apply, wLsInv_wLs]; rfl

end E9PMerge

namespace E9PMerge

variable {R : Type} [CommRing R] {C : Scheme.{0}} {c : C ⟶ Spec (CommRingCat.of R)} {U : C.Opens}
  {ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {σ : C ≅ C} (hσ : σ.hom ≫ c = c)
  (hσε : ε.1 ≫ σ.hom = ε'.1) (hσU : σ.hom ⁻¹ᵁ U = U) [IsSeparated c]
  (hε'U : Set.range ε'.1.base ⊆ (U : Set C)) (f : R)

private scoped instance isIso_wL : IsIso (wL hσ f) := ⟨⟨wLinv hσ f, wL_wLinv hσ f, wLinv_wL hσ f⟩⟩

private theorem range_comp_wL {Y : Scheme.{0}} (g : Y ⟶ pullback (c) (specMap R (Localization.Away f))) :
    Set.range (g ≫ wL hσ f).base = (wL hσ f).base '' Set.range g.base := by
  rw [← Set.range_comp]; rfl

private theorem wLs_fst_base {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange R (c) (Localization.Away f)) s)) :
    (pullback.fst (baseChange R (c) (Localization.Away f)) s).base ((wLs hσ f s).base y) =
      (wL hσ f).base ((pullback.fst (baseChange R (c) (Localization.Away f)) s).base y) := by
  rw [← Scheme.Hom.comp_apply, wLs_fst, Scheme.Hom.comp_apply]

private theorem wLsInv_fst_base {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange R (c) (Localization.Away f)) s)) :
    (pullback.fst (baseChange R (c) (Localization.Away f)) s).base ((wLsInv hσ f s).base y) =
      (wLinv hσ f).base ((pullback.fst (baseChange R (c) (Localization.Away f)) s).base y) := by
  rw [← Scheme.Hom.comp_apply, wLsInv_fst, Scheme.Hom.comp_apply]

section Far

variable {M : ℕ} (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]

private def farB : Fin (M + 1) → Type := Fin.cases (Localization.Away f) B

private scoped instance farCommRing : ∀ i, CommRing (farB f B i) :=
  Fin.cases (inferInstanceAs (CommRing (Localization.Away f))) (fun j => inferInstanceAs (CommRing (B j)))

private scoped instance farAlgebra : ∀ i, Algebra (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Algebra (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Algebra (Localization.Away f) (B j)))

private theorem farFinite [∀ i, Module.Finite (Localization.Away f) (B i)] : ∀ i, Module.Finite (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Module.Finite (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Module.Finite (Localization.Away f) (B j)))

private theorem farEtale [∀ i, Algebra.Etale (Localization.Away f) (B i)] : ∀ i, Algebra.Etale (Localization.Away f) (farB f B i) :=
  Fin.cases (inferInstanceAs (Algebra.Etale (Localization.Away f) (Localization.Away f)))
    (fun j => inferInstanceAs (Algebra.Etale (Localization.Away f) (B j)))

private def farDeg (deg : Fin M → ℕ) : Fin (M + 1) → ℕ := Fin.cases 1 deg

private def farφ (R' : Type) [CommRing R'] [Algebra (Localization.Away f) R'] (deg : Fin M → ℕ)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R')) :
    ∀ i, TensorProduct (Localization.Away f) R' (farB f B i) ≃ₐ[R'] (Fin (farDeg deg i) → R') :=
  Fin.cases ((Algebra.TensorProduct.rid (Localization.Away f) R' R').trans (AlgEquiv.funUnique R' (Fin 1) R').symm)
    (fun j => φ j)

private def farZ (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (c) (specMap R (Localization.Away f))) :
    ∀ i, Spec (CommRingCat.of (farB f B i)) ⟶ pullback (c) (specMap R (Localization.Away f)) :=
  Fin.cases (sectionBaseChange (Localization.Away f) ε').1 (fun j => z j ≫ wL hσ f)

private theorem farZ_isClosedImmersion (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (c) (specMap R (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)] : ∀ i, IsClosedImmersion (farZ hσ f B ε' z i) :=
  Fin.cases (isClosedImmersion_εzero f) (fun j => inferInstanceAs (IsClosedImmersion (z j ≫ wL hσ f)))

@[scoped simp] private theorem farB_zero : farB f B 0 = Localization.Away f := rfl
@[scoped simp] private theorem farB_succ (j : Fin M) : farB f B j.succ = B j := rfl
@[scoped simp] private theorem farDeg_zero (deg : Fin M → ℕ) : farDeg deg 0 = 1 := rfl
@[scoped simp] private theorem farDeg_succ (deg : Fin M → ℕ) (j : Fin M) : farDeg deg j.succ = deg j := rfl
@[scoped simp] private theorem farZ_zero (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (c) (specMap R (Localization.Away f))) :
    farZ hσ f B ε' z 0 = (sectionBaseChange (Localization.Away f) ε').1 := rfl
@[scoped simp] private theorem farZ_succ (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (c) (specMap R (Localization.Away f)))
    (j : Fin M) : farZ hσ f B ε' z j.succ = z j ≫ wL hσ f := rfl

end Far

end E9PMerge
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso.E9PMerge"

open E9PMerge in

theorem solution
    (R : Type) [CommRing R] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (σ : C ≅ C) (hσ : σ.hom ≫ c = c)

    (hσε : ε.1 ≫ σ.hom = ε'.1) (hσU : σ.hom ⁻¹ᵁ U = U)
    [IsSeparated c] (hε'U : Set.range ε'.1.base ⊆ (U : Set C))
    (A₀ B₀ n₀ : ℕ) (f : R)
    (hfar : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f))),
      ¬ Smooth (pullback.snd (baseChange R c (Localization.Away f)) s) →
      (∀ y : ↥(pullback (baseChange R c (Localization.Away f)) s),
        y ∈ connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)) →
        (pullback.map (baseChange R c (Localization.Away f)) s (baseChange R c (Localization.Away f)) s
            (curveChange σ.hom hσ (specMap R (Localization.Away f))) (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (curveChange_snd _ _ _).symm)
            ((Category.comp_id _).trans (Category.id_comp _).symm)).base y ∈
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧
      ((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε') s).1).base (IsLocalRing.closedPoint k) ∈
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)))
    (b M : ℕ) (hM : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) [CommRing R'] [Algebra R R'] [Algebra (Localization.Away f) R'] [IsScalarTower R (Localization.Away f) R']
    [Module.Finite (Localization.Away f) R'] [Algebra.Etale (Localization.Away f) R'] [Module.FaithfullyFlat (Localization.Away f) R']
    (B : Fin M → Type) [∀ i, CommRing (B i)] [∀ i, Algebra (Localization.Away f) (B i)]
    [∀ i, Module.Finite (Localization.Away f) (B i)] [∀ i, Algebra.Etale (Localization.Away f) (B i)]
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) (hdegb : ∀ i, deg i ≤ b)
    (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
    [∀ i, IsClosedImmersion (z i)]
    (hz₁ : ∀ i, z i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B i))
    (hz₂ : ∀ i, Set.range (z i).base ⊆
      ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
        Set ↥(pullback c (specMap R (Localization.Away f)))))
    (hz₃ : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (hz₄ : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
              (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k)))
    (hzinf : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) ε).1.base))
    (hzzero : ∀ i, Disjoint (Set.range (z i).base) (Set.range (sectionBaseChange (Localization.Away f) ε').1.base))
    (hzw : ∀ i j, Disjoint (Set.range (z i).base)
      (Set.range (z j ≫ curveChange σ.hom hσ (specMap R (Localization.Away f))).base)) :
    ∃ (b M M' : ℕ)
      (_ : A₀ * b ^ n₀ + B₀ < M) (_ : A₀ * b ^ n₀ + B₀ < M')
      (R' : Type) (_ : CommRing R') (_ : Algebra R R')
      (_ : Algebra (Localization.Away f) R') (_ : IsScalarTower R (Localization.Away f) R')
      (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
      (_ : Module.FaithfullyFlat (Localization.Away f) R')
      (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
      (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
      (φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
      (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z i))
      (B' : Fin M' → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra (Localization.Away f) (B' i))
      (_ : ∀ i, Module.Finite (Localization.Away f) (B' i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B' i))
      (deg' : Fin M' → ℕ) (_ : ∀ i, 1 ≤ deg' i) (_ : ∀ i, deg' i ≤ b)
      (φ' : ∀ i, TensorProduct (Localization.Away f) R' (B' i) ≃ₐ[R'] (Fin (deg' i) → R'))
      (z' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ pullback c (specMap R (Localization.Away f)))
      (_ : ∀ i, IsClosedImmersion (z' i)),

      (∀ i, z i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
      (∀ i, Set.range (z i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M),
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) ∧

      (∃ j, deg' j ≤ 1) ∧
      (∀ i, z' i ≫ baseChange R c (Localization.Away f) = specMap (Localization.Away f) (B' i)) ∧
      (∀ i, Set.range (z' i).base ⊆
        ((pullback.fst c (specMap R (Localization.Away f)) ⁻¹ᵁ U : (pullback c (specMap R (Localization.Away f))).Opens) :
          Set ↥(pullback c (specMap R (Localization.Away f))))) ∧
      (Pairwise fun i j => Disjoint (Set.range (z' i).base) (Set.range (z' j).base)) ∧
      (∀ i j, Disjoint (Set.range (z i).base) (Set.range (z' j).base)) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
        (i : Fin M'), ¬ Smooth (pullback.snd (baseChange R c (Localization.Away f)) s) →
        (pullback.fst (baseChange R c (Localization.Away f)) s).base ⁻¹' Set.range (z' i).base ⊆
          (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s)) \
          connectedComponentIn
            (((pullback.fst (baseChange R c (Localization.Away f)) s ≫ pullback.fst c (specMap R (Localization.Away f))) ⁻¹ᵁ U :
                (pullback (baseChange R c (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange R c (Localization.Away f)) s))
            (((sectionFibrePoint (sectionBaseChange (Localization.Away f) ε) s).1).base (IsLocalRing.closedPoint k))) := by
  have hM0 : 0 < M := lt_of_le_of_lt (Nat.zero_le _) hM
  have h1b : 1 ≤ b := (hdeg ⟨0, hM0⟩).trans (hdegb ⟨0, hM0⟩)
  refine ⟨b, M, M + 1, hM, Nat.lt_succ_of_lt hM, R', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, B, inferInstance, inferInstance, inferInstance, inferInstance,
    deg, hdeg, hdegb, φ, z, inferInstance, farB f B, inferInstance, inferInstance, farFinite f B, farEtale f B, farDeg deg,
    Fin.cases le_rfl hdeg, Fin.cases h1b hdegb, farφ f B R' deg φ, farZ hσ f B ε' z, farZ_isClosedImmersion hσ f B z,
    hz₁, hz₂, hz₃, hz₄, ⟨0, le_rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine Fin.cases ?_ (fun j => ?_)
    · show (sectionBaseChange (Localization.Away f) ε').1 ≫ _ = Spec.map (CommRingCat.ofHom (RingHom.id _))
      rw [(sectionBaseChange (Localization.Away f) ε').2, CommRingCat.ofHom_id, Spec.map_id]
    · show (z j ≫ wL hσ f) ≫ _ = _
      rw [Category.assoc, wL_snd]
      exact hz₁ j
  ·
    refine Fin.cases (range_εzero_subset hε'U f) (fun j => ?_)
    show Set.range (z j ≫ wL hσ f).base ⊆ _
    rw [range_comp_wL]
    rintro _ ⟨x, hx, rfl⟩
    exact wL_base_mem_preimage_smoothLocus hσ hσU f (hz₂ j hx)
  ·
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        show Disjoint (Set.range (sectionBaseChange (Localization.Away f) ε').1.base) (Set.range (z j ≫ wL hσ f).base)
        rw [range_εzero_eq hσ hσε f, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective hσ f)).2 (hzinf j).symm
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        show Disjoint (Set.range (z i ≫ wL hσ f).base) (Set.range (sectionBaseChange (Localization.Away f) ε').1.base)
        rw [range_εzero_eq hσ hσε f, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective hσ f)).2 (hzinf i)
      | succ j =>
        show Disjoint (Set.range (z i ≫ wL hσ f).base) (Set.range (z j ≫ wL hσ f).base)
        rw [range_comp_wL, range_comp_wL]
        exact (Set.disjoint_image_iff (wL_base_injective hσ f)).2 (hz₃ fun h => hij (congrArg Fin.succ h))
  ·
    intro i j
    induction j using Fin.cases with
    | zero => exact hzzero i
    | succ j => exact hzw i j
  ·
    intro k _ _ s i hns
    induction i using Fin.cases with
    | zero =>
      intro y hy
      rw [eq_sectionFibrePoint_of_mem f s (sectionBaseChange (Localization.Away f) ε') y hy]
      exact (hfar k s hns).2
    | succ j =>
      intro y hy
      change (pullback.fst (baseChange R (c) (Localization.Away f)) s).base y ∈
        Set.range (z j ≫ wL hσ f).base at hy
      rw [range_comp_wL] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hy₀ : (pullback.fst (baseChange R (c) (Localization.Away f)) s).base ((wLsInv hσ f s).base y) ∈
          Set.range (z j).base := by
        rw [wLsInv_fst_base, ← hxy, wLinv_base_wL_base]
        exact hx
      have key := (hfar k s hns).1 ((wLsInv hσ f s).base y) (hz₄ k s j hy₀)
      rwa [wLs_base_wLsInv_base] at key

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso.E9PMerge"

end S_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_twoSidedPool_of_oneSided_of_iso (solution)
