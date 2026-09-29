-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7a6d77c3-5545-5c01-8658-1187c2c6c28b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

noncomputable section

namespace LevelFibreLaw
set_option backward.isDefEq.respectTransparency false

section generic
universe v u
variable {C : Type u} [Category.{v} C]

theorem isSplitMono_of_comp_eq {X Y Z : C} (φ : X ⟶ Y) (g : Y ⟶ Z) (ι : X ⟶ Z) [IsIso ι] (h : φ ≫ g = ι) :
    IsSplitMono φ :=
  IsSplitMono.mk' ⟨g ≫ inv ι, by rw [← Category.assoc, h, IsIso.hom_inv_id]⟩

theorem isIso_of_comp_eq_of_mono {X Y Z : C} (φ : X ⟶ Y) (g : Y ⟶ Z) (ι : X ⟶ Z) [IsIso ι] [Mono g]
    (h : φ ≫ g = ι) : IsIso φ := by
  refine ⟨⟨g ≫ inv ι, by rw [← Category.assoc, h, IsIso.hom_inv_id], ?_⟩⟩
  apply (cancel_mono (g ≫ inv ι)).1
  rw [Category.assoc, Category.id_comp, ← Category.assoc φ g (inv ι), h, IsIso.hom_inv_id, Category.comp_id]

end generic

section fib
variable {A : Scheme.{0}}

theorem fib_mapComp_inv_app (a b : A ⟶ A) (N : A.Modules) :
    (Scheme.Modules.fibration.mapComp b.op.toLoc a.op.toLoc).inv.toNatTrans.app N =
      (Scheme.Modules.pullbackComp a b).hom.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]
  rfl

theorem fib_mapId_inv_app (N : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).inv.toNatTrans.app N = (Scheme.Modules.pullbackId A).inv.app N := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]

theorem pullbackCongr_hom_app {X Y : Scheme.{0}} {b c : X ⟶ Y} (h : b = c) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackCongr_inv_app {X Y : Scheme.{0}} {b c : X ⟶ Y} (h : b = c) (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app N = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

variable (M : A.Modules)

theorem id_fiber_eq :
    (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).fiber =
      (Scheme.Modules.pullbackId A).inv.app M := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_base, modulePair_fiber, fib_mapId_inv_app]

theorem isIso_fiber (a : Aut (modulePair (A := A) M)) :
    IsIso (show M ⟶ (Scheme.Modules.pullback a.hom.base).obj M from a.hom.fiber) := by
  obtain ⟨u, v, h1, h2⟩ := a
  obtain ⟨b, φ⟩ := u
  obtain ⟨b', φ'⟩ := v
  have e1 := Pseudofunctor.CoGrothendieck.Hom.congr h1
  have e2 := Pseudofunctor.CoGrothendieck.Hom.congr h2
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber,
    Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, modulePair_fiber, modulePair_base,
    Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app, fib_mapId_inv_app] at e1 e2
  change IsIso φ
  have sm' : IsSplitMono φ' := isSplitMono_of_comp_eq φ' _ _ e2
  haveI : Mono ((Scheme.Modules.pullback b).map φ') := (sm'.exists_splitMono.some.map (Scheme.Modules.pullback b)).mono
  exact isIso_of_comp_eq_of_mono φ _ _ e1

def fibreIso (a : Aut (modulePair (A := A) M)) {T : A ⟶ A} (h : a.hom.base = T) :
    M ≅ (Scheme.Modules.pullback T).obj M :=
  @asIso _ _ _ _ (show M ⟶ (Scheme.Modules.pullback a.hom.base).obj M from a.hom.fiber) (isIso_fiber M a) ≪≫
    (Scheme.Modules.pullbackCongr h).app M

theorem fibreIso_hom (a : Aut (modulePair (A := A) M)) {T : A ⟶ A} (h : a.hom.base = T) :
    (fibreIso M a h).hom = (show M ⟶ (Scheme.Modules.pullback a.hom.base).obj M from a.hom.fiber) ≫
      (Scheme.Modules.pullbackCongr h).hom.app M := rfl

theorem fibreIso_congr {a a' : Aut (modulePair (A := A) M)} (e : a = a') {T : A ⟶ A} (h : a.hom.base = T)
    (h' : a'.hom.base = T) : fibreIso M a h = fibreIso M a' h' := by
  subst e
  rfl

theorem fibreIso_one {T : A ⟶ A} (h : (1 : Aut (modulePair (A := A) M)).hom.base = T) (hT : T = 𝟙 A) :
    fibreIso M 1 h = ((Scheme.Modules.pullbackId A).app M).symm ≪≫ ((Scheme.Modules.pullbackCongr hT).app M).symm := by
  subst hT
  ext : 1
  simp only [fibreIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, pullbackCongr_hom_app, pullbackCongr_inv_app]
  change (𝟙 (modulePair (A := A) M) : modulePair (A := A) M ⟶ modulePair (A := A) M).fiber ≫ _ = _
  rw [id_fiber_eq]

theorem comp_fiber_congr (u v : modulePair (A := A) M ⟶ modulePair (A := A) M) {T T' T'' : A ⟶ A}
    (h : u.base = T) (h' : v.base = T') (hh : (u ≫ v).base = T'') (e : T'' = T ≫ T') :
    (u ≫ v).fiber ≫ (Scheme.Modules.pullbackCongr hh).hom.app M ≫ (Scheme.Modules.pullbackCongr e).hom.app M =
      ((show M ⟶ (Scheme.Modules.pullback u.base).obj M from u.fiber) ≫ (Scheme.Modules.pullbackCongr h).hom.app M) ≫
        (Scheme.Modules.pullback T).map
          ((show M ⟶ (Scheme.Modules.pullback v.base).obj M from v.fiber) ≫ (Scheme.Modules.pullbackCongr h').hom.app M) ≫
        (Scheme.Modules.pullbackComp T T').hom.app M := by
  obtain ⟨b, φ⟩ := u
  obtain ⟨b', φ'⟩ := v
  change b = T at h
  change b' = T' at h'
  subst h h'
  change b ≫ b' = T'' at hh
  subst hh
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, Pseudofunctor.CoGrothendieck.categoryStruct_comp_base,
    modulePair_fiber, Scheme.Modules.fibration_map_toFunctor, fib_mapComp_inv_app, pullbackCongr_hom_app, eqToHom_refl,
    Category.comp_id]

theorem fibreIso_mul (a a' : Aut (modulePair (A := A) M)) {T T' T'' : A ⟶ A}
    (h : a.hom.base = T) (h' : a'.hom.base = T') (hh : (a' * a).hom.base = T'') (e : T'' = T ≫ T') :
    fibreIso M (a' * a) hh =
      fibreIso M a h ≪≫ (Scheme.Modules.pullback T).mapIso (fibreIso M a' h') ≪≫ (Scheme.Modules.pullbackComp T T').app M ≪≫
        ((Scheme.Modules.pullbackCongr e).app M).symm := by
  ext : 1
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, fibreIso_hom]
  rw [← cancel_mono ((Scheme.Modules.pullbackCongr e).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact comp_fiber_congr M a.hom a'.hom h h' hh e

end fib

section level
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ)
  (K : Subgroup (thetaGroup f L hc M))
  (hKpt : ∀ Q : L.AlgPoints hc k, (∃ g ∈ K, thetaGroup.pt f L hc M g = Multiplicative.ofAdd Q) ↔ n • Q = 0)

def gOf (P : L.AlgPoints hc k) (hP : n • P = 0) : thetaGroup f L hc M := ((hKpt P).mpr hP).choose

theorem gOf_mem (P : L.AlgPoints hc k) (hP : n • P = 0) : gOf f L hc M n K hKpt P hP ∈ K :=
  ((hKpt P).mpr hP).choose_spec.1

theorem pt_gOf (P : L.AlgPoints hc k) (hP : n • P = 0) :
    thetaGroup.pt f L hc M (gOf f L hc M n K hKpt P hP) = Multiplicative.ofAdd P :=
  ((hKpt P).mpr hP).choose_spec.2

theorem base_gOf (P : L.AlgPoints hc k) (hP : n • P = 0) :
    (gOf f L hc M n K hKpt P hP).1.1.hom.base = translation f L (RelativeGroupLaw.AlgPoints.toPoint P) := by
  rw [thetaGroup.base_eq f L hc M]
  have h := pt_gOf f L hc M n K hKpt P hP
  rw [thetaGroup.pt_apply] at h
  rw [h, toAdd_ofAdd]

include hKpt in
theorem main
    (hKinj : ∀ g ∈ K, ∀ h ∈ K, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h → g = h) :
    ∃ ψ : ∀ P : L.AlgPoints hc k, n • P = 0 →
        (M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).obj M),
      (∀ h0 : n • (0 : L.AlgPoints hc k) = 0,
        ψ 0 h0 = ((Scheme.Modules.pullbackId A).app M).symm ≪≫
          ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
              (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).app M ≪≫
            ((Scheme.Modules.pullbackCongr (translation_toPoint_add f L hc P Q)).app M).symm) := by
  refine ⟨fun P hP => fibreIso M (gOf f L hc M n K hKpt P hP).1.1 (base_gOf f L hc M n K hKpt P hP),
    fun h0 => ?_, fun P Q hP hQ hPQ => ?_⟩
  · have e0 : gOf f L hc M n K hKpt 0 h0 = 1 :=
      hKinj _ (gOf_mem f L hc M n K hKpt 0 h0) _ K.one_mem (by rw [pt_gOf, map_one, ofAdd_zero])
    dsimp only
    rw [fibreIso_congr M (show (gOf f L hc M n K hKpt 0 h0).1.1 = (1 : Aut (modulePair (A := A) M)) from
      congrArg (fun g : thetaGroup f L hc M => g.1.1) e0) (base_gOf f L hc M n K hKpt 0 h0)
      ((translation_toPoint_zero f L hc).symm)]
    exact fibreIso_one M _ _
  · have e : gOf f L hc M n K hKpt (P + Q) hPQ = gOf f L hc M n K hKpt Q hQ * gOf f L hc M n K hKpt P hP :=
      hKinj _ (gOf_mem f L hc M n K hKpt _ hPQ) _ (K.mul_mem (gOf_mem f L hc M n K hKpt Q hQ) (gOf_mem f L hc M n K hKpt P hP))
        (by rw [pt_gOf, map_mul, pt_gOf, pt_gOf, ← ofAdd_add, add_comm])
    have hh : ((gOf f L hc M n K hKpt Q hQ).1.1 * (gOf f L hc M n K hKpt P hP).1.1).hom.base =
        translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)) := by
      change (gOf f L hc M n K hKpt P hP).1.1.hom.base ≫ (gOf f L hc M n K hKpt Q hQ).1.1.hom.base = _
      rw [base_gOf, base_gOf, ← translation_toPoint_add]
    dsimp only
    rw [fibreIso_congr M (show (gOf f L hc M n K hKpt (P + Q) hPQ).1.1 =
        (gOf f L hc M n K hKpt Q hQ).1.1 * (gOf f L hc M n K hKpt P hP).1.1 from
      congrArg (fun g : thetaGroup f L hc M => g.1.1) e) (base_gOf f L hc M n K hKpt (P + Q) hPQ) hh]
    exact fibreIso_mul M (gOf f L hc M n K hKpt P hP).1.1 (gOf f L hc M n K hKpt Q hQ).1.1
      (base_gOf f L hc M n K hKpt P hP) (base_gOf f L hc M n K hKpt Q hQ) hh (translation_toPoint_add f L hc P Q)

end level

end LevelFibreLaw

end

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ)
    (K : Subgroup (thetaGroup f L hc M))
    (hKinj : ∀ g ∈ K, ∀ h ∈ K, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h → g = h)
    (hKpt : ∀ Q : L.AlgPoints hc k, (∃ g ∈ K, thetaGroup.pt f L hc M g = Multiplicative.ofAdd Q) ↔ n • Q = 0) :
    ∃ ψ : ∀ P : L.AlgPoints hc k, n • P = 0 →
        (M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).obj M),
      (∀ h0 : n • (0 : L.AlgPoints hc k) = 0,
        ψ 0 h0 = ((Scheme.Modules.pullbackId A).app M).symm ≪≫
          ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
              (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).app M ≪≫
            ((Scheme.Modules.pullbackCongr (translation_toPoint_add f L hc P Q)).app M).symm) :=
  LevelFibreLaw.main f L hc M n K hKpt hKinj

end S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_iso_pullback_translation_of_injOn_pt_of_range_pt_eq_torsion (solution)
