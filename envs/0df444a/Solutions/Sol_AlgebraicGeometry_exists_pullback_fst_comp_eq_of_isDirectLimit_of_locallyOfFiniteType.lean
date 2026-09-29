-- Prove2me | solution 1 for AlgebraicGeometry.exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7e769602-4554-5142-8aed-5decfce4c1b7

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry Opposite"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp quasiSeparatedSpace_of_quasiSeparated isAffineHom_of_isAffine QuasiCompact LocallyOfFiniteType Spec Spec.map Scheme Scheme.Spec QuasiSeparated IsAffineHom Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType"
namespace IsDirectLimitStages
p2m_open "AlgebraicGeometry"

variable {ι : Type u} [Preorder ι]
  {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => ⇑(φ i j h)]
  {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)

theorem φ_self (i : ι) (x : G i) : φ i i le_rfl x = x :=
  DirectedSystem.map_self (f := fun i j (h : i ≤ j) => ⇑(φ i j h)) x

theorem φ_trans {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i) : φ j k hjk (φ i j hij x) = φ i k (hij.trans hjk) x :=
  DirectedSystem.map_map (f := fun i j (h : i ≤ j) => ⇑(φ i j h)) hij hjk x

def ringDiag : ι ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (G i)
  map {i j} h := CommRingCat.ofHom (φ i j h.le)
  map_id i := by ext x; exact φ_self φ i x
  map_comp {i j k} h₁ h₂ := by ext x; exact (φ_trans φ h₁.le h₂.le x).symm

@[scoped simp] theorem ringDiag_obj (i : ι) : (ringDiag φ).obj i = CommRingCat.of (G i) := rfl
@[scoped simp] theorem ringDiag_map {i j : ι} (h : i ⟶ j) : (ringDiag φ).map h = CommRingCat.ofHom (φ i j h.le) := rfl

variable (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))

def ringCocone : Cocone (ringDiag φ) where
  pt := CommRingCat.of R
  ι := { app := fun i => CommRingCat.ofHom (g i)
         naturality := fun {i j} h => by
           ext x
           simp only [Functor.const_obj_obj, ringDiag_map, CommRingCat.hom_comp, Functor.const_obj_map,
             Category.comp_id]
           exact hR.compatibility i j h.le x }

@[scoped simp] theorem ringCocone_pt : (ringCocone φ g hR).pt = CommRingCat.of R := rfl
@[scoped simp] theorem ringCocone_ι_app (i : ι) : (ringCocone φ g hR).ι.app i = CommRingCat.ofHom (g i) := rfl

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

section Desc

variable (s : Cocone (ringDiag φ))

def descFun (r : R) : s.pt :=
  (s.ι.app (hR.surj r).choose).hom (hR.surj r).choose_spec.choose

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
theorem cocone_w_apply {i j : ι} (h : i ≤ j) (x : G i) : (s.ι.app j).hom (φ i j h x) = (s.ι.app i).hom x := by
  have := s.w (homOfLE h)
  rw [← this]
  rfl

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
theorem descFun_apply (i : ι) (x : G i) : descFun φ g hR s (g i x) = (s.ι.app i).hom x := by
  unfold descFun
  set j := (hR.surj (g i x)).choose
  have hy : g j (hR.surj (g i x)).choose_spec.choose = g i x := (hR.surj (g i x)).choose_spec.choose_spec
  set y := (hR.surj (g i x)).choose_spec.choose
  obtain ⟨k, hjk, hik, hk⟩ := hR.inj j i y x hy
  rw [← cocone_w_apply φ s hjk, ← cocone_w_apply φ s hik, hk]

omit [Nonempty ι] in
include hR in
theorem exists_common (r r' : R) : ∃ (k : ι) (x x' : G k), g k x = r ∧ g k x' = r' := by
  obtain ⟨i, x, rfl⟩ := hR.surj r
  obtain ⟨j, y, rfl⟩ := hR.surj r'
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  exact ⟨k, φ i k hik x, φ j k hjk y, hR.compatibility i k hik x, hR.compatibility j k hjk y⟩

def descHom : R →+* s.pt where
  toFun := descFun φ g hR s
  map_one' := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have h1 : (1 : R) = g i 1 := (map_one _).symm
    rw [h1, descFun_apply]; exact map_one (s.ι.app i).hom
  map_mul' r r' := by
    obtain ⟨k, x, x', rfl, rfl⟩ := exists_common φ g hR r r'
    rw [← (g k).map_mul, descFun_apply, descFun_apply, descFun_apply]; exact map_mul (s.ι.app k).hom x x'
  map_zero' := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have h0 : (0 : R) = g i 0 := (map_zero _).symm
    rw [h0, descFun_apply]; exact map_zero (s.ι.app i).hom
  map_add' r r' := by
    obtain ⟨k, x, x', rfl, rfl⟩ := exists_common φ g hR r r'
    rw [← (g k).map_add, descFun_apply, descFun_apply, descFun_apply]; exact map_add (s.ι.app k).hom x x'

end Desc

def ringCoconeIsColimit : IsColimit (ringCocone φ g hR) where
  desc s := CommRingCat.ofHom (descHom φ g hR s)
  fac s i := by
    ext x
    exact descFun_apply φ g hR s i x
  uniq s m hm := by
    ext r
    obtain ⟨i, x, rfl⟩ := hR.surj r
    have := congrArg (fun q => (q : CommRingCat.of (G i) ⟶ s.pt) x) (hm i)
    simp only [ringCocone_ι_app] at this
    exact this.trans (descFun_apply φ g hR s i x).symm

def specDiag : ιᵒᵖ ⥤ Scheme.{u} := (ringDiag φ).op ⋙ Scheme.Spec

def specCone : Cone (specDiag φ) := Scheme.Spec.mapCone (ringCocone φ g hR).op

def specConeIsLimit : IsLimit (specCone φ g hR) :=
  isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit φ g hR).op

@[scoped simp] theorem specDiag_obj (j : ιᵒᵖ) : (specDiag φ).obj j = Spec (CommRingCat.of (G j.unop)) := rfl
@[scoped simp] theorem specDiag_map {j k : ιᵒᵖ} (h : j ⟶ k) :
    (specDiag φ).map h = Spec.map (CommRingCat.ofHom (φ k.unop j.unop h.unop.le)) := rfl
@[scoped simp] theorem specCone_pt : (specCone φ g hR).pt = Spec (CommRingCat.of R) := rfl
@[scoped simp] theorem specCone_π_app (j : ιᵒᵖ) : (specCone φ g hR).π.app j = Spec.map (CommRingCat.ofHom (g j.unop)) := rfl

variable (i : ι) {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (G i)))

abbrev J := Over (op i)

abbrev idx {i : ι} (X : J i) : ι := X.left.unop

theorem le_idx {i : ι} (X : J i) : i ≤ idx X := X.hom.unop.le

def stageDiag : J i ⥤ Scheme.{u} :=
  Over.post (specDiag φ) ⋙ Over.pullback w ⋙ Over.forget W

def stageCone : Cone (stageDiag φ i w) :=
  (Over.pullback w ⋙ Over.forget W).mapCone ((Over.conePost (specDiag φ) (op i)).obj (specCone φ g hR))

attribute [local instance] IsCofiltered.isConnected

def stageConeIsLimit : IsLimit (stageCone φ g hR i w) :=
  isLimitOfPreserves (Over.pullback w ⋙ Over.forget W) (Over.isLimitConePost (op i) (specConeIsLimit φ g hR))

abbrev trS {i : ι} (X : J i) : (Spec (CommRingCat.of (G (idx X))) : Scheme.{u}) ⟶ Spec (CommRingCat.of (G i)) :=
  Spec.map (CommRingCat.ofHom (φ i (idx X) (le_idx X)))

abbrev spS (j : ι) : (Spec (CommRingCat.of R) : Scheme.{u}) ⟶ Spec (CommRingCat.of (G j)) :=
  Spec.map (CommRingCat.ofHom (g j))

theorem stageDiag_obj (X : J i) : (stageDiag φ i w).obj X = pullback (trS φ X) w := rfl

theorem stageCone_pt : (stageCone φ g hR i w).pt = pullback (spS g i) w := rfl

theorem stageDiag_map_fst {X Y : J i} (f : X ⟶ Y) :
    (stageDiag φ i w).map f ≫ pullback.fst (trS φ Y) w =
      pullback.fst (trS φ X) w ≫ Spec.map (CommRingCat.ofHom (φ (idx Y) (idx X) f.left.unop.le)) := by
  simp only [stageDiag, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem stageDiag_map_snd {X Y : J i} (f : X ⟶ Y) :
    (stageDiag φ i w).map f ≫ pullback.snd (trS φ Y) w = pullback.snd (trS φ X) w := by
  simp only [stageDiag, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

theorem stageCone_π_app_fst (X : J i) :
    (stageCone φ g hR i w).π.app X ≫ pullback.fst (trS φ X) w = pullback.fst (spS g i) w ≫ spS g (idx X) := by
  simp only [stageCone, Functor.mapCone_π_app, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem stageCone_π_app_snd (X : J i) :
    (stageCone φ g hR i w).π.app X ≫ pullback.snd (trS φ X) w = pullback.snd (spS g i) w := by
  simp only [stageCone, Functor.mapCone_π_app, Functor.comp_map, Over.forget_map, Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

def stageOver : stageDiag φ i w ⟶ (Functor.const (J i)).obj (Spec (CommRingCat.of (G i))) where
  app X := pullback.snd (trS φ X) w ≫ w
  naturality {X Y} f := by
    show (stageDiag φ i w).map f ≫ pullback.snd (trS φ Y) w ≫ w = (pullback.snd (trS φ X) w ≫ w) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, stageDiag_map_snd]
    rfl

theorem stageOver_app (X : J i) : (stageOver φ i w).app X = pullback.snd (trS φ X) w ≫ w := rfl

theorem isPullback_stageDiag_map {X Y : J i} (f : X ⟶ Y) :
    IsPullback (pullback.fst (trS φ X) w) ((stageDiag φ i w).map f)
      (Spec.map (CommRingCat.ofHom (φ (idx Y) (idx X) f.left.unop.le))) (pullback.fst (trS φ Y) w) := by
  refine IsPullback.of_bot ?_ (stageDiag_map_fst φ i w f).symm (IsPullback.of_hasPullback (trS φ Y) w)
  erw [stageDiag_map_snd]
  have : Spec.map (CommRingCat.ofHom (φ (idx Y) (idx X) f.left.unop.le)) ≫ trS φ Y = trS φ X := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => φ_trans φ _ _ x
  rw [this]
  exact IsPullback.of_hasPullback _ _

scoped instance isAffineHom_stageDiag_map {X Y : J i} (f : X ⟶ Y) : IsAffineHom ((stageDiag φ i w).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_stageDiag_map φ i w f)
    (isAffineHom_of_isAffine _)

scoped instance compactSpace_stageDiag_obj [QuasiCompact w] (X : J i) : CompactSpace ((stageDiag φ i w).obj X) := by
  rw [stageDiag_obj]; infer_instance

scoped instance quasiSeparatedSpace_stageDiag_obj [QuasiSeparated w] (X : J i) :
    QuasiSeparatedSpace ((stageDiag φ i w).obj X) := by
  rw [stageDiag_obj]
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

include hR in

theorem exists_fst_comp_eq {V : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of (G i)))
    [QuasiCompact w] [LocallyOfFiniteType v] (a b : W ⟶ V) (ha : a ≫ v = w) (hb : b ≫ v = w)
    (hab : pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ a = pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ b) :
    ∃ (j : ι) (hij : i ≤ j),
      pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ a =
        pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ b := by
  let X₀ : J i := Over.mk (𝟙 (op i))
  obtain ⟨X, f, hf⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (stageDiag φ i w)
    (stageOver φ i w) v (stageCone φ g hR i w) (stageConeIsLimit φ g hR i w) (i := X₀)
    (pullback.snd (trS φ X₀) w ≫ a) (pullback.snd (trS φ X₀) w ≫ b)
    (by rw [stageOver_app, Category.assoc, ha]; rfl) (by rw [stageOver_app, Category.assoc, hb]; rfl) (by
      have e := stageCone_π_app_snd φ g hR i w X₀
      have e' : pullback.snd (spS g i) w ≫ a = pullback.snd (spS g i) w ≫ b := by
        rw [← pullbackSymmetry_hom_comp_fst, Category.assoc, Category.assoc]
        exact congrArg (fun q => (pullbackSymmetry (spS g i) w).hom ≫ q) hab
      have s1 : (stageCone φ g hR i w).π.app X₀ ≫ pullback.snd (trS φ X₀) w ≫ a = pullback.snd (spS g i) w ≫ a := by
        rw [← e]; exact (Category.assoc _ _ _).symm
      have s2 : (stageCone φ g hR i w).π.app X₀ ≫ pullback.snd (trS φ X₀) w ≫ b = pullback.snd (spS g i) w ≫ b := by
        rw [← e]; exact (Category.assoc _ _ _).symm
      exact s1.trans (e'.trans s2.symm))
  refine ⟨idx X, le_idx X, ?_⟩
  have e := stageDiag_map_snd φ i w f
  have h1 : pullback.snd (trS φ X) w ≫ a = (stageDiag φ i w).map f ≫ pullback.snd (trS φ X₀) w ≫ a := by
    rw [← e]; exact Category.assoc _ _ _
  have h2 : pullback.snd (trS φ X) w ≫ b = (stageDiag φ i w).map f ≫ pullback.snd (trS φ X₀) w ≫ b := by
    rw [← e]; exact Category.assoc _ _ _
  have hf' : pullback.snd (trS φ X) w ≫ a = pullback.snd (trS φ X) w ≫ b := h1.trans (hf.trans h2.symm)
  rw [← pullbackSymmetry_inv_comp_snd, Category.assoc, Category.assoc, hf']

end AlgebraicGeometry.IsDirectLimitStages
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry.IsDirectLimitStages"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType.AlgebraicGeometry.IsDirectLimitStages"

theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {W V : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of (G i))) (v : V ⟶ Spec (CommRingCat.of (G i)))
    [QuasiCompact w] [LocallyOfFiniteType v] (a b : W ⟶ V) (ha : a ≫ v = w) (hb : b ≫ v = w)
    (hab : pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ a =
      pullback.fst w (Spec.map (CommRingCat.ofHom (g i))) ≫ b) :
    ∃ (j : ι) (hij : i ≤ j),
      pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ a =
        pullback.fst w (Spec.map (CommRingCat.ofHom (φ i j hij))) ≫ b :=
  AlgebraicGeometry.IsDirectLimitStages.exists_fst_comp_eq φ g hR i w v a b ha hb hab

end S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType (solution)
