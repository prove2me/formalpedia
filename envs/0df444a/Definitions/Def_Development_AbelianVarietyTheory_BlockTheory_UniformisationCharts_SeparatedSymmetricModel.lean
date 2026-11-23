-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_SeparatedSymmetricModel
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_SeparatedSymmetricModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:42:26.266083+00:00
-- url     : https://prove2.me/theorems/656d9a1f-bf80-47a3-b491-ad3599f4499c
-- title:
--   Separated Symmetric Model
-- statement:
--   Definitions and structural lemmas for Separated Symmetric Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/SeparatedSymmetricModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_CanonicalRigidImages
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel
section BaseChange
variable {S S' : Scheme.{0}} (p : S' ⟶ S)
def dn {G : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) :
    Over.mk (T.hom ≫ p) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom p) (by
    have h := Over.w y
    dsimp at h ⊢
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])
@[simp] lemma dn_left {G : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) :
    (dn p y).left = y.left ≫ pullback.fst G.hom p := rfl
lemma dn_map {G G' : Over S} {T : Over S'} (y : T ⟶ (Over.pullback p).obj G) (f : G ⟶ G') :
    dn p (y ≫ (Over.pullback p).map f) = dn p y ≫ f := by
  ext
  have h : ((Over.pullback p).map f).left ≫ pullback.fst G'.hom p =
      pullback.fst G.hom p ≫ f.left := pullback.lift_fst _ _ _
  change (y.left ≫ ((Over.pullback p).map f).left) ≫ pullback.fst G'.hom p =
    (y.left ≫ pullback.fst G.hom p) ≫ f.left
  rw [Category.assoc, Category.assoc, h]
variable {G : Over S} [GrpObj G] [IsCommMonObj G]
instance isComm_baseChange : IsCommMonObj ((Over.pullback p).obj G) :=
  Functor.isCommMonObj_obj
lemma dn_padd {T : Over S'} (a b : T ⟶ (Over.pullback p).obj G) :
    dn p (padd _ a b) = padd G (dn p a) (dn p b) := by
  rw [padd, padd, Functor.obj.μ_def, ← Category.assoc, dn_map]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_fst, lift_fst, lift_fst]
  · rw [← dn_map, Category.assoc, Functor.Monoidal.μ_snd, lift_snd, lift_snd]
lemma dn_pzero (T : Over S') : dn p (pzero ((Over.pullback p).obj G) T) = pzero G _ := by
  rw [pzero, pzero, Functor.obj.η_def, ← Category.assoc, dn_map]
  congr 1
  exact toUnit_unique _ _
lemma dn_foldr {T : Over S'} {n : ℕ} (x : Fin n → (T ⟶ (Over.pullback p).obj G))
    (l : List (Fin n)) :
    dn p (l.foldr (fun k acc => padd _ (x k) acc) (pzero _ T)) =
      l.foldr (fun k acc => padd G (dn p (x k)) acc) (pzero G _) := by
  induction l with
  | nil => exact dn_pzero p T
  | cons a l ih => simp only [List.foldr_cons]; rw [dn_padd, ih]
variable {H : Over S'} [GrpObj H] [IsCommMonObj H]
def dn3 (f : H ⟶ (Over.pullback p).obj G) : Over.mk ((G3 H).hom ≫ p) ⟶ G3 G :=
  lift (dn p (x3 H 0 ≫ f)) (lift (dn p (x3 H 1 ≫ f)) (dn p (x3 H 2 ≫ f)))
omit [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] in
lemma downThree_comp_proj (f : H ⟶ (Over.pullback p).obj G) (k : Fin 3) :
    dn3 p f ≫ x3 G k = dn p (x3 H k ≫ f) := by
  fin_cases k <;> simp [x3, dn3]
def bcMap (f : H ⟶ (Over.pullback p).obj G) [IsMonHom f] : CubeMap H G where
  F := (dn p f).left
  F3 := (dn3 p f).left
  e := p
  e_comm := by
    have h1 : eSec H ≫ (dn p f).left = (dn p (η[H] ≫ f)).left :=
      (Category.assoc _ _ _).symm
    have h2 : η[H] ≫ f = pzero _ (𝟙_ (Over S')) := by
      rw [IsMonHom.one_hom, pzero, toUnit_unit, Category.id_comp]
    rw [h1, h2, dn_pzero, pzero, Over.comp_left, eSec]
    congr 1
  psum_comm := fun I => by
    have h1 : (psum H (x3 H) I).left ≫ (dn p f).left = (dn p (psum H (x3 H) I ≫ f)).left := by
      simp
    have h2 : (dn3 p f).left ≫ (psum G (x3 G) I).left = (dn3 p f ≫ psum G (x3 G) I).left := rfl
    rw [h1, h2]
    congr 1
    simp only [psum]
    rw [foldr_padd_comp, dn_foldr, ← foldr_padd_pre]
    simp only [downThree_comp_proj]
omit [IsCommMonObj G] [IsCommMonObj H] in
lemma inv_dn (f : H ⟶ (Over.pullback p).obj G) [IsMonHom f] :
    (ι[H]).left ≫ (dn p f).left = (dn p f).left ≫ (ι[G]).left := by
  have h1 : (ι[H]).left ≫ (dn p f).left = (dn p (ι[H] ≫ f)).left :=
    (Category.assoc _ _ _).symm
  rw [h1, GrpObj.inv_hom, Functor.obj.ι_def, dn_map]
  rfl
end BaseChange
section Sym
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
abbrev SymGen (L : LB G.left) :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
variable {G} {S' : Scheme.{0}} {H : Over S'} [GrpObj H]
lemma symPull_le (F : H.left ⟶ G.left) (hF : (ι[H]).left ≫ F = F ≫ (ι[G]).left) (L : LB G.left)
    (j : Fin 2 → PUnit → L.ι) :
    LB.wchart (L.pull F) ![(ι[H]).left, 𝟙 H.left] j ≤
      F ⁻¹ᵁ LB.wchart L ![(ι[G]).left, 𝟙 G.left] (fun k => j k ⟨⟩) := by
  intro y hy
  refine Set.mem_iInter.2 fun k => ?_
  have h1 := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) ⟨⟩
  fin_cases k
  · change (F ≫ (ι[G]).left).base y ∈ (L.U (j 0 ⟨⟩) : Set _)
    rw [← hF]
    exact h1
  · exact h1
def symPull (F : H.left ⟶ G.left) (hF : (ι[H]).left ≫ F = F ≫ (ι[G]).left) (L : LB G.left)
    (s : SymGen G L) : SymGen H (L.pull F) where
  s := fun j => res (symPull_le F hF L j) (pullU F _ (s.s (fun k => j k ⟨⟩)))
end Sym
section IsoPull
variable {X X' Y Y' : Scheme.{0}} (L : LB X) (M : LB X')
lemma isoPull_le (h : Y' ⟶ Y) {a : Y ⟶ X} {b : Y ⟶ X'} {a' : Y' ⟶ X} {b' : Y' ⟶ X'}
    (ha : h ≫ a = a') (hb : h ≫ b = b') (j : (PUnit → M.ι) × (PUnit → L.ι)) :
    (LB.div (M.pull b') (L.pull a')).U j ≤ h ⁻¹ᵁ (LB.div (M.pull b) (L.pull a)).U j := by
  subst ha hb
  intro y hy
  exact ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k,
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k⟩
def isoPull (h : Y' ⟶ Y) {a : Y ⟶ X} {b : Y ⟶ X'} {a' : Y' ⟶ X} {b' : Y' ⟶ X'}
    (ha : h ≫ a = a') (hb : h ≫ b = b') (w : LB.Iso (L.pull a) (M.pull b)) :
    LB.Iso (L.pull a') (M.pull b') where
  s := fun j => res (isoPull_le L M h ha hb j) (pullU h _ (w.s j))
end IsoPull
section Generic
variable (R : Type) [CommRing R] [IsDomain R]
structure Model (P : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (rA : LB.Gen (P.L.pull (eSec P.A)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom

  rA_gen : rA.IsGen

  gen : P.A ≅ (Over.pullback (jK R)).obj G
  [gen_hom : IsMonHom gen.hom]

  LG : RigLB G

  cub : CubicalStr G LG

  sym : SymGen G LG.L
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ sym (eSec G)) (LB.oneGen LG.L)

  ext : LB.Iso P.L (LG.L.pull (bcMap (jK R) gen.hom).F)
  ext_gen : ext.IsGen
  ext_rig : LB.Gen.Maps (LB.linCombIso ext (K := PUnit) (fun _ => eSec P.A) (fun _ => 1)) rA
    ((bcMap (jK R) gen.hom).rigPull LG.L LG.rig)
end Generic
section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
abbrev toG (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : CubeMap (thickObj R I e G) G :=
  bcMap (thick R I e) (𝟙 (thickObj R I e G))
def toB {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) : CubeMap (thickObj R I e G) D.P.A :=
  haveI := j.q_hom
  bcMap (thick R I e) j.q
omit [IsDomain R] in
lemma toG_inv (I : Ideal R) (e : ℕ) :
    (ι[thickObj R I e G]).left ≫ (toG I e G).F = (toG I e G).F ≫ (ι[G]).left :=
  inv_dn (thick R I e) (𝟙 (thickObj R I e G))
lemma toB_inv {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) :
    (ι[thickObj R I e G]).left ≫ (toB j).F = (toB j).F ≫ (ι[D.P.A]).left :=
  haveI := j.q_hom
  inv_dn (thick R I e) j.q
omit [IsDomain R] in
lemma thickMap_fst (I : Ideal R) (e : ℕ) (Z : Over (Spec (CommRingCat.of R))) :
    thickMap R I e Z ≫ pullback.fst Z.hom (thick R I (e + 1)) =
      pullback.fst Z.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)
omit [IsDomain R] in
lemma thickMap_toG (I : Ideal R) (e : ℕ) :
    thickMap R I e G ≫ (toG I (e + 1) G).F = (toG I e G).F := by
  simp [toG, bcMap, thickMap_fst]
lemma thickMap_toB {e : ℕ} (j : CanonicalRigidImages.GtIso D I e G) (j' : CanonicalRigidImages.GtIso D I (e + 1) G)
    (h : thickMap R I e G ≫ j'.q.left = j.q.left ≫ thickMap R I e D.P.A) :
    thickMap R I e G ≫ (toB j').F = (toB j).F := by
  change thickMap R I e G ≫ j'.q.left ≫ pullback.fst D.P.A.hom _ =
    j.q.left ≫ pullback.fst D.P.A.hom _
  rw [← Category.assoc, h, Category.assoc, thickMap_fst]
end Levels
structure UnifPre (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (P : PolAV (Spec (CommRingCat.of (FractionRing R)))) (rA : LB.Gen (P.L.pull (eSec P.A)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    extends Model R P rA G where

  adm : AdmBase R I

  j : ∀ e : ℕ, CanonicalRigidImages.GtIso D.toPre I e G

  j_q : ∀ e, thickMap R I e G ≫ (j (e + 1)).q.left = (j e).q.left ≫ thickMap R I e D.toPre.P.A

  uniformization_corr : ∀ e χ, LB.Gen.Corr D.toPre.P.L _ _ _ _
    (LB.pullGen D.toPre.P.L _ _ ((j (e + 1)).x χ) (thickMap R I e G)) ((j e).x χ)

  ph : ∀ e : ℕ, LB.Iso (LG.L.pull (toG I e G).F) (D.toPre.P.L.pull (toB (j e)).F)
  ph_gen : ∀ e, (ph e).IsGen

  ph_rig : ∀ e, LB.Gen.Maps
    (LB.linCombIso (ph e) (K := PUnit) (fun _ => eSec (thickObj R I e G)) (fun _ => 1))
    ((toG I e G).rigPull LG.L LG.rig) ((toB (j e)).rigPull D.toPre.P.L D.toPre.rig)

  ph_cub : ∀ e, LB.Gen.Maps
    (LB.linCombIso (ph e) (thφ (thickObj R I e G) (x3 (thickObj R I e G))) thε)
    ((toG I e G).thetaPull LG.L cub.t) ((toB (j e)).thetaPull D.toPre.P.L D.toPre.cub.t)

  ph_even : ∀ e, LB.Gen.Maps
    (LB.linCombIso (ph e) (K := Fin 2) ![(ι[thickObj R I e G]).left, 𝟙 _] ![1, -1])
    (symPull (toG I e G).F (toG_inv I e) LG.L sym)
    (symPull (toB (j e)).F (toB_inv (j e)) D.toPre.P.L D.toPre.sym)

  ph_compat : ∀ e, isoPull LG.L D.toPre.P.L (thickMap R I e G) (thickMap_toG I e)
    (thickMap_toB (j e) (j (e + 1)) (j_q e)) (ph (e + 1)) = ph e
example {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ}
    (j : CanonicalRigidImages.GtIso D I e G) : (toB j).F = (CanonicalRigidImages.down D I e j.q).left := rfl
example {R : Type} [CommRing R] {I : Ideal R} (h : AdmBase R I) : I ≠ ⊤ := by
  rintro rfl
  obtain ⟨_, hd, _, hc⟩ := h
  have : (1 : R) = 0 := hc.toIsHausdorff.haus 1 fun n => by simp [SModEq.zero, Ideal.top_pow]
  exact one_ne_zero this
end GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel


