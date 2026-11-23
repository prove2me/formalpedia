-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:28.215543+00:00
-- url     : https://prove2.me/theorems/8677a244-3db1-43ee-90d6-734b02430c90
-- title:
--   Group Hom Pullback
-- statement:
--   Definitions and structural lemmas for Group Hom Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
section Bundles
variable {X X' Y Y' : Scheme.{u}}
def pr (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, V)ˣ :=
  Units.map (f.appLE U V h).hom
lemma res_pullU (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    res h (pullU f U a) = pr f h a := by
  ext; rfl
lemma res_refl {U : X.Opens} (a : Γ(X, U)ˣ) : res le_rfl a = a := by
  ext
  change (X.presheaf.map (𝟙 (op U))).hom _ = _
  rw [X.presheaf.map_id]; rfl
lemma res_pr (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ V)
    (a : Γ(X, U)ˣ) : res h' (pr f h a) = pr f (h'.trans h) a := by
  ext
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom _ = _
  rw [Scheme.Hom.appLE_map]; rfl
lemma pr_res (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h' : U ≤ U') (h : V ≤ f ⁻¹ᵁ U)
    (a : Γ(X, U')ˣ) : pr f h (res h' a) = pr f (h.trans fun _ hy => h' hy) a := by
  ext
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom _ = _
  rw [Scheme.Hom.map_appLE]; rfl
lemma pr_pr (g : Y' ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Y'.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pr g h' (pr f h a) = pr (g ≫ f) (fun _ hy => h (h' hy)) a := by
  ext
  change (f.appLE U V h ≫ g.appLE V W h').hom _ = _
  rw [Scheme.Hom.appLE_comp_appLE]; rfl
lemma pr_congr {f g : Y ⟶ X} (e : f = g) {U : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) (a : Γ(X, U)ˣ) : pr f h a = pr g h' a := by
  subst e; rfl
def isoUnit {L M : LB X} (u : LB.Iso L M) (j : M.ι) (i : L.ι) : Γ(X, M.U j ⊓ L.U i)ˣ := u.s (j, i)
def Carries {L M : LB X} (u : LB.Iso L M) (s : LB.Gen L) (t : LB.Gen M) : Prop :=
  ∀ (j : M.ι) (i : L.ι),
    res (inf_le_left : M.U j ⊓ L.U i ≤ M.U j) (t.s j) =
      isoUnit u j i * res (inf_le_right : M.U j ⊓ L.U i ≤ L.U i) (s.s i)
def isoRefl (L : LB X) : LB.Iso L L where
  s := fun p => L.g p.1 p.2
example (L : LB X) (s : LB.Gen L) : Carries (isoRefl L) s s ↔ s.IsGen := Iff.rfl
def CommSq {L L' M M' : LB X} (u : LB.Iso L L') (a : LB.Iso L M) (b : LB.Iso L' M')
    (v : LB.Iso M M') : Prop :=
  ∀ (i : L.ι) (i' : L'.ι) (j : M.ι) (j' : M'.ι),
    res (U := M'.U j' ⊓ L'.U i') (V := (L.U i ⊓ L'.U i') ⊓ (M.U j ⊓ M'.U j'))
        (le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right))
        (isoUnit b j' i') *
      res (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
        (isoUnit u i' i) =
    res (le_inf (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_left))
        (isoUnit v j' j) *
      res (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left))
        (isoUnit a j i)
variable {K : Type u} [Fintype K]
lemma le_pre_inf (M L : LB X) (φ : K → (Y ⟶ X)) (j : K → M.ι) (i : K → L.ι) (k : K) :
    LB.wchart M φ j ⊓ LB.wchart L φ i ≤ φ k ⁻¹ᵁ (M.U (j k) ⊓ L.U (i k)) :=
  le_inf (inf_le_left.trans (LB.wchart_le M φ j k)) (inf_le_right.trans (LB.wchart_le L φ i k))
lemma res_linComb_g (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a b : K → L.ι) {W : Y.Opens}
    (h : W ≤ LB.wchart L φ a ⊓ LB.wchart L φ b) :
    res (U := LB.wchart L φ a ⊓ LB.wchart L φ b) h ((LB.LinComb L φ ε).g a b) =
      ∏ k, pr (φ k) (h.trans (le_pre_inf L L φ a b k)) (L.g (a k) (b k)) ^ ε k := by
  change res h (∏ k, (res (le_pre_inf L L φ a b k) (pullU (φ k) _ (L.g (a k) (b k)))) ^ ε k) = _
  simp only [map_prod, map_zpow, res_pullU, res_pr]
def isoLinComb {L M : LB X} (u : LB.Iso L M) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb M φ ε) where
  s := fun p => ∏ k, (pr (φ k) (le_pre_inf M L φ p.1 p.2 k) (isoUnit u (p.1 k) (p.2 k))) ^ (ε k)
abbrev isoPull {L M : LB X} (u : LB.Iso L M) (f : Y ⟶ X) : LB.Iso (L.pull f) (M.pull f) :=
  isoLinComb u (K := PUnit) (fun _ => f) (fun _ => 1)
theorem isLB_linComb {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (LB.LinComb L φ ε).IsLB where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    have h : ∀ k, ∃ i, (φ k).base y ∈ L.U i := fun k =>
      Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((φ k).base y)))
    choose j hj using h
    exact Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  g_self := by
    intro j
    refine (res_linComb_g L φ ε j j _).trans ?_
    refine Finset.prod_eq_one fun k _ => ?_
    have := congrArg (pr (φ k) (LB.wchart_le L φ j k)) (hL.g_self (j k))
    simp only [pr_res, map_one] at this
    exact (congrArg (· ^ ε k) this).trans (one_zpow _)
  cocycle := by
    intro a b c
    refine (congrArg₂ (· * ·) (res_linComb_g L φ ε a b _) (res_linComb_g L φ ε b c _)).trans
      (Eq.trans ?_ (res_linComb_g L φ ε a c _).symm)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow]
    congr 1
    have hh : LB.wchart L φ a ⊓ LB.wchart L φ b ⊓ LB.wchart L φ c ≤
        φ k ⁻¹ᵁ (L.U (a k) ⊓ L.U (b k) ⊓ L.U (c k)) :=
      le_inf (inf_le_left.trans (le_pre_inf L L φ a b k))
        (inf_le_right.trans (LB.wchart_le L φ c k))
    have := congrArg (pr (φ k) hh) (hL.cocycle (a k) (b k) (c k))
    simp only [map_mul, pr_res] at this
    exact this
lemma wchart_square (L : LB X) {f : X' ⟶ X} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {h : Y' ⟶ Y}
    (sq : ∀ k, φ' k ≫ f = h ≫ φ k) (j : K → (L.pull f).ι) :
    LB.wchart (L.pull f) φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j k PUnit.unit) := by
  intro y hy
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : y ∈ (φ' k ≫ f) ⁻¹ᵁ L.U (j k PUnit.unit) :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hy k) PUnit.unit
  rw [sq k] at h1
  exact h1
def genSquare (L : LB X) {f : X' ⟶ X} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {h : Y' ⟶ Y}
    (sq : ∀ k, φ' k ≫ f = h ≫ φ k) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (L.pull f) φ' ε) where
  s := fun j => pr h (wchart_square L sq j) (t.s fun k => j k PUnit.unit)
theorem genSquare_isGen (L : LB X) {f : X' ⟶ X} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')}
    {h : Y' ⟶ Y} (sq : ∀ k, φ' k ≫ f = h ≫ φ k) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) : (genSquare L sq ε t).IsGen := by
  intro a b
  let a' : K → L.ι := fun k => a k PUnit.unit
  let b' : K → L.ι := fun k => b k PUnit.unit
  have h0 : res (inf_le_left : LB.wchart L φ a' ⊓ LB.wchart L φ b' ≤ _) (t.s a') =
      res (U := LB.wchart L φ a' ⊓ LB.wchart L φ b') le_rfl ((LB.LinComb L φ ε).g a' b') *
        res inf_le_right (t.s b') :=
    (ht a' b').trans (congrArg (· * res inf_le_right (t.s b')) (res_refl _).symm)
  rw [res_linComb_g] at h0
  have hh : LB.wchart (L.pull f) φ' a ⊓ LB.wchart (L.pull f) φ' b ≤
      h ⁻¹ᵁ (LB.wchart L φ a' ⊓ LB.wchart L φ b') :=
    le_inf (inf_le_left.trans (wchart_square L sq a)) (inf_le_right.trans (wchart_square L sq b))
  have := congrArg (pr h hh) h0
  simp only [map_mul, map_prod, map_zpow, pr_pr] at this
  refine (res_pr h (wchart_square L sq a) inf_le_left _).trans ?_
  refine ((pr_res h _ _ _).symm.trans this).trans ?_
  refine congrArg₂ (· * ·) ?_ ((pr_res h _ _ _).trans
    (res_pr h (wchart_square L sq b) inf_le_right _).symm)
  refine Eq.trans ?_ (res_refl _)
  refine Eq.trans ?_ (res_linComb_g (L.pull f) φ' ε a b le_rfl).symm
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  have h1 := (res_refl _).symm.trans
    (res_linComb_g L (K := PUnit) (fun _ => f) (fun _ => 1) (a k) (b k) le_rfl)
  rw [Fintype.prod_unique, zpow_one] at h1
  refine Eq.trans ?_ (congrArg (pr (φ' k) _) h1).symm
  refine Eq.trans ?_ (pr_pr _ _ _ _ _).symm
  exact pr_congr (sq k).symm _ _ _
end Bundles
section Group
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{u}}
def ptOver {G' : Over S'} {G : Over S} (base : S' ⟶ S) (tot : G'.left ⟶ G.left)
    (w : tot ≫ G.hom = G'.hom ≫ base) {T : Over S'} (a : T ⟶ G') : (Over.map base).obj T ⟶ G :=
  Over.homMk (a.left ≫ tot) (by
    change (a.left ≫ tot) ≫ G.hom = T.hom ≫ base
    rw [Category.assoc, w, ← Category.assoc, Over.w a])
structure GrpHom (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G : Over S) [GrpObj G]
    [IsCommMonObj G] where

  base : S' ⟶ S

  tot : G'.left ⟶ G.left
  w : tot ≫ G.hom = G'.hom ≫ base
  map_zero : ∀ T : Over S', ptOver base tot w (pzero G' T) = pzero G _
  map_add : ∀ (T : Over S') (a b : T ⟶ G'),
    ptOver base tot w (padd G' a b) = padd G (ptOver base tot w a) (ptOver base tot w b)
namespace GrpHom
section Examples
def ofHom {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (f : G' ⟶ G) [IsMonHom f] : GrpHom G' G where
  base := 𝟙 S
  tot := f.left
  w := by simp
  map_zero T := by
    have h (a : T ⟶ G') : ptOver (𝟙 S) f.left (by simp) a =
        (Over.mapId S).hom.app T ≫ a ≫ f := by
      ext; simp [ptOver]
    rw [h]
    simp only [pzero, Category.assoc, IsMonHom.one_hom]
    rw [← Category.assoc]
    congr 1
  map_add T a b := by
    have h (a : T ⟶ G') : ptOver (𝟙 S) f.left (by simp) a =
        (Over.mapId S).hom.app T ≫ a ≫ f := by
      ext; simp [ptOver]
    rw [h, h, h]
    simp only [padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, ← comp_lift_assoc]
open scoped CategoryTheory.Obj in

def baseChange (b : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] :
    GrpHom ((Over.pullback b).obj G) G where
  base := b
  tot := pullback.fst G.hom b
  w := pullback.condition
  map_zero T := by
    have h (a : T ⟶ (Over.pullback b).obj G) :
        ptOver b (pullback.fst G.hom b) pullback.condition a =
        ((Over.mapPullbackAdj b).homEquiv _ _).symm a := by
      ext; simp [ptOver, Adjunction.homEquiv_counit]
    rw [h, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
    simp only [pzero, Functor.map_comp, Functor.obj.η_def]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback b))]
    exact toUnit_unique _ _
  map_add T a a' := by
    have h (a : T ⟶ (Over.pullback b).obj G) :
        ptOver b (pullback.fst G.hom b) pullback.condition a =
        ((Over.mapPullbackAdj b).homEquiv _ _).symm a := by
      ext; simp [ptOver, Adjunction.homEquiv_counit]
    rw [h, h, h, Equiv.symm_apply_eq]
    obtain ⟨x, rfl⟩ := ((Over.mapPullbackAdj b).homEquiv _ _).surjective a
    obtain ⟨x', rfl⟩ := ((Over.mapPullbackAdj b).homEquiv _ _).surjective a'
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp only [Adjunction.homEquiv_unit, padd, Functor.map_comp,
      Functor.obj.μ_def]
    rw [← comp_lift_assoc, Functor.Monoidal.lift_μ_assoc]
def neg (G : Over S) [GrpObj G] [IsCommMonObj G] : GrpHom G G := ofHom (GrpObj.inv (X := G))
end Examples
variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {G : Over S} [GrpObj G] [IsCommMonObj G]
  (f : GrpHom G' G)
abbrev pt {T : Over S'} (a : T ⟶ G') : (Over.map f.base).obj T ⟶ G := ptOver f.base f.tot f.w a
lemma pt_psum {T : Over S'} {n : ℕ} (x : Fin n → (T ⟶ G')) (I : Finset (Fin n)) :
    f.pt (psum G' x I) = psum G (fun i => f.pt (x i)) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact f.map_zero T
  | cons k l ih => simp only [List.foldr_cons]; rw [← ih]; exact f.map_add T _ _
lemma comp_psum {T T' : Over S} (g : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    g ≫ psum G x I = psum G (fun i => g ≫ x i) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => simp [pzero]
  | cons k l ih => simp only [List.foldr_cons]; rw [← ih]; simp only [padd, comp_lift_assoc]
def cubeOver : (Over.map f.base).obj (G3 G') ⟶ G3 G :=
  lift (f.pt (x3 G' 0)) (lift (f.pt (x3 G' 1)) (f.pt (x3 G' 2)))
def cube : (G3 G').left ⟶ (G3 G).left := f.cubeOver.left
lemma cube_sq (I : thK.{u}) : thφ G' (x3 G') I ≫ f.tot = f.cube ≫ thφ G (x3 G) I := by
  have h : f.pt (psum G' (x3 G') I.down) = f.cubeOver ≫ psum G (x3 G) I.down := by
    rw [pt_psum, comp_psum]
    congr 1
    funext i
    fin_cases i <;> simp [cubeOver, x3]
  exact congrArg CommaMorphism.left h
def unitMap : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f.base
lemma eSec_sq : eSec G' ≫ f.tot = f.unitMap ≫ eSec G := by
  have h := congrArg CommaMorphism.left (f.map_zero (𝟙_ (Over S')))
  simpa [pzero, ptOver, eSec, unitMap] using h
def pullRigGen (L : RigLB G) : LB.Gen ((L.L.pull f.tot).pull (eSec G')) :=
  genSquare L.L (K := PUnit) (φ := fun _ => eSec G) (φ' := fun _ => eSec G') (h := f.unitMap)
    (fun _ => f.eSec_sq) (fun _ => 1) L.rig
def pullRig (L : RigLB G) : RigLB G' where
  L := L.L.pull f.tot
  rig := f.pullRigGen L
  isLB := isLB_linComb L.isLB _ _
  rigGen := genSquare_isGen _ _ _ L.rigGen
def pullCube (L : LB G.left) (t : LB.Gen (Theta G L)) : LB.Gen (Theta G' (L.pull f.tot)) :=
  genSquare L (φ := thφ G (x3 G)) (φ' := thφ G' (x3 G')) (h := f.cube) f.cube_sq thε t
end GrpHom
variable {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {G : Over S} [GrpObj G] [IsCommMonObj G]
def IsRigIso (L M : RigLB G) (u : LB.Iso L.L M.L) : Prop :=
  u.IsGen ∧ Carries (isoPull u (eSec G)) L.rig M.rig
def thetaIso {L M : LB G.left} (u : LB.Iso L M) : LB.Iso (Theta G L) (Theta G M) :=
  isoLinComb u (thφ G (x3 G)) thε
def IsCubicalPullIso (f : GrpHom G' G) {L : RigLB G} (c : CubicalStr G L) {L' : RigLB G'}
    (c' : CubicalStr G' L') (u : LB.Iso (f.pullRig L).L L'.L) : Prop :=
  IsRigIso (f.pullRig L) L' u ∧ Carries (thetaIso u) (f.pullCube L.L c.t) c'.t
def IsCubicalPullback (f : GrpHom G' G) (L : RigLB G) (c : CubicalStr G L) (L' : RigLB G')
    (c' : CubicalStr G' L') : Prop :=
  ∃ u : LB.Iso (f.pullRig L).L L'.L, IsCubicalPullIso f c c' u
def IsSymmetric (L : RigLB G) : Prop :=
  ∃ σ : LB.Iso ((GrpHom.neg G).pullRig L).L L.L, IsRigIso ((GrpHom.neg G).pullRig L) L σ
def IsEven {L M : RigLB G} (σ : LB.Iso ((GrpHom.neg G).pullRig L).L L.L)
    (τ : LB.Iso ((GrpHom.neg G).pullRig M).L M.L) (u : LB.Iso L.L M.L) : Prop :=
  CommSq σ (isoPull u (GrpHom.neg G).tot) u τ
end Group
end
end GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback


