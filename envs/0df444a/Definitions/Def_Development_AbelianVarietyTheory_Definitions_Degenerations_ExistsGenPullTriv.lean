-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsGenPullTriv
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsGenPullTriv
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:36.505341+00:00
-- url     : https://prove2.me/theorems/b57081e3-bb04-4046-92f4-4197a94068a7
-- title:
--   Exists Gen Pull Triv
-- statement:
--   Definitions and structural lemmas for Exists Gen Pull Triv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsGenPullTriv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
import Theorems.Thm_GlobalTheory_SplitTorus_bcIso_hom_fst
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_bcMap_comp
import Theorems.Thm_GlobalTheory_UU_isLevelCP_triv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
structure TowerR (I : Ideal R) (P : CP G) (X : Type) [AddCommGroup X] where
  l : ∀ e, Lev I P X e
  tor : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (l e).Q.i (l (e + 1)).Q.i
  β : ∀ e, (l e).Q.B.left ⟶ (l (e + 1)).Q.B.left
  β_pb : ∀ e, IsCPPullback (l e).D.M (l (e + 1)).D.M (thickTrans R I e) (β e)
  β_q : ∀ e, (l e).Q.q.left ≫ β e = thickMap R I e G ≫ (l (e + 1)).Q.q.left
structure TowerR.Alg {P : CP G} {X : Type} [AddCommGroup X] (t : TowerR I P X) where
  B : Over (Spec (CommRingCat.of R))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B
  M : CP B
  ample : RelAmple B M.L.L
  b : ∀ e, (t.l e).Q.B.left ⟶ B.left
  b_pb : ∀ e, IsCPPullback (t.l e).D.M M (thick R I e) (b e)
  b_β : ∀ e, t.β e ≫ b (e + 1) = b e
attribute [instance] TowerR.Alg.grp TowerR.Alg.comm
def TowerR.Alg.RepWt {P : CP G} {X : Type} [AddCommGroup X] {t : TowerR I P X} (a : t.Alg) (c : 𝟙_ _ ⟶ a.B) (χ : X) (e : ℕ) : Prop :=
  ∃ u : LB.Gen ((LB.LinComb a.M.L.L (K := Fin 2) ![((toUnit a.B ≫ c) * 𝟙 a.B).left, 𝟙 a.B.left] ![-1, 1]).pull
      ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ
open GlobalTheory.SplitTorus
theorem isGrpPullback_unit' {S S' : Scheme.{0}} (f : S' ⟶ S) : IsGrpPullback (𝟙_ (Over S')) (𝟙_ (Over S)) f f :=
  ⟨IsPullback.of_vert_isIso (fst := f) (snd := 𝟙 S') (f := 𝟙 S) (g := f) ⟨by simp⟩, fun T x y x₀ y₀ hx _ => by
    rw [toUnit_unique (x₀ * y₀) x₀, toUnit_unique (x * y) x, hx]⟩
theorem isCPPullback_unit {S S' : Scheme.{0}} (f : S' ⟶ S) :
    IsCPPullback (CP.triv (𝟙_ (Over S'))) (CP.triv (𝟙_ (Over S))) f f :=
  ⟨isGrpPullback_unit' f, _, IsCPMap.triv fun _ _ _ => toUnit_unique _ _⟩
def torusTQ {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    TQ ((Over.pullback f).obj (splitTorus S X)) X where
  B := 𝟙_ (Over S')
  isAb := isAbelianScheme_unit S'
  q := toUnit _
  i := (bcIso f X).hom
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by
    rw [Rosenlicht.toUnit_left]
    have := Diag.flat_hom S X
    show Flat (pullback.snd (splitTorus S X).hom f); infer_instance
  q_surj := by
    rw [Rosenlicht.toUnit_left]
    have := Diag.surjective_hom S X
    show Surjective (pullback.snd (splitTorus S X).hom f); infer_instance
  q_affine := by
    rw [Rosenlicht.toUnit_left]
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (splitTorus S X).hom f) (Diag.isAffineHom_hom S X)
  isKernel := by
    have : IsIso (η[𝟙_ (Over S')]) := by rw [toUnit_unique η[𝟙_ (Over S')] (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  loc _ χ := ⟨⊤, trivial, chV (bcIso f X).inv χ, isWt_of_retraction (bcIso f X).inv (bcIso f X).hom_inv_id χ⟩
def torusTower (I : Ideal R) (X : Type) [AddCommGroup X] :
    TowerR I (CP.triv (splitTorus (Spec (CommRingCat.of R)) X)) X where
  l e := ⟨torusTQ (thick R I e) X, CP.triv _, isLevelCP_triv I e _, TQ.Desc.triv _⟩
  tor e := by
    rw [torusCompat_iff]
    refine pullback.hom_ext ?_ ?_
    · show (bcMap _ X ≫ (bcIso (thick R I (e + 1)) X).hom.left) ≫ pullback.fst _ _ =
        ((bcIso (thick R I e) X).hom.left ≫ thickMap R I e _) ≫ pullback.fst _ _
      rw [Category.assoc, bcIso_hom_fst, ← bcMap_comp, thickTrans_comp, Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.comp_id, bcIso_hom_fst]
    · show (bcMap _ X ≫ (bcIso (thick R I (e + 1)) X).hom.left) ≫ pullback.snd _ _ =
        ((bcIso (thick R I e) X).hom.left ≫ thickMap R I e _) ≫ pullback.snd _ _
      rw [Category.assoc, Category.assoc]
      have h₁ : (bcIso (thick R I (e + 1)) X).hom.left ≫ pullback.snd _ _ = _ := Over.w (bcIso (thick R I (e + 1)) X).hom
      have h₂ : (bcIso (thick R I e) X).hom.left ≫ pullback.snd _ _ = _ := Over.w (bcIso (thick R I e) X).hom
      have h₃ : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫ pullback.snd _ _ =
          pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
      rw [h₁, h₃, ← Category.assoc, h₂, bcMap_hom]
  β e := thickTrans R I e
  β_pb e := isCPPullback_unit _
  β_q e := by
    show (toUnit _ : _ ⟶ 𝟙_ (Over _)).left ≫ _ = _ ≫ (toUnit _ : _ ⟶ 𝟙_ (Over _)).left
    have h₃ : thickMap R I e (splitTorus (Spec (CommRingCat.of R)) X) ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    exact (congrArg (· ≫ thickTrans R I e) (Rosenlicht.toUnit_left _)).trans
      (h₃.symm.trans (congrArg (thickMap R I e _ ≫ ·)
        (Rosenlicht.toUnit_left (thickObj R I (e + 1) (splitTorus (Spec (CommRingCat.of R)) X))).symm))
def torusAlg (I : Ideal R) (X : Type) [AddCommGroup X] : (torusTower I X).Alg where
  B := 𝟙_ _
  isAb := isAbelianScheme_unit _
  M := CP.triv _
  ample := (Inh.zeroPolAV _).ample
  b e := thick R I e
  b_pb e := isCPPullback_unit _
  b_β e := thickTrans_comp R I e
theorem exists_gen_pull_triv {Y Z : Scheme.{0}} (φ : Fin 2 → (Y ⟶ Y)) (ε : Fin 2 → ℤ) (r : Z ⟶ Y) (u : Γ(Z, ⊤)ˣ) :
    ∃ t : LB.Gen ((LB.LinComb (Inh.trivLB Y) φ ε).pull r), t.IsGen ∧ ∀ j, t.s j = res le_top u := by
  let o : LB.Gen ((LB.LinComb (Inh.trivLB Y) φ ε).pull r) := ⟨fun _ => 1⟩
  have ho : o.IsGen := fun i j => by
    have g1 : ((LB.LinComb (Inh.trivLB Y) φ ε).pull r).g i j = 1 := by
      have key : ∀ (N : LB Y), (∀ a b, N.g a b = 1) → ∀ a b, (N.pull r).g a b = 1 := fun N hN a b => by
        dsimp only [LB.pull, LB.LinComb]
        simp only [hN]
        rw [Fintype.prod_unique, zpow_one]; erw [map_one, map_one]; rfl
      exact key _ (Inh.linComb_triv_g φ ε) i j
    rw [g1, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  exact ⟨scaleGen u o, scaleGen_isGen u ho, fun j => _root_.mul_one _⟩
omit [IsLocalRing R] in

theorem torusAlg_repWt (I : Ideal R) (X : Type) [AddCommGroup X] (χ : X) (e : ℕ) :
    (torusAlg I X).RepWt 1 χ e := by
  have hu := isWt_of_retraction (i := (bcIso (thick R I e) X).hom) (bcIso (thick R I e) X).inv
    (bcIso (thick R I e) X).hom_inv_id χ
  obtain ⟨t, ht, hs⟩ := exists_gen_pull_triv
    ![((toUnit (torusAlg I X).B ≫ 1) * 𝟙 (torusAlg I X).B).left, 𝟙 (torusAlg I X).B.left] ![-1, 1]
    (((torusTower I X).l e).Q.q.left ≫ (torusAlg I X).b e) (chV (bcIso (thick R I e) X).inv χ)
  exact ⟨t, ht, fun j => (congrArg (fun a => IsWt _ _ (Units.val a) χ) (hs j)).mpr (hu.res le_top)⟩
example : Nonempty (torusTower (Ideal.span {(PowerSeries.X : PowerSeries ℚ)}) ℤ).Alg := ⟨torusAlg _ _⟩
example (e : ℕ) : (torusAlg (Ideal.span {(PowerSeries.X : PowerSeries ℚ)}) ℤ).RepWt 1 (1 : ℤ) e :=
  torusAlg_repWt _ _ _ _
example {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {H : Over (Spec (CommRingCat.of V))} [GrpObj H] [IsCommMonObj H] (s : HidaSetting V A H) :
    Tower s ≃ TowerR (IsLocalRing.maximalIdeal V) s.P s.X where
  toFun t := ⟨t.l, t.tor, t.β, t.β_pb, t.β_q⟩
  invFun t := ⟨t.l, t.tor, t.β, t.β_pb, t.β_q⟩
  left_inv _ := rfl
  right_inv _ := rfl
end GlobalTheory.LN
end


