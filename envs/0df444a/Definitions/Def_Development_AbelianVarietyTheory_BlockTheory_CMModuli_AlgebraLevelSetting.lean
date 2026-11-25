-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_AlgebraLevelSetting
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_AlgebraLevelSetting
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:44:31.034905+00:00
-- url     : https://prove2.me/theorems/1aa0c914-dfe5-453a-9b22-51cba0ea7690
-- title:
--   Algebra Level Setting
-- statement:
--   Definitions and structural lemmas for Algebra Level Setting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/AlgebraLevelSetting.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_val_sym_triv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting
structure SymTriv {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {f : S' ⟶ S}
    {H : Over S'} [GrpObj H] (j : H.left ⟶ G.left) (hj : j ≫ G.hom = H.hom ≫ f) where

  s : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![j, H.hom ≫ f ≫ eSec G] ![1, -1])
  gen : s.IsGen
  cub : ∀ (T : Over S') (x y u : T ⟶ H) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι), Good P.L.L z J →
    val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J =
      @id (T.left.presheaf.stalk z)ˣ
          (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hj x) (toBase hj y) (toBase hj u)) *
        val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J
  even : ∀ (T : Over S') (x : T ⟶ H) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι), Good P.L.L z J →
    val s (x⁻¹).left z J = val P.sym (x.left ≫ j) z J * val s x.left z J
section Levels
variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
structure Level (P : CP G) (X : Type) [AddCommGroup X] (f : S₁ ⟶ S) (G₁ : Over S₁) [GrpObj G₁] [IsCommMonObj G₁]
    (F : G₁.left ⟶ G.left) (hF : F ≫ G.hom = G₁.hom ≫ f) where

  Q : TQ G₁ X

  Pe : CP G₁

  v : LB.Iso Pe.L.L (P.L.L.pull F)
  v_map : IsCPMap Pe P f F hF v

  D : Q.Desc Pe
variable {P : CP G} {X : Type} [AddCommGroup X] {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S}
  {G₁ : Over S₁} [GrpObj G₁] [IsCommMonObj G₁] {F₁ : G₁.left ⟶ G.left} {h₁ : F₁ ≫ G.hom = G₁.hom ≫ f₁}
  {G₂ : Over S₂} [GrpObj G₂] [IsCommMonObj G₂] {F₂ : G₂.left ⟶ G.left} {h₂ : F₂ ≫ G.hom = G₂.hom ≫ f₂}
structure Step (L₁ : Level P X f₁ G₁ F₁ h₁) (L₂ : Level P X f₂ G₂ F₂ h₂) (t : S₁ ⟶ S₂) (m : G₁.left ⟶ G₂.left) where
  torus : TorusCompat t m L₁.Q.i L₂.Q.i

  β : L₁.Q.B.left ⟶ L₂.Q.B.left
  β_pull : IsGrpPullback L₁.Q.B L₂.Q.B t β
  q_β : L₁.Q.q.left ≫ β = m ≫ L₂.Q.q.left

  u : LB.Iso L₁.D.M.L.L (L₂.D.M.L.L.pull β)
  u_map : IsCPMap L₁.D.M L₂.D.M t β β_pull.1.w u

  compat : ∀ (Z : Scheme.{0}) (x : Z ⟶ G₁.left) (z : Z) (l : P.L.L.ι) (k₁ : L₁.Pe.L.L.ι) (k₂ : L₂.Pe.L.L.ι)
    (j₁ : L₁.D.M.L.L.ι) (j₂ : L₂.D.M.L.L.ι),
    (x ≫ F₁) z ∈ P.L.L.U l → x z ∈ L₁.Pe.L.L.U k₁ → (x ≫ m) z ∈ L₂.Pe.L.L.U k₂ →
    (x ≫ L₁.Q.q.left) z ∈ L₁.D.M.L.L.U j₁ → (x ≫ L₁.Q.q.left ≫ β) z ∈ L₂.D.M.L.L.U j₂ →
    gw u (x ≫ L₁.Q.q.left) z j₂ j₁ * gw L₁.D.w x z j₁ k₁ * gw L₂.v (x ≫ m) z l k₂ =
      gw L₂.D.w (x ≫ m) z j₂ k₂ * gw L₁.v x z l k₁
variable {B : Over S} [GrpObj B] [IsCommMonObj B]
structure Level.Red (L₁ : Level P X f₁ G₁ F₁ h₁) (M : CP B) where

  toB : L₁.Q.B.left ⟶ B.left
  toB_pull : IsGrpPullback L₁.Q.B B f₁ toB

  a : LB.Iso L₁.D.M.L.L (M.L.L.pull toB)
  a_map : IsCPMap L₁.D.M M f₁ toB toB_pull.1.w a
def Step.Compat {L₁ : Level P X f₁ G₁ F₁ h₁} {L₂ : Level P X f₂ G₂ F₂ h₂} {t : S₁ ⟶ S₂} {m : G₁.left ⟶ G₂.left}
    (s : Step L₁ L₂ t m) {M : CP B} (r₁ : L₁.Red M) (r₂ : L₂.Red M) : Prop :=
  s.β ≫ r₂.toB = r₁.toB ∧
    ∀ (Z : Scheme.{0}) (y : Z ⟶ L₁.Q.B.left) (z : Z) (j : M.L.L.ι) (k₂ : L₂.D.M.L.L.ι) (k₁ : L₁.D.M.L.L.ι),
      (y ≫ r₁.toB) z ∈ M.L.L.U j → (y ≫ s.β) z ∈ L₂.D.M.L.L.U k₂ → y z ∈ L₁.D.M.L.L.U k₁ →
      gw r₁.a y z j k₁ = gw r₂.a (y ≫ s.β) z j k₂ * gw s.u y z k₂ k₁
namespace Level.Red
variable {L₁ : Level P X f₁ G₁ F₁ h₁} {M : CP B} (r : L₁.Red M)
def pt : Over.mk (L₁.Q.B.hom ≫ f₁) ⟶ B := Over.homMk r.toB r.toB_pull.1.w
def lamφ (c : 𝟙_ (Over S) ⟶ B) : Fin 4 → (L₁.Q.B.left ⟶ B.left) :=
  ![((toUnit (Over.mk (L₁.Q.B.hom ≫ f₁)) ≫ c) * r.pt).left, (toUnit (Over.mk (L₁.Q.B.hom ≫ f₁)) ≫ c).left,
    r.pt.left, (1 : Over.mk (L₁.Q.B.hom ≫ f₁) ⟶ B).left]
def lamInv (c : 𝟙_ (Over S) ⟶ B) : LB L₁.Q.B.left := LB.LinComb M.L.L (r.lamφ c) ![-1, 1, 1, -1]
def Represents (c : 𝟙_ (Over S) ⟶ B) (χ : X) : Prop :=
  ∃ t : LB.Gen ((r.lamInv c).pull L₁.Q.q.left), L₁.Q.GenWt (r.lamInv c) t χ
end Level.Red
end Levels
section Formal
variable {R : Type} [CommRing R] (I : Ideal R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {X : Type} [AddCommGroup X]
abbrev Lv (e : ℕ) : Scheme.{0} := Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))
abbrev pr (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : (thickObj R I e G).left ⟶ G.left :=
  pullback.fst G.hom (thick R I e)
structure FormalTorus (i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G) where

  i : ∀ e : ℕ, splitTorus (Lv I e) X ⟶ thickObj R I e G
  hom : ∀ e, IsMonHom (i e)
  zero : i 0 = i₀
  compat : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (i e) (i (e + 1))
variable {I}
omit [GrpObj G] in

theorem torus_w {e : ℕ} (i : splitTorus (Lv I e) X ⟶ thickObj R I e G) :
    (i.left ≫ pr I e G) ≫ G.hom = (splitTorus (Lv I e) X).hom ≫ thick R I e := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ thick R I e) (Over.w i)
variable [IsCommMonObj G]
instance (priority := high) isCommMonObj_thickObj (e : ℕ) : IsCommMonObj (thickObj R I e G) := inferInstance
def FormalTorus.HasSymTriv {i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G} (F : FormalTorus I i₀) (P : CP G) : Prop :=
  ∃ σ : ∀ e : ℕ, SymTriv P ((F.i e).left ≫ pr I e G) (torus_w (F.i e)),
    ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (splitTorus (Lv I e) X).left) (z : Z) (J : (Z ⟶ G.left) → P.L.L.ι),
      Good P.L.L z J →
      val (σ (e + 1)).s (r ≫ SplitTorus.bcMap (thickTrans R I e) X) z J = val (σ e).s r z J
variable (I)
structure Tower (P : CP G) (i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G) where

  lv : ∀ e : ℕ, Level P X (thick R I e) (thickObj R I e G) (pr I e G) pullback.condition

  zero : (lv 0).Q.i = i₀

  step : ∀ e : ℕ, Step (lv e) (lv (e + 1)) (thickTrans R I e) (thickMap R I e G)
variable {I} {P : CP G} {i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G}
def Tower.formalTorus (W : Tower I P i₀) : FormalTorus I i₀ :=
  ⟨fun e => (W.lv e).Q.i, fun e => (W.lv e).Q.i_hom, W.zero, fun e => (W.step e).torus⟩
structure Alg (W : Tower I P i₀) where

  B : Over (Spec (CommRingCat.of R))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  M : CP B
  ample : RelAmple B M.L.L

  red : ∀ e : ℕ, (W.lv e).Red M

  compat : ∀ e : ℕ, (W.step e).Compat (red e) (red (e + 1))
attribute [instance] Alg.grp Alg.comm
def Alg.Represents {W : Tower I P i₀} (A : Alg W) (e : ℕ) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A.B) (χ : X) :
    Prop :=
  (A.red e).Represents c χ
end Formal
structure HidaSetting (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] where
  cdvr : CDVR V

  A : PolAV (Spec (CommRingCat.of (FractionRing V)))

  G : Over (Spec (CommRingCat.of V))
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  smooth : Smooth G.hom
  separated : IsSeparated G.hom
  quasiCompact : QuasiCompact G.hom

  gen : (Over.pullback (jK V)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom

  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]

  Q₀ : TQ (thickObj V (IsLocalRing.maximalIdeal V) 0 G) X

  P : CP G

  wA : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK V)))
  wA_gen : wA.IsGen

  symTriv : ∀ F : FormalTorus (IsLocalRing.maximalIdeal V) Q₀.i, F.HasSymTriv P
attribute [instance] HidaSetting.grp HidaSetting.comm HidaSetting.addX HidaSetting.freeX HidaSetting.finX
namespace HidaSetting
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (S : HidaSetting V)
abbrev Tower := AlgebraLevelSetting.Tower (IsLocalRing.maximalIdeal V) S.P S.Q₀.i
abbrev Alg (W : S.Tower) := AlgebraLevelSetting.Alg W
end HidaSetting
def SymTriv.triv {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {f : S' ⟶ S}
    {H : Over S'} [GrpObj H] (j : H.left ⟶ G.left) (hj : j ≫ G.hom = H.hom ≫ f) : SymTriv (CP.triv G) j hj where
  s := unitGen _ _
  gen := unitGen_isGen _ _
  cub T x y u z J _ := by
    have e : ∀ r, val (L := (CP.triv G).L.L) (unitGen ![j, H.hom ≫ f ≫ eSec G] ![1, -1]) r z J = 1 :=
      fun r => val_unitGen _ _ _ _ _
    have b : @id (T.left.presheaf.stalk z)ˣ (cubV (CP.triv G).c (T := Over.mk (T.hom ≫ f)) z J (toBase hj x)
        (toBase hj y) (toBase hj u)) = 1 := cubV_trivCub G _ _ _ _ _
    simp only [e, b, _root_.mul_one]
  even T x z J _ := (val_unitGen _ _ _ _ _).trans ((congrArg₂ (· * ·) (val_sym_triv _ _ _ _)
    (val_unitGen _ _ _ _ _)).trans (_root_.mul_one 1)).symm
example {R : Type} [CommRing R] (I : Ideal R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {X : Type} [AddCommGroup X] {i₀ : splitTorus (Lv I 0) X ⟶ thickObj R I 0 G} (F : FormalTorus I i₀) :
    F.HasSymTriv (CP.triv G) :=
  ⟨fun _ => SymTriv.triv _ _, fun _ _ _ _ _ _ => (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting
end


