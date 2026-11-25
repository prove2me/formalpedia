-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:01:08.923064+00:00
-- url     : https://prove2.me/theorems/f552c111-5e8e-4842-b20a-29e488aadb6f
-- title:
--   Is CPPullback
-- statement:
--   Definitions and structural lemmas for Is CPPullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/IsCPPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
instance (priority := high) thickComm {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] : IsCommMonObj (thickObj R I e G) := inferInstance
structure Lev {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (P : CP G) (X : Type) [AddCommGroup X] (e : ℕ) where
  Q : TQ (thickObj R I e G) X
  Pe : CP (thickObj R I e G)
  lev : IsLevelCP I e Pe P
  D : Q.Desc Pe
def Lev.B {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {P : CP G} {X : Type} [AddCommGroup X] {e : ℕ} (l : Lev I P X e) : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := l.Q.B
def IsCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B]
    (M' : CP B') (M : CP B) (f : S' ⟶ S) (β : B'.left ⟶ B.left) : Prop :=
  ∃ h : IsGrpPullback B' B f β, ∃ v, IsCPMap M' M f β h.1.w v
variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
structure HidaSetting (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] where
  cdvr : CDVR V
  semi : IsSemiAbelian G
  gen : (Over.pullback (jK V)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom
  P : CP G
  wA : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK V)))
  wA_gen : wA.IsGen
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  Q₀ : TQ (thickObj V (IsLocalRing.maximalIdeal V) 0 G) X
  P₀ : CP (thickObj V (IsLocalRing.maximalIdeal V) 0 G)
  lev₀ : IsLevelCP _ 0 P₀ P
  even₀ : ∃ σ : CubTriv P₀.c Q₀.i, σ.Even
attribute [instance] HidaSetting.addX HidaSetting.freeX HidaSetting.finX
variable {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
structure Tower (s : HidaSetting V A G) where
  l : ∀ e, Lev (IsLocalRing.maximalIdeal V) s.P s.X e
  tor : ∀ e, TorusCompat (thickTrans V _ e) (thickMap V _ e G) (l e).Q.i (l (e + 1)).Q.i
  β : ∀ e, (l e).Q.B.left ⟶ (l (e + 1)).Q.B.left
  β_pb : ∀ e, IsCPPullback (l e).D.M (l (e + 1)).D.M (thickTrans V _ e) (β e)
  β_q : ∀ e, (l e).Q.q.left ≫ β e = thickMap V _ e G ≫ (l (e + 1)).Q.q.left
structure Tower.Alg {s : HidaSetting V A G} (t : Tower s) where
  B : Over (Spec (CommRingCat.of V))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B
  M : CP B
  ample : RelAmple B M.L.L
  b : ∀ e, (t.l e).Q.B.left ⟶ B.left
  b_pb : ∀ e, IsCPPullback (t.l e).D.M M (thick V _ e) (b e)
  b_β : ∀ e, t.β e ≫ b (e + 1) = b e
attribute [instance] Tower.Alg.grp Tower.Alg.comm
def AllSet (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], HidaSetting V A G → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (s : HidaSetting V A G), p s
def Tower.Alg.RepWt {s : HidaSetting V A G} {t : Tower s} (a : t.Alg) (c : 𝟙_ _ ⟶ a.B) (χ : s.X) (e : ℕ) : Prop :=
  ∃ u : LB.Gen ((LB.LinComb a.M.L.L (K := Fin 2) ![((toUnit a.B ≫ c) * 𝟙 a.B).left, 𝟙 a.B.left] ![-1, 1]).pull
      ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ
end GlobalTheory.UU
end


