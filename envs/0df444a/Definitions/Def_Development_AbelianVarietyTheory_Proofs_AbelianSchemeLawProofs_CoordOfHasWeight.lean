-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:59:50.282953+00:00
-- url     : https://prove2.me/theorems/9bcedf24-68e8-55b4-ac8d-6922382e847b
-- title:
--   Coord Of Has Weight
-- statement:
--   Definitions and structural lemmas for Coord Of Has Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoordOfHasWeight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback

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
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
namespace GlobalTheory
namespace GtBaseChange
section Chart
variable {Y Y' Z : Scheme.{0}}
def genPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (t : LB.Gen A) : LB.Gen A' :=
  ⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩
theorem gm_res_pullU (r : Z ⟶ Y') (h : Y' ⟶ Y) (z : Z) {U : Y.Opens} {V : Y'.Opens} (le : V ≤ h ⁻¹ᵁ U)
    (hz : r z ∈ V) (a : Γ(Y, U)ˣ) : gm r z V (res le (pullU h U a)) = gm (r ≫ h) z U a :=
  (gm_res r z le hz _).trans (gm_pull r h z U (le hz) a)
theorem gm_res_pullU' (h : Y' ⟶ Y) (z : Y') {U : Y.Opens} {V : Y'.Opens} (le : V ≤ h ⁻¹ᵁ U)
    (hz : z ∈ V) (a : Γ(Y, U)ˣ) : gm (𝟙 Y') z V (res le (pullU h U a)) = gm h z U a :=
  (gm_res_pullU (𝟙 Y') h z le hz a).trans (by rw [Category.id_comp])
theorem genPull_isGen {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) {t : LB.Gen A}
    (ht : t.IsGen) : (genPull a t).IsGen := fun p q => unit_ext fun y hy => by
  have hm : h y ∈ A.U (a.idx p) ⊓ A.U (a.idx q) := ⟨a.le _ hy.1, a.le _ hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx p) ⊓ A.U (a.idx q))) (ht (a.idx p) (a.idx q))
  rw [map_mul, gm_res h y _ hm, gm_res h y _ hm] at e
  rw [map_mul, gm_res (𝟙 Y') y _ hy, gm_res (𝟙 Y') y _ hy, a.g y p q hy.1 hy.2]
  exact (gm_res_pullU' h y (a.le p) hy.1 _).trans
    (e.trans (congrArg _ (gm_res_pullU' h y (a.le q) hy.2 _).symm))
def chartPullDiv {A' B' : LB Y'} {A B : LB Y} {h : Y' ⟶ Y} (b : ChartPull B' B h) (a : ChartPull A' A h) :
    ChartPull (LB.div B' A') (LB.div B A) h where
  idx p := (b.idx p.1, a.idx p.2)
  le p y hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := by
    refine (gm_div A' B' (𝟙 Y') y p q ⟨hp, hq⟩).trans (Eq.trans ?_
      (gm_div A B h y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
        ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, b.le _ hq.1, a.le _ hq.2⟩).symm)
    rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1]
end Chart
section Ext
variable {S S' : Scheme.{0}} (f : S' ⟶ S)
theorem eSec_fst (G : Over S) [GrpObj G] :
    eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f =
      (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have h := isGrpPullback_pullback G f
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G) = η[(Over.pullback f).obj G] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]
def rigChart (B : Over S) [GrpObj B] (L : LB B.left) :
    ChartPull ((L.pull (pullback.fst B.hom f)).pull (eSec ((Over.pullback f).obj B))) (L.pull (eSec B))
      (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) :=
  chartPullLinComb L _ _ _ _ _ fun _ => eSec_fst f B
def rigBC (B : Over S) [GrpObj B] (L : RigLB B) : RigLB ((Over.pullback f).obj B) where
  L := L.L.pull (pullback.fst B.hom f)
  rig := genPull (rigChart f B L.L) L.rig
  isLB := pull_isLB L.isLB _
  rigGen := genPull_isGen _ L.rigGen
theorem exists_lamChart (B : Over S) [GrpObj B] [IsCommMonObj B] (L : LB B.left) :
    ∃ U, Nonempty (ChartPull (abelian₂ ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f))) (abelian₂ B L) U) := by
  have : IsCommMonObj ((Over.pullback f).obj B) := Functor.isCommMonObj_obj
  have h := isGrpPullback_pullback B f
  let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj B) ((Over.pullback f).obj B)))
    (pushPt h.1.w (snd ((Over.pullback f).obj B) ((Over.pullback f).obj B)))
  refine ⟨U.left, ⟨chartPullLinComb L _ _ _ _ U.left
    fun I => psum_push h (x2 _) (x2 B) U (fun i => ?_) I.down⟩⟩
  fin_cases i <;> simp [U, x2]
def extBC (E : SplitExt S) : SplitExt S' where
  B := (Over.pullback f).obj E.B
  isAbelian := Out.TLinPf.isAb_pullback f E.B E.isAbelian
  X := E.X
  O χ := rigBC f E.B (E.O χ)
  addIso χ χ' := LBIso.chartPull (chartPullPull _ _ _ rfl)
    (chartPullDiv (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl)) (E.addIso χ χ')
  zeroTriv := by
    obtain ⟨t, ht⟩ := E.zeroTriv
    exact ⟨_, genPull_isGen (chartPullPull _ _ _ rfl) ht⟩
  primitive χ := by
    obtain ⟨t, ht⟩ := E.primitive χ
    have := E.isAbelian.comm
    obtain ⟨U, ⟨a⟩⟩ := exists_lamChart f E.B (E.O χ).L
    exact ⟨_, genPull_isGen a ht⟩
end Ext
section Weight
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
def HasWeight (i : splitTorus S X ⟶ G) (U : G.left.Opens) (u : Γ(G.left, U)ˣ) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ U →
    gm ((t ≫ i) * g).left z U u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z U u
end Weight
section Datum
variable {S S' : Scheme.{0}} (f : S' ⟶ S)
end Datum
end GtBaseChange
end GlobalTheory


