-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:13.762159+00:00
-- url     : https://prove2.me/theorems/4ff8c9e4-a3c7-5923-94c4-f049c5bba64c
-- title:
--   Point Eq Of Subsingleton
-- statement:
--   Definitions and structural lemmas for Point Eq Of Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/PointEqOfSubsingleton.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {S S' : Scheme.{0}}
structure CP (G : Over S) [GrpObj G] [IsCommMonObj G] where

  L : RigLB G

  c : CubicalStr G L

  sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)
  sym_cub : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J), Good L.L z J →
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J
structure IsCPMap {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (P' : CP G') (P : CP G) (f : S' ⟶ S) (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f)
    (w : LB.Iso P'.L.L (P.L.L.pull F)) : Prop where
  mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y
  gen : w.IsGen
  vals : ∀ (T : Over S') (z : T.left) (J' : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ G.left) → P.L.L.ι),
    Good P'.L.L z J' → Good P.L.L z J →
    ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      (val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ f) z J =
        W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig T.hom z J') ∧
      (∀ x : T ⟶ G', val P.sym (x.left ≫ F) z J * W x = W x⁻¹ * val P'.sym x.left z J') ∧
      ∀ x y u : T ⟶ G', @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw x) (toBase hw y) (toBase hw u)) *
          W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u * cubV P'.c z J' x y u
section
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]
def lamφ (i : H ⟶ G) : Fin 4 → ((H ⊗ G).left ⟶ G.left) :=
  ![((fst H G ≫ i) * snd H G).left, (fst H G ≫ i).left, (snd H G).left, (1 : H ⊗ G ⟶ G).left]
structure BiTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) where

  s : LB.Gen (LB.LinComb L.L (lamφ i) Oε)
  gen : s.IsGen
  law1 : ∀ (T : Over S) (t t' : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L.L z J →
    val s (lift (t * t') x).left z J = cubV c z J (t ≫ i) (t' ≫ i) x * val s (lift t x).left z J * val s (lift t' x).left z J
  law2 : ∀ (T : Over S) (t : T ⟶ H) (x x' : T ⟶ G) (z : T.left) (J), Good L.L z J →
    val s (lift t (x * x')).left z J = cubV c z J (t ≫ i) x x' * val s (lift t x).left z J * val s (lift t x').left z J
structure CubTriv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) where

  s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])
  gen : s.IsGen
  cub : ∀ (T : Over S) (x y u : T ⟶ H) (z : T.left) (J), Good L.L z J →
    val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J =
      cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J
def CubTriv.Even {P : CP G} {i : H ⟶ G} (σ : CubTriv P.c i) : Prop :=
  ∀ (T : Over S) (x : T ⟶ H) (z : T.left) (J), Good P.L.L z J →
    val σ.s (x⁻¹).left z J = val P.sym (x ≫ i).left z J * val σ.s x.left z J
def CubWeil {L : RigLB G} (c : CubicalStr G L) (N : ℕ) {T : Over S} (x y : T ⟶ G) (ζ : Γ(T.left, ⊤)ˣ) : Prop :=
  x ^ N = 1 ∧ y ^ N = 1 ∧ ∀ (z : T.left) (J), Good L.L z J →
    gm (𝟙 T.left) z ⊤ ζ * cubN (cubV c z J) N 1 x y = cubN (cubV c z J) N 1 y x
end
def IsWt {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) (V : G.left.Opens)
    (u : Γ(G.left, V)) (χ : X) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u
structure TQ (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] where

  B : Over S
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  q : G ⟶ B

  i : splitTorus S X ⟶ G
  q_hom : IsMonHom q
  i_hom : IsMonHom i
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  isKernel : IsPullback i (toUnit _) q (η[B])
  loc : ∀ (b : B.left) (χ : X), ∃ V : B.left.Opens, b ∈ V ∧ ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ
attribute [instance] TQ.grp TQ.comm
structure TQ.Desc {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (P : CP G) where

  M : CP Q.B

  w : LB.Iso P.L.L (M.L.L.pull Q.q.left)
  map : IsCPMap P M (𝟙 S) Q.q.left (by simp) w
def TQ.GenWt {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (N : LB Q.B.left)
    (t : LB.Gen (N.pull Q.q.left)) (χ : X) : Prop :=
  t.IsGen ∧ ∀ j, IsWt Q.i _ (t.s j).val χ
def IsLevelCP {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (P' : CP (thickObj R I e G)) (P : CP G) : Prop :=
  ∃ w, IsCPMap P' P (thick R I e) (pullback.fst G.hom (thick R I e)) pullback.condition w
section Basic
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
theorem exists_good_pt {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  exact ⟨fun ψ => (exists_chart hL (ψ z)).choose, fun ψ => (exists_chart hL (ψ z)).choose_spec⟩
def scaleGen {M : LB Y} (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩
theorem scaleGen_isGen {M : LB Y} (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scaleGen u t).IsGen := by
  have rr : ∀ {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (a : Γ(Y, U)ˣ),
      res h₁ (res h₂ a) = res (h₁.trans h₂) a := by
    intro U V W h₁ h₂ a
    refine unit_ext fun x hx => ?_
    rw [gm_res (𝟙 Y) x h₁ hx, gm_res (𝟙 Y) x h₂ (h₁ hx), gm_res (𝟙 Y) x (h₁.trans h₂) hx]
  intro i j
  have e := ht i j
  simp only [scaleGen, map_mul]
  rw [e, rr, rr]
  exact mul_left_comm _ _ _
theorem val_scaleGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε))
    (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) : val (scaleGen u t) r z J = gm r z ⊤ u * val t r z J := by
  have hm := hJ.mem φ r
  have e := map_mul (gm r z (LB.wchart L φ fun k => J (r ≫ φ k))) (res le_top u) (t.s fun k => J (r ≫ φ k))
  exact e.trans (congrArg (· * gm r z _ (t.s fun k => J (r ≫ φ k))) (gm_res r z le_top hm u))
def unitGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) : LB.Gen (LB.LinComb (Inh.trivLB X) φ ε) := ⟨fun _ => 1⟩
theorem unitGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (unitGen φ ε).IsGen := by
  intro i j
  have e₁ : ∀ {A B : Y.Opens} (h : A ≤ B), res h (1 : Γ(Y, B)ˣ) = 1 := fun h => map_one _
  have e₂ : ∀ {A : X.Opens} (f : Y ⟶ X), pullU f A (1 : Γ(X, A)ˣ) = 1 := fun f => map_one _
  have e₃ : ∀ a b, (Inh.trivLB X).g a b = 1 := fun _ _ => rfl
  simp only [unitGen]
  rw [e₁, e₁, _root_.mul_one]
  symm
  refine Finset.prod_eq_one fun k _ => ?_
  rw [e₃, e₂]
  exact (congrArg (· ^ ε k) (e₁ _)).trans (one_zpow _)
theorem val_unitGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (J) : val (unitGen φ ε) r z J = 1 := by
  exact map_one _
theorem gm_top (r : Z ⟶ Y) (z : Z) (u : Γ(Y, ⊤)ˣ) :
    gm r z ⊤ u = gm (𝟙 Z) z ⊤ (Units.map r.appTop.hom.toMonoidHom u) := by
  have h := gm_pull (𝟙 Z) r z ⊤ trivial u
  rw [Category.id_comp] at h
  exact h.symm
end Basic
theorem one_left (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  have h : (toUnit T).left = T.hom := by simp
  rw [← h]
  rfl
section Triv
variable (G : Over S) [GrpObj G] [IsCommMonObj G]
def trivRig : RigLB G := ⟨Inh.trivLB _, unitGen _ _, Inh.trivLB_isLB _, unitGen_isGen _ _⟩
def trivCub : CubicalStr G (trivRig G) :=
  CubTransport.cubicalOfVal (unitGen (thφ G (x3 G)) thε) (unitGen_isGen _ _) fun _ _ _ _ =>
    ⟨fun _ _ => val_unitGen _ _ _ _ _, fun _ _ _ => (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm,
      fun _ _ _ => (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm,
      fun _ _ _ _ => congrArg₂ (· * ·) ((val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm)
        ((val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm)⟩
theorem cubV_trivCub {T : Over S} (z : T.left) (J) (x y u : T ⟶ G) : cubV (trivCub G) z J x y u = 1 := by
  exact val_unitGen _ _ _ _ _
def CP.triv : CP G where
  L := trivRig G
  c := trivCub G
  sym := unitGen _ _
  sym_gen := unitGen_isGen _ _
  sym_rig := corr_of_val (Inh.trivLB_isLB _) fun _ _ hJ =>
    (val_pull hJ _ _ _).trans ((val_unitGen _ _ _ _ _).trans (val_one _).symm)
  sym_cub T x y u z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen ![(ι[G]).left, 𝟙 G.left] ![1, -1]) r z J = 1 :=
      fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]
instance : Inhabited (CP G) := ⟨CP.triv G⟩
variable {G} {H : Over S} [GrpObj H]
theorem CP.val_sym_one (P : CP G) {T : Over S} {z : T.left} {J} (hJ : Good P.L.L z J) :
    val P.sym (1 : T ⟶ G).left z J = 1 := by
  rw [one_left, ← val_pull hJ, val_corr hJ P.sym_rig, val_one]
def BiTriv.triv (i : H ⟶ G) : BiTriv (trivCub G) i where
  s := unitGen _ _
  gen := unitGen_isGen _ _
  law1 T t t' x z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen (lamφ i) Oε) r z J = 1 := fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]
  law2 T t x x' z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen (lamφ i) Oε) r z J = 1 := fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]
def CubTriv.triv (i : H ⟶ G) : CubTriv (trivCub G) i where
  s := unitGen _ _
  gen := unitGen_isGen _ _
  cub T x y u z J _ := by
    have e : ∀ r, val (L := (trivRig G).L) (unitGen ![i.left, (1 : H ⟶ G).left] ![1, -1]) r z J = 1 :=
      fun r => val_unitGen _ _ _ _ _
    simp only [cubV_trivCub, e, _root_.mul_one]
theorem CubTriv.triv_even (i : H ⟶ G) : CubTriv.Even (P := CP.triv G) (CubTriv.triv i) := by
  intro T x z J _
  erw [val_unitGen, val_unitGen, val_unitGen, _root_.mul_one]
end Triv
section Maps
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
def toBaseHom (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) (T : Over S') :
    (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' (toBase hw) (mul T)
theorem toBase_mul_of_isMonHom {A B : Over S} [GrpObj A] [GrpObj B] (q : A ⟶ B) [IsMonHom q]
    (hq : q.left ≫ B.hom = A.hom ≫ 𝟙 S) (T : Over S) (x y : T ⟶ A) :
    toBase hq (x * y) = toBase hq x * toBase hq y := by
  have e : ∀ a : T ⟶ A, toBase hq a = (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 S) ⟶ T) ≫ a ≫ q := by
    intro a
    ext
    simp [toBase]
  rw [e, e, e, MonObj.mul_comp, MonObj.comp_mul]
theorem IsCPMap.triv (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) :
    IsCPMap (CP.triv G') (CP.triv G) f F hw ⟨fun _ => 1⟩ where
  mul := mul
  gen := by
    rw [isGen_iff]
    intro Y f' y j j' k k' _ _ _ _
    have e1 : gw (⟨fun _ => 1⟩ : LB.Iso (CP.triv G').L.L ((CP.triv G).L.L.pull F)) f' y j k = 1 := map_one _
    have e2 : gw (⟨fun _ => 1⟩ : LB.Iso (CP.triv G').L.L ((CP.triv G).L.L.pull F)) f' y j' k' = 1 := map_one _
    have e3 : gm (f' ≫ F) y _ ((CP.triv G).L.L.g j j') = 1 := map_one _
    have e4 : gm f' y _ ((CP.triv G').L.L.g k k') = 1 := map_one _
    rw [e1, e2, e3, e4, inv_one, _root_.mul_one, _root_.mul_one]
  vals := by
    intro T z J' J _ _ W hW
    have hW1 : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [hW1, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · rw [hW1, hW1, _root_.mul_one, _root_.one_mul]
      exact (val_unitGen _ _ _ _ _).trans (val_unitGen _ _ _ _ _).symm
    · have ha : cubV (CP.triv G).c z J (toBase hw x) (toBase hw y) (toBase hw u) = 1 := cubV_trivCub _ _ _ _ _ _
      have hb : cubV (CP.triv G').c z J' x y u = 1 := cubV_trivCub _ _ _ _ _ _
      rw [id_eq, ha, hb, hW1 (x * y), hW1 (x * u), hW1 (y * u), hW1 1, hW1 (x * y * u), hW1 x, hW1 y, hW1 u]
def idIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (le_inf (fun _ hx => mem_pull.1 hx.1) inf_le_right :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩
theorem gw_idIso {X Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) {j k : L.ι} (hj : r y ∈ L.U j) (hk : r y ∈ L.U k) :
    gw (idIso L) r y j k = gm r y _ (L.g j k) :=
  gm_res r y (V := (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k) _
    (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj, hk⟩) _
theorem idIso_isGen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : (idIso L).IsGen := by
  rw [isGen_iff]
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_idIso L f y hj hk, gw_idIso L f y hj' hk', Category.comp_id]
  have c1 := congrArg Additive.ofMul (gm_cocycle hL f y hj hj' hk')
  have c2 := congrArg Additive.ofMul (gm_cocycle hL f y hj hk hk')
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at c1 c2 ⊢
  linear_combination (norm := abel) c2 - c1
theorem val_change {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, gm (r ≫ φ k) z _ (L.g (J (r ≫ φ k)) (J' (r ≫ φ k))) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)
theorem cubV_toBase_id {L : RigLB G} (c : CubicalStr G L) (h : 𝟙 G.left ≫ G.hom = G.hom ≫ 𝟙 S) {T : Over S}
    (z : T.left) (J) (x y u : T ⟶ G) :
    cubV c (T := Over.mk (T.hom ≫ 𝟙 S)) z J (toBase h x) (toBase h y) (toBase h u) = cubV c z J x y u := by
  have e : ∀ a : T ⟶ G, toBase h a = (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 S) ⟶ T) ≫ a := by
    intro a
    ext
    simp [toBase]
  unfold cubV
  rw [e, e, e, ← comp_lift, ← comp_lift]
  simp only [Over.comp_left, Over.homMk_left]
  exact congrArg (fun r => val c.t r z J) (Category.id_comp _)
theorem prod_sym {T : Over S} (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Category.comp_id]
  rfl
theorem IsCPMap.id (P : CP G) : IsCPMap P P (𝟙 S) (𝟙 G.left) (by simp) (idIso P.L.L) where
  mul := fun T x y => toBase_mul_of_isMonHom (𝟙 G) _ T x y
  gen := idIso_isGen P.L.isLB
  vals := by
    intro T z J' J hJ' hJ W hW
    simp only [Category.comp_id] at hW
    have hW1 : ∀ x : T ⟶ G, W x = gm x.left z _ (P.L.L.g (J x.left) (J' x.left)) := fun x =>
      (hW x).trans (gw_idIso P.L.L x.left z (hJ x.left) (hJ' x.left))
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [Category.comp_id, val_change P.L.rigGen _ hJ hJ', hW1 1, one_left]
      simp only [Fintype.prod_unique, zpow_one]
    · rw [Category.comp_id, val_change P.sym_gen _ hJ hJ',
        prod_sym x (fun ψ => gm ψ z _ (P.L.L.g (J ψ) (J' ψ))), hW1, hW1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have hc0 := val_change (φ := thφ G (x3 G)) (ε := thε) P.c.isGen (lift x (lift y u)).left hJ hJ'
      have hc : cubV P.c z J x y u = _ :=
        hc0.trans (congrArg (fun a => a * val P.c.t (lift x (lift y u)).left z J')
          (prod_cub x y u (fun ψ => gm ψ z _ (P.L.L.g (J ψ) (J' ψ)))))
      have hc2 : cubV P.c z J' x y u = val P.c.t (lift x (lift y u)).left z J' := rfl
      rw [id_eq, cubV_toBase_id, hc, ← hc2]
      simp only [hW1]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
def pullIso {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X) : LB.Iso (L.pull F) (L.pull F) :=
  ⟨fun p => (L.pull F).g p.1 p.2⟩
end Maps
section Abelian
variable {G : Over S} [GrpObj G] [IsCommMonObj G]
theorem sym_cub_of_surjective (h3 : Function.Surjective (G3 G).hom.appTop.hom) {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L))
    (T : Over S) (x y u : T ⟶ G) (z : T.left) (J) (hJ : Good L.L z J) :
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J *
        val sym u.left z J := by
  have hq : ∀ {T' : Over S} (a b d : T' ⟶ G), lift a (lift b d) ≫ x3 G 0 = a ∧ lift a (lift b d) ≫ x3 G 1 = b ∧
      lift a (lift b d) ≫ x3 G 2 = d := fun a b d => by simp [x3]
  let g1 := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 0)⁻¹ (lift (x3 G 1)⁻¹ (x3 G 2)⁻¹)).left)
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 1).left))
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 2).left))
      (LB.pullGen L.L _ _ sym (x3 G 1 * x3 G 2).left)
  let g2 := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 0) (lift (x3 G 1) (x3 G 2))).left)
      (LB.pullGen L.L _ _ sym (x3 G 0 * x3 G 1 * x3 G 2).left))
      (LB.pullGen L.L _ _ sym (x3 G 0).left))
      (LB.pullGen L.L _ _ sym (x3 G 1).left))
      (LB.pullGen L.L _ _ sym (x3 G 2).left)
  have hg1 : g1.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.pullGen_isGen _ _ _ _ hs _))
    (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)
  have hg2 : g2.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.pullGen_isGen _ _ _ _ hs _))
    (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ hs _)

  have vals3 : ∀ {T' : Over S} (a b d : T' ⟶ G) (w : T'.left) (J' : (T'.left ⟶ G.left) → L.L.ι), Good L.L w J' →
      val g1 (lift a (lift b d)).left w J' = cubV c w J' a⁻¹ b⁻¹ d⁻¹ * val sym (a * b).left w J' *
        val sym (a * d).left w J' * val sym (b * d).left w J' ∧
      val g2 (lift a (lift b d)).left w J' = cubV c w J' a b d * val sym (a * b * d).left w J' *
        val sym a.left w J' * val sym b.left w J' * val sym d.left w J' := by
    intro T' a b d w J' hJ'
    obtain ⟨h0, h1, h2⟩ := hq a b d
    constructor
    · rw [val_mul hJ', val_mul hJ']
      erw [val_mul hJ', val_cub c (lift a (lift b d)) hJ']
      rw [val_pull hJ', val_pull hJ', val_pull hJ']
      simp only [← Over.comp_left, MonObj.comp_mul, GrpObj.comp_inv, h0, h1, h2]
    · rw [val_mul hJ', val_mul hJ', val_mul hJ']
      erw [val_mul hJ', val_cub c (lift a (lift b d)) hJ']
      rw [val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
      simp only [← Over.comp_left, MonObj.comp_mul, h0, h1, h2]
  clear_value g1 g2

  have hone : ∀ (w : (𝟙_ (Over S)).left) (J'), Good L.L w J' → val sym (1 : 𝟙_ (Over S) ⟶ G).left w J' = 1 := by
    intro w J' hJ'
    rw [one_left G (𝟙_ (Over S))]
    have e1 := val_corr hJ' hr (𝟙_ (Over S)).hom
    rwa [val_pull hJ', val_one] at e1

  have hagree : ∀ w J', Good L.L w J' → val g1 (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left w J' =
      val g2 (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left w J' := by
    intro w J' hJ'
    rw [(vals3 1 1 1 w J' hJ').1, (vals3 1 1 1 w J' hJ').2]
    simp only [inv_one, _root_.mul_one, hone w J' hJ', (isCub_cubV c hJ').face]
  have key : val g1 (lift x (lift y u)).left z J = val g2 (lift x (lift y u)).left z J := by
    refine gen_unique' L.isLB ?_ (G3 G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left
      (Over.w (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1))) h3 hg1 hg2 hagree T.left _ z J hJ
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, prod_sym]
    erw [prod_cub, prod_cub]
    simp only [_root_.mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [(vals3 x y u z J hJ).1, (vals3 x y u z J hJ).2] at key
  exact key
def CP.ofSurjective (h3 : Function.Surjective (G3 G).hom.appTop.hom) (L : RigLB G) (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L)) : CP G :=
  ⟨L, c, sym, hs, hr, sym_cub_of_surjective h3 c sym hs hr⟩
theorem surjective_cube (hG : GlobalFnsSt) (hA : IsAbelianScheme G) : Function.Surjective (G3 G).hom.appTop.hom := by
  have h1 : Function.Surjective G.hom.appTop.hom := (hG S G hA).2
  have h2 : Function.Surjective (G ⊗ G).hom.appTop.hom := by
    rw [← Over.w (snd G G)]
    exact surj_comp (surj_snd hG hA G) h1
  have h3 : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom := by
    rw [← Over.w (snd G (G ⊗ G))]
    exact surj_comp (surj_snd hG hA (G ⊗ G)) h2
  exact h3
def CP.ofDegPre (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : CP D.P.A :=
  CP.ofSurjective (surjective_cube hG D.P.isAb) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub D.sym D.sym_gen D.sym_rig
end Abelian
section Weil
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x y : T ⟶ G}
theorem CubWeil.symm {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : CubWeil c N y x ζ⁻¹ := by
  refine ⟨h.2.1, h.1, fun z J hJ => ?_⟩
  rw [map_inv, ← h.2.2 z J hJ, inv_mul_cancel_left]
variable {i : H ⟶ G} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
theorem CubTriv.val_one [IsMonHom i] (σ : CubTriv c i) (hJ : Good L.L z J) : val σ.s (1 : T ⟶ H).left z J = 1 := by
  have e := σ.cub T 1 1 1 z J hJ
  simp only [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, _root_.one_mul] at e
  exact mul_left_cancel (e.trans (_root_.mul_one _).symm)
end Weil
section Torus
variable {X : Type} [AddCommGroup X]
def chV {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : Γ(Z.left, ⊤)ˣ :=
  splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)
theorem chV_val {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV t χ).val = t.left.appTop.hom (charUnit S X χ).val := by
  exact splitTorusPointsEquiv_val S X Z t χ
theorem chV_mul {Z : Over S} (t t' : Z ⟶ splitTorus S X) (χ : X) : chV (t * t') χ = chV t χ * chV t' χ := by
  simp only [chV, map_mul, MonoidHom.mul_apply]
theorem chV_inv {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : chV t⁻¹ χ = (chV t χ)⁻¹ := by
  simp only [chV, map_inv, MonoidHom.inv_apply]
theorem chV_add {Z : Over S} (t : Z ⟶ splitTorus S X) (χ χ' : X) : chV t (χ + χ') = chV t χ * chV t χ' := by
  simp only [chV, ofAdd_add, map_mul]
theorem chV_zero {Z : Over S} (t : Z ⟶ splitTorus S X) : chV t 0 = 1 := by
  simp only [chV, ofAdd_zero, map_one]
theorem gm_charUnit {Z : Over S} (t : Z ⟶ splitTorus S X) (z : Z.left) (χ : X) :
    gm t.left z ⊤ (charUnit S X χ) = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  rw [gm_top]
  congr 1
  ext
  rw [chV_val]
  rfl
section Twist
variable {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G}
def CubTriv.twist {L : RigLB G} {c : CubicalStr G L} (σ : CubTriv c i) (χ : X) : CubTriv c i where
  s := scaleGen (charUnit S X χ) σ.s
  gen := scaleGen_isGen _ σ.gen
  cub T x y u z J hJ := by
    have e := σ.cub T x y u z J hJ
    simp only [val_scaleGen _ _ _ hJ, gm_charUnit, chV_mul, map_mul]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at e' ⊢
    linear_combination (norm := abel) e'
theorem CubTriv.val_twist {L : RigLB G} {c : CubicalStr G L} (σ : CubTriv c i) (χ : X) {T : Over S}
    (x : T ⟶ splitTorus S X) {z : T.left} {J} (hJ : Good L.L z J) :
    val (σ.twist χ).s x.left z J = gm (𝟙 T.left) z ⊤ (chV x χ) * val σ.s x.left z J := by
  show val (scaleGen (charUnit S X χ) σ.s) x.left z J = _
  rw [val_scaleGen _ _ _ hJ, gm_charUnit]
theorem CubTriv.twist_even_iff {P : CP G} {σ : CubTriv P.c i} (hσ : σ.Even) (χ : X) :
    (σ.twist χ).Even ↔ ∀ (T : Over S) (t : T ⟶ splitTorus S X), chV t (χ + χ) = 1 := by
  constructor
  · intro htw T t
    apply unit_ext
    intro z _
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    have h1 := htw T t z J hJ
    have h0 := hσ T t z J hJ
    rw [CubTriv.val_twist _ _ _ hJ, CubTriv.val_twist _ _ _ hJ, h0, chV_inv, map_inv] at h1
    have h2 : (gm (𝟙 T.left) z ⊤ (chV t χ))⁻¹ = gm (𝟙 T.left) z ⊤ (chV t χ) :=
      mul_right_cancel (b := val P.sym (t ≫ i).left z J * val σ.s t.left z J) (by rw [h1, mul_left_comm])
    rw [chV_add, map_mul, map_one]
    have h3 := mul_inv_cancel (gm (𝟙 T.left) z ⊤ (chV t χ))
    rwa [h2] at h3
  · intro h T x z J hJ
    have hc : (chV x χ)⁻¹ = chV x χ := inv_eq_of_mul_eq_one_right (by rw [← chV_add]; exact h T x)
    rw [CubTriv.val_twist _ _ _ hJ, CubTriv.val_twist _ _ _ hJ, hσ T x z J hJ, chV_inv, hc, mul_left_comm]
def CP.twistSym (P : CP (splitTorus S X)) (χ : X) : CP (splitTorus S X) where
  L := P.L
  c := P.c
  sym := scaleGen (charUnit S X χ) P.sym
  sym_gen := scaleGen_isGen _ P.sym_gen
  sym_rig := corr_of_val P.L.isLB fun y J hJ => by
    have e := (val_scaleGen (charUnit S X χ) P.sym (1 : 𝟙_ (Over S) ⟶ splitTorus S X).left hJ).trans
      (congrArg₂ (· * ·) (gm_charUnit _ y χ) (P.val_sym_one hJ))
    have o : chV (1 : 𝟙_ (Over S) ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
    rw [o, map_one, _root_.one_mul, one_left] at e
    exact (val_pull hJ _ _ _).trans (e.trans (val_one _).symm)
  sym_cub T x y u z J hJ := by
    have e := P.sym_cub T x y u z J hJ
    simp only [val_scaleGen _ _ _ hJ, gm_charUnit, chV_mul, map_mul]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at e' ⊢
    linear_combination (norm := abel) e'
end Twist
section Wt
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V V' : G.left.Opens}
theorem isWt_one : IsWt i V 1 0 := by
  intro Z t g h₁ h₂
  rw [← chV_val, chV_zero]
  simp
theorem IsWt.res {u : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ) (h : V' ≤ V) :
    IsWt i V' ((G.left.presheaf.map (homOfLE h).op).hom u) χ := by
  intro Z t g h₁ h₂
  have k : ∀ (f : Z.left ⟶ G.left) (e : ⊤ ≤ f ⁻¹ᵁ V'),
      (f.appLE V' ⊤ e).hom ((G.left.presheaf.map (homOfLE h).op).hom u) =
        (f.appLE V ⊤ (e.trans (f.preimage_mono h))).hom u := by
    intro f e
    exact congrArg (fun φ => φ.hom u) (Scheme.Hom.map_appLE f e (homOfLE h).op)
  rw [k, k]
  exact hu Z t g _ _
theorem isWt_top_iff {u : Γ(G.left, ⊤)} {χ : X} : IsWt i ⊤ u χ ↔ ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G),
    ((t ≫ i) * g).left.appTop.hom u = (chV t χ).val * g.left.appTop.hom u := by
  have k : ∀ {Y : Scheme.{0}} (f : Y ⟶ G.left) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), (f.appLE ⊤ ⊤ e).hom u = f.appTop.hom u := by
    intro Y f e
    exact congrArg (fun φ => φ.hom u) (Scheme.Hom.appLE_eq_app f (U := ⊤))
  constructor
  · intro h Z t g
    rw [chV_val, ← k ((t ≫ i) * g).left (Scheme.Hom.preimage_top _).ge, ← k g.left (Scheme.Hom.preimage_top _).ge]
    exact h Z t g _ _
  · intro h Z t g h₁ h₂
    rw [k, k, ← chV_val]
    exact h Z t g
theorem isWt_of_retraction (p : G ⟶ splitTorus S X) [IsMonHom p] (hp : i ≫ p = 𝟙 _) (χ : X) :
    IsWt i ⊤ (chV p χ).val χ := by
  rw [isWt_top_iff]
  intro Z t g
  have k : ∀ {Y : Over S} (f : Y ⟶ G), f.left.appTop.hom (chV p χ).val = (chV (f ≫ p) χ).val := by
    intro Y f
    rw [chV_val, chV_val]
    rfl
  rw [k, k, MonObj.mul_comp, chV_mul, Units.val_mul, Category.assoc, hp, Category.comp_id]
theorem isWt_charUnit (χ : X) : IsWt (𝟙 (splitTorus S X)) ⊤ (charUnit S X χ).val χ := by
  have e : (charUnit S X χ).val = (chV (𝟙 (splitTorus S X)) χ).val := by
    rw [chV_val]
    rfl
  rw [e]
  exact isWt_of_retraction (𝟙 _) (Category.id_comp _) χ
end Wt
theorem isAbelianScheme_unit (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) := by
  constructor
  all_goals first
    | infer_instance
    | (show Smooth (𝟙 S); infer_instance)
    | (show IsProper (𝟙 S); infer_instance)
    | (show GeometricallyConnected (𝟙 S)
       refine ⟨fun K _ y Z fst snd h => ?_⟩
       have : IsIso snd := h.isIso_snd_of_isIso
       exact ObjectProperty.prop_of_iso (fun Y : Scheme.{0} => ConnectedSpace Y) (asIso snd).symm
         (inferInstance : ConnectedSpace (Spec (CommRingCat.of K))))
def TQ.torus (S : Scheme.{0}) (X : Type) [AddCommGroup X] : TQ (splitTorus S X) X where
  B := 𝟙_ (Over S)
  isAb := isAbelianScheme_unit S
  q := toUnit _
  i := 𝟙 _
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by rw [Rosenlicht.toUnit_left]; exact Diag.flat_hom S X
  q_surj := by rw [Rosenlicht.toUnit_left]; exact Diag.surjective_hom S X
  q_affine := by rw [Rosenlicht.toUnit_left]; exact Diag.isAffineHom_hom S X
  isKernel := by
    have : IsIso (η[𝟙_ (Over S)]) := by rw [toUnit_unique η[𝟙_ (Over S)] (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  loc _ χ := ⟨⊤, trivial, charUnit S X χ, isWt_charUnit χ⟩
theorem point_eq_of_subsingleton [Subsingleton X] {Z : Over S} (t t' : Z ⟶ splitTorus S X) : t = t' := by
  refine (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun x => ?_)
  rw [show x = 1 from Multiplicative.toAdd.injective (Subsingleton.elim _ _), map_one, map_one]
def TQ.abelian (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) (X : Type) [AddCommGroup X] [Subsingleton X] :
    TQ G X where
  B := G
  comm := hG.comm
  isAb := hG
  q := 𝟙 G
  i := toUnit _ ≫ η[G]
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by rw [Over.id_left]; infer_instance
  q_surj := by rw [Over.id_left]; infer_instance
  q_affine := by rw [Over.id_left]; infer_instance
  isKernel := by
    have : IsIso (toUnit (splitTorus S X)) := ⟨η, point_eq_of_subsingleton _ _, toUnit_unique _ _⟩
    exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  loc _ χ := ⟨⊤, trivial, 1, Subsingleton.elim 0 χ ▸ isWt_one⟩
def TQ.prod (X : Type) [AddCommGroup X] (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    TQ (splitTorus S X ⊗ A) X where
  B := A
  comm := hA.comm
  isAb := hA
  q := snd _ _
  i := lift (𝟙 _) (toUnit _ ≫ η[A])
  q_hom := inferInstance
  i_hom := inferInstance
  q_flat := by show Flat (pullback.snd _ _); infer_instance
  q_surj := by show Surjective (pullback.snd _ _); infer_instance
  q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (splitTorus S X).hom A.hom) (Diag.isAffineHom_hom S X)
  isKernel := IsPullback.of_isLimit' ⟨lift_snd _ _⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst _ _)
    (fun s => by
      ext
      · simp
      · simp only [Category.assoc, lift_snd]
        rw [s.condition, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) s.snd])
    (fun s => toUnit_unique _ _) (fun s m h _ => by rw [← h]; simp))
  loc _ χ := ⟨⊤, trivial, chV (fst _ _) χ, isWt_of_retraction (fst _ _) (lift_fst _ _) χ⟩
def TQ.Desc.triv {G : Over S} [GrpObj G] [IsCommMonObj G] (Q : TQ G X) : Q.Desc (CP.triv G) where
  M := CP.triv Q.B
  w := ⟨fun _ => 1⟩
  map := IsCPMap.triv (have := Q.q_hom; toBase_mul_of_isMonHom Q.q _)
def TQ.Desc.abelian {G : Over S} [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) [Subsingleton X] (P : CP G) :
    (TQ.abelian G hG X).Desc P where
  M := P
  w := idIso P.L.L
  map := IsCPMap.id P
theorem TQ.genWt_triv {G : Over S} [GrpObj G] (Q : TQ G X) (u : Γ(G.left, ⊤)ˣ) {χ : X} (hu : IsWt Q.i ⊤ u.val χ) :
    Q.GenWt (Inh.trivLB _) (scaleGen u (unitGen _ _)) χ := by
  refine ⟨scaleGen_isGen u (unitGen_isGen _ _), fun j => ?_⟩
  show IsWt Q.i _ (res le_top u * 1).val χ
  rw [_root_.mul_one]
  exact hu.res le_top
example (χ : X) : (TQ.torus S X).GenWt (Inh.trivLB _) (scaleGen (charUnit S X χ) (unitGen _ _)) χ :=
  (TQ.torus S X).genWt_triv _ (isWt_charUnit χ)
end Torus
section Basic₂
theorem exists_point_two : ∃ t : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ splitTorus (Spec (CommRingCat.of ℚ)) ℤ,
    ∀ n : ℤ, chV t n = 1 → n = 0 := by
  let e : ℚ ≃+* Γ(Spec (CommRingCat.of ℚ), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv
  let u : Γ(Spec (CommRingCat.of ℚ), ⊤)ˣ := Units.map e.toMonoidHom (Units.mk0 2 two_ne_zero)
  refine ⟨(splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ u), fun n hn => ?_⟩
  have h1 : u ^ n = 1 := by
    simpa only [chV, MulEquiv.apply_symm_apply, zpowersHom_apply, toAdd_ofAdd] using hn
  have h2 : (Units.mk0 (2:ℚ) two_ne_zero) ^ n = 1 := by
    have hu : Units.map e.symm.toMonoidHom u = Units.mk0 2 two_ne_zero := Units.ext (by simp [u])
    rw [← hu, ← map_zpow, h1, map_one]
  have h3 : (2:ℚ) ^ n = 1 := by
    have h4 := congrArg Units.val h2
    rwa [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_one] at h4
  exact zpow_right_injective₀ (by norm_num : (0:ℚ) < 2) (by norm_num) (h3.trans (zpow_zero (2:ℚ)).symm)
example : ¬ CubTriv.Even (P := CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ))
    ((CubTriv.triv (𝟙 _)).twist (1 : ℤ)) := fun h => by
  obtain ⟨t, ht⟩ := exists_point_two
  exact absurd (ht _ ((CubTriv.twist_even_iff (CubTriv.triv_even _) 1).1 h _ t)) (by norm_num)
example : ¬ CubTriv.Even (P := (CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1)
    (CubTriv.triv (𝟙 _)) := fun h => by
  obtain ⟨t, ht⟩ := exists_point_two
  refine absurd (ht 1 (unit_ext fun z _ => ?_)) one_ne_zero
  obtain ⟨J, hJ⟩ := exists_good_pt (Inh.trivLB_isLB (splitTorus (Spec (CommRingCat.of ℚ)) ℤ).left) z
  have e := ((val_unitGen _ _ _ _ _).symm.trans (h _ t z J hJ)).trans (congrArg₂ (· * ·)
    ((val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) (gm_charUnit _ z _) (val_unitGen _ _ _ _ _)))
    (val_unitGen _ _ _ _ _))
  rw [_root_.mul_one, _root_.mul_one, Category.comp_id] at e
  exact e.symm.trans (map_one _).symm
example : IsWt (𝟙 _) ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1).val (1 : ℤ) ∧
    ¬ IsWt (𝟙 _) ⊤ (charUnit (Spec (CommRingCat.of ℚ)) ℤ 1).val (-1 : ℤ) := by
  refine ⟨isWt_charUnit 1, fun h => ?_⟩
  obtain ⟨t, ht⟩ := exists_point_two
  have a := isWt_top_iff.1 h _ t t
  rw [Category.comp_id, ← chV_val, ← chV_val, chV_mul, ← Units.val_mul, Units.val_inj, mul_left_inj] at a
  have b : chV t (1 + 1) = 1 := by
    rw [chV_add]
    exact (congrArg (· * chV t 1) a).trans (by rw [← chV_add, neg_add_cancel, chV_zero])
  exact absurd (ht _ b) (by norm_num)
example : Nonempty (TQ (splitTorus S ℤ) ℤ) := ⟨TQ.torus S ℤ⟩
example (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) : Nonempty (TQ G PUnit) := ⟨TQ.abelian G hG PUnit⟩
end Basic₂
end GlobalTheory.UU
end


