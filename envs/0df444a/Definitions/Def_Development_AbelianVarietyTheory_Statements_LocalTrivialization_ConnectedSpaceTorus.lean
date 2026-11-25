-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_ConnectedSpaceTorus
-- name    : Development_AbelianVarietyTheory_Statements_LocalTrivialization_ConnectedSpaceTorus
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:23:06.838867+00:00
-- url     : https://prove2.me/theorems/c1cc0780-9b73-5d63-9dc1-3a81bd9c6517
-- title:
--   Connected Space Torus
-- statement:
--   Definitions and structural lemmas for Connected Space Torus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/ConnectedSpaceTorus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_of_section
import Theorems.Thm_GlobalTheory_GroupConn_connectedSpace_tensor
import Theorems.Thm_GlobalTheory_SplitTorus_mul_left_bcMap
import Theorems.Thm_GlobalTheory_UU_BiTriv_val_one_left
import Theorems.Thm_GlobalTheory_UU_BiTriv_val_one_right
import Theorems.Thm_GlobalTheory_UU_CubTriv_twist_even_twistSym
import Theorems.Thm_GlobalTheory_UU_IsCPMap_exists_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_UU_TQ_exists_desc
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_exists_isCPMap
import Theorems.Thm_GlobalTheory_UU_pullIso_isGen
import Theorems.Thm_GlobalTheory_UU_val_sym_triv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_over_appTop_comp

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
def CPPullSt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
  (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f),
  (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) → ∀ P : CP G,
  ∃ (P' : CP G') (w : _), P'.L.L = P.L.L.pull F ∧ IsCPMap P' P f F hw w
def CPCompSt : Prop := ∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G]
  (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G')
  (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f')
  (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w →
  (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧
  ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) →
    ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')
def CubicUnitSt : Prop := GlobalFnsSt → ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
  (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ),
  (∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) →
    U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) → u = 1
def BiTrivUniqSt : Prop := ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G] [IsCommMonObj G]
  [ConnectedSpace G.left] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus S X ⟶ G), IsMonHom i →
  ∀ s s' : BiTriv c i, s = s'
def BiTrivFieldSt : Prop := ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
  (L : RigLB G) (c : CubicalStr G L) (i : splitTorus _ X ⟶ G), IsMonHom i → Nonempty (BiTriv c i)
def BiTrivLiftSt : Prop := ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
  (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] [ConnectedSpace G₀.left]
  (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
  ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i →
  Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c i)
def CubTrivLiftSt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → J ≠ ⊤ →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
  (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀]
  (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
  ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i →
  Nonempty (BiTriv P.c i) → (∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c i, σ.Even
def CubTrivDeltaSt : Prop := ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
  (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (i : splitTorus S X ⟶ G), IsMonHom i →
  (∀ (s : BiTriv P.c i) (σ : CubTriv P.c i) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
    val σ.s (t * t').left z J = val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J) ∧
  ∀ σ σ' : CubTriv P.c i, σ.Even → σ'.Even → σ = σ'
def EquivDescSt : Prop := ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over S) [GrpObj G] (Q : TQ G X) (L : LB G.left), L.IsLB →
  ∀ a : LB.Gen (LB.LinComb L (K := Fin 2)
    ![((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left, (snd (splitTorus S X) G).left] ![1, -1]), a.IsGen →
  (∀ (T : Over S) (t t' : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J), Good L z J →
    val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ Q.i) * x)).left z J * val a (lift t' x).left z J) →
  ∃ (M : LB Q.B.left) (w : LB.Iso L (M.pull Q.q.left)), M.IsLB ∧ w.IsGen ∧
    ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J →
      Q.q.left (x.left z) ∈ M.U j →
      gw w ((t ≫ Q.i) * x).left z j (J ((t ≫ Q.i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left)
def DescSt : Prop := ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (Q : TQ G X) (P : CP G), Nonempty (BiTriv P.c Q.i) →
  (∃ σ : CubTriv P.c Q.i, σ.Even) → Nonempty (Q.Desc P)
def IsoDescSt : Prop := ∀ (S S' : Scheme.{0}) [ConnectedSpace S'] (f : S' ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
  (G' : Over S') [GrpObj G'] [IsCommMonObj G'] [ConnectedSpace G'.left] (Q : TQ G' X) (P' : CP G') (D : Q.Desc P')
  (B : Over S) [GrpObj B] [IsCommMonObj B] (M : CP B) (β : Q.B.left ⟶ B.left) (hβ : β ≫ B.hom = Q.B.hom ≫ f) (hw) (w),
  (∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y) →
  IsCPMap P' M f (Q.q.left ≫ β) hw w → ∃ v, IsCPMap D.M M f β hβ v
def WtBundleSt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X]
  (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (χ : X),
  ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ ∧ ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen
def BiextDescentSt : Prop :=
  CPPullSt ∧ CPCompSt ∧ CubicUnitSt ∧ BiTrivUniqSt ∧ BiTrivFieldSt ∧ BiTrivLiftSt ∧ CubTrivLiftSt ∧ CubTrivDeltaSt ∧
    EquivDescSt ∧ DescSt ∧ IsoDescSt ∧ WtBundleSt
namespace BiextCheck
open SplitTorus (bcMap bcMap_hom)
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]
abbrev twCP (S : Scheme.{0}) (χ : X) : CP (splitTorus S X) := (CP.triv (splitTorus S X)).twistSym χ
abbrev twTriv (S : Scheme.{0}) (χ ψ : X) : CubTriv (twCP S χ).c (𝟙 _) := (CubTriv.triv (𝟙 _)).twist ψ
theorem twTriv_even (S : Scheme.{0}) (ψ : X) : (twTriv S (-(ψ + ψ)) ψ).Even :=
  CubTriv.twist_even_twistSym (CubTriv.triv_even _) ψ
theorem good_triv {Y Z : Scheme.{0}} (z : Z) (J) : Good (Inh.trivLB Y) z J := fun _ => trivial
theorem val_sym_twCP (χ : X) {Z : Scheme.{0}} (r : Z ⟶ (splitTorus S X).left) (z : Z) (J) :
    val (twCP S χ).sym r z J = gm r z ⊤ (charUnit S X χ) :=
  (val_scaleGen (L := Inh.trivLB _) (charUnit S X χ) _ r (good_triv z J)).trans
    ((congrArg (_ * ·) (val_unitGen _ _ _ _ _)).trans (_root_.mul_one _))
theorem val_twTriv (χ ψ : X) {T : Over S} (t : T ⟶ splitTorus S X) (z : T.left) (J) :
    val (twTriv S χ ψ).s t.left z J = gm (𝟙 T.left) z ⊤ (chV t ψ) :=
  (CubTriv.val_twist (CubTriv.triv (𝟙 _)) ψ t (good_triv z J)).trans
    ((congrArg (_ * ·) (val_unitGen _ _ _ _ _)).trans (_root_.mul_one _))
theorem gw_scale {Y Y' Z : Scheme.{0}} (F : Y' ⟶ Y) (u : Γ(Y', ⊤)ˣ) (r : Z ⟶ Y') (z : Z) (j k) :
    gw (L := Inh.trivLB Y) (L' := Inh.trivLB Y') (F := F) (scaleGen u ⟨fun _ => 1⟩) r z j k = gm r z ⊤ u :=
  (congrArg (gm r z _) (_root_.mul_one _)).trans
    (gm_res r z _ (show r z ∈ ((Inh.trivLB Y).pull F).U (fun _ => j) ⊓ (Inh.trivLB Y').U k from
      ⟨mem_pull.2 trivial, trivial⟩) u)
theorem connectedSpace_torus (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    ConnectedSpace (splitTorus S X).left :=
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  GroupConn.connectedSpace_of_section (splitTorus S X).hom (η : 𝟙_ (Over S) ⟶ splitTorus S X).left (Over.w _)
theorem toBase_mul_bcMap (f : S' ⟶ S) (T : Over S') (x y : T ⟶ splitTorus S' X) :
    toBase (bcMap_hom f X) (x * y) = toBase (bcMap_hom f X) x * toBase (bcMap_hom f X) y :=
  Over.OverMorphism.ext (SplitTorus.mul_left_bcMap f X T x y _ _ rfl rfl).symm
theorem isCPMap_bcMap (f : S' ⟶ S) (χ : X) :
    IsCPMap (twCP S' χ) (twCP S χ) f (bcMap f X) (bcMap_hom f X) ⟨fun _ => 1⟩ := by
  have h := IsCPMap.triv (toBase_mul_bcMap (X := X) f)
  refine ⟨h.mul, h.gen, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨a, -, c⟩ := h.vals T z J' J hJ' hJ W hW
  refine ⟨a, fun x => ?_, c⟩
  have e : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
  rw [e, e, val_sym_twCP, val_sym_twCP, _root_.mul_one, _root_.one_mul]
  exact (gm_pull x.left (bcMap f X) z ⊤ trivial _).symm.trans (congrArg _ (Units.ext (bcMap_charUnit f χ)))
theorem chV_neg {Z : Over S} (t : Z ⟶ splitTorus S X) (χ : X) : chV t (-χ) = (chV t χ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← chV_add, neg_add_cancel, chV_zero])
theorem chV_one {Z : Over S} (χ : X) : chV (1 : Z ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
theorem val_fst {G : Over S} {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → ((splitTorus S X ⊗ G).left ⟶ Y))
    (ε : K → ℤ) (χ : X) {T : Over S} (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J) :
    val (scaleGen (chV (fst (splitTorus S X) G) χ) (unitGen φ ε)) (lift t x).left z J =
      gm (𝟙 T.left) z ⊤ (chV t χ) := by
  refine (val_scaleGen _ _ _ (good_triv z J)).trans ?_
  rw [val_unitGen, _root_.mul_one, gm_top]
  refine congrArg _ (Units.ext ?_)
  show (lift t x).left.appTop.hom (chV _ χ).val = _
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp, lift_fst]
def twDesc (S : Scheme.{0}) (ψ : X) : (TQ.torus S X).Desc (twCP S (-(ψ + ψ))) where
  M := CP.triv _
  w := scaleGen (charUnit S X (-ψ)) ⟨fun _ => 1⟩
  map := by
    have h := (TQ.Desc.triv (TQ.torus S X)).map
    refine ⟨h.mul, scaleGen_isGen _ h.gen, fun T z J' J hJ' hJ W hW => ?_⟩
    have e : ∀ x, W x = (gm (𝟙 T.left) z ⊤ (chV x ψ))⁻¹ := fun x =>
      (hW x).trans ((gw_scale _ _ _ _ _ _).trans ((gm_charUnit x z _).trans (by rw [chV_neg, map_inv])))
    refine ⟨(val_unitGen _ _ _ _ _).trans ?_, fun x => ?_, fun x y u => ?_⟩
    · rw [e, chV_one, map_one, inv_one, _root_.one_mul]; exact (val_unitGen _ _ _ _ _).symm
    · rw [e, e, val_sym_triv, val_sym_twCP, gm_charUnit, chV_inv, chV_neg, chV_add]
      simp only [map_inv, map_mul, inv_inv, mul_inv, _root_.one_mul, mul_inv_cancel_left]
    · have b : ∀ p q r, @id (T.left.presheaf.stalk z)ˣ
          (cubV (CP.triv (TQ.torus S X).B).c (T := Over.mk (T.hom ≫ 𝟙 S)) z J p q r) = 1 :=
        fun _ _ _ => cubV_trivCub _ _ _ _ _ _
      have c : cubV (twCP S (-(ψ + ψ))).c z J' x y u = 1 := cubV_trivCub _ _ _ _ _ _
      rw [b, c]
      simp only [e, chV_mul, chV_one, map_mul, map_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
example : CPPullSt := fun _ _ _ _ _ _ _ _ _ F _ mul P => by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := exists_isCPMap P mul _ (pull_isLB P.L.isLB F) _ (pullIso_isGen P.L.isLB F)
  exact ⟨_, _, rfl, h⟩
example {S'' : Scheme.{0}} (f : S' ⟶ S) (f' : S'' ⟶ S') (χ : X)
    (hw'' : (bcMap f' X ≫ bcMap f X) ≫ (splitTorus S X).hom = (splitTorus S'' X).hom ≫ f' ≫ f) :
    ∃ w w' w'', IsCPMap (twCP S' χ) (twCP S χ) f (bcMap f X) (bcMap_hom f X) w ∧
      IsCPMap (twCP S'' χ) (twCP S' χ) f' (bcMap f' X) (bcMap_hom f' X) w' ∧
      IsCPMap (twCP S'' χ) (twCP S χ) (f' ≫ f) (bcMap f' X ≫ bcMap f X) hw'' w'' ∧ Tri w w' w'' := by
  obtain ⟨w'', a, b⟩ := (isCPMap_bcMap f χ).exists_comp (isCPMap_bcMap f' χ) hw''
  exact ⟨_, _, w'', isCPMap_bcMap f χ, isCPMap_bcMap f' χ, b, a⟩
abbrev SQ : Scheme.{0} := Spec (CommRingCat.of ℚ)
instance : ConnectedSpace (splitTorus SQ ℤ).left := connectedSpace_torus _ _
example (χ : X) (T : Over S) (U : (T ⟶ splitTorus S X) → Γ(T.left, ⊤))
    (hU : ∀ x, U x = x.left.appTop.hom (charUnit S X χ).val) :
    U 1 = 1 ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v) := by
  simp only [hU, ← chV_val, chV_mul, chV_one, Units.val_mul, Units.val_one, true_and]
  intros; ring
example (n : ℤ) : (∀ (T : Over SQ) (U : (T ⟶ splitTorus SQ ℤ) → Γ(T.left, ⊤)),
    (∀ x, U x = x.left.appTop.hom (charUnit SQ ℤ n).val) → U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧
      ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) ↔ charUnit SQ ℤ n = 1 := by
  refine ⟨fun h => ?_, fun h T U hU => ?_⟩
  · obtain ⟨t, ht⟩ := exists_point_two
    have a := (h _ (fun x => (chV x n).val) (fun x => chV_val x n)).2.1 t
    have b : chV t (n + n) = 1 := by
      rw [chV_add]
      exact (congrArg (· * chV t n) ((Units.ext a).symm.trans (chV_inv t n))).trans (inv_mul_cancel _)
    obtain rfl : n = 0 := by have := ht _ b; omega
    exact Units.ext ((by simp : _ = (𝟙 (splitTorus SQ ℤ) :).left.appTop.hom _).trans
      ((chV_val (𝟙 _) 0).symm.trans (congrArg Units.val (chV_zero _))))
  · simp only [hU, h, Units.val_one, map_one, _root_.mul_one, implies_true, and_self]
example [Subsingleton X] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L}
    {i : splitTorus S X ⟶ G} [IsMonHom i] (s s' : BiTriv c i) {T : Over S} (p : T ⟶ splitTorus S X ⊗ G) (z : T.left)
    (J) (hJ : Good L.L z J) : val s.s p.left z J = val s'.s p.left z J := by
  rw [← lift_comp_fst_snd p, point_eq_of_subsingleton (p ≫ fst _ _) 1, s.val_one_left hJ, s'.val_one_left hJ]
example (n : ℤ) (s : BiTriv (trivCub (splitTorus SQ ℤ)) (𝟙 _))
    (hs : s.s = scaleGen (chV (fst _ _) n) (unitGen _ _)) : n = 0 := by
  obtain ⟨t, ht⟩ := exists_point_two
  refine ht n (unit_ext fun z _ => ?_)
  have a := s.val_one_right (good_triv z fun _ => PUnit.unit) t
  rw [hs] at a
  exact (val_fst _ _ n t 1 z _).symm.trans (a.trans (map_one _).symm)
example (k : Type) [Field k] : Smooth (splitTorus (Spec (CommRingCat.of k)) ℤ).hom ∧
    GeometricallyConnected (splitTorus (Spec (CommRingCat.of k)) ℤ).hom ∧
    IsMonHom (𝟙 (splitTorus (Spec (CommRingCat.of k)) ℤ)) ∧
    Nonempty (BiTriv (trivCub (splitTorus (Spec (CommRingCat.of k)) ℤ)) (𝟙 _)) :=
  ⟨inferInstance, inferInstance, inferInstance, ⟨BiTriv.triv _⟩⟩
example : IsLocalRing (ZMod 4) ∧ IsNilpotent (Ideal.span {(2 : ZMod 4)}) ∧ Ideal.span {(2 : ZMod 4)} ≠ ⊤ ∧
    Ideal.span {(2 : ZMod 4)} ≠ ⊥ := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  refine ⟨IsLocalRing.of_isUnit_or_isUnit_one_sub_self (by decide), ⟨2, ?_⟩, ?_, ?_⟩
  · rw [Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; decide
  · rw [Ne, Ideal.span_singleton_eq_top]; decide
  · rw [Ne, Ideal.span_singleton_eq_bot]; decide
example (χ ψ : X) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J) :
    val (twTriv S χ ψ).s (t * t').left z J =
      val (BiTriv.triv (𝟙 (splitTorus S X))).s (lift t (t' ≫ 𝟙 _)).left z J * val (twTriv S χ ψ).s t.left z J *
        val (twTriv S χ ψ).s t'.left z J := by
  have e : val (BiTriv.triv (𝟙 (splitTorus S X))).s (lift t (t' ≫ 𝟙 _)).left z J = 1 := val_unitGen _ _ _ _ _
  rw [e, val_twTriv, val_twTriv, val_twTriv, chV_mul, map_mul, _root_.one_mul]
example (m n : ℤ) : (twTriv SQ (-(m + m)) n).Even ↔ n = m := by
  refine ⟨fun h => ?_, fun h => h ▸ twTriv_even _ _⟩
  obtain ⟨t, ht⟩ := exists_point_two
  have : n + n + -(m + m) = 0 := ht _ (unit_ext fun z _ => by
    have a := ((val_twTriv _ _ _ _ _).symm.trans (h _ t z _ (good_triv z fun _ => PUnit.unit))).trans
      (congrArg₂ (· * ·) ((val_sym_twCP _ _ _ _).trans (gm_charUnit _ _ _)) (val_twTriv _ _ _ _ _))
    rw [Category.comp_id, chV_inv, map_inv] at a
    rw [chV_add, chV_add, map_mul, map_mul, map_one, _root_.mul_assoc, mul_comm _ (gm _ z ⊤ (chV t (-(m + m)))), ← a,
      mul_inv_cancel])
  omega
abbrev chAct (S : Scheme.{0}) (χ : X) : LB.Gen (LB.LinComb (Inh.trivLB (splitTorus S X).left) (K := Fin 2)
    ![((fst (splitTorus S X) (splitTorus S X) ≫ (TQ.torus S X).i) * snd (splitTorus S X) (splitTorus S X)).left,
      (snd (splitTorus S X) (splitTorus S X)).left] ![1, -1]) :=
  scaleGen (chV (fst _ _) χ) (unitGen _ _)
theorem val_chAct (χ : X) {T : Over S} (t x : T ⟶ splitTorus S X) (z : T.left) (J) :
    val (chAct S χ) (lift t x).left z J = gm (𝟙 T.left) z ⊤ (chV t χ) :=
  val_fst _ _ χ t x z J
example (χ : X) : (chAct S χ).IsGen ∧
    (∀ (T : Over S) (t t' : T ⟶ splitTorus S X) (x : T ⟶ splitTorus S X) (z : T.left) (J),
      val (chAct S χ) (lift (t * t') x).left z J =
        val (chAct S χ) (lift t ((t' ≫ (TQ.torus S X).i) * x)).left z J * val (chAct S χ) (lift t' x).left z J) ∧
    ∃ (M : LB (TQ.torus S X).B.left) (w : LB.Iso (Inh.trivLB _) (M.pull (TQ.torus S X).q.left)), M.IsLB ∧ w.IsGen ∧
      ∀ (T : Over S) (t x : T ⟶ splitTorus S X) (z : T.left) (J) (j : M.ι),
        gw w ((t ≫ (TQ.torus S X).i) * x).left z j (J ((t ≫ (TQ.torus S X).i) * x).left) *
          val (chAct S χ) (lift t x).left z J = gw w x.left z j (J x.left) := by
  refine ⟨scaleGen_isGen _ (unitGen_isGen _ _), fun T t t' x z J => ?_, Inh.trivLB _,
    scaleGen (charUnit S X (-χ)) ⟨fun _ => 1⟩, Inh.trivLB_isLB _,
    scaleGen_isGen _ (TQ.Desc.triv (TQ.torus S X)).map.gen, fun T t x z J j => ?_⟩
  · rw [val_chAct, val_chAct, val_chAct, chV_mul, map_mul]
  · have e : t ≫ (TQ.torus S X).i = t := Category.comp_id t
    rw [gw_scale, gw_scale, val_chAct, gm_charUnit, gm_charUnit, e, chV_mul, chV_neg t, map_mul, map_inv,
      mul_right_comm, inv_mul_cancel, _root_.one_mul]
example [ConnectedSpace S] [Module.Free ℤ X] (ψ : X) : ConnectedSpace (splitTorus S X).left ∧
    Nonempty (BiTriv (twCP S (-(ψ + ψ))).c (TQ.torus S X).i) ∧
    (∃ σ : CubTriv (twCP S (-(ψ + ψ))).c (TQ.torus S X).i, σ.Even) ∧
    Nonempty ((TQ.torus S X).Desc (twCP S (-(ψ + ψ)))) :=
  ⟨connectedSpace_torus _ _, ⟨BiTriv.triv _⟩, ⟨_, twTriv_even S ψ⟩, ⟨twDesc S ψ⟩⟩
example [ConnectedSpace S] [Module.Free ℤ X] (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    [ConnectedSpace A.left] (M : CP (TQ.prod X A hA).B) :
    ConnectedSpace (splitTorus S X ⊗ A).left ∧ ∃ (P : CP (splitTorus S X ⊗ A)) (D : (TQ.prod X A hA).Desc P), D.M = M :=
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  ⟨GroupConn.connectedSpace_tensor _ A, (TQ.prod X A hA).exists_desc M⟩
theorem exists_isCPMap_comp (f : S' ⟶ S) {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] (Q : TQ G' X) {P' : CP G'}
    (D : Q.Desc P') {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) (β : Q.B.left ⟶ B.left)
    (hβ : β ≫ B.hom = Q.B.hom ≫ f) (hw) {v} (h : IsCPMap D.M M f β hβ v) :
    ∃ w, IsCPMap P' M f (Q.q.left ≫ β) hw w := by
  have key : ∀ g (_ : 𝟙 S' ≫ f = g) (hg), ∃ w, IsCPMap P' M g (Q.q.left ≫ β) hg w := by
    rintro _ rfl hg
    exact (h.exists_comp D.map hg).imp fun _ => And.right
  exact key f (Category.id_comp f) hw
example (ψ : X) (hβ : 𝟙 _ ≫ (TQ.torus S X).B.hom = (TQ.torus S X).B.hom ≫ 𝟙 S) (hw) :
    (∀ (T : Over S) (x y : T ⟶ (TQ.torus S X).B), toBase hβ (x * y) = toBase hβ x * toBase hβ y) ∧
    (∃ w, IsCPMap (twCP S (-(ψ + ψ))) (twDesc S ψ).M (𝟙 S) ((TQ.torus S X).q.left ≫ 𝟙 _) hw w) ∧
    ∃ v, IsCPMap (twDesc S ψ).M (twDesc S ψ).M (𝟙 S) (𝟙 _) hβ v :=
  ⟨(IsCPMap.id (twDesc S ψ).M).mul, exists_isCPMap_comp _ _ _ _ _ _ _ (IsCPMap.id _), _, IsCPMap.id _⟩
example (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (χ : X) :
    ∃ (N : LB (TQ.prod X A hA).B.left) (t : LB.Gen (N.pull (TQ.prod X A hA).q.left)), N.IsLB ∧
      (TQ.prod X A hA).GenWt N t χ ∧ ∃ u : LB.Gen (abelian₂ (TQ.prod X A hA).B N), u.IsGen :=
  ⟨_, _, Inh.trivLB_isLB _, (TQ.prod X A hA).genWt_triv (chV (fst _ _) χ)
    (isWt_of_retraction (fst _ _) (lift_fst _ _) χ), unitGen _ _, unitGen_isGen _ _⟩
end BiextCheck
end GlobalTheory.UU
end


