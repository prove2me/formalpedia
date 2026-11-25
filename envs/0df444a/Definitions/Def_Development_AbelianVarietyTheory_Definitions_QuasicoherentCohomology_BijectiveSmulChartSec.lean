-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:04.639923+00:00
-- url     : https://prove2.me/theorems/d7299204-3ae6-4d93-99ca-3f974af6244e
-- title:
--   Bijective Smul Chart Sec
-- statement:
--   Definitions and structural lemmas for Bijective Smul Chart Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_g_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_lcg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_invIso_spec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace LB
variable {X Y : Scheme.{0}}
@[simp] theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
@[simp] theorem resG_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [resG, this, X.presheaf.map_id]; rfl
theorem val_res {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    ((res h a : Γ(X, V)ˣ) : Γ(X, V)) = resG X h (a : Γ(X, U)) := rfl
theorem fun_ext_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) {a b : Γ(X, V)} (h : ∀ k, resG X (hW k) a = resG X (hW k) b) : a = b :=
  X.sheaf.eq_of_locally_eq' W V (fun k => homOfLE (hW k)) hc a b h
theorem exists_fun_of_cover {ι : Type*} {V : X.Opens} (W : ι → X.Opens) (hW : ∀ k, W k ≤ V)
    (hc : V ≤ iSup W) (a : ∀ k, Γ(X, W k))
    (h : ∀ k l, resG X (inf_le_left : W k ⊓ W l ≤ W k) (a k) =
      resG X (inf_le_right : W k ⊓ W l ≤ W l) (a l)) :
    ∃ b : Γ(X, V), ∀ k, resG X (hW k) b = a k :=
  (X.sheaf.existsUnique_gluing' W V (fun k => homOfLE (hW k)) hc a h).exists
theorem le_iSup_inf {ι : Type*} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (V : X.Opens) :
    V ≤ ⨆ i, V ⊓ U i := by
  rw [← inf_iSup_eq, hU, inf_top_eq]
abbrev unitMod (X : Scheme.{0}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
def homOfLinear {F G : X.Modules} (φ : ∀ V : X.Opens, Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V))
    (hφ : ∀ {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V)),
      φ W (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ V s)) : F ⟶ G :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (φ V.unop).toAddMonoidHom
      naturality := fun _ _ f => by
        ext s
        exact hφ (leOfHom f.unop) s }
    (fun V r m => (φ V.unop).map_smul r m)
@[simp] theorem homOfLinear_app {F G : X.Modules} (φ : ∀ V : X.Opens, Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V))
    (hφ : ∀ {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V)),
      φ W (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ V s))
    (V : X.Opens) (s : Γ(F, V)) : (homOfLinear φ hφ).app V s = φ V s := rfl
def isoOfLinear {F G : X.Modules} (φ : ∀ V : X.Opens, Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V))
    (hφ : ∀ {V W : X.Opens} (h : W ≤ V) (s : Γ(F, V)),
      φ W (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ V s)) : F ≅ G where
  hom := homOfLinear (fun V => (φ V).toLinearMap) hφ
  inv := homOfLinear (fun V => (φ V).symm.toLinearMap) fun {V W} h s => by
    apply (φ W).injective
    rw [hφ]
    simp
  hom_inv_id := by
    ext V s
    exact (φ V).symm_apply_apply s
  inv_hom_id := by
    ext V s
    exact (φ V).apply_symm_apply s
variable (L : LB X)
def secGroup (V : X.Opens) : AddSubgroup (∀ i, Γ(X, V ⊓ L.U i)) where
  carrier := secOn L V
  add_mem' := fun {s t} hs ht i j => by
    simp only [Pi.add_apply, map_add, hs i j, ht i j, mul_add]
  zero_mem' := fun i j => by simp only [Pi.zero_apply, map_zero, mul_zero]
  neg_mem' := fun {s} hs i j => by simp only [Pi.neg_apply, map_neg, hs i j, mul_neg]
variable {L} in

theorem secOn_rel {V : X.Opens} {s : ∀ i, Γ(X, V ⊓ L.U i)} (hs : s ∈ secOn L V) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (s i) = resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (s j) := by
  have := congrArg (resG X (le_inf hi (hj.trans inf_le_right) : W ≤ V ⊓ L.U i ⊓ L.U j)) (hs i j)
  simpa only [map_mul, resG_resG] using this
instance secGroupModule (V : X.Opens) : Module Γ(X, V) (secGroup L V) where
  smul a s := ⟨fun i => resG X inf_le_left a * s.1 i, fun i j => by
    rw [map_mul, map_mul, s.2 i j, resG_resG, resG_resG, mul_left_comm]⟩
  one_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 1 * s.1 i = _
    rw [map_one, one_mul]
  mul_smul a b s := Subtype.ext <| funext fun i => by
    change resG X _ (a * b) * s.1 i = resG X _ a * (resG X _ b * s.1 i)
    rw [map_mul, mul_assoc]
  smul_zero a := Subtype.ext <| funext fun i => mul_zero _
  smul_add a s t := Subtype.ext <| funext fun i => mul_add _ _ _
  add_smul a b s := Subtype.ext <| funext fun i => by
    change resG X _ (a + b) * s.1 i = resG X _ a * s.1 i + resG X _ b * s.1 i
    rw [map_add, add_mul]
  zero_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 0 * s.1 i = 0
    rw [map_zero, zero_mul]
def secRes {V W : X.Opens} (h : W ≤ V) : secGroup L V →+ secGroup L W where
  toFun s := ⟨fun i => resG X (inf_le_inf_right _ h) (s.1 i), fun i j => by
    rw [resG_resG, resG_resG]
    exact secOn_rel s.2 i j _ _ _⟩
  map_zero' := Subtype.ext <| funext fun i => map_zero _
  map_add' s t := Subtype.ext <| funext fun i => map_add _ _ _
theorem secRes_smul {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (m : secGroup L V) :
    secRes L h (r • m) = resG X h r • secRes L h m :=
  Subtype.ext <| funext fun i => by
    change resG X _ (resG X _ r * m.1 i) = resG X _ (resG X h r) * resG X _ (m.1 i)
    rw [map_mul, resG_resG, resG_resG]
def secPresheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (secGroup L V.unop)
  map f := AddCommGrpCat.ofHom (secRes L (leOfHom f.unop))
  map_id V := by
    ext s i
    exact resG_self _ _
  map_comp f g := by
    ext s i
    exact (resG_resG _ _ _).symm
theorem isSheaf_secPresheaf : (secPresheaf L).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc (i : L.ι) : iSup W ⊓ L.U i ≤ ⨆ k, W k ⊓ L.U i := by rw [iSup_inf_eq]
  have hW (i : L.ι) (k : κ) : W k ⊓ L.U i ≤ iSup W ⊓ L.U i := inf_le_inf_right _ (le_iSup W k)
  have H (i : L.ι) : ∃ b : Γ(X, iSup W ⊓ L.U i), ∀ k, resG X (hW i k) b = (sf k).1 i := by
    refine exists_fun_of_cover (fun k => W k ⊓ L.U i) (hW i) (hc i) (fun k => (sf k).1 i)
      fun k l => ?_
    have e : resG X (inf_le_inf_right (L.U i) (inf_le_left : W k ⊓ W l ≤ W k)) ((sf k).1 i) =
        resG X (inf_le_inf_right (L.U i) (inf_le_right : W k ⊓ W l ≤ W l)) ((sf l).1 i) :=
      congrFun (congrArg Subtype.val (hsf k l)) i
    have := congrArg (resG X (le_inf (inf_le_inf inf_le_left inf_le_left)
      (inf_le_left.trans inf_le_right) :
        (W k ⊓ L.U i) ⊓ (W l ⊓ L.U i) ≤ W k ⊓ W l ⊓ L.U i)) e
    simpa only [resG_resG] using this
  choose b hb using H
  refine ⟨⟨b, fun i j => ?_⟩, fun k => Subtype.ext (funext fun i => hb i k), fun t ht => ?_⟩
  · refine fun_ext_of_cover (fun k => W k ⊓ L.U i ⊓ L.U j)
      (fun k => inf_le_inf_right _ (hW i k)) (by rw [iSup_inf_eq, iSup_inf_eq]) fun k => ?_
    have := (sf k).2 i j
    rw [← hb i k, ← hb j k] at this
    simpa only [map_mul, resG_resG] using this
  · refine Subtype.ext (funext fun i => fun_ext_of_cover _ (hW i) (hc i) fun k => ?_)
    rw [hb i k]
    exact congrFun (congrArg Subtype.val (ht k)) i
def toMod : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((secPresheaf L).obj V) :=
    fun V => secGroupModule L V.unop
  { val := PresheafOfModules.ofPresheaf (secPresheaf L) fun _ _ f r m =>
      secRes_smul L (leOfHom f.unop) r m
    isSheaf := isSheaf_secPresheaf L }
variable {L}
def coord {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) : Γ(X, V ⊓ L.U i) :=
  (show secGroup L V from s).1 i
theorem coord_mem {V : X.Opens} (s : Γ(toMod L, V)) : coord s ∈ secOn L V :=
  (show secGroup L V from s).2
def mkSec {V : X.Opens} (f : ∀ i, Γ(X, V ⊓ L.U i)) (hf : f ∈ secOn L V) : Γ(toMod L, V) :=
  (⟨f, hf⟩ : secGroup L V)
@[simp] theorem coord_mkSec {V : X.Opens} (f : ∀ i, Γ(X, V ⊓ L.U i)) (hf : f ∈ secOn L V) :
    coord (mkSec f hf) = f := rfl
@[ext] theorem sec_ext {V : X.Opens} {s t : Γ(toMod L, V)} (h : ∀ i, coord s i = coord t i) :
    s = t := Subtype.ext (funext h)
variable (L) in

def secOnEquiv (V : X.Opens) : Γ(toMod L, V) ≃ secOn L V where
  toFun s := ⟨coord s, coord_mem s⟩
  invFun f := mkSec f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] theorem coord_zero {V : X.Opens} (i : L.ι) : coord (0 : Γ(toMod L, V)) i = 0 := rfl
@[simp] theorem coord_add {V : X.Opens} (s t : Γ(toMod L, V)) (i : L.ι) :
    coord (s + t) i = coord s i + coord t i := rfl
@[simp] theorem coord_neg {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) :
    coord (-s) i = - coord s i := rfl
@[simp] theorem coord_sub {V : X.Opens} (s t : Γ(toMod L, V)) (i : L.ι) :
    coord (s - t) i = coord s i - coord t i := rfl
@[simp] theorem coord_smul {V : X.Opens} (a : Γ(X, V)) (s : Γ(toMod L, V)) (i : L.ι) :
    coord (a • s) i = resG X inf_le_left a * coord s i := rfl
@[simp] theorem coord_map {V W : X.Opens} (h : W ≤ V) (s : Γ(toMod L, V)) (i : L.ι) :
    coord ((toMod L).presheaf.map (homOfLE h).op s) i =
      resG X (inf_le_inf_right _ h) (coord s i) := rfl
theorem coord_rel {V : X.Opens} (s : Γ(toMod L, V)) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (coord s i) =
      resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (coord s j) :=
  secOn_rel (coord_mem s) i j hi hj hij
theorem resG_g_self (hL : L.IsLB) (i : L.ι) {W : X.Opens} (h : W ≤ L.U i ⊓ L.U i) :
    resG X h (L.g i i : Γ(X, L.U i ⊓ L.U i)) = 1 :=
  congrArg Units.val (Semi.LB.res_g_self hL i h)
theorem resG_cocycle (hL : L.IsLB) (i j k : L.ι) {W : X.Opens}
    (h₁ : W ≤ L.U i ⊓ L.U j) (h₂ : W ≤ L.U j ⊓ L.U k) (h₃ : W ≤ L.U i ⊓ L.U k) :
    resG X h₁ (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X h₂ (L.g j k : Γ(X, L.U j ⊓ L.U k)) =
      resG X h₃ (L.g i k : Γ(X, L.U i ⊓ L.U k)) :=
  congrArg Units.val (Semi.LB.res_cocycle hL i j k h₁ h₂ h₃)
section Global
open ReciprocityTheory.ChartRestriction.G.DVR
instance : Zero (LB.Sec L) := ⟨SecOps.secZero⟩
instance : Add (LB.Sec L) := ⟨SecOps.secAdd⟩
instance : Neg (LB.Sec L) := ⟨SecOps.secNeg⟩
instance : SMul Γ(X, ⊤) (LB.Sec L) := ⟨SecOps.secScale⟩
instance : Sub (LB.Sec L) :=
  ⟨fun s t => ⟨fun i => s.f i - t.f i, fun i j => by
    simp only [map_sub, s.compat, t.compat, mul_sub]⟩⟩
instance : SMul ℕ (LB.Sec L) :=
  ⟨fun n s => ⟨fun i => n • s.f i, fun i j => by
    simp only [map_nsmul, s.compat, mul_smul_comm]⟩⟩
instance : SMul ℤ (LB.Sec L) :=
  ⟨fun n s => ⟨fun i => n • s.f i, fun i j => by
    simp only [map_zsmul, s.compat, mul_smul_comm]⟩⟩
theorem f_injective : Function.Injective (LB.Sec.f : LB.Sec L → ∀ i, Γ(X, L.U i)) :=
  fun _ _ h => SecOps.sec_ext (congrFun h)
instance secAddCommGroup : AddCommGroup (LB.Sec L) :=
  f_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)
@[simp] theorem zero_f (i : L.ι) : (0 : LB.Sec L).f i = 0 := rfl
@[simp] theorem add_f (s t : LB.Sec L) (i : L.ι) : (s + t).f i = s.f i + t.f i := rfl
@[simp] theorem neg_f (s : LB.Sec L) (i : L.ι) : (-s).f i = - s.f i := rfl
@[simp] theorem sub_f (s t : LB.Sec L) (i : L.ι) : (s - t).f i = s.f i - t.f i := rfl
@[simp] theorem smul_f (a : Γ(X, ⊤)) (s : LB.Sec L) (i : L.ι) :
    (a • s).f i = resG X le_top a * s.f i := rfl
instance secModuleTop : Module Γ(X, ⊤) (LB.Sec L) where
  one_smul s := SecOps.sec_ext fun i => by rw [smul_f, map_one, one_mul]
  mul_smul a b s := SecOps.sec_ext fun i => by rw [smul_f, smul_f, smul_f, map_mul, mul_assoc]
  smul_zero a := SecOps.sec_ext fun i => by rw [smul_f, zero_f, mul_zero]
  smul_add a s t := SecOps.sec_ext fun i => by simp only [smul_f, add_f, mul_add]
  add_smul a b s := SecOps.sec_ext fun i => by simp only [smul_f, add_f, map_add, add_mul]
  zero_smul s := SecOps.sec_ext fun i => by rw [smul_f, map_zero, zero_mul, zero_f]
theorem sec_rel (s : LB.Sec L) (i j : L.ι) {W : X.Opens} (hi : W ≤ L.U i) (hj : W ≤ L.U j)
    (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (s.f i) = resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (s.f j) := by
  have : resG X inf_le_left (s.f i) = _ * resG X inf_le_right (s.f j) := s.compat i j
  simpa only [map_mul, resG_resG] using congrArg (resG X hij) this
def ofSec (s : LB.Sec L) (V : X.Opens) : Γ(toMod L, V) :=
  mkSec (fun i => resG X inf_le_right (s.f i)) fun i j => by
    rw [resG_resG, resG_resG]
    exact sec_rel s i j _ _ _
@[simp] theorem coord_ofSec (s : LB.Sec L) (V : X.Opens) (i : L.ι) :
    coord (ofSec s V) i = resG X inf_le_right (s.f i) := rfl
@[simp] theorem map_ofSec (s : LB.Sec L) {V W : X.Opens} (h : W ≤ V) :
    (toMod L).presheaf.map (homOfLE h).op (ofSec s V) = ofSec s W :=
  sec_ext fun i => by rw [coord_map, coord_ofSec, resG_resG, coord_ofSec]
variable (L) in

def globalEquiv : Γ(toMod L, ⊤) ≃ₗ[Γ(X, ⊤)] LB.Sec L where
  toFun s := ⟨fun i => resG X (le_inf le_top le_rfl) (coord s i), fun i j => by
    change resG X _ (resG X _ _) = _ * resG X _ (resG X _ _)
    rw [resG_resG, resG_resG, coord_rel s i j _ _ le_rfl, resG_self]⟩
  invFun s := ofSec s ⊤
  map_add' s t := SecOps.sec_ext fun i => map_add _ _ _
  map_smul' a s := SecOps.sec_ext fun i => by
    change resG X _ (resG X _ a * _) = resG X _ a * _
    rw [map_mul, resG_resG]
    rfl
  left_inv s := sec_ext fun i => by
    change resG X _ (resG X _ _) = _
    rw [resG_resG, resG_self]
  right_inv s := SecOps.sec_ext fun i => by
    change resG X _ (resG X _ _) = _
    rw [resG_resG, resG_self]
@[simp] theorem globalEquiv_f (s : Γ(toMod L, ⊤)) (i : L.ι) :
    (globalEquiv L s).f i = resG X (le_inf le_top le_rfl) (coord s i) := rfl
@[simp] theorem globalEquiv_symm_apply (s : LB.Sec L) : (globalEquiv L).symm s = ofSec s ⊤ := rfl
end Global
section OverBase
open MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L₀ : LB A.left) (a : ℤ) (T : Over S)
def globalEquivSecM : Γ(toMod (LPow A L₀ a T), ⊤) ≃+ SecM A L₀ a T where
  toFun s := SecM.ofSec A (globalEquiv _ s)
  invFun f := (globalEquiv _).symm (SecM.toSec A f)
  left_inv s := (globalEquiv _).symm_apply_apply s
  right_inv f := congrArg (SecM.ofSec A) ((globalEquiv _).apply_symm_apply (SecM.toSec A f))
  map_add' s t := congrArg (SecM.ofSec A) (map_add (globalEquiv _) s t)
end OverBase
def chartSec (hL : L.IsLB) (i : L.ι) : Γ(toMod L, L.U i) :=
  mkSec (fun j => resG X (le_inf inf_le_right inf_le_left) (L.g j i : Γ(X, L.U j ⊓ L.U i)))
    fun j k => by
      rw [resG_resG, resG_resG]
      exact (resG_cocycle hL j k i _ _ _).symm
@[simp] theorem coord_chartSec (hL : L.IsLB) (i j : L.ι) :
    coord (chartSec hL i) j =
      resG X (le_inf inf_le_right inf_le_left) (L.g j i : Γ(X, L.U j ⊓ L.U i)) := rfl
def chartEquiv (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Γ(toMod L, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toFun s := resG X (le_inf le_rfl h) (coord s i)
  invFun a := a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i)
  map_add' s t := map_add _ _ _
  map_smul' a s := by
    simp only [coord_smul, map_mul, resG_resG, resG_self, RingHom.id_apply, smul_eq_mul]
  left_inv s := sec_ext fun j => by
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG]
    rw [mul_comm, ← coord_rel s j i le_rfl, resG_self]
  right_inv a := by
    simp only [coord_smul, coord_map, coord_chartSec, map_mul, resG_resG, resG_self,
      resG_g_self hL, map_one, mul_one]
theorem bijective_smul_chartSec (hL : L.IsLB) (i : L.ι) (V : X.Opens) (h : V ≤ L.U i) :
    Function.Bijective
      fun a : Γ(X, V) => a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i) :=
  (chartEquiv hL i h).symm.bijective
def chartIso (hL : L.IsLB) (i : L.ι) :
    unitMod (L.U i).toScheme ≅ (toMod L).restrict (L.U i).ι :=
  Descent.freeIso (Descent.bijective_smul_stalk (bijective_smul_chartSec hL i))
set_option backward.isDefEq.respectTransparency false in

def chartOverIso (hL : L.IsLB) (i : L.ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (L.U i)) PUnit.{1} ≅ (toMod L).over (L.U i) :=
  let e := Scheme.Modules.overEquiv (L.U i)
  Limits.coproductUniqueIso (fun _ : PUnit.{1} => SheafOfModules.unit _) ≪≫
    ((L.U i).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
    e.inverse.mapIso (chartIso hL i) ≪≫
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv (L.U i)).app (toMod L)).symm ≪≫
      (e.unitIso.app ((toMod L).over (L.U i))).symm
set_option backward.isDefEq.respectTransparency false in

theorem isIso_ofEpi_π.{v, u} {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} [HasWeakSheafify J AddCommGrpCat.{0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}] {M : SheafOfModules.{0} R} {I : Type}
    (e : SheafOfModules.free I ≅ M) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi e.hom).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  exact inferInstanceAs (IsIso (𝟙 (SheafOfModules.free I) ≫ e.hom))
set_option backward.isDefEq.respectTransparency false in

def generatorsOfIso {F : X.Modules} {ι : Type} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) PUnit.{1} ≅ F.over (U i)) :
    SheafOfModules.LocalGeneratorsData.{0} F where
  I := ι
  X := U
  coversTop := by
    rw [Opens.coversTop_iff]
    exact hU
  generators i := (SheafOfModules.free.generatingSections PUnit.{1}).ofEpi (e i).hom
set_option backward.isDefEq.respectTransparency false in

theorem isLocallyFree_of_iso {F : X.Modules} {ι : Type} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤)
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) PUnit.{1} ≅ F.over (U i)) :
    F.IsLocallyFree ∧ F.IsFiniteType :=
  haveI : (generatorsOfIso hU e).IsLocallyFreeData := ⟨fun i => isIso_ofEpi_π (e i)⟩
  ⟨(generatorsOfIso hU e).isLocallyFree,
    ⟨generatorsOfIso hU e, ⟨fun _ => ⟨inferInstanceAs (Finite PUnit.{1})⟩⟩⟩⟩
theorem isLocallyFree_toMod (hL : L.IsLB) : (toMod L).IsLocallyFree :=
  (isLocallyFree_of_iso hL.cover (chartOverIso hL)).1
set_option backward.isDefEq.respectTransparency false in

theorem isQuasicoherent_toMod (hL : L.IsLB) : (toMod L).IsQuasicoherent :=
  haveI := isLocallyFree_toMod hL
  inferInstance
section Hom
variable {M : LB X}
def homCoord (w : LB.Sec (LB.div M L)) (p : M.ι) (q : L.ι) : Γ(X, M.U p ⊓ L.U q) := w.f (p, q)
theorem homCoord_rel (w : LB.Sec (LB.div M L)) (p p' : M.ι) (q q' : L.ι) {W : X.Opens}
    (h : W ≤ M.U p ⊓ L.U q) (h' : W ≤ M.U p' ⊓ L.U q') (hp : W ≤ M.U p ⊓ M.U p')
    (hq : W ≤ L.U q ⊓ L.U q') :
    resG X h (homCoord w p q) * resG X hq (L.g q q' : Γ(X, L.U q ⊓ L.U q')) =
      resG X hp (M.g p p' : Γ(X, M.U p ⊓ M.U p')) * resG X h' (homCoord w p' q') := by
  have e : resG X h (homCoord w p q) =
      ((res (le_inf h h') (Semi.LB.dg M L (p, q) (p', q')) : Γ(X, W)ˣ) : Γ(X, W)) *
        resG X h' (homCoord w p' q') := sec_rel w (p, q) (p', q') h h' (le_inf h h')
  have e₂ : res (le_inf h h') (Semi.LB.dg M L (p, q) (p', q')) =
      res hp (M.g p p') * (res hq (L.g q q'))⁻¹ := Semi.LB.res_dg M L (p, q) (p', q') _
  rw [e, e₂, ← val_res hq, ← val_res hp, Units.val_mul, mul_right_comm,
    Units.inv_mul_cancel_right]
theorem exists_mul_sec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V : X.Opens}
    (s : Γ(toMod L, V)) : ∃ t : Γ(toMod M, V), ∀ (p : M.ι) (q : L.ι) (W : X.Opens)
      (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q),
      resG X hp (coord t p) = resG X h (homCoord w p q) * resG X hq (coord s q) := by
  have l₁ (p : M.ι) (q : L.ι) : V ⊓ M.U p ⊓ L.U q ≤ M.U p ⊓ L.U q :=
    inf_le_inf_right _ inf_le_right
  have l₂ (p : M.ι) (q : L.ι) : V ⊓ M.U p ⊓ L.U q ≤ V ⊓ L.U q := inf_le_inf_right _ inf_le_left
  have H (p : M.ι) : ∃ b : Γ(X, V ⊓ M.U p), ∀ q, resG X inf_le_left b =
      resG X (l₁ p q) (homCoord w p q) * resG X (l₂ p q) (coord s q) := by
    refine exists_fun_of_cover (fun q => V ⊓ M.U p ⊓ L.U q) (fun _ => inf_le_left)
      (le_iSup_inf hL.cover _) _ fun q q' => ?_
    simp only [map_mul, resG_resG]
    rw [coord_rel s q q' _ (inf_le_right.trans (l₂ p q')) (inf_le_inf inf_le_right inf_le_right),
      ← mul_assoc, homCoord_rel w p p q q' _ (inf_le_right.trans (l₁ p q'))
        (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
          (inf_le_left.trans (inf_le_left.trans inf_le_right))), resG_g_self hM, one_mul]
  choose b hb using H
  have hb' (p : M.ι) (q : L.ι) (W : X.Opens) (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q)
      (h : W ≤ M.U p ⊓ L.U q) :
      resG X hp (b p) = resG X h (homCoord w p q) * resG X hq (coord s q) := by
    simpa only [map_mul, resG_resG] using
      congrArg (resG X (le_inf hp (h.trans inf_le_right))) (hb p q)
  refine ⟨mkSec b fun p p' => ?_, hb'⟩
  refine fun_ext_of_cover (fun q => V ⊓ M.U p ⊓ M.U p' ⊓ L.U q) (fun _ => inf_le_left)
    (le_iSup_inf hL.cover _) fun q => ?_
  have hq : V ⊓ M.U p ⊓ M.U p' ⊓ L.U q ≤ V ⊓ L.U q :=
    inf_le_inf_right _ (inf_le_left.trans inf_le_left)
  have h₁ : V ⊓ M.U p ⊓ M.U p' ⊓ L.U q ≤ M.U p ⊓ L.U q :=
    inf_le_inf_right _ (inf_le_left.trans inf_le_right)
  have h₂ : V ⊓ M.U p ⊓ M.U p' ⊓ L.U q ≤ M.U p' ⊓ L.U q := inf_le_inf_right _ inf_le_right
  simp only [map_mul, resG_resG]
  rw [hb' p q _ _ hq h₁, hb' p' q _ _ hq h₂, ← mul_assoc,
    ← homCoord_rel w p p' q q h₁ h₂ _ (le_inf inf_le_right inf_le_right), resG_g_self hL, mul_one]
theorem sec_ext_of_cover {ι : Type*} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) {V : X.Opens}
    {t t' : Γ(toMod M, V)}
    (h : ∀ p q, resG X (inf_le_left : V ⊓ M.U p ⊓ U q ≤ V ⊓ M.U p) (coord t p) =
      resG X inf_le_left (coord t' p)) : t = t' :=
  sec_ext fun p => fun_ext_of_cover (fun q => V ⊓ M.U p ⊓ U q) (fun _ => inf_le_left)
    (le_iSup_inf hU _) (h p)
def mulFun (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V : X.Opens}
    (s : Γ(toMod L, V)) : Γ(toMod M, V) :=
  (exists_mul_sec hL hM w s).choose
theorem coord_mulFun (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V : X.Opens}
    (s : Γ(toMod L, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resG X hp (coord (mulFun hL hM w s) p) = resG X h (homCoord w p q) * resG X hq (coord s q) :=
  (exists_mul_sec hL hM w s).choose_spec p q W hp hq h
theorem coord_mulFun' (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V : X.Opens}
    (s : Γ(toMod L, V)) (p : M.ι) (q : L.ι) :
    resG X (inf_le_left : V ⊓ M.U p ⊓ L.U q ≤ V ⊓ M.U p) (coord (mulFun hL hM w s) p) =
      resG X (inf_le_inf_right _ inf_le_right) (homCoord w p q) *
        resG X (inf_le_inf_right _ inf_le_left) (coord s q) :=
  coord_mulFun hL hM w s p q _ _ _
def mulLinear (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) (V : X.Opens) :
    Γ(toMod L, V) →ₗ[Γ(X, V)] Γ(toMod M, V) where
  toFun := mulFun hL hM w
  map_add' s t := sec_ext_of_cover hL.cover fun p q => by
    simp only [coord_add, map_add, coord_mulFun', mul_add]
  map_smul' a s := sec_ext_of_cover hL.cover fun p q => by
    simp only [coord_smul, map_mul, coord_mulFun', resG_resG, RingHom.id_apply]
    ring
theorem mulFun_map (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V W : X.Opens}
    (h : W ≤ V) (s : Γ(toMod L, V)) :
    mulFun hL hM w ((toMod L).presheaf.map (homOfLE h).op s) =
      (toMod M).presheaf.map (homOfLE h).op (mulFun hL hM w s) :=
  sec_ext_of_cover hL.cover fun p q => by
    simp only [coord_map, coord_mulFun', resG_resG]
    exact (coord_mulFun hL hM w s p q _ _ _).symm
def homOfSec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) : toMod L ⟶ toMod M :=
  homOfLinear (mulLinear hL hM w) (mulFun_map hL hM w)
theorem mulFun_mulFun (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    (w' : LB.Sec (LB.div L M))
    (h : ∀ p q, homCoord w p q * resG X (le_inf inf_le_right inf_le_left) (homCoord w' q p) = 1)
    {V : X.Opens} (t : Γ(toMod M, V)) : mulFun hL hM w (mulFun hM hL w' t) = t :=
  sec_ext_of_cover hL.cover fun p q => by
    have := congrArg (resG X (inf_le_inf_right _ inf_le_right :
      V ⊓ M.U p ⊓ L.U q ≤ M.U p ⊓ L.U q)) (h p q)
    simp only [map_mul, map_one, resG_resG] at this
    rw [coord_mulFun', coord_mulFun hM hL w' t q p _ inf_le_left
      (le_inf inf_le_right (inf_le_left.trans inf_le_right)), ← mul_assoc, this, one_mul]
def isoOfGen (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) : toMod L ≅ toMod M where
  hom := homOfSec hL hM (DVR.genSec w hw)
  inv := homOfSec hM hL (DVR.genSec (Transport.invIso w) (Transport.invIso_spec hL hM w hw).1)
  hom_inv_id := by
    ext V s : 3
    refine mulFun_mulFun hM hL _ _ (fun q p => ?_) s
    exact (res (le_inf inf_le_right inf_le_left : L.U q ⊓ M.U p ≤ M.U p ⊓ L.U q)
      (w.s (p, q))).inv_mul
  inv_hom_id := by
    ext V s : 3
    refine mulFun_mulFun hL hM _ _ (fun p q => ?_) s
    have e (v : Γ(X, M.U p ⊓ L.U q)ˣ) : v.val *
        (res (le_inf inf_le_right inf_le_left : M.U p ⊓ L.U q ≤ L.U q ⊓ M.U p)
          (res (le_inf inf_le_right inf_le_left : L.U q ⊓ M.U p ≤ M.U p ⊓ L.U q) v)⁻¹).val = 1 := by
      rw [map_inv, Semi.LB.res_res, Units.mul_inv_eq_one, val_res, resG_self]
    exact e (w.s (p, q))
end Hom
def unitHom (σ : LB.Sec L) : unitMod X ⟶ toMod L :=
  homOfLinear (F := unitMod X) (fun V => LinearMap.toSpanSingleton Γ(X, V) _ (ofSec σ V))
    fun {V W} h (a : Γ(X, V)) => by
      change resG X h a • ofSec σ W = (toMod L).presheaf.map (homOfLE h).op (a • ofSec σ V)
      rw [Scheme.Modules.map_smul, map_ofSec]
theorem bijective_smul_genSec (hL : ⨆ i, L.U i = ⊤) {t : LB.Gen L} (ht : t.IsGen) (V : X.Opens) :
    Function.Bijective fun a : Γ(X, V) => a • ofSec (DVR.genSec t ht) V := by
  constructor
  · intro a b hab
    refine fun_ext_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left) (le_iSup_inf hL V)
      fun i => ?_
    exact (res (inf_le_right : V ⊓ L.U i ≤ L.U i) (t.s i)).mul_left_inj.1
      (congrArg (fun s => coord s i) hab)
  · intro s
    obtain ⟨a, ha⟩ := exists_fun_of_cover (fun i => V ⊓ L.U i) (fun _ => inf_le_left)
      (le_iSup_inf hL V)
      (fun i => coord s i * ((res (inf_le_right : V ⊓ L.U i ≤ L.U i) (t.s i))⁻¹ : Γ(X, _)ˣ))
      fun i j => by
        have l : V ⊓ L.U i ⊓ (V ⊓ L.U j) ≤ L.U i ⊓ L.U j := inf_le_inf inf_le_right inf_le_right
        have e := congrArg (res l) (ht i j)
        simp only [map_mul, Semi.LB.res_res] at e
        rw [map_mul, map_mul, ← val_res, ← val_res, map_inv, map_inv, Semi.LB.res_res,
          Semi.LB.res_res, e, coord_rel s i j _ inf_le_right l, ← val_res l, mul_inv,
          Units.val_mul, mul_mul_mul_comm, Units.mul_inv, one_mul]
    refine ⟨a, sec_ext fun i => ?_⟩
    change resG X _ a * (res (inf_le_right : V ⊓ L.U i ≤ L.U i) (t.s i)).val = _
    rw [ha i, Units.inv_mul_cancel_right]
def unitIso (hL : L.IsLB) (t : LB.Gen L) (ht : t.IsGen) : unitMod X ≅ toMod L :=
  haveI : IsIso (unitHom (DVR.genSec t ht)) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun V =>
      (ConcreteCategory.isIso_iff_bijective _).2 (bijective_smul_genSec hL.cover ht V)
  asIso (unitHom (DVR.genSec t ht))
section Pull
variable (f : Y ⟶ X)
theorem pull_U_le (j : (L.pull f).ι) : (L.pull f).U j ≤ f ⁻¹ᵁ L.U (j PUnit.unit) :=
  Semi.LB.wchart_le L (fun _ : PUnit.{1} => f) j PUnit.unit
theorem pull_U (j : (L.pull f).ι) : (L.pull f).U j = f ⁻¹ᵁ L.U (j PUnit.unit) :=
  le_antisymm (pull_U_le f j) fun _ hy => Set.mem_iInter.2 fun _ => hy
theorem appLE_resG {U U' : X.Opens} (h : U' ≤ U) {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ U')
    (a : Γ(X, U)) :
    (f.appLE U' W e).hom (resG X h a) = (f.appLE U W (e.trans (f.preimage_mono h))).hom a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
@[simp] theorem resG_appLE {U : X.Opens} {W W' : Y.Opens} (e : W ≤ f ⁻¹ᵁ U) (h : W' ≤ W)
    (a : Γ(X, U)) :
    resG Y h ((f.appLE U W e).hom a) = (f.appLE U W' (h.trans e)).hom a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
theorem resG_app {U : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    resG Y e ((f.app U).hom a) = (f.appLE U W e).hom a := rfl
theorem resG_pull_g (i j : (L.pull f).ι) {W : Y.Opens}
    (h : W ≤ (L.pull f).U i ⊓ (L.pull f).U j) :
    resG Y h ((L.pull f).g i j : Γ(Y, (L.pull f).U i ⊓ (L.pull f).U j)) =
      (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) W
        (h.trans (inf_le_inf (pull_U_le f i) (pull_U_le f j)))).hom
        (L.g (i PUnit.unit) (j PUnit.unit) : Γ(X, L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))) := by
  have := Semi.LB.res_lcg L (fun _ : PUnit.{1} => f) (fun _ => 1) i j h
  rw [Fintype.prod_unique, zpow_one] at this
  exact congrArg Units.val this
theorem pull_inf_le (V : X.Opens) (j : (L.pull f).ι) :
    f ⁻¹ᵁ V ⊓ (L.pull f).U j ≤ f ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit)) :=
  inf_le_inf_left _ (pull_U_le f j)
variable (L) in

def pullSec (V : X.Opens) :
    Γ(toMod L, V) →ₛₗ[(f.app V).hom] Γ(toMod (L.pull f), f ⁻¹ᵁ V) where
  toFun s := mkSec (fun j => (f.appLE _ _ (pull_inf_le f V j)).hom (coord s (j PUnit.unit)))
    fun i j => by
      have e : f ⁻¹ᵁ V ⊓ (L.pull f).U i ⊓ (L.pull f).U j ≤
          f ⁻¹ᵁ (V ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
        inf_le_inf (pull_inf_le f V i) (pull_U_le f j)
      have := congrArg (f.appLE _ _ e).hom (coord_mem s (i PUnit.unit) (j PUnit.unit))
      rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
      rw [resG_appLE, resG_appLE, resG_pull_g]
      exact this
  map_add' s t := sec_ext fun j => map_add (f.appLE _ _ (pull_inf_le f V j)).hom _ _
  map_smul' a s := sec_ext fun j => by
    simp only [coord_mkSec, coord_smul, map_mul]
    rw [appLE_resG, resG_app]
    rfl
@[simp] theorem coord_pullSec {V : X.Opens} (s : Γ(toMod L, V)) (j : (L.pull f).ι) :
    coord (pullSec L f V s) j =
      (f.appLE _ _ (pull_inf_le f V j)).hom (coord s (j PUnit.unit)) := rfl
theorem pullSec_map {V W : X.Opens} (h : W ≤ V) (s : Γ(toMod L, V)) :
    pullSec L f W ((toMod L).presheaf.map (homOfLE h).op s) =
      (toMod (L.pull f)).presheaf.map (homOfLE (f.preimage_mono h)).op (pullSec L f V s) :=
  sec_ext fun j => by
    rw [coord_pullSec, coord_map, coord_map, coord_pullSec, resG_appLE, appLE_resG]
variable (L) in

def toPushforward : toMod L ⟶ (Scheme.Modules.pushforward f).obj (toMod (L.pull f)) :=
  homOfLinear (G := (Scheme.Modules.pushforward f).obj (toMod (L.pull f)))
    (fun V =>
      { toFun := pullSec L f V
        map_add' := map_add (pullSec L f V)
        map_smul' := (pullSec L f V).map_smul' })
    (pullSec_map f)
variable (L) in

def pullbackHom : (Scheme.Modules.pullback f).obj (toMod L) ⟶ toMod (L.pull f) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (toPushforward L f)
end Pull
def trivIso (X : Scheme.{0}) : unitMod X ≅ toMod (Out.Inh.trivLB X) :=
  unitIso (Out.Inh.trivLB_isLB X) ⟨fun _ => 1⟩ fun _ _ => by
    exact (one_mul _).symm
def twoChart (U₀ U₁ : X.Opens) (u : Γ(X, U₀ ⊓ U₁)ˣ) : LB X where
  ι := Bool
  U i := cond i U₀ U₁
  g i j := match i, j with
    | true, true => 1
    | true, false => u
    | false, true => (res (le_inf inf_le_right inf_le_left) u)⁻¹
    | false, false => 1
theorem twoChart_isLB {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    (twoChart U₀ U₁ u).IsLB where
  cover := (iSup_bool_eq (f := fun i => cond i U₀ U₁)).trans h
  g_self := by rintro (_ | _) <;> exact map_one _
  cocycle := by
    have aux {W : X.Opens} (h₁ : W ≤ U₁ ⊓ U₀) (h₂ : W ≤ U₀ ⊓ U₁) :
        res h₁ (res (le_inf inf_le_right inf_le_left) u)⁻¹ * res h₂ u = 1 := by
      rw [map_inv, Semi.LB.res_res, inv_mul_cancel]
    rintro (_ | _) (_ | _) (_ | _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (aux _ _).trans (map_one _).symm
    · exact (congrArg (_ * ·) (map_one _)).trans (mul_one _)
    · exact (congrArg (_ * ·) (map_one _)).trans (mul_one _)
    · exact ((mul_comm _ _).trans (aux _ _)).trans (map_one _).symm
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
    · exact (congrArg (· * _) (map_one _)).trans (one_mul _)
theorem mem_secOn_twoChart {U₀ U₁ : X.Opens} (u : Γ(X, U₀ ⊓ U₁)ˣ) (V : X.Opens)
    (a : Γ(X, V ⊓ U₀)) (b : Γ(X, V ⊓ U₁)) :
    (fun i : Bool => match i with | true => a | false => b) ∈ secOn (twoChart U₀ U₁ u) V ↔
      resG X (inf_le_left : V ⊓ U₀ ⊓ U₁ ≤ V ⊓ U₀) a =
        resG X (inf_le_inf_right _ inf_le_right) (u : Γ(X, U₀ ⊓ U₁)) *
          resG X (inf_le_inf_right _ inf_le_left) b := by
  refine ⟨fun h => h true false, fun h => ?_⟩
  rintro (_ | _) (_ | _)
  · change resG X _ b = resG X _ 1 * resG X _ b
    rw [map_one, one_mul]
  · have l : V ⊓ U₁ ⊓ U₀ ≤ V ⊓ U₀ ⊓ U₁ := (inf_right_comm _ _ _).le
    have e := congrArg (resG X l) h
    simp only [map_mul, resG_resG] at e
    change resG X (inf_le_left : V ⊓ U₁ ⊓ U₀ ≤ V ⊓ U₁) b =
      (res (inf_le_inf_right _ inf_le_right : V ⊓ U₁ ⊓ U₀ ≤ U₁ ⊓ U₀)
        (res (le_inf inf_le_right inf_le_left) u)⁻¹).val *
          resG X (inf_le_inf_right _ inf_le_left : V ⊓ U₁ ⊓ U₀ ≤ V ⊓ U₀) a
    rw [e, map_inv, Semi.LB.res_res, ← val_res, Units.inv_mul_cancel_left]
  · exact h
  · change resG X _ a = resG X _ 1 * resG X _ a
    rw [map_one, one_mul]
example (V : X.Opens) :
    (fun i : Bool => match i with | true => -1 | false => 1) ∈
      secOn (twoChart (X := X) ⊤ ⊤ (-1)) V :=
  (mem_secOn_twoChart (-1) V (-1) 1).2 (by
    simp only [map_one, Units.val_neg, Units.val_one, map_neg, mul_one]
    exact congrArg Neg.neg (map_one _))
example (V : X.Opens) :
    (fun i : Bool => match i with | true => 1 | false => 1) ∈
      secOn (twoChart (X := X) ⊤ ⊤ (-1)) V ↔ (2 : Γ(X, V ⊓ ⊤ ⊓ ⊤)) = 0 := by
  refine (mem_secOn_twoChart (-1) V 1 1).trans ?_
  simp only [map_one, Units.val_neg, Units.val_one, map_neg, mul_one]
  rw [eq_neg_iff_add_eq_zero, one_add_one_eq_two]
example {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    coord (chartSec (twoChart_isLB h u) false) true =
      resG X (le_inf inf_le_right inf_le_left : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁) (u : Γ(X, U₀ ⊓ U₁)) := rfl
example {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    (toMod (twoChart U₀ U₁ u)).IsQuasicoherent :=
  isQuasicoherent_toMod (twoChart_isLB h u)
theorem twoChart_isGen {U₀ U₁ : X.Opens} (u : Γ(X, U₀ ⊓ U₁)ˣ) (a : Γ(X, U₀)ˣ) (b : Γ(X, U₁)ˣ)
    (h : res inf_le_left a = u * res inf_le_right b) :
    LB.Gen.IsGen (L := twoChart U₀ U₁ u)
      ⟨fun i : Bool => match i with | true => a | false => b⟩ := by
  rintro (_ | _) (_ | _)
  · exact (one_mul _).symm
  · have e := congrArg (res (le_inf inf_le_right inf_le_left : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁)) h
    rw [map_mul, Semi.LB.res_res, Semi.LB.res_res] at e
    exact eq_inv_mul_of_mul_eq e.symm
  · exact h
  · exact (one_mul _).symm
example (a : Γ(X, ⊤)) : ∃ u : Γ(X, X.basicOpen a ⊓ X.basicOpen (1 - a))ˣ,
    (u : Γ(X, X.basicOpen a ⊓ X.basicOpen (1 - a))) = resG X le_top a ∧
      (twoChart _ _ u).IsLB ∧ Nonempty (unitMod X ≅ toMod (twoChart _ _ u)) := by
  have h : X.basicOpen a ⊔ X.basicOpen (1 - a) = ⊤ := by
    refine eq_top_iff.2 (le_trans ?_ (X.basicOpen_add_le a (1 - a)))
    rw [add_sub_cancel, X.basicOpen_of_isUnit isUnit_one]
  obtain ⟨v, hv⟩ : IsUnit (resG X (le_top : X.basicOpen a ≤ ⊤) a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  refine ⟨res inf_le_left v, by rw [val_res, hv, resG_resG], twoChart_isLB h _,
    ⟨unitIso (twoChart_isLB h _) _ (twoChart_isGen _ v 1 (by rw [map_one, mul_one]))⟩⟩
end LB
end GlobalTheory


