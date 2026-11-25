-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
-- name    : Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:20:43.174032+00:00
-- url     : https://prove2.me/theorems/333a2a34-c22e-41e3-94b3-625b58ab6af0
-- title:
--   Is Scalar Tower Of Algebra Map Eq
-- statement:
--   Definitions and structural lemmas for Is Scalar Tower Of Algebra Map Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Theorems.Thm_GlobalTheory_AbLaw_isLB_tw
import Theorems.Thm_GlobalTheory_AbLaw_tw_g
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_isZero_cechComplex_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
abbrev SecOn (M : LB X) (V : X.Opens) : Type := Γ(GlobalTheory.LB.toMod M, V)
namespace SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
variable (M V) in

def equivFamilies : SecOn M V ≃ Geo.Tor.secOn M V := secOnEquiv M V
theorem compat (s : SecOn M V) (i j : M.ι) {O : X.Opens} (hi : O ≤ V ⊓ M.U i) (hj : O ≤ V ⊓ M.U j)
    (hij : O ≤ M.U i ⊓ M.U j) :
    rs X hi (coord s i) = rs X hij (M.g i j).val * rs X hj (coord s j) :=
  coord_rel s i j hi hj hij
variable (M) in

def restrict (h : W ≤ V) : SecOn M V →ₛₗ[rs X h] SecOn M W where
  toFun s := (toMod M).presheaf.map (homOfLE h).op s
  map_add' s t := sec_ext fun i => by simp only [coord_map, coord_add, map_add]
  map_smul' a s := sec_ext fun i => by simp only [coord_map, coord_smul, map_mul, rs_rs]
@[simp] theorem coord_restrict (h : W ≤ V) (s : SecOn M V) (i : M.ι) :
    coord (restrict M h s) i = rs X (inf_le_inf_right _ h) (coord s i) := rfl
@[simp] theorem restrict_self (h : V ≤ V) (s : SecOn M V) : restrict M h s = s :=
  sec_ext fun _ => rs_self _ _
@[simp] theorem restrict_restrict {O : X.Opens} (h₁ : W ≤ V) (h₂ : O ≤ W) (s : SecOn M V) :
    restrict M h₂ (restrict M h₁ s) = restrict M (h₂.trans h₁) s :=
  sec_ext fun _ => rs_rs _ _ _
variable (M) in

def topEquiv : SecOn M ⊤ ≃ₗ[Γ(X, ⊤)] LB.Sec M := globalEquiv M
@[simp] theorem restrict_ofSec (s : LB.Sec M) (h : W ≤ V) :
    restrict M h (ofSec s V) = ofSec s W := map_ofSec s h
def chart (hM : M.IsLB) (i : M.ι) (h : V ≤ M.U i) : SecOn M V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  chartEquiv hM i h
theorem coord_chart_symm (hM : M.IsLB) (i j : M.ι) (h : V ≤ M.U i) (a : Γ(X, V)) :
    coord ((chart hM i h).symm a) j = rs X inf_le_left a *
      rs X (le_inf inf_le_right (inf_le_left.trans h) : V ⊓ M.U j ≤ M.U j ⊓ M.U i) (M.g j i).val :=
  congrArg (rs X inf_le_left a * ·) (rs_rs _ _ _)
def congr (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) (V : X.Opens) :
    SecOn L V ≃ₗ[Γ(X, V)] SecOn M V :=
  LinearEquiv.ofBijective (mulLinear hL hM (DVR.genSec w hw) V)
    (ConcreteCategory.bijective_of_isIso ((isoOfGen hL hM w hw).hom.app V))
theorem congr_restrict (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) (h : W ≤ V)
    (s : SecOn L V) :
    congr hL hM w hw W (restrict L h s) = restrict M h (congr hL hM w hw V s) :=
  mulFun_map hL hM _ h s
variable (M) in

def pull (π : X' ⟶ X) (V : X.Opens) :
    SecOn M V →ₛₗ[(π.app V).hom] SecOn (M.pull π) (π ⁻¹ᵁ V) := pullSec M π V
variable (M) in

def pullLE (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V) :
    SecOn M V →ₛₗ[(π.appLE V V' e).hom] SecOn (M.pull π) V' where
  toFun s := restrict (M.pull π) e (pull M π V s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' a s := by
    rw [map_smulₛₗ, map_smulₛₗ]
    rfl
variable {t : ℤ}
def twCoord (x : SecOn (tw M H t) V) (p : M.ι) (k : H.ι) : Γ(X, V ⊓ (M.U p ⊓ H.U k)) :=
  coord x (p, k)
theorem tw_ext {x y : SecOn (tw M H t) V} (h : ∀ p k, twCoord x p k = twCoord y p k) : x = y :=
  sec_ext fun p => h p.1 p.2
@[simp] theorem twCoord_add (x y : SecOn (tw M H t) V) (p : M.ι) (k : H.ι) :
    twCoord (x + y) p k = twCoord x p k + twCoord y p k := rfl
@[simp] theorem twCoord_smul (a : Γ(X, V)) (x : SecOn (tw M H t) V) (p : M.ι) (k : H.ι) :
    twCoord (a • x) p k = rs X inf_le_left a * twCoord x p k := rfl
@[simp] theorem twCoord_restrict (h : W ≤ V) (x : SecOn (tw M H t) V) (p : M.ι) (k : H.ι) :
    twCoord (restrict (tw M H t) h x) p k = rs X (inf_le_inf_right _ h) (twCoord x p k) := rfl
theorem res_tw_g (t : ℤ) (p q : M.ι) (k l : H.ι) {O : X.Opens}
    (h : O ≤ M.U p ⊓ H.U k ⊓ (M.U q ⊓ H.U l)) (hM : O ≤ M.U p ⊓ M.U q) (hH : O ≤ H.U k ⊓ H.U l) :
    res h ((tw M H t).g (p, k) (q, l)) = res hM (M.g p q) * res hH (H.g k l) ^ t := by
  refine (congrArg (res h) (tw_g M H t (p, k) (q, l))).trans ?_
  rw [map_mul, map_zpow, LB.res_res, LB.res_res]
theorem twCoord_compat (x : SecOn (tw M H t) V) (p q : M.ι) (k l : H.ι) {O : X.Opens}
    (hp : O ≤ V ⊓ (M.U p ⊓ H.U k)) (hq : O ≤ V ⊓ (M.U q ⊓ H.U l))
    (hM : O ≤ M.U p ⊓ M.U q) (hH : O ≤ H.U k ⊓ H.U l) :
    rs X hp (twCoord x p k) =
      (res hM (M.g p q) * res hH (H.g k l) ^ t).val * rs X hq (twCoord x q l) :=
  (compat x (p, k) (q, l) hp hq (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right))).trans
    (congrArg (fun u : Γ(X, O)ˣ => u.val * rs X hq (twCoord x q l)) (res_tw_g t p q k l _ hM hH))
def twMk (t : ℤ) (y : ∀ (p : M.ι) (k : H.ι), Γ(X, V ⊓ (M.U p ⊓ H.U k)))
    (hy : ∀ (p q : M.ι) (k l : H.ι) (O : X.Opens)
      (hp : O ≤ V ⊓ (M.U p ⊓ H.U k)) (hq : O ≤ V ⊓ (M.U q ⊓ H.U l))
      (hM : O ≤ M.U p ⊓ M.U q) (hH : O ≤ H.U k ⊓ H.U l),
      rs X hp (y p k) = (res hM (M.g p q) * res hH (H.g k l) ^ t).val * rs X hq (y q l)) :
    SecOn (tw M H t) V :=
  mkSec (L := tw M H t) (fun p => y p.1 p.2) fun p q =>
    have hM : V ⊓ (M.U p.1 ⊓ H.U p.2) ⊓ (M.U q.1 ⊓ H.U q.2) ≤ M.U p.1 ⊓ M.U q.1 :=
      inf_le_inf (inf_le_right.trans inf_le_left) inf_le_left
    have hH : V ⊓ (M.U p.1 ⊓ H.U p.2) ⊓ (M.U q.1 ⊓ H.U q.2) ≤ H.U p.2 ⊓ H.U q.2 :=
      inf_le_inf (inf_le_right.trans inf_le_right) inf_le_right
    (hy p.1 q.1 p.2 q.2 _ inf_le_left (inf_le_inf_right _ inf_le_left) hM hH).trans
      (congrArg (fun u : Γ(X, V ⊓ (M.U p.1 ⊓ H.U p.2) ⊓ (M.U q.1 ⊓ H.U q.2))ˣ =>
          u.val * rs X (inf_le_inf_right _ inf_le_left) (y q.1 q.2))
        (res_tw_g (M := M) (H := H) t p.1 q.1 p.2 q.2 (inf_le_inf_right _ inf_le_right) hM hH).symm)
@[simp] theorem twCoord_twMk (y : ∀ (p : M.ι) (k : H.ι), Γ(X, V ⊓ (M.U p ⊓ H.U k))) (hy) (p : M.ι)
    (k : H.ι) : twCoord (twMk t y hy) p k = y p k := rfl
variable (M t) in

def mulSec (s : LB.Sec H) (V : X.Opens) :
    SecOn (tw M H t) V →ₗ[Γ(X, V)] SecOn (tw M H (t + 1)) V where
  toFun x := twMk (t + 1)
    (fun p k => rs X (inf_le_right.trans inf_le_right) (s.f k) * twCoord x p k)
    fun p q k l O hp hq hM hH => by
      rw [map_mul, map_mul, rs_rs, rs_rs, twCoord_compat x p q k l hp hq hM hH,
        sec_rel s k l _ (hH.trans inf_le_right) hH, zpow_add_one, ← val_res hH]
      simp only [Units.val_mul]
      ring
  map_add' x y := tw_ext fun p k => by simp only [twCoord_twMk, twCoord_add, mul_add]
  map_smul' a x := tw_ext fun p k => mul_left_comm _ _ _
@[simp] theorem twCoord_mulSec (s : LB.Sec H) (x : SecOn (tw M H t) V) (p : M.ι) (k : H.ι) :
    twCoord (mulSec M t s V x) p k =
      rs X (inf_le_right.trans inf_le_right) (s.f k) * twCoord x p k := rfl
theorem mulSec_restrict (s : LB.Sec H) (h : W ≤ V) (x : SecOn (tw M H t) V) :
    mulSec M t s W (restrict _ h x) = restrict _ h (mulSec M t s V x) :=
  tw_ext fun p k => by simp only [twCoord_mulSec, twCoord_restrict, map_mul, rs_rs]
theorem isUnit_rs_of_le_nonzeroLocus (s : LB.Sec H) (k : H.ι) {O : X.Opens} (hk : O ≤ H.U k)
    (h : O ≤ nonzeroLocus s) : IsUnit (rs X hk (s.f k)) := by
  have hb : O ≤ X.basicOpen (s.f k) := by
    intro x hx
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (h hx)
    have e := congrArg X.basicOpen (s.compat k l)
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (H.g k l).isUnit] at e
    erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
    have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk hx, X.basicOpen_le _ hl⟩
    exact (e.ge ⟨hx', hx', hl⟩).2
  have hu : IsUnit (rs X (X.basicOpen_le (s.f k)) (s.f k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.f k)
  simpa only [rs_rs] using hu.map (rs X hb)
theorem mulSec_bijective (s : LB.Sec H) (h : V ≤ nonzeroLocus s) :
    Function.Bijective (mulSec M t s V) := by
  have hu (p : M.ι) (k : H.ι) := isUnit_rs_of_le_nonzeroLocus s k
    (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U k) ≤ H.U k) (inf_le_left.trans h)
  refine ⟨fun x y e => tw_ext fun p k => (hu p k).mul_left_cancel (congrArg (twCoord · p k) e),
    fun y => ?_⟩
  have hv (p : M.ι) (k : H.ι) : rs X (inf_le_right.trans inf_le_right) (s.f k) *
      (((hu p k).unit⁻¹).val * twCoord y p k) = twCoord y p k := by
    rw [← _root_.mul_assoc, IsUnit.mul_val_inv, _root_.one_mul]
  refine ⟨twMk t (fun p k => ((hu p k).unit⁻¹).val * twCoord y p k)
    fun p q k l O hp hq hM hH => ?_, tw_ext hv⟩
  have e := twCoord_compat y p q k l hp hq hM hH
  rw [← hv p k, ← hv q l, map_mul (rs X hp), map_mul (rs X hq), rs_rs, rs_rs] at e
  refine (isUnit_rs_of_le_nonzeroLocus s k (hH.trans inf_le_left)
    (hp.trans (inf_le_left.trans h))).mul_left_cancel (e.trans ?_)
  rw [sec_rel s k l (hH.trans inf_le_left) (hH.trans inf_le_right) hH, zpow_add_one, ← val_res hH]
  simp only [Units.val_mul]
  ring
variable (M t) in

def mulSecEquiv (s : LB.Sec H) (h : V ≤ nonzeroLocus s) :
    SecOn (tw M H t) V ≃ₗ[Γ(X, V)] SecOn (tw M H (t + 1)) V :=
  LinearEquiv.ofBijective _ (mulSec_bijective s h)
@[simp] theorem mulSecEquiv_apply (s : LB.Sec H) (h : V ≤ nonzeroLocus s)
    (x : SecOn (tw M H t) V) : mulSecEquiv M t s h x = mulSec M t s V x := rfl
variable (M H) in

def twZeroIso : LB.Iso M (tw M H 0) where
  s a := res (inf_le_inf_right _ inf_le_left : M.U a.1.1 ⊓ H.U a.1.2 ⊓ M.U a.2 ≤ M.U a.1.1 ⊓ M.U a.2)
    (M.g a.1.1 a.2)
theorem twZeroIso_isGen (hM : M.IsLB) : (twZeroIso M H).IsGen := by
  rintro ⟨⟨p, k⟩, q⟩ ⟨⟨p', k'⟩, q'⟩
  let O := M.U p ⊓ H.U k ⊓ M.U q ⊓ (M.U p' ⊓ H.U k' ⊓ M.U q')
  have h₁ : O ≤ M.U p := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have h₂ : O ≤ M.U q := inf_le_left.trans inf_le_right
  have h₃ : O ≤ M.U p' := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have h₄ : O ≤ M.U q' := inf_le_right.trans inf_le_right
  have e := res_tw_g (M := M) (H := H) 0 p p' k k' (O := O) (inf_le_inf inf_le_left inf_le_left) (le_inf h₁ h₃)
    (inf_le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right))
  rw [zpow_zero, _root_.mul_one] at e
  have key : res (le_inf h₁ h₂) (M.g p q) = res (le_inf h₁ h₃) (M.g p p') *
      (res (le_inf h₂ h₄) (M.g q q'))⁻¹ * res (le_inf h₃ h₄) (M.g p' q') := by
    rw [mul_right_comm, LB.res_cocycle hM p p' q' _ _ (le_inf h₁ h₄),
      ← LB.res_cocycle hM p q q' (le_inf h₁ h₂) (le_inf h₂ h₄), mul_inv_cancel_right]
  exact (LB.res_res _ _ _).trans (key.trans (congrArg₂ (· * ·)
    (congrArg (· * (res (le_inf h₂ h₄) (M.g q q'))⁻¹) e.symm) (LB.res_res _ _ _).symm))
def twZeroEquiv (hM : M.IsLB) (hH : H.IsLB) (V : X.Opens) :
    SecOn M V ≃ₗ[Γ(X, V)] SecOn (tw M H 0) V :=
  congr hM (isLB_tw hM hH 0) (twZeroIso M H) (twZeroIso_isGen hM) V
end SecOn
abbrev cstAlgebra (f : X ⟶ Spec (CommRingCat.of R)) (V : X.Opens) : Algebra R Γ(X, V) :=
  (cst f V).toAlgebra
theorem appLE_cst {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {π : X' ⟶ X} {g : R →+* R'} (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    {V : X.Opens} {V' : X'.Opens} (e : V' ≤ π ⁻¹ᵁ V) (r : R) :
    (π.appLE V V' e).hom (cst f V r) = cst f' V' (g r) := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ π.appTop =
      CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ f'.appTop := by
    rw [← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  exact (GlobalTheory.LB.appLE_resG π le_top e _).trans
    (congrArg (rs X' (le_top : V' ≤ ⊤)) (congrArg (fun q => q.hom r) h))
def SecOnR (_f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) (V : X.Opens) : Type := SecOn M V
namespace SecOnR
variable (f : X ⟶ Spec (CommRingCat.of R)) {L M H : LB X} {V W : X.Opens}
instance : AddCommGroup (SecOnR f M V) := inferInstanceAs (AddCommGroup (SecOn M V))
instance : Module Γ(X, V) (SecOnR f M V) := inferInstanceAs (Module Γ(X, V) (SecOn M V))
instance : Module R (SecOnR f M V) := Module.compHom (SecOnR f M V) (cst f V)
instance isScalarTower :
    @IsScalarTower R Γ(X, V) (SecOnR f M V) (cstAlgebra f V).toSMul _ _ :=
  letI := cstAlgebra f V
  ⟨fun r a s => mul_smul (cst f V r) a s⟩
instance : SMulCommClass R Γ(X, V) (SecOnR f M V) := ⟨fun r a s => smul_comm (cst f V r) a s⟩
instance : SMulCommClass Γ(X, V) R (SecOnR f M V) := SMulCommClass.symm _ _ _
variable (M V) in

def of : SecOn M V ≃ₗ[Γ(X, V)] SecOnR f M V := LinearEquiv.refl _ _
variable {f} in

def coord (s : SecOnR f M V) (i : M.ι) : Γ(X, V ⊓ M.U i) := GlobalTheory.LB.coord ((of f M V).symm s) i
@[simp] theorem coord_of (s : SecOn M V) (i : M.ι) : coord (of f M V s) i = GlobalTheory.LB.coord s i := rfl
variable {f}
@[ext] theorem ext {s t : SecOnR f M V} (h : ∀ i, coord s i = coord t i) : s = t :=
  GlobalTheory.LB.sec_ext h
@[simp] theorem coord_zero (i : M.ι) : coord (0 : SecOnR f M V) i = 0 := rfl
@[simp] theorem coord_add (s t : SecOnR f M V) (i : M.ι) :
    coord (s + t) i = coord s i + coord t i := rfl
@[simp] theorem coord_neg (s : SecOnR f M V) (i : M.ι) : coord (-s) i = -coord s i := rfl
@[simp] theorem coord_sub (s t : SecOnR f M V) (i : M.ι) :
    coord (s - t) i = coord s i - coord t i := rfl
@[simp] theorem coord_smul (a : Γ(X, V)) (s : SecOnR f M V) (i : M.ι) :
    coord (a • s) i = rs X inf_le_left a * coord s i := rfl
@[simp] theorem coord_base_smul (r : R) (s : SecOnR f M V) (i : M.ι) :
    coord (r • s) i = cst f _ r * coord s i :=
  congrArg (· * coord s i) (rs_cst f inf_le_left r)
variable (f)
variable (M) in

def restrict (h : W ≤ V) : SecOnR f M V →ₗ[R] SecOnR f M W where
  toFun s := of f M W (SecOn.restrict M h ((of f M V).symm s))
  map_add' s t := (SecOn.restrict M h).map_add s t
  map_smul' r s := ((SecOn.restrict M h).map_smulₛₗ (cst f V r) s).trans
    (congrArg (· • SecOn.restrict M h s) (rs_cst f h r))
@[simp] theorem restrict_of (h : W ≤ V) (s : SecOn M V) :
    restrict f M h (of f M V s) = of f M W (SecOn.restrict M h s) := rfl
@[simp] theorem coord_restrict (h : W ≤ V) (s : SecOnR f M V) (i : M.ι) :
    coord (restrict f M h s) i = rs X (inf_le_inf_right _ h) (coord s i) := rfl
@[simp] theorem restrict_self (h : V ≤ V) (s : SecOnR f M V) : restrict f M h s = s :=
  SecOn.restrict_self h _
@[simp] theorem restrict_restrict {O : X.Opens} (h₁ : W ≤ V) (h₂ : O ≤ W) (s : SecOnR f M V) :
    restrict f M h₂ (restrict f M h₁ s) = restrict f M (h₂.trans h₁) s :=
  SecOn.restrict_restrict h₁ h₂ _
def lin (φ : SecOn L V →ₗ[Γ(X, V)] SecOn M V) : SecOnR f L V →ₗ[R] SecOnR f M V where
  toFun s := of f M V (φ ((of f L V).symm s))
  map_add' s t := φ.map_add s t
  map_smul' r s := φ.map_smul (cst f V r) s
@[simp] theorem lin_of (φ : SecOn L V →ₗ[Γ(X, V)] SecOn M V) (s : SecOn L V) :
    lin f φ (of f L V s) = of f M V (φ s) := rfl
def linEquiv (φ : SecOn L V ≃ₗ[Γ(X, V)] SecOn M V) : SecOnR f L V ≃ₗ[R] SecOnR f M V :=
  LinearEquiv.ofBijective (lin f φ.toLinearMap) φ.bijective
@[simp] theorem linEquiv_of (φ : SecOn L V ≃ₗ[Γ(X, V)] SecOn M V) (s : SecOn L V) :
    linEquiv f φ (of f L V s) = of f M V (φ s) := rfl
variable (M) in

def topEquiv : SecOnR f M ⊤ ≃ₗ[Γ(X, ⊤)] LB.Sec M := (of f M ⊤).symm ≪≫ₗ SecOn.topEquiv M
def chart (hM : M.IsLB) (i : M.ι) (h : V ≤ M.U i) : SecOnR f M V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (of f M V).symm ≪≫ₗ SecOn.chart hM i h
variable (M) in

def mulSec (t : ℤ) (s : LB.Sec H) (V : X.Opens) :
    SecOnR f (tw M H t) V →ₗ[R] SecOnR f (tw M H (t + 1)) V := lin f (SecOn.mulSec M t s V)
theorem mulSec_bijective (t : ℤ) (s : LB.Sec H) (h : V ≤ nonzeroLocus s) :
    Function.Bijective (mulSec f M t s V) := SecOn.mulSec_bijective s h
def twZeroEquiv (hM : M.IsLB) (hH : H.IsLB) (V : X.Opens) :
    SecOnR f M V ≃ₗ[R] SecOnR f (tw M H 0) V := linEquiv f (SecOn.twZeroEquiv hM hH V)
section Pull
variable {f} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X} {g : R →+* R'}
  (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
variable (M) in

def pull (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V) :
    SecOnR f M V →ₛₗ[g] SecOnR f' (M.pull π) V' where
  toFun s := of f' _ V' (SecOn.pullLE M π V V' e ((of f M V).symm s))
  map_add' s t := (SecOn.pullLE M π V V' e).map_add s t
  map_smul' r s := ((SecOn.pullLE M π V V' e).map_smulₛₗ (cst f V r) s).trans
    (congrArg (· • SecOn.pullLE M π V V' e s) (appLE_cst w e r))
@[simp] theorem pull_of {V' : X'.Opens} (e : V' ≤ π ⁻¹ᵁ V) (s : SecOn M V) :
    pull M w V V' e (of f M V s) = of f' _ V' (SecOn.pullLE M π V V' e s) := rfl
end Pull
end SecOnR
section Cech
variable {κ : Type} (f : X ⟶ Spec (CommRingCat.of R)) {L : LB X} (M : LB X) (D : κ → X.Opens)
theorem iInf_le_iInf_of_subset {s t : Finset κ} (h : s ⊆ t) : ⨅ i ∈ t, D i ≤ ⨅ i ∈ s, D i :=
  biInf_mono fun _ hi => h hi
def secCube : GlobalTheory.Cube.{0} κ R :=
  GlobalTheory.Cube.mk (fun s => ModuleCat.of R (SecOnR f M (⨅ i ∈ s, D i)))
    (fun h => SecOnR.restrict f M (iInf_le_iInf_of_subset D h))
    (fun _ x => SecOnR.restrict_self f _ x) (fun _ _ x => SecOnR.restrict_restrict f _ _ x)
def cechLB [LinearOrder κ] : CochainComplex (ModuleCat.{0} R) ℕ := cechComplex (secCube f M D)
theorem isZero_cechLB_X [LinearOrder κ] [Fintype κ] {p : ℕ} (h : Fintype.card κ ≤ p) :
    IsZero ((cechLB f M D).X p) := isZero_cechComplex_X _ h
variable {M}
def secCubeMap (φ : ∀ V : X.Opens, SecOn L V →ₗ[Γ(X, V)] SecOn M V)
    (hφ : ∀ {V W : X.Opens} (h : W ≤ V) (s : SecOn L V),
      φ W (SecOn.restrict L h s) = SecOn.restrict M h (φ V s)) :
    secCube f L D ⟶ secCube f M D :=
  GlobalTheory.Cube.homMk (fun _ => SecOnR.lin f (φ _)) fun h x => hφ (iInf_le_iInf_of_subset D h) x
def secCubeIso (φ : ∀ V : X.Opens, SecOn L V ≃ₗ[Γ(X, V)] SecOn M V)
    (hφ : ∀ {V W : X.Opens} (h : W ≤ V) (s : SecOn L V),
      φ W (SecOn.restrict L h s) = SecOn.restrict M h (φ V s)) :
    secCube f L D ≅ secCube f M D :=
  GlobalTheory.Cube.isoMk (fun _ => SecOnR.linEquiv f (φ _)) fun h x => hφ (iInf_le_iInf_of_subset D h) x
def secCubeCongr (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) :
    secCube f L D ≅ secCube f M D :=
  secCubeIso f D (SecOn.congr hL hM w hw) (SecOn.congr_restrict hL hM w hw)
def cechLBCongr [LinearOrder κ] (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) :
    cechLB f L D ≅ cechLB f M D :=
  (cechFunctor κ R).mapIso (secCubeCongr f D hL hM w hw)
def cechLBTwZero [LinearOrder κ] {H : LB X} (hM : M.IsLB) (hH : H.IsLB) :
    cechLB f M D ≅ cechLB f (tw M H 0) D :=
  cechLBCongr f D hM (isLB_tw hM hH 0) (SecOn.twZeroIso M H) (SecOn.twZeroIso_isGen hM)
variable (M) in

def secCubeMul {H : LB X} (t : ℤ) (s : LB.Sec H) :
    secCube f (tw M H t) D ⟶ secCube f (tw M H (t + 1)) D :=
  secCubeMap f D (SecOn.mulSec M t s) (SecOn.mulSec_restrict s)
theorem preimage_biInf (π : X' ⟶ X) (s : Finset κ) :
    π ⁻¹ᵁ (⨅ i ∈ s, D i) = ⨅ i ∈ s, π ⁻¹ᵁ D i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => rw [Finset.iInf_insert, Finset.iInf_insert, ← ih]; rfl
variable {f} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X} {g : R →+* R'}
  (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
variable (M) in

def secCubePull (s : Finset κ) :
    (secCube f M D).obj s →ₛₗ[g] (secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i).obj s :=
  SecOnR.pull M w _ _ (preimage_biInf D π s).ge
end Cech
def secOnTrivEquiv (V : X.Opens) : SecOn (Inh.trivLB X) V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  SecOn.chart (Inh.trivLB_isLB X) PUnit.unit le_top
def secOnRTrivEquiv (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] {V : X.Opens} (hV : V = ⊤) :
    R ≃ₗ[R] SecOnR f (Inh.trivLB X) V :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton R _ (SecOnR.of f _ V ((secOnTrivEquiv V).symm 1)))
    (by
      have e : ⇑(LinearMap.toSpanSingleton R _ (SecOnR.of f _ V ((secOnTrivEquiv V).symm 1))) =
          (secOnTrivEquiv V).symm ∘ cst f V := funext fun r =>
        (((secOnTrivEquiv V).symm.map_smul (cst f V r) 1).symm).trans
          (congrArg (secOnTrivEquiv V).symm (_root_.mul_one _))
      rw [e]
      exact (secOnTrivEquiv V).symm.bijective.comp (cst_bijective f hV))
example : Nonempty (ℤ ≃ₗ[ℤ]
    (secCube (𝟙 (Spec (CommRingCat.of ℤ))) (Inh.trivLB _) (fun _ : Fin 2 => ⊤)).obj {0, 1}) :=
  ⟨secOnRTrivEquiv (𝟙 (Spec (CommRingCat.of ℤ))) (by simp)⟩
example : ¬ IsZero ((cechLB (𝟙 (Spec (CommRingCat.of ℚ))) (Inh.trivLB _)
      (fun _ : Fin 1 => ⊤)).X 0) ∧
    IsZero ((cechLB (𝟙 (Spec (CommRingCat.of ℚ))) (Inh.trivLB _) (fun _ : Fin 1 => ⊤)).X 1) := by
  refine ⟨fun h => ?_, isZero_cechLB_X _ _ _ (by simp)⟩
  have hs := ModuleCat.isZero_iff_subsingleton.1 h
  let e (s : {s : Finset (Fin 1) // s.card = 0 + 1}) :=
    secOnRTrivEquiv (𝟙 (Spec (CommRingCat.of ℚ))) (V := ⨅ _i ∈ s.1, ⊤) (by simp)
  have := congrFun (hs.elim (fun s => e s 1) (fun s => e s 0)) ⟨{0}, rfl⟩
  exact one_ne_zero ((e _).injective this)
example (M : LB X) (t : ℤ) (V : X.Opens) : Function.Bijective (SecOn.mulSec M t (oneSec X) V) :=
  SecOn.mulSec_bijective _ ((nonzeroLocus_oneSec X).symm ▸ le_top)
example {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    GlobalTheory.LB.coord ((SecOn.chart (GlobalTheory.LB.twoChart_isLB h u) false (le_rfl : U₁ ≤ U₁)).symm 1) true =
      rs X (le_inf inf_le_right inf_le_left : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁) u.val :=
  (SecOn.coord_chart_symm (GlobalTheory.LB.twoChart_isLB h u) false true le_rfl 1).trans
    ((congrArg (· * rs X (le_inf inf_le_right inf_le_left : U₁ ⊓ U₀ ≤ U₀ ⊓ U₁) u.val)
      (map_one (rs X (inf_le_left : U₁ ⊓ U₀ ≤ U₁)))).trans (_root_.one_mul _))
end GlobalTheory.AbLaw


