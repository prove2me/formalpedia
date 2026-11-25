-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:49.51197+00:00
-- url     : https://prove2.me/theorems/98fb1ecb-3377-4a6c-b6bc-c15f1a8f08dd
-- title:
--   Invertible Dual
-- statement:
--   Definitions and structural lemmas for Invertible Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resR_resR
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_eq_of_locally
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_exists_glue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
namespace GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
@[ext]
structure DualSec (P : PMod X) (U : X.Opens) where

  app : ∀ (V : X.Opens), V ≤ U → P.obj (op V) →ₗ[ringOn X V] ringOn X V
  compat : ∀ (V W : X.Opens) (h : V ≤ U) (i : W ≤ V) (m : P.obj (op V)),
    app W (i.trans h) (resM P i m) = resR i (app V h m)
lemma resR_refl {V : X.Opens} (r : ringOn X V) : resR (le_refl V) r = r := by
  change ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 (op V))).hom r = r
  rw [CategoryTheory.Functor.map_id]
  rfl
namespace DualSec
variable {P : PMod X} {U : X.Opens}
instance : Zero (DualSec P U) := ⟨⟨fun _ _ => 0, fun _ _ _ _ _ => (map_zero _).symm⟩⟩
instance : Add (DualSec P U) := ⟨fun φ ψ => ⟨fun V h => φ.app V h + ψ.app V h,
  fun V W h i m => by simp only [LinearMap.add_apply]; rw [φ.compat, ψ.compat, map_add]⟩⟩
instance : Neg (DualSec P U) := ⟨fun φ => ⟨fun V h => -φ.app V h,
  fun V W h i m => by simp only [LinearMap.neg_apply]; rw [φ.compat, map_neg]⟩⟩
instance : Sub (DualSec P U) := ⟨fun φ ψ => ⟨fun V h => φ.app V h - ψ.app V h,
  fun V W h i m => by simp only [LinearMap.sub_apply]; rw [φ.compat, ψ.compat, map_sub]⟩⟩
instance : SMul ℕ (DualSec P U) := ⟨fun n φ => ⟨fun V h => n • φ.app V h,
  fun V W h i m => by simp only [LinearMap.smul_apply]; rw [φ.compat, map_nsmul]⟩⟩
instance : SMul ℤ (DualSec P U) := ⟨fun n φ => ⟨fun V h => n • φ.app V h,
  fun V W h i m => by simp only [LinearMap.smul_apply]; rw [φ.compat, map_zsmul]⟩⟩
@[simp] lemma zero_app' (V : X.Opens) (h : V ≤ U) : (0 : DualSec P U).app V h = 0 := rfl
@[simp] lemma add_app' (φ ψ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (φ + ψ).app V h = φ.app V h + ψ.app V h := rfl
@[simp] lemma neg_app' (φ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (-φ).app V h = -φ.app V h := rfl
@[simp] lemma sub_app' (φ ψ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (φ - ψ).app V h = φ.app V h - ψ.app V h := rfl
@[simp] lemma nsmul_app' (n : ℕ) (φ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (n • φ).app V h = n • φ.app V h := rfl
@[simp] lemma zsmul_app' (n : ℤ) (φ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (n • φ).app V h = n • φ.app V h := rfl
instance : AddCommGroup (DualSec P U) where
  add_assoc a b c := by ext V h m; simp [add_assoc]
  zero_add a := by ext V h m; simp
  add_zero a := by ext V h m; simp
  add_comm a b := by ext V h m; simp [add_comm]
  neg_add_cancel a := by ext V h m; simp
  sub_eq_add_neg a b := by ext V h m; simp [sub_eq_add_neg]
  nsmul n φ := n • φ
  zsmul n φ := n • φ
  nsmul_zero a := by ext V h m; simp
  nsmul_succ n a := by ext V h m; simp [add_smul]
  zsmul_zero' a := by ext V h m; simp
  zsmul_succ' n a := by ext V h m; simp [add_smul]
  zsmul_neg' n a := by ext V h m; simp [negSucc_zsmul, add_smul]
noncomputable instance : SMul (ringOn X U) (DualSec P U) := ⟨fun r φ => ⟨fun V h => resR h r • φ.app V h,
  fun V W h i m => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [φ.compat, map_mul, resR_resR]⟩⟩
@[simp] lemma smul_app' (r : ringOn X U) (φ : DualSec P U) (V : X.Opens) (h : V ≤ U) :
    (r • φ).app V h = resR h r • φ.app V h := rfl
lemma one_smul' (φ : DualSec P U) : (1 : ringOn X U) • φ = φ := by
  ext V h m; repeat rw [smul_app']
  simp
lemma mul_smul' (r s : ringOn X U) (φ : DualSec P U) : (r * s) • φ = r • s • φ := by
  ext V h m; repeat rw [smul_app']
  simp [mul_assoc]
lemma smul_zero' (r : ringOn X U) : r • (0 : DualSec P U) = 0 := by
  ext V h m; repeat rw [smul_app']
  simp
lemma smul_add' (r : ringOn X U) (φ ψ : DualSec P U) : r • (φ + ψ) = r • φ + r • ψ := by
  ext V h m; rw [add_app', smul_app', smul_app', smul_app']
  simp [mul_add]
lemma add_smul' (r s : ringOn X U) (φ : DualSec P U) : (r + s) • φ = r • φ + s • φ := by
  ext V h m; rw [add_app', smul_app', smul_app', smul_app']
  simp [add_mul]
lemma zero_smul' (φ : DualSec P U) : (0 : ringOn X U) • φ = 0 := by
  ext V h m; repeat rw [smul_app']
  simp
noncomputable instance : Module (ringOn X U) (DualSec P U) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_zero := smul_zero'
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul := zero_smul'
end DualSec
namespace DualSec
variable {P : PMod X}
def restr {U U' : X.Opens} (hU : U' ≤ U) (φ : DualSec P U) : DualSec P U' :=
  ⟨fun V h => φ.app V (h.trans hU), fun V W h i m => φ.compat V W (h.trans hU) i m⟩
@[simp] lemma restr_app {U U' : X.Opens} (hU : U' ≤ U) (φ : DualSec P U) (V : X.Opens)
    (h : V ≤ U') : (restr hU φ).app V h = φ.app V (h.trans hU) := rfl
lemma restr_smul {U U' : X.Opens} (hU : U' ≤ U) (r : ringOn X U) (φ : DualSec P U) :
    restr hU (r • φ) = resR hU r • restr hU φ := by
  ext V h m
  rw [smul_app', restr_app, restr_app, smul_app', resR_resR]
end DualSec
lemma resR_injective_of_le {V W : X.Opens} (h : W ≤ V) (h' : V ≤ W) :
    Function.Injective (resR h) := by
  intro a b e
  have := congrArg (resR h') e
  rw [resR_resR, resR_resR, resR_refl, resR_refl] at this
  exact this
variable (P : PMod X) in

noncomputable def dualAb : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of (DualSec P U.unop)
  map f := AddCommGrpCat.ofHom ⟨⟨DualSec.restr f.unop.le, rfl⟩, fun _ _ => rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl
noncomputable instance (P : PMod X) (U : (Opens X)ᵒᵖ) :
    Module ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) ((dualAb P).obj U) :=
  inferInstanceAs (Module (ringOn X U.unop) (DualSec P U.unop))
variable (P : PMod X) in

noncomputable def dualPre : PMod X :=
  PresheafOfModules.ofPresheaf (dualAb P) (fun _ _ f r φ => DualSec.restr_smul f.unop.le r φ)
namespace DualSec
variable {P : PMod X} {ι : Type u} {U : ι → X.Opens} (sf : ∀ i, DualSec P (U i))
noncomputable def glueLocal {V : X.Opens} (m : P.obj (op V)) (i : ι) : ringOn X (V ⊓ U i) :=
  (sf i).app (V ⊓ U i) inf_le_right (resM P inf_le_left m)
variable {sf}
variable (hsf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (m : P.obj (op V)),
  (sf i).app V hi m = (sf j).app V hj m)
include hsf
lemma glueLocal_compat {V : X.Opens} (m : P.obj (op V)) (i j : ι) :
    resR (inf_le_left : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U i) (glueLocal sf m i) =
      resR (inf_le_right : (V ⊓ U i) ⊓ (V ⊓ U j) ≤ V ⊓ U j) (glueLocal sf m j) := by
  rw [glueLocal, glueLocal, ← (sf i).compat, ← (sf j).compat, resM_resM, resM_resM]
  exact hsf i j _ _ _ _
lemma exists_glue {V : X.Opens} (hV : V ≤ iSup U) (m : P.obj (op V)) :
    ∃ r : ringOn X V, ∀ i, resR (inf_le_left : V ⊓ U i ≤ V) r = glueLocal sf m i := by
  obtain ⟨r, hr⟩ := sheaf_exists_glue X.sheaf (V := V) (fun i => V ⊓ U i) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hV hx)
      exact ⟨i, hx, hi⟩) (fun i => glueLocal sf m i) (fun i j => glueLocal_compat hsf m i j)
  exact ⟨r, hr⟩
omit hsf in
lemma glue_unique {V : X.Opens} (hV : V ≤ iSup U) (m : P.obj (op V)) (r s : ringOn X V)
    (hr : ∀ i, resR (inf_le_left : V ⊓ U i ≤ V) r = glueLocal sf m i)
    (hs : ∀ i, resR (inf_le_left : V ⊓ U i ≤ V) s = glueLocal sf m i) : r = s := by
  apply sheaf_eq_of_locally X.sheaf (V := V) r s
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hV hx)
  exact ⟨V ⊓ U i, inf_le_left, ⟨hx, hi⟩, (hr i).trans (hs i).symm⟩
noncomputable def glueFun {V : X.Opens} (hV : V ≤ iSup U) (m : P.obj (op V)) : ringOn X V :=
  Classical.choose (exists_glue hsf hV m)
lemma glueFun_spec {V : X.Opens} (hV : V ≤ iSup U) (m : P.obj (op V)) (i : ι) :
    resR (inf_le_left : V ⊓ U i ≤ V) (glueFun hsf hV m) = glueLocal sf m i :=
  Classical.choose_spec (exists_glue hsf hV m) i
noncomputable def glueLin {V : X.Opens} (hV : V ≤ iSup U) : P.obj (op V) →ₗ[ringOn X V] ringOn X V where
  toFun := glueFun hsf hV
  map_add' m m' := by
    refine glue_unique hV _ _ _ (glueFun_spec hsf hV _) (fun i => ?_)
    rw [map_add, glueFun_spec, glueFun_spec, glueLocal, glueLocal, glueLocal, resM_add, map_add]
  map_smul' r m := by
    refine glue_unique hV _ _ _ (glueFun_spec hsf hV _) (fun i => ?_)
    rw [RingHom.id_apply, smul_eq_mul, map_mul, glueFun_spec, glueLocal, glueLocal, resM_smul,
      map_smul, smul_eq_mul]
noncomputable def glue : DualSec P (iSup U) :=
  ⟨fun V hV => glueLin hsf hV, fun V W hV i m => by
    change glueFun hsf (i.trans hV) (resM P i m) = resR i (glueFun hsf hV m)
    refine glue_unique (i.trans hV) _ _ _ (glueFun_spec hsf _ _) (fun j => ?_)
    rw [resR_resR, ← resR_resR (inf_le_left : V ⊓ U j ≤ V) (inf_le_inf_right (U j) i), glueFun_spec,
      glueLocal, glueLocal, ← (sf j).compat, resM_resM, resM_resM]⟩
lemma glue_restr (i : ι) : restr (le_iSup U i) (glue hsf) = sf i := by
  ext V h m
  rw [restr_app]
  have hV : V ≤ V ⊓ U i := le_inf le_rfl h
  apply resR_injective_of_le (inf_le_left : V ⊓ U i ≤ V) hV
  change resR _ (glueFun hsf (h.trans (le_iSup U i)) m) = _
  rw [glueFun_spec, glueLocal, (sf i).compat]
omit hsf in
lemma eq_of_restr (hV : ∀ x, x ∈ iSup U → ∃ i, x ∈ U i) (φ ψ : DualSec P (iSup U))
    (h : ∀ i, restr (le_iSup U i) φ = restr (le_iSup U i) ψ) : φ = ψ := by
  ext V hVU m
  apply sheaf_eq_of_locally X.sheaf (V := V)
  intro x hx
  obtain ⟨i, hi⟩ := hV x (hVU hx)
  refine ⟨V ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change resR _ (φ.app V hVU m) = resR _ (ψ.app V hVU m)
  rw [← φ.compat, ← ψ.compat]
  have := congrArg (fun ξ => DualSec.app ξ (V ⊓ U i) inf_le_right (resM P inf_le_left m)) (h i)
  exact this
end DualSec
lemma dualAb_isSheaf (P : PMod X) : (dualAb P).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (m : P.obj (op V)),
      (sf i).app V hi m = (sf j).app V hj m := by
    intro i j V hi hj m
    exact congrArg (fun ξ : DualSec P (U i ⊓ U j) => ξ.app V (le_inf hi hj) m) (hsf i j)
  refine ⟨DualSec.glue hsf', fun i => DualSec.glue_restr hsf' i, fun φ hφ => ?_⟩
  apply DualSec.eq_of_restr (fun x hx => Opens.mem_iSup.1 hx)
  intro i
  rw [DualSec.glue_restr hsf' i]
  exact hφ i
noncomputable def dualSheaf (M : X.Modules) : X.Modules where
  val := dualPre ((preMod X).obj M)
  isSheaf := dualAb_isSheaf _
noncomputable def pairingLin (M : X.Modules) (U : X.Opens) :
    DualSec ((preMod X).obj M) U →ₗ[ringOn X U] ((preMod X).obj M).obj (op U) →ₗ[ringOn X U]
      ringOn X U :=
  LinearMap.mk₂ _ (fun φ m => φ.app U le_rfl m)
    (fun φ ψ m => rfl)
    (fun r φ m => by
      change (resR le_rfl r • φ.app U le_rfl) m = r * φ.app U le_rfl m
      rw [resR_refl]
      rfl)
    (fun φ m m' => map_add _ _ _)
    (fun r φ m => map_smul _ _ _)
noncomputable def evalPre (M : X.Modules) :
    (preMod X).obj (dualSheaf M) ⊗ (preMod X).obj M ⟶ (preMod X).obj (𝟙_ X.Modules) where
  app U := ModuleCat.ofHom (X := ((preMod X).obj (dualSheaf M) ⊗ (preMod X).obj M).obj U)
    (Y := ((preMod X).obj (𝟙_ X.Modules)).obj U) (by exact TensorProduct.lift (pairingLin M U.unop))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro φ m
    change (φ.app V.unop f.unop.le (resM _ f.unop.le m)) = resR f.unop.le (φ.app U.unop le_rfl m)
    rw [← φ.compat]
noncomputable def dualEval (M : X.Modules) : dualSheaf M ⊗ M ⟶ 𝟙_ X.Modules :=
  tensorLift (evalPre M)
namespace DualSec
variable {P : PMod X} {U : X.Opens} {s : P.obj (op U)}
noncomputable def coordEquiv (hs : IsBasisOn P U s) (V : X.Opens) (h : V ≤ U) :
    ringOn X V ≃ₗ[ringOn X V] P.obj (op V) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P h s)) (hs V h)
lemma coordEquiv_apply (hs : IsBasisOn P U s) (V : X.Opens) (h : V ≤ U) (r : ringOn X V) :
    coordEquiv hs V h r = r • resM P h s := rfl
noncomputable def dualBasis (hs : IsBasisOn P U s) : DualSec P U where
  app V h := (coordEquiv hs V h).symm.toLinearMap
  compat V W h i m := by
    apply (coordEquiv hs W (i.trans h)).injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [coordEquiv_apply]
    conv_lhs => rw [← (coordEquiv hs V h).apply_symm_apply m]
    rw [coordEquiv_apply, resM_smul, resM_resM]
end DualSec
noncomputable def dualIsoHom (M : X.Modules) : dualPre ((preMod X).obj M) ⟶ (preMod X).obj (dualSheaf M) where
  app U := ModuleCat.ofHom (X := (dualPre ((preMod X).obj M)).obj U)
    (Y := ((preMod X).obj (dualSheaf M)).obj U)
    { toFun := fun φ => φ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  naturality _ := rfl
noncomputable def dualIsoInv (M : X.Modules) : (preMod X).obj (dualSheaf M) ⟶ dualPre ((preMod X).obj M) where
  app U := ModuleCat.ofHom (X := ((preMod X).obj (dualSheaf M)).obj U)
    (Y := (dualPre ((preMod X).obj M)).obj U)
    { toFun := fun φ => φ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  naturality _ := rfl
instance (M : X.Modules) : IsIso (dualIsoHom M) :=
  ⟨dualIsoInv M, rfl, rfl⟩
end GroundTheory.Arith.SchemeCoh


