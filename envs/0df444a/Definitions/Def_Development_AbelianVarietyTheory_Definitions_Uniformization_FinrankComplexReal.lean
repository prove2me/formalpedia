-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:45:51.523819+00:00
-- url     : https://prove2.me/theorems/14f98636-3dc1-48ad-9213-af1863b155b7
-- title:
--   Finrank Complex Real
-- statement:
--   Definitions and structural lemmas for Finrank Complex Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/FinrankComplexReal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.UU
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}
@[simp] theorem sec_mk (s : LB.Sec N) : (mk p s).sec = s := rfl
@[simp] theorem mk_sec (s : SecMod p N) : mk p s.sec = s := rfl
@[simp] theorem add_f (s t : SecMod p N) (j : N.ι) : (s + t).sec.f j = s.sec.f j + t.sec.f j := rfl
@[simp] theorem neg_f (s : SecMod p N) (j : N.ι) : (-s).sec.f j = - s.sec.f j := rfl
@[simp] theorem smul_f (c : F) (s : SecMod p N) (j : N.ι) :
    (c • s).sec.f j = resTop _ (scal p c) * s.sec.f j := rfl
@[simp] theorem zero_f (j : N.ι) : (0 : SecMod p N).sec.f j = 0 := rfl
@[ext] theorem ext {s t : SecMod p N} (h : ∀ j, s.sec.f j = t.sec.f j) : s = t :=
  DVR.SecOps.sec_ext h
@[simp] theorem sub_f (s t : SecMod p N) (j : N.ι) : (s - t).sec.f j = s.sec.f j - t.sec.f j := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_f, neg_f]
section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ
end Val
theorem resTop_top (c : Γ(Y, ⊤)) : resTop ⊤ c = c := by
  show (Y.presheaf.map (𝟙 _)).hom c = c
  rw [CategoryTheory.Functor.map_id]; rfl
variable (p) in

def ofFun (a : Γ(Y, ⊤)) : SecMod p (Inh.trivLB Y) :=
  mk p ⟨fun _ => a, fun _ _ => by erw [Units.val_one, _root_.one_mul]; rfl⟩
@[simp] theorem ofFun_f (a : Γ(Y, ⊤)) (j) : (ofFun p a).sec.f j = a := rfl
theorem smul_ofFun (c : F) (a : Γ(Y, ⊤)) : c • ofFun p a = ofFun p (scal p c * a) :=
  ext fun _ => congrArg (· * a) (resTop_top (scal p c))
theorem ofFun_injective : Function.Injective (ofFun p) :=
  fun _ _ h => congrArg (fun s : SecMod p (Inh.trivLB Y) => s.sec.f PUnit.unit) h
theorem ofFun_surjective : Function.Surjective (ofFun p) :=
  fun s => ⟨s.sec.f PUnit.unit, ext fun _ => rfl⟩
theorem scal_specMap {A : Type} [CommRing A] (f : F →+* A) (c : F) :
    scal (Spec.map (CommRingCat.ofHom f)) c = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (f c) := by
  have := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact this.symm
def trivEquiv (F A : Type) [CommRing F] [CommRing A] [Algebra F A] :
    A ≃ₗ[F] SecMod (Spec.map (CommRingCat.ofHom (algebraMap F A))) (Inh.trivLB (Spec (CommRingCat.of A))) :=
  LinearEquiv.ofBijective
    { toFun := fun a => ofFun _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
      map_add' := fun a b => ext fun _ => map_add _ a b
      map_smul' := fun c a => by
        rw [RingHom.id_apply, smul_ofFun, scal_specMap, ← map_mul, Algebra.smul_def] }
    (Function.Bijective.comp (g := ofFun (Spec.map (CommRingCat.ofHom (algebraMap F A))))
      (f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) ⟨ofFun_injective, ofFun_surjective⟩
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.bijective)
end SecMod
end GlobalTheory.UU
end


