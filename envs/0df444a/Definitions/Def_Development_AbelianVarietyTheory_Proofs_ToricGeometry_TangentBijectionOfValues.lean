-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:46.053657+00:00
-- url     : https://prove2.me/theorems/6ed988c2-2ffe-4cbd-b63c-f72a8cd12821
-- title:
--   Tangent Bijection Of Values
-- statement:
--   Definitions and structural lemmas for Tangent Bijection Of Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.TangentOrigin
section Points
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
def evalPt (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
theorem evalPt_spMap_comp (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evalPt (spMap φ ≫ x) U h' f = φ (evalPt x U h f) := by
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold evalPt
  rw [e1, Category.assoc, e2]
  rfl
theorem evalPt_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    evalPt x U h (constFn p U a) = evalPt (x ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  have := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  unfold evalPt constFn
  rw [← this]
  rfl
theorem evalPt_spMap (φ : R →+* R') (a : R) :
    evalPt (spMap φ) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = φ a := by
  have := evalPt_spMap_comp φ (𝟙 (Sp R)) ⊤ le_rfl le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  simp only [Category.comp_id] at this
  rw [this]
  congr 1
  have e : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  unfold evalPt
  rw [e, Category.id_comp]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a
theorem valAt'_eq_evalPt (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = evalPt x U h f := by
  unfold valAt'
  rw [dif_pos h]
  rfl
abbrev fstC : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
end Points
section Jets
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
theorem ex_left_comp (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ) := Over.w (u.ex z)
theorem eventually_mem {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) :
    ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ W :=
  (u.hol W 0).1.mem_nhds h
theorem differentiableAt_val {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    DifferentiableAt ℂ (fun z => valAt' (u.ex z).left W f) 0 :=
  (u.hol W f).2.differentiableAt (eventually_mem u h)
theorem fderiv_val_const {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (a : ℂ) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (constFn A.hom W a)) 0 = 0 := by
  have : (fun z => valAt' (u.ex z).left W (constFn A.hom W a)) =ᶠ[𝓝 0] fun _ => a := by
    filter_upwards [eventually_mem u h] with z hz
    rw [valAt'_eq_evalPt _ _ hz, evalPt_constFn]
    have e : (u.ex z).left ≫ A.hom = spMap (RingHom.id ℂ) :=
      (ex_left_comp u z).trans (Spec.map_id _).symm
    exact (congrArg (fun y : Sp ℂ ⟶ Sp ℂ => evalPt y ⊤ le_rfl
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (evalPt_spMap _ a)
  rw [this.fderiv_eq]
  simp
theorem fderiv_val_add {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f f' : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (f + f')) 0 =
      fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 +
        fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 := by
  have : (fun z => valAt' (u.ex z).left W (f + f')) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left W f + valAt' (u.ex z).left W f' := by
    filter_upwards [eventually_mem u h] with z hz
    simp only [valAt'_eq_evalPt _ _ hz, map_add]
  rw [this.fderiv_eq, fderiv_fun_add (differentiableAt_val u h f) (differentiableAt_val u h f')]
theorem fderiv_val_mul {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f f' : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (f * f')) 0 =
      valAt' (u.ex 0).left W f • fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 +
        valAt' (u.ex 0).left W f' • fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 := by
  have : (fun z => valAt' (u.ex z).left W (f * f')) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left W f * valAt' (u.ex z).left W f' := by
    filter_upwards [eventually_mem u h] with z hz
    simp only [valAt'_eq_evalPt _ _ hz, map_mul]
  rw [this.fderiv_eq, fderiv_fun_mul (differentiableAt_val u h f) (differentiableAt_val u h f')]
def jet (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) :
    Γ(A.left, W) →+* DualNumber ℂ where
  toFun f := (evalPt (u.ex 0).left W h f, fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
  map_one' := by
    refine TrivSqZeroExt.ext (map_one (evalPt (u.ex 0).left W h)) ?_
    have := fderiv_val_const u h 1
    rw [show constFn A.hom W 1 = 1 by simp [constFn]] at this
    change fderiv ℂ (fun z => valAt' (u.ex z).left W 1) 0 w = 0
    rw [this]
    rfl
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero (evalPt (u.ex 0).left W h)) ?_
    have := fderiv_val_const u h 0
    rw [show constFn A.hom W 0 = 0 by simp [constFn]] at this
    change fderiv ℂ (fun z => valAt' (u.ex z).left W 0) 0 w = 0
    rw [this]
    rfl
  map_add' f f' := by
    refine TrivSqZeroExt.ext (map_add (evalPt (u.ex 0).left W h) f f') ?_
    change fderiv ℂ (fun z => valAt' (u.ex z).left W (f + f')) 0 w = _
    rw [fderiv_val_add u h]
    rfl
  map_mul' f f' := by
    refine TrivSqZeroExt.ext (map_mul (evalPt (u.ex 0).left W h) f f') ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change fderiv ℂ (fun z => valAt' (u.ex z).left W (f * f')) 0 w =
      evalPt (u.ex 0).left W h f * fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 w +
        fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w * evalPt (u.ex 0).left W h f'
    rw [fderiv_val_mul u h, valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt _ _ h,
      mul_comm (fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)]
    rfl
variable {u}
end Jets
end GlobalTheory.TangentOrigin


