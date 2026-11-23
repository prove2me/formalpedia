-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:55.597667+00:00
-- url     : https://prove2.me/theorems/a211e01a-5840-4ae2-bd9e-cd8bcc72f27c
-- title:
--   Is Extension Pull Over
-- statement:
--   Definitions and structural lemmas for Is Extension Pull Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionPullOver.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Fn
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
def constHom (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : R →+* Γ(Y, U) :=
  ((Y.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
def constVal (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (c : R) : Z.presheaf.stalk z :=
  gs π z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
theorem gs_scal (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal π c) = constVal (r ≫ π) z c := gs_pull r π z ⊤ trivial _
theorem gs_const (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (resTop U (scal π c)) = constVal (r ≫ π) z c :=
  (gs_res r z le_top h _).trans (gs_scal π r z c)
theorem constVal_specMap (π : Z ⟶ Spec (CommRingCat.of R')) (φ : R →+* R') (z : Z) (c : R) :
    constVal (π ≫ Spec.map (CommRingCat.ofHom φ)) z c = constVal π z (φ c) := by
  refine (gs_pull π (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial _).symm.trans (congrArg (gs π z ⊤) ?_)
  have := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm
def FnOver (_π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : Type := Γ(Y, U)
instance (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : CommRing (FnOver π U) :=
  inferInstanceAs (CommRing Γ(Y, U))
instance (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : Algebra R (FnOver π U) :=
  (constHom π U).toAlgebra
theorem gs_smul (π : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (c : R)
    (a : FnOver π U) : gs r z U (c • a : FnOver π U) = constVal (r ≫ π) z c * gs r z U a :=
  (gs_mul r z U h _ _).trans (congrArg (· * _) (gs_const π r z U h c))
def pullFn {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')} {φ : R →+* R'}
    {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom φ)) {U : Y.Opens} {U' : Y'.Opens}
    (h : U' ≤ p ⁻¹ᵁ U) : FnOver π U →ₛₗ[φ] FnOver π' U' where
  toFun a := (Y'.presheaf.map (homOfLE h).op).hom ((p.app U).hom a)
  map_add' a b := by erw [map_add, map_add]; rfl
  map_smul' c a := fn_ext fun y hy => by
    have v : ∀ b : Γ(Y, U), gs (𝟙 Y') y U' ((Y'.presheaf.map (homOfLE h).op).hom ((p.app U).hom b)) =
        gs p y U b := fun b => (gs_res _ y h hy _).trans ((gs_pull _ p y U (h hy) b).trans (by rw [Category.id_comp]))
    refine (v _).trans ((gs_smul π p y U (h hy) c a).trans (Eq.trans ?_ (gs_smul π' _ y U' hy _ _).symm))
    rw [hp, constVal_specMap, Category.id_comp]
    exact congrArg _ (v a).symm
theorem gs_pullFn {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')} {φ : R →+* R'}
    {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom φ)) {U : Y.Opens} {U' : Y'.Opens}
    (h : U' ≤ p ⁻¹ᵁ U) (a : FnOver π U) (r : Z ⟶ Y') (z : Z) (hz : r z ∈ U') :
    gs r z U' (pullFn hp h a) = gs (r ≫ p) z U a :=
  (gs_res r z h hz _).trans (gs_pull r p z U (h hz) a)
def resFn (π : Y ⟶ Spec (CommRingCat.of R)) {U V : Y.Opens} (h : V ≤ U) : FnOver π U →ₗ[R] FnOver π V where
  toFun a := (Y.presheaf.map (homOfLE h).op).hom a
  map_add' a b := map_add _ _ _
  map_smul' c a := fn_ext fun y hy =>
    (gs_res _ y h hy _).trans ((gs_smul π _ y U (h hy) c a).trans
      (Eq.trans (congrArg _ (gs_res _ y h hy _).symm) (gs_smul π _ y V hy _ _).symm))
end Fn
section Sec
variable {R R' : Type} [CommRing R] [CommRing R'] {X Y Y' Z : Scheme.{0}}
def SecOver (_π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) : Type := LB.Sec M
variable (π : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
instance : Zero (SecOver π M) := ⟨SecOps.secZero⟩
instance : Add (SecOver π M) := ⟨SecOps.secAdd⟩
instance : Neg (SecOver π M) := ⟨SecOps.secNeg⟩
instance : SMul R (SecOver π M) := ⟨fun c => SecOps.secScale (scal π c)⟩
def chartFun (j : M.ι) (s : SecOver π M) : FnOver π (M.U j) := LB.Sec.f s j
theorem SecOver.ext {s t : SecOver π M} (h : ∀ j, chartFun π M j s = chartFun π M j t) : s = t :=
  SecOps.sec_ext h
instance : AddCommGroup (SecOver π M) where
  add_assoc a b c := SecOver.ext π M fun j => add_assoc (chartFun π M j a) _ _
  zero_add a := SecOver.ext π M fun j => zero_add (chartFun π M j a)
  add_zero a := SecOver.ext π M fun j => add_zero (chartFun π M j a)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := SecOver.ext π M fun j => neg_add_cancel (chartFun π M j a)
  add_comm a b := SecOver.ext π M fun j => add_comm (chartFun π M j a) _
instance : Module R (SecOver π M) where
  one_smul a := SecOver.ext π M fun j => one_smul R (chartFun π M j a)
  mul_smul x y a := SecOver.ext π M fun j => mul_smul x y (chartFun π M j a)
  smul_zero x := SecOver.ext π M fun j => smul_zero (A := FnOver π (M.U j)) x
  smul_add x a b := SecOver.ext π M fun j => smul_add x (chartFun π M j a) _
  add_smul x y a := SecOver.ext π M fun j => add_smul x y (chartFun π M j a)
  zero_smul a := SecOver.ext π M fun j => zero_smul R (chartFun π M j a)
def chartLin (j : M.ι) : SecOver π M →ₗ[R] FnOver π (M.U j) where
  toFun := chartFun π M j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {π} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
section Val
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ
end Val
theorem mem_wchart {j : K → L.ι} {y : Y} : y ∈ LB.wchart L φ j ↔ ∀ k, φ k y ∈ L.U (j k) :=
  Set.mem_iInter
theorem wchart_eq {φ' : K → (Y' ⟶ X)} {p : Y' ⟶ Y} (hφ : ∀ k, φ' k = p ≫ φ k) (j : K → L.ι) :
    LB.wchart L φ' j = p ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : φ' = fun k => p ≫ φ k := funext hφ
  ext y
  exact (mem_wchart (φ := fun k => p ≫ φ k)).trans (mem_wchart (φ := φ) (y := p y)).symm
theorem trF_comp {φ' : K → (Y' ⟶ X)} {p : Y' ⟶ Y} (hφ : ∀ k, φ' k = p ≫ φ k) (r : Z ⟶ Y') (z : Z)
    (j j' : K → L.ι) : Geo.Tor.trF φ' ε r z j j' = Geo.Tor.trF φ ε (r ≫ p) z j j' :=
  Finset.prod_congr rfl fun k _ => by rw [hφ, Category.assoc]
variable {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'} {p : Y' ⟶ Y}
  (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)} (hφ : ∀ k, φ' k = p ≫ φ k)
variable (L ε) in

def pullOver : SecOver π (LB.LinComb L φ ε) →ₛₗ[f] SecOver π' (LB.LinComb L φ' ε) where
  toFun s :=
    { f := fun j => pullFn hp (wchart_eq hφ j).le (chartFun π (LB.LinComb L φ ε) j s)
      compat := fun j j' => fn_ext fun y hy => by
        refine ((gs_res _ y _ hy _).trans (gs_pullFn hp _ _ _ y hy.1)).trans (Eq.trans ?_
          ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
            (congrArg Units.val (gm_linComb L φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
            ((gs_res _ y _ hy _).trans (gs_pullFn hp _ _ _ y hy.2)))).symm)
        exact (sec_trans s (𝟙 Y' ≫ p) y ((wchart_eq hφ j).le hy.1) ((wchart_eq hφ j').le hy.2)).trans
          (congrArg (fun u : (Y'.presheaf.stalk y)ˣ => u.val * _) (trF_comp hφ _ y j j').symm) }
  map_add' s t := SecOver.ext _ _ fun j => map_add (pullFn hp (wchart_eq hφ j).le) _ _
  map_smul' c s := SecOver.ext _ _ fun j => map_smulₛₗ (pullFn hp (wchart_eq hφ j).le) _ _
end Sec
section Field
variable {K F : Type} [Field K] [Field F] [Algebra K F] {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F)))) [NoetherianSpace Y]
variable {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} (ε : I → ℤ) {φ' : I → (Y' ⟶ X)}
  (hφ : ∀ k, φ' k = p ≫ φ k)
end Field
end GlobalTheory.FieldBaseChange


