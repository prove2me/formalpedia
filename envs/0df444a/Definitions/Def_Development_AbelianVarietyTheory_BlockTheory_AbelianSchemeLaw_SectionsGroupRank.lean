-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SectionsGroupRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:49.929528+00:00
-- url     : https://prove2.me/theorems/2bba6e49-fbae-49c2-874f-7ca1256a50ec
-- title:
--   Sections Group Rank
-- statement:
--   Definitions and structural lemmas for Sections Group Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/SectionsGroupRank.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Cech
variable {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
theorem map_ev (f : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : V' ≤ V)
    (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE i).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (i.trans e)).hom x :=
  congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, V') => φ.hom x) (f.appLE_map e (homOfLE i).op)
theorem ev_map (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (i : U ≤ U')
    (e' : V ≤ f ⁻¹ᵁ U') (x : Γ(X, U')) :
    (f.appLE U V e).hom ((X.presheaf.map (homOfLE i).op).hom x) = (f.appLE U' V e').hom x :=
  congrArg (fun φ : Γ(X, U') ⟶ Γ(Y, V) => φ.hom x) (f.map_appLE e (homOfLE i).op)
theorem ev_ev (f : Z ⟶ Y) (g : Y ⟶ X) (k : Z ⟶ X) (hk : f ≫ g = k) {U : X.Opens} {V : Y.Opens}
    {W : Z.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ k ⁻¹ᵁ U) (x : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (k.appLE U W e₃).hom x := by
  subst hk
  exact congrArg (fun φ : Γ(X, U) ⟶ Γ(Z, W) => φ.hom x)
    (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)
theorem transition_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X))
    (hφ : ∀ k, h ≫ φ k = φ' k) (j j' : K → L.ι)
    (e : LB.wchart L φ' j ⊓ LB.wchart L φ' j' ≤ h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    (h.appLE _ _ e).hom
      (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j') from ((LB.LinComb L φ ε).g j j').val) =
      (show Γ(Z, LB.wchart L φ' j ⊓ LB.wchart L φ' j') from ((LB.LinComb L φ' ε).g j j').val) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext fun k => (hφ k).symm
  have key : Units.map (h.appLE _ _ e).hom.toMonoidHom ((LB.LinComb L φ ε).g j j') =
      (LB.LinComb L (fun k => h ≫ φ k) ε).g j j' := by
    simp only [LB.LinComb, map_prod, map_zpow]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    ext
    exact ev_ev h (φ k) _ rfl (U := L.U (j k) ⊓ L.U (j' k))
      (le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k)))
      e (le_inf (inf_le_left.trans (LB.wchart_le L (fun k => h ≫ φ k) j k))
        (inf_le_right.trans (LB.wchart_le L (fun k => h ≫ φ k) j' k))) (L.g (j k) (j' k)).val
  exact congrArg Units.val key
end Cech
section Sections
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
def Secs (L : LB A.left) (a : ℤ) (T : Over S) : Type := LB.Sec (LPow A L a T)
variable {A} {L : LB A.left} {a : ℤ} {T : Over S}
theorem Secs.ext {s t : Secs A L a T} (h : ∀ j, LB.Sec.f s j = LB.Sec.f t j) : s = t := by
  cases s; cases t; congr; exact funext h
theorem liftFun_eq {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) :
    liftFun A W r = ((fst T A).left.appLE ⊤ W le_top).hom r := rfl
theorem map_liftFun {W W' : (T ⊗ A).left.Opens} (e : W' ≤ W) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE e).op).hom (liftFun A W r) = liftFun A W' r :=
  map_ev (fst T A).left le_top e r
instance : Zero (Secs A L a T) := ⟨⟨fun _ => 0, fun _ _ => by simp⟩⟩
instance : Add (Secs A L a T) :=
  ⟨fun s t => ⟨fun j => s.f j + t.f j, fun i j => by
    rw [map_add, map_add, s.compat i j, t.compat i j, mul_add]⟩⟩
instance : Neg (Secs A L a T) :=
  ⟨fun s => ⟨fun j => - s.f j, fun i j => by rw [map_neg, map_neg, s.compat i j, mul_neg]⟩⟩
instance : SMul Γ(T.left, ⊤) (Secs A L a T) :=
  ⟨fun r s => ⟨fun j => liftFun A _ r * s.f j, fun i j => by
    rw [map_mul, map_mul, map_liftFun, map_liftFun, s.compat i j, mul_left_comm]⟩⟩
theorem zero_f (j) : LB.Sec.f (0 : Secs A L a T) j = 0 := rfl
theorem add_f (s t : Secs A L a T) (j) : LB.Sec.f (s + t) j = LB.Sec.f s j + LB.Sec.f t j := rfl
theorem smul_f (r : Γ(T.left, ⊤)) (s : Secs A L a T) (j) :
    LB.Sec.f (r • s) j = liftFun A _ r * LB.Sec.f s j := rfl
instance : AddCommGroup (Secs A L a T) where
  add_assoc s t u := Secs.ext fun j => add_assoc _ _ _
  zero_add s := Secs.ext fun j => zero_add _
  add_zero s := Secs.ext fun j => add_zero _
  add_comm s t := Secs.ext fun j => add_comm _ _
  neg_add_cancel s := Secs.ext fun j => neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec
instance : Module Γ(T.left, ⊤) (Secs A L a T) where
  one_smul s := Secs.ext fun j => by rw [smul_f, liftFun_eq, map_one, _root_.one_mul]
  mul_smul r r' s := Secs.ext fun j => by
    rw [smul_f, smul_f, smul_f, liftFun_eq, liftFun_eq, liftFun_eq, map_mul, _root_.mul_assoc]
  smul_zero r := Secs.ext fun j => mul_zero _
  smul_add r s t := Secs.ext fun j => mul_add _ _ _
  add_smul r r' s := Secs.ext fun j => by
    rw [add_f, smul_f, smul_f, smul_f, liftFun_eq, liftFun_eq, liftFun_eq, map_add, add_mul]
  zero_smul s := Secs.ext fun j => by rw [smul_f, liftFun_eq, map_zero, zero_mul, zero_f]
theorem appLE_liftFun {T' : Over S} (H : T' ⊗ A ⟶ T ⊗ A) (u : T' ⟶ T)
    (hH : H ≫ fst T A = fst T' A ≫ u) (W : (T ⊗ A).left.Opens) (W' : (T' ⊗ A).left.Opens)
    (e : W' ≤ H.left ⁻¹ᵁ W) (r : Γ(T.left, ⊤)) :
    (H.left.appLE W W' e).hom (liftFun A W r) = liftFun A W' (u.left.appTop.hom r) := by
  have hl : H.left ≫ (fst T A).left = (fst T' A).left ≫ u.left := by
    rw [← Over.comp_left, hH, Over.comp_left]
  have h2 : u.left.appTop.hom r = (u.left.appLE ⊤ ⊤ le_top).hom r :=
    congrArg (fun φ : Γ(T.left, ⊤) ⟶ Γ(T'.left, ⊤) => φ.hom r) (u.left.app_eq_appLE (U := ⊤))
  rw [h2]
  exact (ev_ev H.left (fst T A).left _ hl le_top e le_top r).trans
    (ev_ev (fst T' A).left u.left _ rfl (U := ⊤) (V := ⊤) (W := W') le_top le_top le_top r).symm
def pullSec {T' : Over S} (u : T' ⟶ T) (s : Secs A L a T) : Secs A L a T' where
  f j := ((u ▷ A).left.appLE _ _ (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a j)).hom (s.f j)
  compat i j := by
    have e : (LPow A L a T').U i ⊓ (LPow A L a T').U j ≤
        (u ▷ A).left ⁻¹ᵁ ((LPow A L a T).U i ⊓ (LPow A L a T).U j) :=
      inf_le_inf (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a i)
        (chart_le_res A L (u ▷ A) (whiskerRight_snd _ _) a j)
    have h := congrArg ((u ▷ A).left.appLE _ _ e).hom (s.compat i j)
    rw [map_mul] at h
    have hg := transition_pull L (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (u ▷ A).left
      (fun _ => (snd T' A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd]) i j e
    refine (map_ev _ _ _ _).trans ((ev_map _ e _ _ _).symm.trans (h.trans ?_))
    exact congrArg₂ (· * ·) hg ((ev_map _ e _ _ _).trans (map_ev _ _ _ _).symm)
theorem pullSec_zero {T' : Over S} (u : T' ⟶ T) : pullSec u (0 : Secs A L a T) = 0 :=
  Secs.ext fun _ => map_zero _
theorem pullSec_add {T' : Over S} (u : T' ⟶ T) (s t : Secs A L a T) :
    pullSec u (s + t) = pullSec u s + pullSec u t :=
  Secs.ext fun _ => map_add _ _ _
theorem pullSec_smul {T' : Over S} (u : T' ⟶ T) (r : Γ(T.left, ⊤)) (s : Secs A L a T) :
    pullSec u (r • s) = u.left.appTop.hom r • pullSec u s :=
  Secs.ext fun j => by
    refine (map_mul _ _ _).trans ?_
    rw [appLE_liftFun (u ▷ A) u (whiskerRight_fst _ _)]
    rfl
theorem twist_comb {R R' C : Type} [CommRing R] [CommRing R'] [CommRing C] (F : R →+* C)
    (G : R' →+* C) (c : C) {x' y' r' : R} {x y r : R'} (hx : F x' = c * G x) (hy : F y' = c * G y)
    (hr : F r' = G r) :
    F 0 = c * G 0 ∧ F (x' + y') = c * G (x + y) ∧ F (r' * x') = c * G (r * x) := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [map_add, map_add, hx, hy, mul_add]
  · rw [map_mul, map_mul, hx, hr, mul_left_comm]
theorem isActOf_comb (θ : ThetaGrp A L a T) {s t s' t' : Secs A L a T} (hs : IsActOf A L a θ s s')
    (ht : IsActOf A L a θ t t') (r : Γ(T.left, ⊤)) :
    IsActOf A L a θ (s + t) (s' + t') ∧ IsActOf A L a θ (r • s) (r • s') := by
  have key := fun j : Fin 2 → L.ι => twist_comb
    ((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L (translPt A θ.pt) j)).op).hom
    ((translT A θ.pt).left.appLE _ _
      (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j)).hom
    _ (r' := liftFun A _ r) (r := liftFun A _ r) (hs j) (ht j) (by
      have h := appLE_liftFun (translT A θ.pt) (𝟙 T) (by simp [translT]) _ _
        (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j) r
      have hr : (𝟙 T : T ⟶ T).left.appTop.hom r = r := by simp
      rw [hr] at h
      exact (map_liftFun _ r).trans h.symm)
  exact ⟨fun j => (key j).2.1, fun j => (key j).2.2⟩
theorem isActOf_zero (θ : ThetaGrp A L a T) :
    IsActOf A L a θ (0 : Secs A L a T) (0 : Secs A L a T) := fun j =>
  (map_zero ((T ⊗ A).left.presheaf.map
    (homOfLE (chart_le_zero A L (translPt A θ.pt) j)).op).hom).trans
    ((mul_zero _).symm.trans (congrArg (_ * ·) (map_zero ((translT A θ.pt).left.appLE _ _
      (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j)).hom).symm))
end Sections
variable {S : Scheme.{0}}
def VV (P : PolAV S) (N m : ℕ) (T : Over S) : Submodule Γ(T.left, ⊤) (Secs P.A P.L N T) :=
  Submodule.span Γ(T.left, ⊤) {s | InVV P N m s}
def eigenSecs (P : PolAV S) (N : ℕ) {T : Over S} {I : Type} (h : I → (T ⟶ P.A))
    (χ : I → Γ(T.left, ⊤)ˣ) : Submodule Γ(T.left, ⊤) (Secs P.A P.L N T) where
  carrier := {s | ∀ (V : T.left.Opens) (i : I) (U : ThetaGrp P.A P.L N (overRes V)),
    SymLift P.A P.L N N (overResι V ≫ h i) U →
      IsActOf P.A P.L N U (pullSec (overResι V) s)
        ((unitRes V (χ i) : Γ((overRes V).left, ⊤)) • pullSec (overResι V) s)}
  zero_mem' := fun V i U _ => by
    rw [pullSec_zero, smul_zero]; exact isActOf_zero U
  add_mem' := fun {s t} hs ht V i U hU => by
    rw [pullSec_add, smul_add]; exact (isActOf_comb U (hs V i U hU) (ht V i U hU) 0).1
  smul_mem' := fun r s hs V i U hU => by
    rw [pullSec_smul, smul_comm]; exact (isActOf_comb U (hs V i U hU) (hs V i U hU) _).2
def VVWeight (P : PolAV S) (N m : ℕ) {T : Over S} (_hodd : Odd N)
    (_hinv : IsUnit (N : Γ(T.left, ⊤))) {I : Type} (h : I → (T ⟶ P.A)) (_hh : ∀ i, h i ^ N = 1)
    (χ : I → Γ(T.left, ⊤)ˣ) : Submodule Γ(T.left, ⊤) (Secs P.A P.L N T) :=
  VV P N m T ⊓ eigenSecs P N h χ
abbrev de (P : PolAV S) (T : Over S) : Type := Module.Dual Γ(T.left, ⊤) (Secs P.A P.L 1 T)
def VVLocallyFree (P : PolAV S) (N m n : ℕ) (T : Over S) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ b : Fin n → Secs P.A P.L N (overRes V),
    ∀ W : (overRes V).left.Opens,
      ∃ β : Module.Basis (Fin n) Γ((overRes W).left, ⊤) (VV P N m (overRes W)),
        ∀ l, (β l : Secs P.A P.L N (overRes W)) = pullSec (overResι W) (b l)
def VVRank (S : Scheme.{0}) : Prop :=
  ∀ (P : PolAV S) (m : ℕ) (ze : Γ(S, ⊤)ˣ), Odd m → IsUnit (m : Γ(S, ⊤)) →
    Nonempty (Level P (m ^ 2) ze) →
    ∀ T : Over S, VVLocallyFree P (m ^ 2) m ((m ^ 2) ^ P.g) T
example (P : PolAV S) (N m : ℕ) {T : Over S} (ho : Odd N) (hi : IsUnit (N : Γ(T.left, ⊤))) :
    VVWeight P N m ho hi (I := Empty) Empty.elim (fun i => i.elim) Empty.elim = VV P N m T :=
  inf_eq_left.2 fun _ _ _ i => i.elim
example (P : PolAV S) (N m : ℕ) {T : Over S} (s : Secs P.A P.L N T) (hs : InVV P N m s) :
    s ∈ VV P N m T := Submodule.subset_span hs
end GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank


