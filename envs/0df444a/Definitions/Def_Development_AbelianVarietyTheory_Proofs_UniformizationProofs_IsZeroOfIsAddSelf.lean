-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsZeroOfIsAddSelf
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsZeroOfIsAddSelf
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:29.236096+00:00
-- url     : https://prove2.me/theorems/6b33e9d2-eedc-44f7-9899-40b4505d5b15
-- title:
--   Is Zero Of Is Add Self
-- statement:
--   Definitions and structural lemmas for Is Zero Of Is Add Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsZeroOfIsAddSelf.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_TorusPointForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isIota_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cubAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GtPointsCompare
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
section Cast
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
def castGen (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) := h ▸ t
theorem castGen_isGen (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (castGen h t).IsGen := by
  subst h; exact ht
theorem castGen_castGen (h : φ = φ') (h' : φ' = φ) (t : LB.Gen (LB.LinComb L φ ε)) :
    castGen h' (castGen h t) = t := by
  subst h; rfl
theorem corr_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) (u : LB.Gen (LB.LinComb L ψ δ)) :
    LB.Gen.Corr L _ _ _ _ (castGen h t) u ↔ LB.Gen.Corr L _ _ _ _ t u := by
  subst h; rfl
theorem corr_mul_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ}
    {φ₁ φ₁' φ₂ φ₂' : K → (Y ⟶ X)} (h : φ = φ') (h₁ : φ₁ = φ₁') (h₂ : φ₂ = φ₂')
    (t : LB.Gen (LB.LinComb L φ ε)) (c : LB.Gen (LB.LinComb L ψ δ))
    (t₁ : LB.Gen (LB.LinComb L φ₁ ε)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (castGen h t) c)
        (LB.mulGen L _ _ _ _ (castGen h₁ t₁) (castGen h₂ t₂)) ↔
      LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t c) (LB.mulGen L _ _ _ _ t₁ t₂) := by
  subst h h₁ h₂; rfl
end Cast
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
theorem oφ_eq (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : oφ D b χ = DegPre.gtφ D F b χ := by
  have : padd D.P.A b (cPt D _ χ) = padd D.P.A (DegPre.cF D F χ) b := mul_comm b (cPt D _ χ)
  unfold oφ DegPre.gtφ
  rw [this]; rfl
theorem corr_one_of_mult (b : TF (R := R) F ⟶ D.P.A)
    (s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b 0) DegPre.gtε))
    (s' : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b (0 + 0)) DegPre.gtε)) (hs : HEq s' s)
    (m : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ s' (DegPre.cubAt D F (DegPre.cF D F 0) (DegPre.cF D F 0) b))
      (LB.mulGen D.P.L _ _ _ _ s s)) :
    LB.Gen.Corr D.P.L _ _ _ _ s (LB.oneGen D.P.L) := by
  revert s'
  rw [add_zero (0 : D.X)]
  intro s' hs m
  obtain rfl := eq_of_heq hs
  refine corr_of_val D.P.isLB fun y J hJ => Eq.trans ?_ (val_one _).symm
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
      ((val_corr hJ m _).trans (val_mul hJ _ _ _))
  have z : DegPre.cF D F 0 = 1 := cPoint_zero _
  rw [z, C.face] at e
  exact (mul_left_cancel e).symm
def ptEquiv : GtPt D F ≃ GtPtF D F where
  toFun g :=
    { b := g.base
      s := fun χ => castGen (oφ_eq D F g.base χ) (g.form χ)
      isGen := fun χ => castGen_isGen _ (g.form_gen χ)
      s_zero := corr_one_of_mult D F g.base _ (castGen (oφ_eq D F g.base (0 + 0)) (g.form (0 + 0)))
        (by rw [add_zero (0 : D.X)])
        ((corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul 0 0))
      mult := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul χ χ') }
  invFun g :=
    { base := g.b
      form := fun χ => castGen (oφ_eq D F g.b χ).symm (g.s χ)
      form_gen := fun χ => castGen_isGen _ (g.isGen χ)
      form_mul := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.mult χ χ') }
  left_inv g := by
    obtain ⟨b, s, h₁, h₂⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _
  right_inv g := by
    obtain ⟨b, s, h₁, h₂, h₃⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _
variable {D F}
theorem isZero_iff (g : GtPt D F) : (ptEquiv D F g).IsZero ↔ g.IsZero :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)
theorem isAdd_iff (g g' h : GtPt D F) :
    (ptEquiv D F g).IsAdd (ptEquiv D F g') (ptEquiv D F h) ↔ g.IsAdd g' h :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_mul_castGen _ _ _ _ _ _ _)
theorem isIota_iff (y : D.X) (g : GtPt D F) :
    GtPtF.IsIota y (ptEquiv D F g) ↔ GtPt.IsIo y g :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)
theorem isNsmul_iff (k : ℕ) (g h : GtPt D F) :
    GtPtF.IsNsmul k (ptEquiv D F g) (ptEquiv D F h) ↔ g.IsNsmul k h := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    have key : ∀ (i : ℕ) (hi : i < k + 1), g.IsNsmul i ((ptEquiv D F).symm (gs ⟨i, hi⟩)) := by
      intro i
      induction i with
      | zero =>
        intro hi
        exact .zero _ ((isZero_iff _).1 (by rw [Equiv.apply_symm_apply]; exact h0))
      | succ i ih =>
        intro hi
        refine .succ i _ _ (ih (by omega)) ((isAdd_iff _ _ _).1 ?_)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hs ⟨i, by omega⟩
    have := key k (Nat.lt_succ_self k)
    rwa [show gs ⟨k, Nat.lt_succ_self k⟩ = ptEquiv D F h from hl, Equiv.symm_apply_apply] at this
  · intro H
    induction H with
    | zero h hz => exact ⟨fun _ => ptEquiv D F h, (isZero_iff h).2 hz, fun i => i.elim0, rfl⟩
    | succ k h h' _ ha ih =>
      obtain ⟨gs, h0, hs, hl⟩ := ih
      refine ⟨Fin.snoc (α := fun _ => GtPtF D F) gs (ptEquiv D F h'), ?_, fun i => ?_, ?_⟩
      · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0
      · rw [Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.succ_last, Fin.snoc_last, hl]; exact (isAdd_iff _ _ _).2 ha
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc]; exact hs j
      · rw [Fin.snoc_last]
variable (D F)
theorem exists_nsmul_iff (k : ℕ) (y : D.X) (g : GtPt D F) :
    (∃ h : GtPtF D F, GtPtF.IsNsmul k (ptEquiv D F g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h := by
  constructor
  · rintro ⟨h, h₁, h₂⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨w, (isNsmul_iff _ _ _).1 h₁, (isIota_iff _ _).1 h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨ptEquiv D F h, (isNsmul_iff _ _ _).2 h₁, (isIota_iff _ _).2 h₂⟩
theorem qkPt_ext {k : ℕ} {q q' : QkPt D F k} (h₁ : q.y = q'.y) (h₂ : q.g = q'.g) : q = q' := by
  obtain ⟨y, g, h⟩ := q
  obtain ⟨y', g', h'⟩ := q'
  obtain rfl : y = y' := h₁
  obtain rfl : g = g' := h₂
  rfl
def pairEquivOf (k : ℕ) (e : GtPt D F ≃ GtPtF D F)
    (H : ∀ y g, (∃ h : GtPtF D F, GtPtF.IsNsmul k (e g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h) : QPair D F k ≃ QkPt D F k where
  toFun p := ⟨p.1.1, e p.1.2, (H _ _).2 p.2⟩
  invFun q := ⟨(q.y, e.symm q.g), (H _ _).1 (by rw [Equiv.apply_symm_apply]; exact q.eq)⟩
  left_inv p := Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply e p.1.2))
  right_inv q := qkPt_ext D F rfl (Equiv.apply_symm_apply e q.g)
def pairEquiv (k : ℕ) : QPair D F k ≃ QkPt D F k :=
  pairEquivOf D F k (ptEquiv D F) (exists_nsmul_iff D F k)
variable {D F}
theorem rel_iff {k : ℕ} (p p' : QPair D F k) :
    QkPt.Equiv D F (pairEquiv D F k p) (pairEquiv D F k p') ↔ QRel D F k p p' := by
  constructor
  · rintro ⟨z, hz, h, hi, ha⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨z, w, (isIota_iff _ _).1 hi, hz, (isAdd_iff _ _ _).1 ha⟩
  · rintro ⟨z, w, hi, hz, ha⟩
    exact ⟨z, hz, ptEquiv D F w, (isIota_iff _ _).2 hi, (isAdd_iff _ _ _).2 ha⟩
variable (D F)
def qkEquiv (k : ℕ) : Qk D F k ≃ Quot (QkPt.Equiv D F (k := k)) :=
  Quot.congr (pairEquiv D F k) fun p p' => (rel_iff p p').symm
theorem isDatumIso_iff (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F)
    (ξ : E.X ≃+ D.X) :
    IsDatumIso D F E β ξ ↔ ∃ h : SplitExtIsD D F E, h.e = β ∧ h.chi = ξ.symm := by
  constructor
  · rintro ⟨hm, ht⟩
    refine ⟨⟨β, hm, ξ.symm, fun χ => ?_⟩, rfl, rfl⟩
    have := LBIso.symm (ht (ξ.symm χ))
    rwa [AddEquiv.apply_symm_apply] at this
  · rintro ⟨⟨e, hm, chi, ht⟩, rfl, rfl⟩
    refine ⟨hm, fun χ => ?_⟩
    have := LBIso.symm (ht (ξ χ))
    rwa [AddEquiv.symm_apply_apply] at this
def datumEquiv (E : SplitExt (Spec (CommRingCat.of F))) :
    {p : (E.B ≅ baseF D F) × (E.X ≃+ D.X) // IsDatumIso D F E p.1 p.2} ≃ SplitExtIsD D F E where
  toFun p := ⟨p.1.1, p.2.1, p.1.2.symm, by
    obtain ⟨h, h₁, h₂⟩ := (isDatumIso_iff D F E _ _).1 p.2
    have := h.oIso
    rwa [h₁, h₂] at this⟩
  invFun h := ⟨(h.e, h.chi.symm), (isDatumIso_iff D F E _ _).2 ⟨h, rfl, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable {D F}
variable (D F)
end GlobalTheory.GtPointsCompare


