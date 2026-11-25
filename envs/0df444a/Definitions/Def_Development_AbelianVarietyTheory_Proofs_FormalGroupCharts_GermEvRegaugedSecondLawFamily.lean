-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:19:58.794068+00:00
-- url     : https://prove2.me/theorems/14f4b222-c5bb-4a3f-9fe6-09a568b037e2
-- title:
--   Germ Ev Regauged Second Law Family
-- statement:
--   Definitions and structural lemmas for Germ Ev Regauged Second Law Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvRegaugedSecondLawFamily.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_expS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_triple_points_zero_constant

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.Regauge
section Points
variable {k : Type} [CommRing k] {d : ℕ}
theorem ev_ev_two {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d) (ha : GP a) (hb : GP b)
    (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]
theorem gp_add (G : FGLaw k d) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) : GP (addOf G.F a b) :=
  gp_addOf _ G.const a b ha hb
theorem gp_act {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G) (c : O) {n : ℕ} {a : Pt k n d} (ha : GP a) :
    GP (comp1 (A.act c) a) := gp_comp1 _ a (A.const c) ha
theorem ax_left {f : PS k 2 d} (hf : ev (n := 1) ![0, pt k d 0] f = 0) {n : ℕ} {a : Pt k n d} (ha : GP a) :
    ev ![0, a] f = 0 := by
  have := congrArg (ev ![a]) hf
  rw [ev_ev_two _ (single_point_zero_constant ha) _ _ gp_zero₂ (gp_pt _), evP_zero _ (single_point_zero_constant ha),
    evP_pt _ (single_point_zero_constant ha), gt_ev_zero _ (single_point_zero_constant ha)] at this
  exact this
theorem ax_right {f : PS k 2 d} (hf : ev (n := 1) ![pt k d 0, 0] f = 0) {n : ℕ} {a : Pt k n d} (ha : GP a) :
    ev ![a, 0] f = 0 := by
  have := congrArg (ev ![a]) hf
  rw [ev_ev_two _ (single_point_zero_constant ha) _ _ (gp_pt _) gp_zero₂, evP_zero _ (single_point_zero_constant ha),
    evP_pt _ (single_point_zero_constant ha), gt_ev_zero _ (single_point_zero_constant ha)] at this
  exact this
theorem zero_addOf (G : FGLaw k d) {n : ℕ} {a : Pt k n d} (ha : GP a) : addOf G.F 0 a = a := by
  funext i
  have := congrArg (ev ![a]) (G.unit i)
  rw [ev_ev_two _ (single_point_zero_constant ha) _ _ gp_zero₂ (gp_pt _), evP_zero _ (single_point_zero_constant ha),
    evP_pt _ (single_point_zero_constant ha), gt_ev_X _ (single_point_zero_constant ha)] at this
  exact this
theorem addOf_comm (G : FGLaw k d) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) :
    addOf G.F a b = addOf G.F b a := by
  funext i
  have hV := pair_points_zero_constant ha hb
  have := congrArg (ev ![a, b]) (G.comm i)
  rw [ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _), evP_pt _ hV, evP_pt _ hV] at this
  exact this.symm
theorem addOf_zero (G : FGLaw k d) {n : ℕ} {a : Pt k n d} (ha : GP a) : addOf G.F a 0 = a := by
  rw [addOf_comm G ha gp_zero₂, zero_addOf G ha]
theorem addOf_assoc (G : FGLaw k d) {n : ℕ} {a b c : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) :
    addOf G.F (addOf G.F a b) c = addOf G.F a (addOf G.F b c) := by
  funext i
  have hV := triple_points_zero_constant ha hb hc
  have h0 : ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] (G.F i) =
      ev (n := 3) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2)] (G.F i) := G.assoc i
  have := congrArg (ev ![a, b, c]) h0
  rw [ev_ev_two _ hV _ _ (gp_add G (gp_pt _) (gp_pt _)) (gp_pt _),
    ev_ev_two _ hV _ _ (gp_pt _) (gp_add G (gp_pt _) (gp_pt _)),
    evP_addOf _ hV _ _ _ (gp_pt _) (gp_pt _), evP_addOf _ hV _ _ _ (gp_pt _) (gp_pt _),
    evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at this
  exact this
variable {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)
theorem act_addOf (c : O) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) :
    comp1 (A.act c) (addOf G.F a b) = addOf G.F (comp1 (A.act c) a) (comp1 (A.act c) b) := by
  have hV := pair_points_zero_constant ha hb
  have := congrArg (evP ![a, b]) (A.hom c)
  rw [evP_comp1 _ hV _ _ (gp_add G (gp_pt _) (gp_pt _)),
    evP_addOf _ hV _ _ _ (gp_pt _) (gp_pt _),
    evP_addOf _ hV _ _ _ (gp_act A c (gp_pt _)) (gp_act A c (gp_pt _)),
    evP_comp1 _ hV _ _ (gp_pt _), evP_comp1 _ hV _ _ (gp_pt _),
    evP_pt _ hV, evP_pt _ hV] at this
  exact this
theorem add_act_pt (b c : O) {n : ℕ} {a : Pt k n d} (ha : GP a) :
    comp1 (A.act (b + c)) a = addOf G.F (comp1 (A.act b) a) (comp1 (A.act c) a) := by
  rw [A.add_act]
  exact evP_addOf ![a] (single_point_zero_constant ha) _ _ _ (A.const b) (A.const c)
theorem mul_act_pt (b c : O) {n : ℕ} {a : Pt k n d} (ha : GP a) :
    comp1 (A.act (b * c)) a = comp1 (A.act b) (comp1 (A.act c) a) := by
  rw [A.mul_act, gt_comp1_comp1 _ _ (A.const c) a ha]
theorem one_act_pt {n : ℕ} {a : Pt k n d} (ha : GP a) : comp1 (A.act 1) a = a := by
  rw [A.one_act, gt_comp1_pt a ha]
theorem act_zero_pt (c : O) {n : ℕ} : comp1 (A.act c) (0 : Pt k n d) = 0 := gt_comp1_zero _ (A.const c)
end Points
section Exp
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
def expR {n : ℕ} (f : PS k n d) : PS k n d := FB.expS k (f - C (constantCoeff f))
theorem expR_eq {n : ℕ} {f : PS k n d} (hf : constantCoeff f = 0) : expR f = FB.expS k f := by
  simp [expR, hf]
theorem expR_add {n : ℕ} (f g : PS k n d) : expR (f + g) = expR f * expR g := by
  unfold expR
  rw [← gt_expS_add _ _ (by simp) (by simp)]
  congr 1
  simp only [map_add]
  ring
theorem expR_zero {n : ℕ} : expR (0 : PS k n d) = 1 := by
  rw [expR_eq (by simp), FB.expS, PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]
  simp
theorem ev_expR {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d) :
    ev V (expR f) = expR (ev V f) := by
  unfold expR
  rw [gt_ev_expS V hV _ (by simp), gt_ev_sub V hV, gt_const_ev_eq V hV]
  congr 2
  unfold ev
  rw [MvPowerSeries.subst_C]
theorem mul_expR {n : ℕ} (P Q f g : PS k n d) : P * expR f * (Q * expR g) = P * Q * expR (f + g) := by
  rw [expR_add]; ring
end Exp
section Families
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O) (h : PS k 2 d)
def ph1 : PS k 3 d := B.ph1 * expR (ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h -
  ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 1, pt k d 2] h)
def ph2 : PS k 3 d := B.ph2 * expR (ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h -
  ev (n := 3) ![pt k d 0, pt k d 1] h - ev (n := 3) ![pt k d 0, pt k d 2] h)
def sy : PS k 2 d := B.sy * expR (ev (n := 2) ![pt k d 0, pt k d 1] h - ev (n := 2) ![pt k d 1, pt k d 0] h)
def ad (a : O) : PS k 2 d := B.ad a * expR (ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h -
  ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h)
theorem germEv_regaugedFirstLawFamily {n : ℕ} {a b c : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (ph1 B h) = ev ![a, b, c] B.ph1 *
      expR (ev ![addOf B.G.F a b, c] h - ev ![a, c] h - ev ![b, c] h) := by
  have hV := triple_points_zero_constant ha hb hc
  rw [ph1, gt_ev_mul _ hV, ev_expR _ hV, gt_ev_sub _ hV, gt_ev_sub _ hV,
    ev_ev_two _ hV _ _ (gp_add _ (gp_pt _) (gp_pt _)) (gp_pt _),
    ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _), ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _),
    evP_addOf _ hV _ _ _ (gp_pt _) (gp_pt _), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV]
  rfl
theorem germEv_regaugedSecondLawFamily {n : ℕ} {a b c : Pt k n d} (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (ph2 B h) = ev ![a, b, c] B.ph2 *
      expR (ev ![a, addOf B.G.F b c] h - ev ![a, b] h - ev ![a, c] h) := by
  have hV := triple_points_zero_constant ha hb hc
  rw [ph2, gt_ev_mul _ hV, ev_expR _ hV, gt_ev_sub _ hV, gt_ev_sub _ hV,
    ev_ev_two _ hV _ _ (gp_pt _) (gp_add _ (gp_pt _) (gp_pt _)),
    ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _), ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _),
    evP_addOf _ hV _ _ _ (gp_pt _) (gp_pt _), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV]
  rfl
theorem ev_sy {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) :
    ev ![a, b] (sy B h) = ev ![a, b] B.sy * expR (ev ![a, b] h - ev ![b, a] h) := by
  have hV := pair_points_zero_constant ha hb
  rw [sy, gt_ev_mul _ hV, ev_expR _ hV, gt_ev_sub _ hV,
    ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _), ev_ev_two _ hV _ _ (gp_pt _) (gp_pt _),
    evP_pt _ hV, evP_pt _ hV]
  rfl
theorem ev_ad (c : O) {n : ℕ} {a b : Pt k n d} (ha : GP a) (hb : GP b) :
    ev ![a, b] (ad B h c) = ev ![a, b] (B.ad c) *
      expR (ev ![a, comp1 (B.A.act (star c)) b] h - ev ![comp1 (B.A.act c) a, b] h) := by
  have hV := pair_points_zero_constant ha hb
  rw [ad, gt_ev_mul _ hV, ev_expR _ hV, gt_ev_sub _ hV,
    ev_ev_two _ hV _ _ (gp_pt _) (gp_act _ _ (gp_pt _)),
    ev_ev_two _ hV _ _ (gp_act _ _ (gp_pt _)) (gp_pt _),
    evP_comp1 _ hV _ _ (gp_pt _), evP_comp1 _ hV _ _ (gp_pt _),
    evP_pt _ hV, evP_pt _ hV]
  rfl
end Families
section Main
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
set_option maxHeartbeats 2000000 in

def regauge (B : FB k d O) (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) : FB k d O where
  G := B.G
  A := B.A
  ph1 := ph1 B h
  ph2 := ph2 B h
  sy := sy B h
  ad := ad B h
  cocycleLeft_zero_fst := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleLeft_zero_fst]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleLeft_zero_snd := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleLeft_zero_snd]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleLeft_zero_thd := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleLeft_zero_thd]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleRight_zero_fst := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleRight_zero_fst]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleRight_zero_snd := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleRight_zero_snd]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleRight_zero_thd := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleRight_zero_thd]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  symmetry_zero_fst := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.symmetry_zero_fst]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  symmetry_zero_snd := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.symmetry_zero_snd]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  adjoint_zero_fst := fun a => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.adjoint_zero_fst a]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  adjoint_zero_snd := fun a => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.adjoint_zero_snd a]
    simp (maxDischargeDepth := 4) only [zero_addOf, addOf_zero, act_zero_pt, ax_left h0, ax_right h1, gp_pt, gp_zero₂, gp_add, gp_act, sub_self, sub_zero, expR_zero, mul_one]
  cocycleLeft_assoc := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleLeft_assoc ]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  cocycleLeft_comm := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleLeft_comm, ph1, addOf_comm B.G (gp_pt 1) (gp_pt 0)]
    congr 2
    ring
  cocycleRight_assoc := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleRight_assoc ]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  cocycleRight_comm := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.cocycleRight_comm, ph2, addOf_comm B.G (gp_pt 2) (gp_pt 1)]
    congr 2
    ring
  interchange := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.interchange ]
    congr 2
    ring
  sy_inv := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [sy, mul_expR, B.sy_inv, one_mul, ← expR_zero]
    congr 1
    ring
  sy_law := by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    simp only [ph2, mul_expR]
    rw [B.sy_law ]
    congr 2
    ring
  adjoint_compat_left := fun a => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.adjoint_compat_left a]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  adjoint_compat_right := fun a => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    rw [B.adjoint_compat_right a]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  ad_one := by
    rw [ad, B.ad_one, star_one, one_act_pt _ (gp_pt _), one_act_pt _ (gp_pt _), sub_self, expR_zero, mul_one]
  ad_mul := fun a b => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    simp only [ad, mul_expR]
    rw [B.ad_mul a b]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  ad_add := fun a b => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    simp only [ad, mul_expR]
    rw [B.ad_add a b]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
  ad_sy := fun a => by
    simp (maxDischargeDepth := 4) only [germEv_regaugedFirstLawFamily, germEv_regaugedSecondLawFamily, ev_sy, ev_ad, gp_pt, gp_zero₂, gp_add, gp_act, mul_expR]
    simp only [ad, mul_expR]
    rw [B.ad_sy a]
    congr 2
    simp (maxDischargeDepth := 4) only [addOf_assoc, act_addOf, add_act_pt, mul_act_pt, star_star, star_mul, star_add, gp_pt, gp_add, gp_act]
    ring
end Main
end GlobalTheory.Regauge
namespace GlobalTheory
open GlobalTheory.Regauge
end GlobalTheory


