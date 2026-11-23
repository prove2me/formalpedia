-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:30.17356+00:00
-- url     : https://prove2.me/theorems/fbc50b24-24eb-46e6-88f5-c85e912760bf
-- title:
--   Exists Action Gauge
-- statement:
--   Definitions and structural lemmas for Exists Action Gauge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsActionGauge.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_ev__a7884319006c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_pair_points
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant

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
namespace GlobalTheory.ActionGauge
section Basic
variable {k : Type} [CommRing k] {d : ℕ}
def evAdd {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) : PS k m d →+ PS k n d :=
  AddMonoidHom.mk' (ev a) (gt_ev_add a ha)
theorem ev_ratSmul [Algebra ℚ k] {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (q : ℚ)
    (f : PS k m d) : ev a (q • f) = q • ev a f :=
  map_rat_smul (evAdd a ha) q f
theorem ev_pt_two (f : PS k 2 d) : ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] f = f := by
  change MvPowerSeries.subst
    (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) f = f
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k (n := 2) d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl
theorem ev_ev_two {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d)
    (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]
theorem ev_left {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), pt k (n := 2) d 1] g) = ev ![comp1 φ a, b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_pt 1),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_pt _ hV, evP_pt _ hV]
  rfl
theorem ev_right {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b)
    (g : PS k 2 d) :
    ev ![a, b] (ev ![pt k (n := 2) d 0, comp1 φ (pt k (n := 2) d 1)] g) = ev ![a, comp1 φ b] g := by
  have hV := pair_points_zero_constant ha hb
  rw [ev_ev_two _ hV _ _ (gp_pt 0) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV]
  rfl
end Basic
section Act
variable {k : Type} [CommRing k] {d : ℕ} {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)
theorem act_addOf (c : O) {n : ℕ} (x y : Pt k n d) (hx : GP x) (hy : GP y) :
    comp1 (A.act c) (addOf G.F x y) = addOf G.F (comp1 (A.act c) x) (comp1 (A.act c) y) := by
  have hV := pair_points_zero_constant hx hy
  have hc : GP (A.act c) := A.const c
  have h := congrArg (evP ![x, y]) (A.hom c)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1),
    evP_addOf _ hV _ _ _ (gp_comp1 _ _ hc (gp_pt 0)) (gp_comp1 _ _ hc (gp_pt 1)),
    evP_comp1 _ hV _ _ (gp_pt 0), evP_comp1 _ hV _ _ (gp_pt 1),
    evP_pt _ hV, evP_pt _ hV] at h
  exact h
theorem add_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a + b)) x = addOf G.F (comp1 (A.act a) x) (comp1 (A.act b) x) := by
  rw [A.add_act]
  exact evP_addOf ![x] (single_point_zero_constant hx) G.F _ _ (A.const a) (A.const b)
theorem mul_act_apply (a b : O) {n : ℕ} (x : Pt k n d) (hx : GP x) :
    comp1 (A.act (a * b)) x = comp1 (A.act a) (comp1 (A.act b) x) := by
  rw [A.mul_act]
  exact gt_comp1_comp1 _ _ (A.const b) x hx
theorem one_act_apply {n : ℕ} (x : Pt k n d) (hx : GP x) : comp1 (A.act 1) x = x := by
  rw [A.one_act]
  exact gt_comp1_pt x hx
end Act
section Biadd
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
def biadd (G : FGLaw k d) : Submodule ℚ (PS k 2 d) where
  carrier := {g | (∀ (n : ℕ) (b : Pt k n d), GP b → ev ![0, b] g = 0) ∧
    (∀ (n : ℕ) (a : Pt k n d), GP a → ev ![a, 0] g = 0) ∧
    (∀ (n : ℕ) (a a' b : Pt k n d), GP a → GP a' → GP b →
      ev ![addOf G.F a a', b] g = ev ![a, b] g + ev ![a', b] g) ∧
    (∀ (n : ℕ) (a b b' : Pt k n d), GP a → GP b → GP b' →
      ev ![a, addOf G.F b b'] g = ev ![a, b] g + ev ![a, b'] g)}
  zero_mem' := by
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · exact gt_ev_zero _ (pair_points_zero_constant gp_zero₂ hb)
    · exact gt_ev_zero _ (pair_points_zero_constant ha gp_zero₂)
    · rw [gt_ev_zero _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha' hb), add_zero]
    · rw [gt_ev_zero _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_zero _ (pair_points_zero_constant ha hb),
        gt_ev_zero _ (pair_points_zero_constant ha hb'), add_zero]
  add_mem' := by
    rintro f g ⟨f1, f2, f3, f4⟩ ⟨g1, g2, g3, g4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [gt_ev_add _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, g1 n b hb, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, g2 n a ha, add_zero]
    · rw [gt_ev_add _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, g3 n a a' b ha ha' hb]
      ring
    · rw [gt_ev_add _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), gt_ev_add _ (pair_points_zero_constant ha hb),
        gt_ev_add _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', g4 n a b b' ha hb hb']
      ring
  smul_mem' := by
    rintro q f ⟨f1, f2, f3, f4⟩
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_ratSmul _ (pair_points_zero_constant gp_zero₂ hb), f1 n b hb, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha gp_zero₂), f2 n a ha, smul_zero]
    · rw [ev_ratSmul _ (pair_points_zero_constant (gp_addOf _ G.const _ _ ha ha') hb), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha' hb), f3 n a a' b ha ha' hb, smul_add]
    · rw [ev_ratSmul _ (pair_points_zero_constant ha (gp_addOf _ G.const _ _ hb hb')), ev_ratSmul _ (pair_points_zero_constant ha hb),
        ev_ratSmul _ (pair_points_zero_constant ha hb'), f4 n a b b' ha hb hb', smul_add]
variable {O : Type} [CommRing O] {G : FGLaw k d} (A : OAct O G)
def leftMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_left _ hc _ _ gp_zero₂ hb, gt_comp1_zero _ hc, g1 n b hb]
    · rw [ev_left _ hc _ _ ha gp_zero₂, g2 n _ (gp_comp1 _ _ hc ha)]
    · rw [ev_left _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha' hb, act_addOf A c _ _ ha ha',
        g3 n _ _ _ (gp_comp1 _ _ hc ha) (gp_comp1 _ _ hc ha') hb]
    · rw [ev_left _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_left _ hc _ _ ha hb,
        ev_left _ hc _ _ ha hb', g4 n _ _ _ (gp_comp1 _ _ hc ha) hb hb']⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_comp1 _ _ (A.const c) (gp_pt 0)) (gp_pt 1)) _ _)
def rightMap (c : O) : Module.End ℚ (biadd G) where
  toFun g := ⟨ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d), by
    have hc : GP (A.act c) := A.const c
    obtain ⟨g, g1, g2, g3, g4⟩ := g
    refine ⟨fun n b hb => ?_, fun n a ha => ?_, fun n a a' b ha ha' hb => ?_,
      fun n a b b' ha hb hb' => ?_⟩
    · rw [ev_right _ hc _ _ gp_zero₂ hb, g1 n _ (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha gp_zero₂, gt_comp1_zero _ hc, g2 n a ha]
    · rw [ev_right _ hc _ _ (gp_addOf _ G.const _ _ ha ha') hb, ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha' hb, g3 n _ _ _ ha ha' (gp_comp1 _ _ hc hb)]
    · rw [ev_right _ hc _ _ ha (gp_addOf _ G.const _ _ hb hb'), ev_right _ hc _ _ ha hb,
        ev_right _ hc _ _ ha hb', act_addOf A c _ _ hb hb',
        g4 n _ _ _ ha (gp_comp1 _ _ hc hb) (gp_comp1 _ _ hc hb')]⟩
  map_add' f g := Subtype.ext
    (gt_ev_add _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)
  map_smul' q f := Subtype.ext
    (ev_ratSmul _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (A.const c) (gp_pt 1))) _ _)
theorem leftMap_val (c : O) (g : biadd G) : (leftMap A c g : PS k 2 d) =
    ev ![comp1 (A.act c) (pt k (n := 2) d 0), pt k (n := 2) d 1] (g : PS k 2 d) := rfl
theorem rightMap_val (c : O) (g : biadd G) : (rightMap A c g : PS k 2 d) =
    ev ![pt k (n := 2) d 0, comp1 (A.act c) (pt k (n := 2) d 1)] (g : PS k 2 d) := rfl
def leftHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := leftMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [leftMap_val, one_act_apply A _ (gp_pt 0), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, leftMap_val, leftMap_val, leftMap_val,
          ev_left _ (A.const b) _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0)) (gp_pt 1),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 0)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (leftMap A (a + b) g : PS k 2 d) = leftMap A a g + leftMap A b g
      rw [leftMap_val, leftMap_val, leftMap_val, add_act_apply A _ _ _ (gp_pt 0)]
      exact g.2.2.2.1 _ _ _ _ (gp_comp1 _ _ (A.const a) (gp_pt 0))
        (gp_comp1 _ _ (A.const b) (gp_pt 0)) (gp_pt 1))
def rightHom : O →+* Module.End ℚ (biadd G) :=
  RingHom.mk'
    { toFun := rightMap A
      map_one' := by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [rightMap_val, one_act_apply A _ (gp_pt 1), ev_pt_two]
        rfl
      map_mul' := fun a b => by
        refine LinearMap.ext fun g => Subtype.ext ?_
        rw [Module.End.mul_apply, rightMap_val, rightMap_val, rightMap_val,
          ev_right _ (A.const b) _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1)),
          mul_comm a b, mul_act_apply A _ _ _ (gp_pt 1)] }
    (fun a b => by
      refine LinearMap.ext fun g => Subtype.ext ?_
      change (rightMap A (a + b) g : PS k 2 d) = rightMap A a g + rightMap A b g
      rw [rightMap_val, rightMap_val, rightMap_val, add_act_apply A _ _ _ (gp_pt 1)]
      exact g.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_comp1 _ _ (A.const a) (gp_pt 1))
        (gp_comp1 _ _ (A.const b) (gp_pt 1)))
end Biadd
section Log
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O)
def logAd (a : O) : PS k 2 d := PowerSeries.subst (B.ad a - 1) (PowerSeries.log k)
end Log
end GlobalTheory.ActionGauge


