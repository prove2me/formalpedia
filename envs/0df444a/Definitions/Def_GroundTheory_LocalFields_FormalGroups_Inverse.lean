-- Prove2me | Definitions.Def_GroundTheory_LocalFields_FormalGroups_Inverse
-- name    : GroundTheory_LocalFields_FormalGroups_Inverse
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:20.424163+00:00
-- url     : https://prove2.me/theorems/e0ce7c3e-4c94-447e-a187-438da344ea3d
-- title:
--   Inverse
-- statement:
--   Definitions and structural lemmas for Inverse, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Inverse.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
import Theorems.Thm_GroundTheory_LocalField_FormalGroup_add_le_order_subst_sub_subst
import Theorems.Thm_GroundTheory_LocalField_FormalGroup_existsUnique_fixedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {R : Type*} [CommRing R] (F : FormalGroup R)
noncomputable def higher : MvPowerSeries (Fin 2) R :=
  F.toPowerSeries - X 0 - X 1
theorem toPowerSeries_eq_X_add_X_add_higher : F.toPowerSeries = X 0 + X 1 + higher F := by
  simp [higher]
theorem two_le_order_higher : (2 : ℕ∞) ≤ order (higher F) := by
  refine nat_le_order fun d hd => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = Finsupp.single 0 a + Finsupp.single 1 b :=
    ⟨d 0, d 1, by ext i; fin_cases i <;> simp⟩
  have hab : a + b < 2 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  have h01 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  have ha : a < 2 := by omega
  have hb : b < 2 := by omega
  interval_cases a <;> interval_cases b <;> simp_all [higher, coeff_X, F.lin_coeff_X,
    F.lin_coeff_Y, F.zero_constantCoeff, Ne.symm h01]
theorem constantCoeff_higher : constantCoeff (higher F) = 0 :=
  one_le_order_iff_constCoeff_eq_zero.1 (le_trans (by norm_num) (two_le_order_higher F))
theorem subst_eq_add_add_subst_higher {τ : Type*} {a b : MvPowerSeries τ R}
    (hab : HasSubst ![a, b]) :
    subst ![a, b] F.toPowerSeries = a + b + subst ![a, b] (higher F) := by
  conv_lhs => rw [toPowerSeries_eq_X_add_X_add_higher F]
  rw [subst_add hab, subst_add hab, subst_X hab, subst_X hab]
  simp
lemma hasSubst_pair {τ : Type*} {a b : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa
noncomputable def invStep (g : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  -X () - subst ![X (), g - C (constantCoeff g)] (higher F)
lemma constantCoeff_sub_C (g : MvPowerSeries Unit R) :
    constantCoeff (g - C (constantCoeff g)) = 0 := by simp
lemma invStep_contract (f g : MvPowerSeries Unit R) (n : ℕ)
    (h : (n : ℕ∞) ≤ order (f - g)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ order (invStep F f - invStep F g) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have key := add_le_order_subst_sub_subst (R := R) (m := 2) (n := (n : ℕ∞))
    (hasSubst_pair hX (constantCoeff_sub_C f)) (hasSubst_pair hX (constantCoeff_sub_C g))
    (fun i => by fin_cases i <;> simp) (fun i => by fin_cases i <;> simp) ?_
    (two_le_order_higher F)
  · have e : invStep F f - invStep F g = -(subst ![X (), f - C (constantCoeff f)] (higher F) -
        subst ![X (), g - C (constantCoeff g)] (higher F)) := by
      simp only [invStep]; ring
    rw [e, order_neg]
    have : ((n + 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) + 2 := by push_cast; ring
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (this ▸ key)
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simp [hn]
      · have h0 : constantCoeff (f - g) = 0 := by
          rw [← coeff_zero_eq_constantCoeff_apply]
          exact coeff_of_lt_order (lt_of_lt_of_le (by simpa using hn) h)
        rw [map_sub, sub_eq_zero] at h0
        rw [h0]
        simpa using h
lemma existsUnique_invStep : ∃! g, invStep F g = g :=
  existsUnique_fixedPoint _ (invStep_contract F)
noncomputable def inv : PowerSeries R :=
  (existsUnique_invStep F).exists.choose
lemma invStep_inv : invStep F (inv F) = inv F :=
  (existsUnique_invStep F).exists.choose_spec
lemma constantCoeff_invStep (g : MvPowerSeries Unit R) :
    constantCoeff (invStep F g) = 0 := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  rw [invStep, map_sub, map_neg, hX,
    constantCoeff_subst_eq_zero (hasSubst_pair hX (constantCoeff_sub_C g))
      (fun i => by fin_cases i <;> simp) (constantCoeff_higher F)]
  simp
theorem constantCoeff_inv : PowerSeries.constantCoeff (inv F) = 0 := by
  rw [← invStep_inv F]
  exact constantCoeff_invStep F _
theorem hasSubst_inv : PowerSeries.HasSubst (inv F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_inv F)
lemma invStep_of_constantCoeff_eq_zero {g : MvPowerSeries Unit R}
    (hg : constantCoeff g = 0) : invStep F g = -X () - subst ![X (), g] (higher F) := by
  simp [invStep, hg]
theorem subst_X_inv :
    subst ![PowerSeries.X, inv F] F.toPowerSeries = (0 : PowerSeries R) := by
  have hX : constantCoeff (X () : MvPowerSeries Unit R) = 0 := by simp
  have hi : constantCoeff (inv F : MvPowerSeries Unit R) = 0 := constantCoeff_inv F
  have := invStep_inv F
  rw [invStep_of_constantCoeff_eq_zero F hi] at this
  change subst ![X (), (inv F : MvPowerSeries Unit R)] F.toPowerSeries = 0
  rw [subst_eq_add_add_subst_higher F (hasSubst_pair hX hi)]
  linear_combination (-1 : MvPowerSeries Unit R) * this
theorem subst_subst_pair {σ : Type*} {g h : PowerSeries R} (hgh : HasSubst ![g, h])
    {x : MvPowerSeries σ R} (hx : PowerSeries.HasSubst x) (G : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst x (subst ![g, h] G : PowerSeries R) =
      subst ![PowerSeries.subst x g, PowerSeries.subst x h] G := by
  have hx' : HasSubst (fun _ : Unit => x) := PowerSeries.hasSubst_iff.mp hx
  rw [PowerSeries.subst_def, subst_comp_subst_apply hgh hx']
  congr 1
  funext s
  fin_cases s <;> rfl
variable {σ : Type*}
noncomputable instance : Neg (F.Point σ) where
  neg x := ⟨PowerSeries.subst x.val (inv F), by
    simpa [PowerSeries.coe_substAlgHom] using (hasSubst_inv F).comp x.prop⟩
theorem neg_point_val (x : F.Point σ) : (-x).val = PowerSeries.subst x.val (inv F) := rfl
lemma add_neg_point (x : F.Point σ) : x + -x = 0 := by
  apply Subtype.ext
  have hX : constantCoeff (PowerSeries.X : PowerSeries R) = 0 := PowerSeries.constantCoeff_X
  have h := congrArg (PowerSeries.subst x.val) (subst_X_inv F)
  rw [subst_subst_pair (hasSubst_pair hX (constantCoeff_inv F)) x.prop,
    PowerSeries.subst_X x.prop] at h
  rw [FormalGroup.add_apply, neg_point_val, h]
  rw [← PowerSeries.coe_substAlgHom x.prop, map_zero]
  rfl
noncomputable instance instAddGroupPoint : AddGroup (F.Point σ) :=
  { (inferInstance : AddMonoid (F.Point σ)) with
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      have h1 := add_neg_point F x
      have h2 := add_neg_point F (-x)
      have hx : x = -(-x) :=
        calc x = x + 0 := (add_zero x).symm
          _ = x + (-x + -(-x)) := by rw [h2]
          _ = (x + -x) + -(-x) := (add_assoc _ _ _).symm
          _ = -(-x) := by rw [h1, zero_add]
      calc -x + x = -x + -(-x) := congrArg (-x + ·) hx
        _ = 0 := h2 }
noncomputable instance instAddCommGroupPoint [F.IsComm] : AddCommGroup (F.Point σ) :=
  { instAddGroupPoint F with
    add_comm := fun x y => Subtype.ext (F.comm' x.prop y.prop) }
noncomputable def pointX : F.Point Unit := ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩
end GroundTheory.LocalField.FormalGroup


