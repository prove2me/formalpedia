-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:34.467429+00:00
-- url     : https://prove2.me/theorems/e3910c2f-388a-4480-8e2c-52900a5da4c0
-- title:
--   Formal Group Action Limits Integral Endomorphisms
-- statement:
--   Definitions and structural lemmas for Formal Group Action Limits Integral Endomorphisms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupActionLimitsIntegralEndomorphisms.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
def Tends (V : VF C) (s : ℕ → C) (x : C) : Prop := ∀ w : ℝ, ∀ᶠ n in atTop, V.Ge w (x - s n)
theorem exists_ge (x : C) : ∃ w : ℝ, w ≤ 0 ∧ V.Ge w x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_rfl, le_top⟩
  | coe t => exact ⟨min t 0, min_le_right _ _, by exact_mod_cast min_le_left _ _⟩
theorem Tends.const (x : C) : Tends V (fun _ => x) x := fun w =>
  Eventually.of_forall fun _ => by simpa using VF.Ge.zero (V := V) w
theorem Tends.add {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n + t n) (x + y) := fun w => by
  filter_upwards [hs w, ht w] with n h1 h2
  have := h1.add h2
  rwa [show x - s n + (y - t n) = x + y - (s n + t n) by ring] at this
theorem Tends.neg {s : ℕ → C} {x : C} (hs : Tends V s x) : Tends V (fun n => -s n) (-x) := fun w => by
  filter_upwards [hs w] with n h1
  have := h1.neg
  rwa [show -(x - s n) = -x - -s n by ring] at this
theorem Tends.mul {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n * t n) (x * y) := fun w => by
  obtain ⟨a, -, ha⟩ := exists_ge (V := V) x
  obtain ⟨b, -, hb⟩ := exists_ge (V := V) y
  filter_upwards [hs (w - b), ht (w - a), ht b] with n h1 h2 h3
  have h4 : V.Ge b (t n) := by simpa using hb.sub h3
  have h5 : V.Ge w (x * (y - t n)) := by simpa using ha.mul h2
  have h6 : V.Ge w ((x - s n) * t n) := by simpa using h1.mul h4
  have := h5.add h6
  rwa [show x * (y - t n) + (x - s n) * t n = x * y - s n * t n by ring] at this
def convRing (V : VF C) : Subring ((ℕ → C) × C) where
  carrier := {p | Tends V p.1 p.2}
  mul_mem' := fun ha hb => Tends.mul ha hb
  one_mem' := Tends.const 1
  add_mem' := fun ha hb => Tends.add ha hb
  zero_mem' := Tends.const 0
  neg_mem' := fun ha => Tends.neg ha
def TendsS (V : VF C) {τ : Type} (f : ℕ → MvPowerSeries τ C) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ, Tends V (fun n => MvPowerSeries.coeff μ (f n)) (MvPowerSeries.coeff μ g)
def TendsS.lift {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C} (h : TendsS V f g) :
    MvPowerSeries τ (convRing V) :=
  fun μ => ⟨(fun n => MvPowerSeries.coeff μ (f n), MvPowerSeries.coeff μ g), h μ⟩
def term (V : VF C) (n : ℕ) : convRing V →+* C :=
  ((Pi.evalRingHom (fun _ : ℕ => C) n).comp (RingHom.fst _ _)).comp (convRing V).subtype
def lim (V : VF C) : convRing V →+* C := (RingHom.snd _ _).comp (convRing V).subtype
variable {dd : ℕ}
end GlobalTheory.ActLimit


