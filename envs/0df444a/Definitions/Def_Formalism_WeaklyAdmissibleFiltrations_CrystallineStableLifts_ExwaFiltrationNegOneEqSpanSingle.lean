-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
-- name    : Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:48.527966+00:00
-- url     : https://prove2.me/theorems/d93ea55f-070a-41b5-a594-d2d4fffd3d61
-- title:
--   Exwa Filtration Neg One Eq Span Single
-- statement:
--   Definitions and structural lemmas for Exwa Filtration Neg One Eq Span Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module
section ExWAConstruction
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
def exwaShift : (ZMod n → LL) ≃ₗ[LL] (ZMod n → LL) :=
  LinearEquiv.funCongrLeft LL LL (Equiv.subRight (1 : ZMod n))
lemma exwaShift_apply (x : ZMod n → LL) (i : ZMod n) : exwaShift x i = x (i - 1) := rfl
lemma exwaShift_single (j : ZMod n) :
    exwaShift (Pi.single j (1 : LL) : ZMod n → LL) = Pi.single (j + 1) 1 := by
  funext i
  simp only [exwaShift_apply, Pi.single_apply, sub_eq_iff_eq_add]
def exwaPhi (c : LL) (hc : c ≠ 0) : (ZMod n → LL) ≃ₗ[LL] (ZMod n → LL) :=
  exwaShift.trans (LinearEquiv.smulOfNeZero LL (ZMod n → LL) c hc)
lemma exwaPhi_apply (c : LL) (hc : c ≠ 0) (x : ZMod n → LL) :
    exwaPhi c hc x = c • exwaShift x := rfl
lemma exwaPhi_single (c : LL) (hc : c ≠ 0) (j : ZMod n) :
    exwaPhi c hc (Pi.single j (1 : LL) : ZMod n → LL) = c • Pi.single (j + 1) 1 := by
  rw [exwaPhi_apply, exwaShift_single]
lemma exwa_internal :
    DirectSum.IsInternal (fun i : ZMod n => LL ∙ (Pi.single i (1 : LL) : ZMod n → LL)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · have h := (Pi.basisFun LL (ZMod n)).linearIndependent.iSupIndep_span_singleton
    simpa using h
  · have h := (Pi.basisFun LL (ZMod n)).span_eq
    rw [Submodule.span_range_eq_iSup] at h
    simpa using h
def exwaF (c : LL) (hc : c ≠ 0) : FilPhi LL (ZMod n → LL) n (ZMod n) where
  letter := id
  e := 1
  fiber := by intro i; simp [Finset.filter_eq']
  Dl := fun i => LL ∙ (Pi.single i (1 : LL) : ZMod n → LL)
  internal := exwa_internal
  φ := exwaPhi c hc
  φ_Dl := by
    intro i
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, exwaPhi_single,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  Fil := fun τ a => if a ≤ -1 then LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL) else ⊥
  Fil_le := by intro τ a; split_ifs <;> simp
  Fil_anti := by
    intro τ a
    split_ifs with h1 h2 <;> first | exact le_rfl | exact bot_le | (exfalso; omega)
  lo := -1
  hi := 0
  lo_le := by norm_num
  Fil_lo := by intro τ a ha; exact if_pos ha
  Fil_hi := by intro τ a ha; exact if_neg (by omega)
end ExWAConstruction
section ExWAVal
variable {LL : Type} [Field LL]
end ExWAVal
section ExWAMain
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
end ExWAMain
end Formalism.WeaklyAdmissibleFiltrations


