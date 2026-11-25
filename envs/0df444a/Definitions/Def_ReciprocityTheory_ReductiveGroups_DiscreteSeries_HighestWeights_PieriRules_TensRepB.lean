-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepB
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:31.394687+00:00
-- url     : https://prove2.me/theorems/a580ac01-cb5b-557a-8524-bfe6985405c6
-- title:
--   Tens Rep B
-- statement:
--   Definitions and structural lemmas for Tens Rep B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_hasDerivAt_tensL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensOp_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensOp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensTau_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_tensTau_cont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensOp_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.HW.tensTau_coe


set_option autoImplicit false
noncomputable section
open Matrix Finset
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
section Lin
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem tensL_add_left (m m' : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (m + m') S = tensL m S + tensL m' S := by
  ext x i
  simp [tensL_apply, add_smul, Finset.sum_add_distrib]
theorem tensL_smul_left (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (c • m) S = c • tensL m S := by
  ext x i
  simp [tensL_apply, mul_smul, Finset.smul_sum]
theorem tensL_add_right (m : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL m (S + S') = tensL m S + tensL m S' := by
  ext x i
  simp [tensL_apply, smul_add, Finset.sum_add_distrib]
theorem tensL_smul_right (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL m (c • S) = c • tensL m S := by
  ext x i
  simp [tensL_apply, Finset.smul_sum, smul_comm c]
end Lin
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
def tensD (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) where
  toFun X := tensL (dρ X) 1 + tensL 1 (T.dτ X)
  map_add' X Y := by
    simp only [map_add, tensL_add_left, tensL_add_right]
    abel
  map_smul' c X := by
    simp only [map_smul, tensL_smul_left, tensL_smul_right, RingHom.id_apply, smul_add]
theorem tens_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 := by
  apply onep_KG_ext
  rw [hγ]
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
  simp
theorem tensD_hasDeriv (ρ : KG ε →* unitary (Matrix ι ι ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (hd : ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
      (dρ X i j) 0) :
    HasDerivAt (fun t : ℝ => ((tensTau T ρ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
      PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (tensD T dρ X) 0 := by
  have h0 := tens_curve_zero γ hγ
  have hD := hasDerivAt_tensL (V := T.V) hd (T.hasDeriv X hX γ hγ)
  simp only [tensTau_coe, tensOp_eq]
  convert hD using 1
  simp [tensD, h0]
include T in

def tensKRep (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) : KRep ε where
  V := PiLp 2 (fun _ : ι => T.V)
  τ := tensTau T ρ
  cont := tensTau_cont T ρ hc
  dτ := tensD T dρ
  hasDeriv X hX γ hγ := tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ)
end ReciprocityTheory.ChartRestriction.DS.HW


