-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:54.524291+00:00
-- url     : https://prove2.me/theorems/ef03e7d1-31df-4af4-be99-6ab4bbd1c4cc
-- title:
--   Pow Pow Succ Sub
-- statement:
--   Definitions and structural lemmas for Pow Pow Succ Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/PowPowSuccSub.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_GK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
noncomputable def sigO (σ : GK p K) : Obar p →+* Obar p :=
  ((σ : PadicAlgCl p →+* PadicAlgCl p).comp (Obar p).subtype).codRestrict (Obar p)
    (fun x => mem_Obar_iff.2 (by
      change ‖σ (x : PadicAlgCl p)‖ ≤ 1
      rw [norm_GK]; exact norm_le_one x))
theorem coe_sigO (σ : GK p K) (x : Obar p) : ((sigO σ x : Obar p) : PadicAlgCl p) = σ x := rfl
noncomputable def sigBar (σ : GK p K) : kbar p →+* kbar p :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Obar p)) (res.comp (sigO σ)) (by
    intro a ha
    have h1 : res a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [res_eq_zero_iff] at h1
    change res (sigO σ a) = 0
    rw [res_eq_zero_iff, coe_sigO, norm_GK]
    exact h1)
variable (K)
noncomputable def eqField (σ τ : GK p K) : IntermediateField ℚ_[p] (PadicAlgCl p) where
  toSubalgebra := AlgHom.equalizer
    ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
    ((τ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
  inv_mem' := by
    intro x hx
    have hx' : σ x = τ x := hx
    change σ x⁻¹ = τ x⁻¹
    rw [map_inv₀, map_inv₀, hx']
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions


