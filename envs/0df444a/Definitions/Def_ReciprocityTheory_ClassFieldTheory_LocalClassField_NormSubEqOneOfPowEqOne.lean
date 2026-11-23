-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:19.618839+00:00
-- url     : https://prove2.me/theorems/10985688-6889-47bb-8eaa-c2ae6cd70db6
-- title:
--   Norm Sub Eq One Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for Norm Sub Eq One Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/NormSubEqOneOfPowEqOne.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
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
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]
noncomputable abbrev res : Obar p →+* kbar p := IsLocalRing.residue (Obar p)
theorem norm_le_one (x : Obar p) : ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff.1 x.2
theorem isUnit_iff (x : Obar p) : IsUnit x ↔ ‖(x : PadicAlgCl p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : Obar p) : PadicAlgCl p) * (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = 1 := by
      have h2 : (((u : Obar p) * ((u⁻¹ : (Obar p)ˣ) : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
        rw [u.mul_inv]; rfl
      exact h2
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have ha := norm_le_one (u : Obar p)
    have hb := norm_le_one ((u⁻¹ : (Obar p)ˣ) : Obar p)
    have hb0 := norm_nonneg ((u : Obar p) : PadicAlgCl p)
    nlinarith
  · intro h
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hi : ‖(x : PadicAlgCl p)⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(x : PadicAlgCl p)⁻¹, mem_Obar_iff.2 hi⟩ : Obar p) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0
theorem res_eq_zero_iff (x : Obar p) : res x = 0 ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  constructor
  · intro h
    by_contra hc
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm (norm_le_one x) (not_lt.1 hc)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit x).2 ((isUnit_iff x).2 h1) h
  · intro h
    by_contra hc
    have := (isUnit_iff x).1 ((IsLocalRing.residue_ne_zero_iff_isUnit x).1 hc)
    exact absurd this (ne_of_lt h)
theorem norm_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
scoped instance charP_kbar : CharP (kbar p) p := by
  obtain ⟨r, hr⟩ := CharP.exists (kbar p)
  have h0 : ((p : ℕ) : kbar p) = 0 := by
    have h1 : res ((p : ℕ) : Obar p) = 0 := by
      rw [res_eq_zero_iff]
      have : (((p : ℕ) : Obar p) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
      rw [this]; exact norm_p_lt_one
    simpa using h1
  have h2 : r ∣ p := (CharP.cast_eq_zero_iff (kbar p) r p).1 h0
  have h3 : r = p := ((Nat.dvd_prime Fact.out).1 h2).resolve_left (CharP.char_ne_one (kbar p) r)
  exact h3 ▸ hr
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions


