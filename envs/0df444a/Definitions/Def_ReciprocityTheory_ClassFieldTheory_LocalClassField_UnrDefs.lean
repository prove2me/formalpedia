-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:18.587484+00:00
-- url     : https://prove2.me/theorems/778cefed-cf0d-4395-bcd0-5c57856b534d
-- title:
--   Unr Defs
-- statement:
--   Definitions and structural lemmas for Unr Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime]
noncomputable abbrev Obar : ValuationSubring (PadicAlgCl p) := (PadicAlgCl.valued p).v.valuationSubring
abbrev kbar : Type := IsLocalRing.ResidueField (Obar p)
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
noncomputable def resK : Subfield (kbar p) where
  toSubring := (K.toSubring.comap (Obar p).subtype).map (IsLocalRing.residue (Obar p))
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    by_cases h0 : IsLocalRing.residue (Obar p) a = 0
    · rw [h0, inv_zero]; exact Subring.zero_mem _
    · have h0 := (IsLocalRing.residue_ne_zero_iff_isUnit a).1 h0
      obtain ⟨u, rfl⟩ := h0
      refine ⟨((u⁻¹ : (Obar p)ˣ) : Obar p), ?_, ?_⟩
      · have h1 : (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = ((u : Obar p) : PadicAlgCl p)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have h2 : ((((u⁻¹ : (Obar p)ˣ) : Obar p) * (u : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
            rw [u.inv_mul]; rfl
          exact h2
        change (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) ∈ K
        rw [h1]
        exact K.inv_mem ha
      · apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, u.inv_mul, map_one]
noncomputable def qK : ℕ := Nat.card (resK p K)
noncomputable def Kn (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}
def IsFrobOn (n : ℕ) (φ : GK p K) : Prop :=
  ∀ x ∈ Kn p K n, ‖x‖ ≤ 1 → ‖φ x - x ^ qK p K‖ < 1
end ReciprocityTheory.DiscreteGroups.LocalClassField


