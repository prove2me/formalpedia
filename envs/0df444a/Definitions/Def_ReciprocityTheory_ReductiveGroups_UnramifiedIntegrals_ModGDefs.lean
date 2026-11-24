-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:36:38.227228+00:00
-- url     : https://prove2.me/theorems/dd44e409-e57a-40ee-9fdc-c76650b5287f
-- title:
--   Mod GDefs
-- statement:
--   Definitions and structural lemmas for Mod GDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGDefs.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_HilbertClassField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open NumberField IsDedekindDomain Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
def sqD (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)
theorem sqD_sq (d : ℕ) : sqD d ^ 2 = -(d : ℂ) := by
  unfold sqD
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring
def KQ (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqD d}
theorem sqD_isIntegral (d : ℕ) : IsIntegral ℚ (sqD d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [sqD_sq]
scoped instance KQ_numberField (d : ℕ) : NumberField (KQ d) where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (sqD_isIntegral d)
def sqK (d : ℕ) : KQ d := ⟨sqD d, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
abbrev Om (d : ℕ) : IntermediateField (KQ d) ℂ := algebraicClosure (KQ d) ℂ
def Aio (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) : ValuationSubring (Om d) :=
  ((NormedField.valuation (K := ℂ_[l])).valuationSubring).comap
    ((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ))
def InertiaEl {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) : Prop :=
  g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ∈ A.nonunits
end ReciprocityTheory.ChartRestriction.L1


