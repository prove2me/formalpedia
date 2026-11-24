-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocB
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:17.04521+00:00
-- url     : https://prove2.me/theorems/cf23d7e0-4f3e-498f-a406-9dfd63950eb7
-- title:
--   Mod Loc B
-- statement:
--   Definitions and structural lemmas for Mod Loc B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
namespace ReciprocityTheory.ChartRestriction.L1
theorem padic_mem_Kur {l : ℕ} [Fact l.Prime] (a : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] a ∈ MaximalUnramifiedExtension l := by
  have hcont : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
  have hclosed : IsClosed ((MaximalUnramifiedExtension l : Set ℂ_[l])) := Subfield.isClosed_topologicalClosure _
  have hpre : IsClosed ((algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l])) := hclosed.preimage hcont
  have hall : Set.range ((↑) : ℚ → ℚ_[l]) ⊆ (algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    rintro _ ⟨q, rfl⟩
    show algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) ∈ MaximalUnramifiedExtension l
    rw [map_ratCast]
    exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) q
  have hmem : a ∈ closure (Set.range ((↑) : ℚ → ℚ_[l])) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr⟩ := Padic.rat_dense (p := l) a hε
    exact ⟨r, ⟨r, rfl⟩, by rw [dist_eq_norm]; exact hr⟩
  exact hpre.closure_subset_iff.mpr hall hmem
def kurAlg (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  ((MaximalUnramifiedExtension l).comap (algebraMap (PadicAlgCl l) ℂ_[l])).toIntermediateField fun a => by
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) a) ∈ MaximalUnramifiedExtension l
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur a
end ReciprocityTheory.ChartRestriction.L1


