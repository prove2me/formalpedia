-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepCompRedOf
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepCompRedOf
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:54:40.60381+00:00
-- url     : https://prove2.me/theorems/ee77fdfd-1883-47c7-a920-239830450cbd
-- title:
--   URep Comp Red Of
-- statement:
--   Definitions and structural lemmas for URep Comp Red Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ContinuousRepresentations/URepCompRedOf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
lemma inUJ_of_mem_K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  simp only [Kset, inUJ, Set.mem_setOf_eq] at *
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]
def cr2K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_K ε hg⟩, hg⟩
def compactRepOfUnitaryDifferential (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (τ : KG ε →* unitary (H →L[ℂ] H)) (hτ : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
      (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0) : KRep ε :=
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  { V := H, τ := τ, cont := hτ, dτ := dτ, hasDeriv := hd }
end ReciprocityTheory.ChartRestriction.DS.HW


