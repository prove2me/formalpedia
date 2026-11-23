-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:46.70781+00:00
-- url     : https://prove2.me/theorems/feca1eb1-bbec-46d4-b96e-f49e9baddbba
-- title:
--   Cas On Low Statement
-- statement:
--   Definitions and structural lemmas for Cas On Low Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/CasOnLowStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def vogSq (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + (2 : ℝ) • rhoC ε)
def VogDropStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam →
    ∀ a b : Fin n, a < b → ε a ≠ ε b →
      vogSq ε (lowK ε lam - root a b) < vogSq ε (lowK ε lam)
def CasOnLowStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D),
    IsURepOn (UJset ε) σ → IsDerivedOn ε σ D E → IsInfUnitary ε E → StdGap ε lam →
    IsKIrrHW ε E (lowK ε lam) V →
    (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k (v : H)) →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ S : Submodule ℂ D, ¬ IsKIrrHW ε E (lowK ε lam - root a b) S) →
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v
end ReciprocityTheory.ChartRestriction.DS.Lap


