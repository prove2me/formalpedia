-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:43.256663+00:00
-- url     : https://prove2.me/theorems/8b6f1a6e-fc32-4579-b880-8650dada16ce
-- title:
--   Kur Defs
-- statement:
--   Definitions and structural lemmas for Kur Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KurDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
section Concrete
variable (l : ℕ) [Fact l.Prime]
def muP : Set ℂ_[l] := {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}
def Rmu : Subring ℂ_[l] := Subring.closure (muP l)
def Kmu : Subfield ℂ_[l] := Subfield.closure (muP l)
def Tch : Set ℂ_[l] := insert 0 (muP l)
end Concrete
structure FrobField (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop where
  prime : l.Prime
  norm_l : ‖(l : K)‖ < 1
  isom : ∀ x : K, ‖σ x‖ = ‖x‖
  frob : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖
  discrete : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖
def ResClosed (K : Type) [NormedField K] (l : ℕ) : Prop :=
  ∀ P : Polynomial K, P.Monic → 0 < P.natDegree → (∀ i, ‖P.coeff i‖ ≤ 1) →
    ∃ x : K, ‖x‖ ≤ 1 ∧ ‖P.eval x‖ ≤ ‖(l : K)‖
end ReciprocityTheory.ChartRestriction.L1


