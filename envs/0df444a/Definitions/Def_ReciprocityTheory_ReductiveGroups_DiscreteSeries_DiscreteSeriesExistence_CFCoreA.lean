-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:28.240299+00:00
-- url     : https://prove2.me/theorems/39eeb984-e412-4e17-b391-5dcad77b063b
-- title:
--   CFCore A
-- statement:
--   Definitions and structural lemmas for CFCore A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCoreA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
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
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Straight
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
def IsKLow (ε : Fin n → Bool) (p : Fin n × Fin n) : Prop := p.2 < p.1 ∧ ε p.1 = ε p.2
def lowWord (E : Fin n → Fin n → Module.End ℂ M) (y : M) : List (Fin n × Fin n) → M
  | [] => y
  | p :: l => E p.1 p.2 (lowWord E y l)
def lowWt (μ : Fin n → ℝ) : List (Fin n × Fin n) → Fin n → ℝ
  | [] => μ
  | p :: l => lowWt μ l + root p.1 p.2
def kLowSpan (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (y : M) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, IsKLow ε p) ∧ x = lowWord E y l}
end Straight
section Unitary
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
end Unitary
end ReciprocityTheory.ChartRestriction.DS


