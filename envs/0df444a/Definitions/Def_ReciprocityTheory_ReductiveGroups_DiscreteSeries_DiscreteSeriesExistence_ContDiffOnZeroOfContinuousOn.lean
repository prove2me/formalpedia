-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:24.429996+00:00
-- url     : https://prove2.me/theorems/182bedfd-35e6-4b90-acc3-e1a66ac1cdaa
-- title:
--   Cont Diff On Zero Of Continuous On
-- statement:
--   Definitions and structural lemmas for Cont Diff On Zero Of Continuous On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/ContDiffOnZeroOfContinuousOn.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS
section Curve
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
end Curve
section GenG
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
def slmG (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) : X →L[ℝ] E :=
  ∑ i, ((C i).comp fd).smulRight (w i)
end GenG
section GenM
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def slmEnt (k b : Fin n) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) k)
def slmC (i : Fin n × Fin n × Fin n × Bool) :=
  if i.2.2.2 then Complex.reCLM.comp (slmEnt i.2.2.1 i.2.1) else Complex.imCLM.comp (slmEnt i.2.2.1 i.2.1)
def slmc (m : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (i : Fin n × Fin n × Fin n × Bool)
    (q : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if i.2.2.2 then m q i.1 i.2.2.1 else Complex.I * m q i.1 i.2.2.1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end GenM
section Lp
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
end Lp
end ReciprocityTheory.ChartRestriction.DS


