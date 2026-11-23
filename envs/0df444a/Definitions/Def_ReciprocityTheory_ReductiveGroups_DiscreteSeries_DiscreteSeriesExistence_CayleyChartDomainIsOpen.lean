-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:10.763263+00:00
-- url     : https://prove2.me/theorems/e848ce13-b146-4ad0-8890-0a9dbbfd607c
-- title:
--   Cayley Chart Domain Is Open
-- statement:
--   Definitions and structural lemmas for Cayley Chart Domain Is Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CayleyChartDomainIsOpen.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
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
section Mat
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
end Mat
section Ret
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
def slmJi (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  JJ ε * gᴴ * JJ ε
def slmP (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Y - JJ ε * Yᴴ * JJ ε)
def slmX (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  slmP ε ((slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹)
def slmRet (ε : Fin n → Bool) (g0 g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹)
def cayleyChartDomain (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | (slmJi ε g0 * g + 1).det ≠ 0}
def slmV (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  cayleyChartDomain ε g0 ∩ (fun g => (1 - slmX ε g0 g).det) ⁻¹' {0}ᶜ
end Ret
end ReciprocityTheory.ChartRestriction.DS


