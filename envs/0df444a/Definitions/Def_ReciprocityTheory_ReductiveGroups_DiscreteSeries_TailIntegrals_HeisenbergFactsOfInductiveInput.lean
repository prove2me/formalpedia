-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergFactsOfInductiveInput
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:26:46.431947+00:00
-- url     : https://prove2.me/theorems/8a18fae6-7784-4789-9c73-93c1ffba3871
-- title:
--   Heisenberg Facts Of Inductive Input
-- statement:
--   Definitions and structural lemmas for Heisenberg Facts Of Inductive Input, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergFactsOfInductiveInput.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RankOneLeviComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_EIntBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section cont
variable (k r' : ℕ)
end cont
section inner
variable (k r' : ℕ)
def Dx (x : HPar k r') : ℝ := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x))
def Psi (s : Fin (1 + r' + 1) → ℝ) (x : HPar k r') : ℝ :=
  ∏ l : Fin (r' + 1), (Ga k (1 + r') (sc r' l) (Yx k r' x) / Ga k (1 + r') 0 (Yx k r' x)) ^ (-s (sc r' l) / 2)
def Qf (A : ℝ) (s1 : Fin (r' + 1) → ℝ) (μ₁ : Measure (Mt k r')) (c : ℂ) : ℝ≥0∞ :=
  ∫⁻ g, EInt k r' A c (Matrix.of g) * FsE k r' s1 (Matrix.of g) ∂μ₁
end inner
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA


