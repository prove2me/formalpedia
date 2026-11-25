-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:36.397212+00:00
-- url     : https://prove2.me/theorems/f706015c-026f-52df-8f74-bb50df926357
-- title:
--   Heisenberg Level Minors
-- statement:
--   Definitions and structural lemmas for Heisenberg Level Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLevelMinors.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def NNMinor : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)
def NNVol : Prop :=
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      μ {x | gN (Matrix.of x : Mat k r) ≤ R} ≤ ENNReal.ofReal (C * R ^ (((2 * r + k + 1 : ℕ) : ℝ) ^ 2))
variable {k r : ℕ}
section vol
open Formalism.FourierDecayAlt.P.B2x6
variable {k r' : ℕ}
end vol
def heisM (k r' : ℕ) (x : Formalism.FourierDecayAlt.B2.HPar k r') : Mt k (1 + r') := Formalism.FourierDecayAlt.B2.heis0 k r' x
def NNMinorL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)), IsCompact K →
    (∀ g ∈ K, g ∈ GV k r ∧ ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ C : ℝ, ∀ g ∈ K, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ n' ∈ Formalism.QuantumDeterminants.Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (3 * r)
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors


