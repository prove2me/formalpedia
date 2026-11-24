-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:23:22.859608+00:00
-- url     : https://prove2.me/theorems/02f570d6-ddce-4b0c-b02d-4a848c775895
-- title:
--   Heisenberg Levi Conjugation Measure
-- statement:
--   Definitions and structural lemmas for Heisenberg Levi Conjugation Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section Herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
end Herm
def i0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := eI k (1 + r') (a0 r')
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := esI k (1 + r') (a0 r')
def res (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (levPos k 1 r' j)
def coord (k r' : ℕ) (g : Mat k (1 + r')) : HPar k r' :=
  (fun j => g (levPos k 1 r' j) (iL k r'), (g (i0 k r') (iL k r')).im)
def heisT (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x
end Formalism.FourierDecayAlt.P.B2x5
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


