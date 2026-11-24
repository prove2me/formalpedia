-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:12:21.258484+00:00
-- url     : https://prove2.me/theorems/5485d8cf-94f5-47f7-a11d-c3c6ea57c76d
-- title:
--   Capelli Word Sum Expansion
-- statement:
--   Definitions and structural lemmas for Capelli Word Sum Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Loc (m : ℕ∞) (f : Mat k r → E) (g : Mat k r) : Prop :=
  ∃ U : Set (Mat k r), ∃ f' : Mat k r → E, IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ (m : WithTop ℕ∞) f' U ∧
    ∀ x ∈ U, x ∈ GV k r → f x = f' x
def Xa (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Mat k r := hpart1 (Hpk k r) (Matrix.single a b 1)
def Xb (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Mat k r := hpart2 (Hpk k r) (Matrix.single a b 1)
def expand (k r : ℕ) : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → List (ℂ × List (Mat k r))
  | [] => [(1, [])]
  | t :: ts =>
    (expand k r ts).map (fun cw => ((if t.2.1 = t.2.2 then t.1 else 0) * cw.1, cw.2)) ++
    (expand k r ts).map (fun cw => (cw.1, Xa k r t.2.1 t.2.2 :: cw.2)) ++
    (expand k r ts).map (fun cw => (Complex.I * cw.1, Xb k r t.2.1 t.2.2 :: cw.2))
def foldT (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E) : Mat k r → E :=
  (ts.map fun t => Top (Q.EH k r) t.1 t.2.1 t.2.2).foldr (fun T h => T h) f
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion


