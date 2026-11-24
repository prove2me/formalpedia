-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:08:31.100365+00:00
-- url     : https://prove2.me/theorems/15054e9e-eb2f-48a5-b736-0611b5cbe8b5
-- title:
--   Jf CVUnder Int Of Parts
-- statement:
--   Definitions and structural lemmas for Jf CVUnder Int Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
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
namespace Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
section WS
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def wsum (L : List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) : E :=
  (L.map fun cw => cw.1 • Rw cw.2 f g).sum
def WOK (L : List (ℂ × List (Mat k r))) (j : ℕ) : Prop :=
  ∀ cw ∈ L, (∀ X ∈ cw.2, inLie k r X) ∧ cw.2.length ≤ j
def stepL (k r : ℕ) (u : ℂ) (c d : Fin (2 * r + k + 1)) (L : List (ℂ × List (Mat k r))) :
    List (ℂ × List (Mat k r)) :=
  (if c = d then L.map (fun cw => (u * cw.1, cw.2)) else []) ++
    ((L.map fun cw => (cw.1, Xa k r c d :: cw.2)) ++
      (L.map fun cw => (cw.1, Xb k r c d :: cw.2)).map fun cw => (Complex.I * cw.1, cw.2))
def foldL (k r : ℕ) (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) : List (ℂ × List (Mat k r)) :=
  ts.foldr (fun t L => stepL k r t.1 t.2.1 t.2.2 L) [(1, [])]
def tsOf {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin t)) :
    List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
  List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), p (σ j), q j)
def qmL (k r : ℕ) {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) : List (ℂ × List (Mat k r)) :=
  (Finset.univ.toList : List (Equiv.Perm (Fin t))).flatMap fun σ =>
    (foldL k r (tsOf p q u σ)).map fun cw => ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * cw.1, cw.2)
def unitL (L : List (ℂ × List (Mat k r))) : List (ℂ × List (Mat k r)) :=
  L.map fun cw => ((((cw.2.map nz).prod : ℝ) : ℂ) * cw.1, cw.2.map nrm)
end WS
end Formalism.FourierDecayAlt.P.JFxB


