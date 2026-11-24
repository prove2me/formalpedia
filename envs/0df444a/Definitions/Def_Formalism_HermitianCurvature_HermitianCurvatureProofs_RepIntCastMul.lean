-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:09:51.232815+00:00
-- url     : https://prove2.me/theorems/dc6b1e82-d9f3-4e40-ac97-a2b257e52a3f
-- title:
--   Rep Int Cast Mul
-- statement:
--   Definitions and structural lemmas for Rep Int Cast Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1)
abbrev VV (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := List (Ix k r) → (Mat k r → E)
abbrev AA (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (VV k r E)
def ell (x : Ix k r) : AA k r E := LinearMap.funLeft ℂ (Mat k r → E) (fun w : List (Ix k r) => w ++ [x])
def Lf (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin (2 * r + k + 1)) : AA k r E :=
  ell (a, b)
def Rep (d : ℕ) (a : AA k r E) : Prop :=
  ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
    ∀ Φ w, a Φ w = (L.map fun p => p.1 • Φ (w ++ p.2)).sum
section RepLemmas
end RepLemmas
def HC (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop a b f)
def HL (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop a b f g = Eop a b f₂ g
def HA (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), CkOn 1 (GV k r) f → CkOn 1 (GV k r) f₂ → ∀ g ∈ GV k r,
    Eop a b (fun x => f x + f₂ x) g = Eop a b f g + Eop a b f₂ g
def HS (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (c : ℂ) (f : Mat k r → E), CkOn 1 (GV k r) f → ∀ g ∈ GV k r, Eop a b (fun x => c • f x) g = c • Eop a b f g
def HGl (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b c d (f : Mat k r → E), CkOn 2 (GV k r) f → ∀ g ∈ GV k r,
    Eop a b (Eop c d f) g - Eop c d (Eop a b f) g =
      (if b = c then Eop a d f g else 0) - (if d = a then Eop c b f g else 0)
def Fw (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (w : List (Ix k r))
    (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun x φ => Eop x.1 x.2 φ) f
def Phi (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (f : Mat k r → E) :
    VV k r E := fun w => Fw Eop w f
def ev (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (a : AA k r E)
    (f : Mat k r → E) : Mat k r → E := a (Phi Eop f) []
section Words
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Words
section Values
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
end Values
end Formalism.FourierDecayAlt.P.JFxE


