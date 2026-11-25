-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_WigMap
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:04.515208+00:00
-- url     : https://prove2.me/theorems/95a9182b-b7d8-5db9-8e3a-2a4cc18d6bda
-- title:
--   Wig Map
-- statement:
--   Definitions and structural lemmas for Wig Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/WigMap.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace GlobalTheory.WigSh
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
def WigMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {V₁ V₂ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (π₂ : Q.Mx k r → (V₂ →L[ℂ] V₂)) (π₁ : Q.Mx k r → (V₁ →L[ℂ] V₁))
    (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) : Prop :=
  (∃ (t : ℕ) (q : Fin t → MvPolynomial (Fin (2 * r + k + 1) ⊕ Fin (2 * r + k + 1)) ℂ) (Lm : Fin t → (V₂ →L[ℂ] V₁)),
      (∀ i, (q i).totalDegree ≤ d) ∧
        ∀ ω, A ω = ∑ i, MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q i) • Lm i) ∧
    (∀ h ∈ UWset k r z, ∀ ω, (A (h *ᵥ ω)).comp (π₂ h) = (π₁ h).comp (A ω)) ∧
    (∀ (t : ℝ) (ω : Fin (2 * r + k + 1) → ℂ), A ((t : ℂ) • ω) = ((t : ℂ) ^ d) • A ω) ∧
    ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ‖A ω‖ ^ 2 ≤ (herm (Hpk k r) ω ω).re ^ d
def omg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  D.prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a)
end GlobalTheory.WigSh


