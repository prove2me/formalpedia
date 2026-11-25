-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:47.890104+00:00
-- url     : https://prove2.me/theorems/67742789-1855-493b-963a-a10ee6fba773
-- title:
--   PBGHead V
-- statement:
--   Definitions and structural lemmas for PBGHead V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHeadV.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
section mirror
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
def rv (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := Fin.rev p
def ep (p : Fin (2 * r + k + 1)) : ℂ := (-1 : ℂ) ^ (p : ℕ)
def Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (p q : Fin (2 * r + k + 1)) : A :=
  -((ep p * ep q) • E (rv q) (rv p))
end mirror
def HeadAlgV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ) (hm : m + 2 ≤ r)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (d ℓ : ℂ),
    Formalism.REAL.GlRel E → C3.RightRuleFn k r z' E La → W.det ≠ 0 → d ≠ 0 →
    (∀ (b : Fin (m + 1)) (x : A), La (E (esI k r ⟨b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * x) =
      (d * W⁻¹ b (Fin.last m)) • La x) →
    (∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), y ⟨a, by omega⟩ q =
      if h : r + k < q.val ∧ 2 * r + k - q.val < m + 1 then W a ⟨2 * r + k - q.val, h.2⟩ else 0) →
    (∀ q : Fin (2 * r + k + 1), y ⟨m + 1, by omega⟩ q = if q.val = 2 * r + k - (m + 1) then d else 0) →
    (W.det * d)⁻¹ • La (C3.AAv k r E y (m + 2) hm ℓ) =
      W.det⁻¹ • La (C3.AAv k r E y (m + 1) (by omega) ℓ *
          (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) -
        (d * W.det⁻¹) • La (C3.AAv k r E y m (by omega) ℓ)
end Formalism.FourierDecayAlt.P.PBG


