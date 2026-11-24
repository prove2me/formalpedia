-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:46.604012+00:00
-- url     : https://prove2.me/theorems/bd4635d1-35e8-408a-b172-11425572f6f6
-- title:
--   Algebraic Quantum Determinant
-- statement:
--   Definitions and structural lemmas for Algebraic Quantum Determinant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AlgebraicQuantumDeterminant.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
def mS {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (i j : Fin t) (w : ℂ) : A :=
  ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • qminor E (skip1 i) (skip1 j) w
def nS {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (a q c p : Fin t) (w : ℂ) : A :=
  if a = q ∨ c = p then 0 else
    (((eps a q : ℤ) : ℂ) * ((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((a : ℕ) + (q : ℕ) + (c : ℕ) + (p : ℕ))) •
      qminor E (skip2 (min a q) (max a q)) (skip2 (min c p) (max c p)) w
section Conv
variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
end Conv
section Red
variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
def Core (y η : Fin t → A) (u : ℂ) (p q : Fin t) : Prop :=
  qdet E (u + 1) * (∑ a, ∑ c, η a * y c * nS E a q c p (u - 1)) +
      (∑ j, y j * mS E q j (u + 1)) * (∑ i, η i * mS E i p (u - 1)) =
    (∑ i, ∑ j, η i * y j * mS E i j u) * mS E q p u
end Red
section Trans
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
end Trans
end Formalism.FourierDecayAlt.P.ScalarCastIdentities


