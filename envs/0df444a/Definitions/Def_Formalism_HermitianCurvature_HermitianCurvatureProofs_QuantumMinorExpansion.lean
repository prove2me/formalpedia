-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:12.065802+00:00
-- url     : https://prove2.me/theorems/4598e8fd-d4e4-491f-b49b-11dc9829d4ef
-- title:
--   Quantum Minor Expansion
-- statement:
--   Definitions and structural lemmas for Quantum Minor Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/QuantumMinorExpansion.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
section ring
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
def EX (a b : Fin n) : A[X] := C (E a b) + if a = b then X else 0
end ring
section core
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
def Xf (σ : ℤ) (q : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2)) (u : ℂ) (p : Fin (m + 2)) : A :=
  ((-1 : ℤ) ^ (p : ℕ)) • (qminor E (q.succAbove i').succAbove j.succAbove (u + 1) * qminor E q.succAbove p.succAbove u -
      qminor E q.succAbove j.succAbove (u + 1) * qminor E (q.succAbove i').succAbove p.succAbove u) -
    (j.insertNth (α := fun _ => A) 0 (fun x : Fin (m + 1) => (σ * (-1 : ℤ) ^ (x : ℕ)) •
      (qdet E (u + 1) * qminor E (q.succAbove ∘ i'.succAbove) (j.succAbove ∘ x.succAbove) u))) p
end core
section final
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
end final
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion


