-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:32:40.152812+00:00
-- url     : https://prove2.me/theorems/322849db-51f0-4896-9e69-91eafc0f8fa7
-- title:
--   Branching Systems
-- statement:
--   Definitions and structural lemmas for Branching Systems, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
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
namespace Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
section Comb
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}
structure Sys {n : ℕ} (L : Fin (n + 1) → ℤ) (P : (Fin n → ℤ) → Prop) : Prop where
  anti : StrictAnti L
  inj : ∀ M, P M → Function.Injective M
  top : P (fun j => L j.castSucc)
  up : ∀ M, P M → ∀ i, (∀ j, M i ≠ L j) → P (Function.update M i (M i + 1))
  down : ∀ M, P M → ∀ i, (∀ j, M i - 1 ≠ L j) → P (Function.update M i (M i - 1))
  fin : ∀ M i, {t : ℤ | P (Function.update M i t)}.Finite
end Comb
section Cap
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
end Cap
end Formalism.FourierDecayAlt.P.BranchingSystems
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr BranchingSystems
end Formalism.FourierDecayAlt.P


