-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:14.404317+00:00
-- url     : https://prove2.me/theorems/9c9ee458-ae94-441e-93de-43423e41ff0d
-- title:
--   Qx Ph Apply
-- statement:
--   Definitions and structural lemmas for Qx Ph Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QxPhApply.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
variable {M M' : GLMod n}
abbrev qx_J (Str : (Fin n → ℤ) → Finset (Fin n → ℤ)) (CF : ColFam M) : Type :=
  Σ j : CF.J, ↥(Str (CF.mu j))
def qx_ph (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M)
    (x : qx_J Str CF) : Matrix M'.ι (TIdx (x.2 : Fin n → ℤ)) ℤ :=
  fun i I => ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I
end Formalism.InvariantFactorPaths.ColumnFamilies


