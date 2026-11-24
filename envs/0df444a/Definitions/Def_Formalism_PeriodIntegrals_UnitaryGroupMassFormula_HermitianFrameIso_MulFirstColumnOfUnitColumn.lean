-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameIso_MulFirstColumnOfUnitColumn
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameIso_MulFirstColumnOfUnitColumn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:39.194681+00:00
-- url     : https://prove2.me/theorems/650102b5-269c-405f-960f-454a642dcde4
-- title:
--   Mul First Column Of Unit Column
-- statement:
--   Definitions and structural lemmas for Mul First Column Of Unit Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameIso/MulFirstColumnOfUnitColumn.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.GaugeFrame
open Matrix Formalism.UG
section Gen
variable {S : Type} [CommRing S] (τ : S →+* S)
variable {m : ℕ}
def low (K : Matrix (Fin (m + 1)) (Fin (m + 1)) S) : Matrix (Fin m) (Fin m) S :=
  K.submatrix Fin.succ Fin.succ
def blk (c : S) (A : Matrix (Fin m) (Fin m) S) : Matrix (Fin (m + 1)) (Fin (m + 1)) S :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i
end Gen
end PI.UnitaryGroupMassFormula.GaugeFrame


