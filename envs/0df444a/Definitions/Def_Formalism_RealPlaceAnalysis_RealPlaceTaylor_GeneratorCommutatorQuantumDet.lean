-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:13.177795+00:00
-- url     : https://prove2.me/theorems/bf5fc078-54eb-46de-8a5e-f549b1aca8b2
-- title:
--   Generator Commutator Quantum Det
-- statement:
--   Definitions and structural lemmas for Generator Commutator Quantum Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
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
namespace Formalism.REAL
def cycleToLast (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) :=
  (Fin.revPerm.trans (Fin.cycleRange j.rev).symm).trans Fin.revPerm
def extendLast {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquivLast.trans (Equiv.optionCongr τ)).trans finSuccEquivLast.symm
def lastColumnSplit (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cycleToLast m p.1 * extendLast p.2
end Formalism.REAL


