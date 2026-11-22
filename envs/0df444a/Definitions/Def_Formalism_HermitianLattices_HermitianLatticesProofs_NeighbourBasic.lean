-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:03.022747+00:00
-- url     : https://prove2.me/theorems/f907f5b9-796a-4973-90ee-56553faa08a1
-- title:
--   Neighbour Basic
-- statement:
--   Definitions and structural lemmas for Neighbour Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Quot
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
end Quot
section DedekindLFunctions
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
end DedekindLFunctions
section Main
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Main
end Formalism.HermitianLatticesTheory


