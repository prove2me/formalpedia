-- Prove2me | Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
-- name    : Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:31.060843+00:00
-- url     : https://prove2.me/theorems/df21d7ba-10bc-4356-8e0e-efc19f4b149f
-- title:
--   Mass Basic
-- statement:
--   Definitions and structural lemmas for Mass Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/MassBasic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.HermitianLatticesTheory
section MassBasicAux
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
end MassBasicAux
end Formalism.HermitianLatticesTheory


