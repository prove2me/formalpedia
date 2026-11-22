-- Prove2me | Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
-- name    : Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:56.226456+00:00
-- url     : https://prove2.me/theorems/930347cf-4bef-4a63-b41c-18562968ac3e
-- title:
--   Covolume Dual
-- statement:
--   Definitions and structural lemmas for Covolume Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/CovolumeDual.lean

import Definitions.Def_Formalism_LatticeTheta_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped RealInnerProductSpace
noncomputable section
namespace Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
lemma covolDual_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m
end Formalism.H


