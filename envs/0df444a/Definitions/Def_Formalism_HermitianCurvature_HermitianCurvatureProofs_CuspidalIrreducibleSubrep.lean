-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:31.467849+00:00
-- url     : https://prove2.me/theorems/d3aa1127-f470-4537-8619-ea3451555cf5
-- title:
--   Cuspidal Irreducible Subrep
-- statement:
--   Definitions and structural lemmas for Cuspidal Irreducible Subrep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
noncomputable def geoS {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ j ∈ Finset.range n, t ^ (n - 1 - j) • (-X) ^ j
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


