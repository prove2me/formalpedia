-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:10.680378+00:00
-- url     : https://prove2.me/theorems/69bd82b6-a6a6-4318-8ad1-99e22cb72381
-- title:
--   Phase Function Derivatives
-- statement:
--   Definitions and structural lemmas for Phase Function Derivatives, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section PartA
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
noncomputable def a_cst (n N : ℕ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin n)).sym N, ((p : Multiset (Fin n)).countPerms : ℝ) *
    ∏ k, ((Multiset.count k (p : Multiset (Fin n))).factorial : ℝ)
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
end Formalism.FourierDecayAlt.P
end PartA
section PartB
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G
end Formalism.FourierDecayAlt.P
end PartB
section PartC
open MeasureTheory
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G
end Formalism.FourierDecayAlt.P
end PartC
section PartD
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
noncomputable def d_M (m : ℕ) (t : ℂ) (x : Fin (m + 1) → ℂ) (q : ℂ × (UT (m + 2) → ℂ)) : Mat (m + 1 + 1) :=
  Mcoord t (strictUpper (redOf m (x, q.2)).2.2.1) (redOf m (x, q.2)).2.2.2
    (Fin.cons q.1 (redOf m (x, q.2)).2.1) (redOf m (x, q.2)).1
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end PartD


