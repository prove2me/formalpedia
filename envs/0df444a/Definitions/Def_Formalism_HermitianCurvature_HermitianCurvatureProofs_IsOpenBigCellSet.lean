-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:31.333601+00:00
-- url     : https://prove2.me/theorems/ac1296dc-2063-48e6-b27c-653c10a8e461
-- title:
--   Is Open Big Cell Set
-- statement:
--   Definitions and structural lemmas for Is Open Big Cell Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IsOpenBigCellSet.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def V0 (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) : Set (Mat k r) :=
  {x | 0 < Gf k r D.z D.z' x} ∩ ⋂ l ∈ L, {x | Dmin k r D.z D.z' x l ≠ 0}
end Formalism.FourierDecayAlt.P.MinorPolynomials


