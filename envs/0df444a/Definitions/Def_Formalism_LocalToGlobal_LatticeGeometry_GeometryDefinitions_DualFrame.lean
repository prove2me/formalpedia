-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
-- name    : Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:00.914543+00:00
-- url     : https://prove2.me/theorems/d1099ecf-f086-460d-88a3-3bfbc4e5dc20
-- title:
--   Dual Frame
-- statement:
--   Definitions and structural lemmas for Dual Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
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
open Module Matrix
namespace Formalism.L2.Geo.Def.G1
section Frame
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
  [IsScalarTower R K V]
end Frame
section Coord
variable {K : Type} [Field K] [StarRing K]
def IsFrame {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K) : Prop :=
  ∀ a b, ∑ i, g i a * ∑ c, star (w i c) * H c b = if a = b then 1 else 0
end Coord
end Formalism.L2.Geo.Def.G1


