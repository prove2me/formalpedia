-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:49.248876+00:00
-- url     : https://prove2.me/theorems/e6a62147-4512-41e2-9143-a92006234f1e
-- title:
--   Is Closed Low Uni
-- statement:
--   Definitions and structural lemmas for Is Closed Low Uni, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
namespace Formalism.DoubleCosetMeasures.P
namespace GeneralLinearIntegersOpenCompact
section Alg
variable {K : Type} [CommRing K]
noncomputable def glR (R : Subring K) (n : ℕ) : Subgroup (GL (Fin n) K) :=
  _root_.UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n
def Dg {n : ℕ} (δ : Fin n → Kˣ) : GL (Fin n) K :=
  ⟨Matrix.diagonal (fun a => (δ a : K)), Matrix.diagonal (fun a => (((δ a)⁻¹ : Kˣ) : K)),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
def ptInv (s : List ℕ) (t : ℕ → Kˣ) : Matrix (Fin s.sum) (Fin s.sum) K :=
  fun a b => if (a : ℕ) = revIn s b then (((t (blk s b))⁻¹ : Kˣ) : K) else 0
end Alg
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end GeneralLinearIntegersOpenCompact
open GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end Formalism.DoubleCosetMeasures.P


