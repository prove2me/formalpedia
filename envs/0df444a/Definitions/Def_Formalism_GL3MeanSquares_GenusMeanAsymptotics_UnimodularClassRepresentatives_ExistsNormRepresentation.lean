-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:57.33418+00:00
-- url     : https://prove2.me/theorems/d600b210-01bd-4cee-9397-f0af7e304ded
-- title:
--   Exists Norm Representation
-- statement:
--   Definitions and structural lemmas for Exists Norm Representation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
def Dv (S : Subring K) (π a : K) : Prop := a * π⁻¹ ∈ S
structure IsUnif (S : Subring K) (π : K) : Prop where
  mem : π ∈ S
  fix : star π = π
  ne : π ≠ 0
  unit_or : ∀ s ∈ S, star s = s → IsUnitIn S s ∨ Dv S π s
  rad : ∀ s ∈ S, IsUnitIn S (1 + π * s)
variable {S : Subring K} {π : K}
theorem Dv.star (hS : IsHermSemilocal S) (hπ : IsUnif S π) {a : K} (ha : Dv S π a) :
    Dv S π (star a) := by
  have := hS.star_mem _ ha
  rw [star_mul', star_inv₀, hπ.fix] at this
  exact this
variable {V : Type*} [AddCommGroup V] [Module K V]
end Formalism.HermitianLattices.Ext.L3.U0


