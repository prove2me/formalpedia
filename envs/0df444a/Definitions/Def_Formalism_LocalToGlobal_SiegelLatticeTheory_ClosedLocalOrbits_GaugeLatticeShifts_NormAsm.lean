-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:35.382779+00:00
-- url     : https://prove2.me/theorems/8dda994a-5dd6-4124-b901-3bf5eb22ec8b
-- title:
--   Norm Asm
-- statement:
--   Definitions and structural lemmas for Norm Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
namespace Formalism.L2.SG.NormCut
section Asm
variable {I : Type*} [Group I] [Fintype I]
def gamOf (U : Set I) (p : I → ℂ) (x : I) : ℂ := ((Nat.card U : ℂ))⁻¹ * ∑ y : I, p (y * x * y⁻¹)
def Zs {τ K Q : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (S : Set τ) (intersection_update_fsHerm_neg_one : τ → Q) (ιt : τ → I)
    (a : τ → K) (q : Q) (i : I) : K :=
  ∑' t, if t ∈ S ∧ intersection_update_fsHerm_neg_one t = q ∧ ιt t = i then a t else 0
end Asm
section Inv
variable {I : Type*} [Group I] [Fintype I]
def fForm (p : I → ℂ) (Gm : I → I → ℂ) (x y : I) : ℂ :=
  ∑ i, ∑ j, conj (p (x⁻¹ * i * y)) * p (x⁻¹ * j * y) * Gm i j
end Inv
section Main
variable {I : Type} [Group I] [Fintype I]
end Main
end Formalism.L2.SG.NormCut


