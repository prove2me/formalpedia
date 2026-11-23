-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:50.39007+00:00
-- url     : https://prove2.me/theorems/4492d6fb-2163-4426-a95b-cef764644056
-- title:
--   Jacquet Rallis Bordered Matrix Normal Form Invariants
-- statement:
--   Definitions and structural lemmas for Jacquet Rallis Bordered Matrix Normal Form Invariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisBorderedMatrixNormalFormInvariants.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
def ev (r : ℕ) (k : Type) [Field k] (i : ℕ) : Fin r → k := fun j => if (j : ℕ) = i then 1 else 0
end GlobalTheory.JR.NormalFormL
namespace GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
end GlobalTheory.JR.NormalFormL
namespace GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
end GlobalTheory.JR.NormalFormL


