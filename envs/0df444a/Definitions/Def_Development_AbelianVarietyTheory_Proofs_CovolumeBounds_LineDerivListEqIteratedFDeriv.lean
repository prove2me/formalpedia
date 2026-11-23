-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:32.326836+00:00
-- url     : https://prove2.me/theorems/a1741135-7039-4495-aaef-3b1646de6647
-- title:
--   Line Deriv List Eq Iterated FDeriv
-- statement:
--   Definitions and structural lemmas for Line Deriv List Eq Iterated FDeriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LineDerivListEqIteratedFDeriv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped ContDiff
namespace GlobalTheory
section Def
variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
noncomputable def lineDerivList : List E → (E → V) → E → V
  | [], F => F
  | v :: l, F => fun z => lineDeriv 𝕜 (lineDerivList l F) z v
variable {𝕜}
end Def
section Analytic
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
end Analytic
end GlobalTheory


