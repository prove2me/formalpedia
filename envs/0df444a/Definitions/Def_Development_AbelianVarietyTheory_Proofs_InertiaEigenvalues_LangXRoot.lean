-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangXRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:29.600248+00:00
-- url     : https://prove2.me/theorems/836f0e81-525d-4805-914c-ee7939a5bc9c
-- title:
--   Lang XRoot
-- statement:
--   Definitions and structural lemmas for Lang XRoot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LangXRoot.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PMonE.LangIsogenyConstruction
open Polynomial
section Lang
variable {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
noncomputable def langX (q : ℕ) (a : ℕ → k) : ℕ → k[X]
  | 0 => C (a 0) * X ^ q
  | (i + 1) => (langX q a i) ^ q + C (a (i + 1)) * X ^ q
def langQ (U : Submodule k V) (F : V → V) (v : V) (r : ℕ) : Prop :=
  ∃ u ∈ U, ∃ a : ℕ → k, F^[r] v = u + ∑ i ∈ Finset.range r, a i • F^[i] v
end Lang
end GlobalTheory.PMonE.LangIsogenyConstruction


