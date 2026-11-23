-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
-- name    : ReciprocityTheory_SemistableReduction_ApproxBasisA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:19.855288+00:00
-- url     : https://prove2.me/theorems/fc47784d-4957-4b1c-842c-3f91e7e27296
-- title:
--   Approx Basis A
-- statement:
--   Definitions and structural lemmas for Approx Basis A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
abbrev ApproxPosIdx (r p : ℕ) := {j : Fin r // (j : ℕ) < p}
def approxPadPos {r p : ℕ} (x : ApproxPosIdx r p → ℂ) : Fin r → ℂ :=
  fun j => if h : (j : ℕ) < p then x ⟨j, h⟩ else 0
end ReciprocityTheory.MultiplicativeHeights


