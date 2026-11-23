-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
-- name    : ReciprocityTheory_SemistableReduction_ApproxGraphA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:20.475945+00:00
-- url     : https://prove2.me/theorems/0d927b0c-3c88-4ba5-bc9a-b387a5d37d2f
-- title:
--   Approx Graph A
-- statement:
--   Definitions and structural lemmas for Approx Graph A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxGraphA.lean

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
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0
def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k
def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph


