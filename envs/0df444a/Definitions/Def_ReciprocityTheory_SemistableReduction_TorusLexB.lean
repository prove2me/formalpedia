-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
-- name    : ReciprocityTheory_SemistableReduction_TorusLexB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:10.239804+00:00
-- url     : https://prove2.me/theorems/1a81c992-4b24-4d01-9ed9-ed76e783e912
-- title:
--   Torus Lex B
-- statement:
--   Definitions and structural lemmas for Torus Lex B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
noncomputable def torusFactor (a b : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ a *
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ b
noncomputable def torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) : ℂ :=
  ∏ i, torusPoint θ i ^ s i
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder


