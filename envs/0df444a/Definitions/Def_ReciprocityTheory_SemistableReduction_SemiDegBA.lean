-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
-- name    : ReciprocityTheory_SemistableReduction_SemiDegBA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:35:41.444586+00:00
-- url     : https://prove2.me/theorems/c5fe981c-52f3-4240-8347-d18a2eee5944
-- title:
--   Semi Deg BA
-- statement:
--   Definitions and structural lemmas for Semi Deg BA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
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
def colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)
end ReciprocityTheory.MultiplicativeHeights


