-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
-- name    : ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:55.127156+00:00
-- url     : https://prove2.me/theorems/089425f9-c53c-4b64-b3d6-aa2fe78184c5
-- title:
--   Emb Mat Mul Vec Injective
-- statement:
--   Definitions and structural lemmas for Emb Mat Mul Vec Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
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
namespace DegAdd
open Matrix NumberField
open scoped ComplexOrder
def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (v : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a j => σ (v j a)
end DegAdd
end ReciprocityTheory.MultiplicativeHeights


