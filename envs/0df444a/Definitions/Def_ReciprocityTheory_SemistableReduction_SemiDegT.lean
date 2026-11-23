-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
-- name    : ReciprocityTheory_SemistableReduction_SemiDegT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:30.888847+00:00
-- url     : https://prove2.me/theorems/ba4a7e12-ab19-4976-98b3-465b92dc6684
-- title:
--   Semi Deg T
-- statement:
--   Definitions and structural lemmas for Semi Deg T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegT.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def matLin {K : Type} [Field K] [NumberField K] {r : ℕ} (Q : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) →ₗ[𝓞 K] (Fin r → K) :=
  (Matrix.mulVecLin Q).restrictScalars (𝓞 K)
def formM {K : Type} [Field K] {r : ℕ} (c : K →+* K) (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) : K :=
  (fun a => c (x a)) ⬝ᵥ (M *ᵥ y)
end ReciprocityTheory.MultiplicativeHeights.SemiPt


