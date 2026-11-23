-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:55.583403+00:00
-- url     : https://prove2.me/theorems/35b26a09-e75c-4d54-b5cf-7aa331b6d139
-- title:
--   Koszul Exact Of Graded Regular
-- statement:
--   Definitions and structural lemmas for Koszul Exact Of Graded Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfGradedRegular.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KosGr
section Abstract
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
def dd (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (r : ℕ) (c : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (j : ℕ) : V j :=
  ∑ i : Fin g, if i.val < r ∧ i ∉ I then
    (-1 : K) ^ (I.filter (· < i)).card • x i j (c (insert i I) (j + 1)) else 0
end Abstract
end GlobalTheory.KeyKa.KosGr
end


