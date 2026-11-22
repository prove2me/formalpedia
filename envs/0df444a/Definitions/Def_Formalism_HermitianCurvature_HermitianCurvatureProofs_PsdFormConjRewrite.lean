-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:08.169464+00:00
-- url     : https://prove2.me/theorems/e2d14f79-8786-468f-86f2-8954ea88355e
-- title:
--   Psd Form Conj Rewrite
-- statement:
--   Definitions and structural lemmas for Psd Form Conj Rewrite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsdFormConjRewrite.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx1
section Tower
variable {E : Type} [Field E]
def Cnd (Sg : ℕ → ℕ → Finset E) (p : TB.Pt E) : Prop :=
  ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ Sg (TB.blockStart p k) (p[k]'hk).1
end Tower
section Agree
variable {α : Type}
end Agree
end Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


