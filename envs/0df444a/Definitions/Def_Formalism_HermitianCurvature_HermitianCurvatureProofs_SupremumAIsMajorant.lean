-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:26.124004+00:00
-- url     : https://prove2.me/theorems/def1e57f-7e7c-4843-8adb-f8496eeb5a10
-- title:
--   Supremum AIs Majorant
-- statement:
--   Definitions and structural lemmas for Supremum AIs Majorant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean

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
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.Jx5
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (G : Sz.Glob (InfinitePlace E)) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
noncomputable def supBS (b s : ℕ) (w : InfinitePlace E) : ℝ :=
  if b = 1 ∧ s = 1 then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w
end
end Formalism.FourierDecayAlt.P.Jx5
namespace Formalism.FourierDecayAlt.P
open Jx5
end Formalism.FourierDecayAlt.P


