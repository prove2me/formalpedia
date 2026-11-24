-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:00.065253+00:00
-- url     : https://prove2.me/theorems/f89d43d0-3da8-4802-a084-e2d43d8c432e
-- title:
--   Local Norm Nonneg
-- statement:
--   Definitions and structural lemmas for Local Norm Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalNormNonneg.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
section defeq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
example : (KB.withRR S RR).W = S.W := rfl
example : (KB.withRR S RR).base.Wall = S.base.Wall := rfl
example : (KB.withRR S RR).base.cnt = S.base.cnt := rfl
example : (KB.withRR S RR).base.K = S.base.K := rfl
example : (KB.withRR S RR).base.Ntop = S.base.Ntop := rfl
example : (KB.withRR S RR).base.av = S.base.av := rfl
example : (KB.withRR S RR).base.vol = S.base.vol := rfl
example : (KB.withRR S RR).base.La = S.base.La := rfl
example : (KB.withRR S RR).base.wt = S.base.wt := rfl
example : (KB.withRR S RR).base.f = S.base.f := rfl
example : (KB.withRR S RR).base.r = S.base.r := rfl
example (v : Fin S.f) ε i a p q : (KB.withRR S RR).gramLoc v ε i a p q =
    ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
      RR v ε i a p q := rfl
end defeq
section conv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
variable {S RR}
end conv
end Formalism.FourierDecayAlt.P.PBA


