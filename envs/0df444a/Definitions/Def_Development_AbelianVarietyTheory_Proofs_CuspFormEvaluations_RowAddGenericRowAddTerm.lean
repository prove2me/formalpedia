-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:27.841478+00:00
-- url     : https://prove2.me/theorems/0b1676d5-a9e1-42fe-8421-03bea1396690
-- title:
--   Row Add Generic Row Add Term
-- statement:
--   Definitions and structural lemmas for Row Add Generic Row Add Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory
section RowAdd
variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]
noncomputable def rowAddTerm (K : Type*) [Field K] (u w : ι → σ) (s : σ) : MvPolynomial σ K :=
  ∑ k, if s = w k then X (u k) else 0
noncomputable def rowAddGeneric (u w : ι → σ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun s => Polynomial.C (X s) + Polynomial.X * Polynomial.C (rowAddTerm K u w s)
end RowAdd
end GlobalTheory


