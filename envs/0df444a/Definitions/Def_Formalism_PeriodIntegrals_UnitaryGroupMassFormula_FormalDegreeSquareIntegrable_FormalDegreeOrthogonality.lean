-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:22.818796+00:00
-- url     : https://prove2.me/theorems/eca6b511-18fc-43f7-ae0d-07cd46c9e606
-- title:
--   Formal Degree Orthogonality
-- statement:
--   Definitions and structural lemmas for Formal Degree Orthogonality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/FormalDegreeOrthogonality.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.HCFdeg
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
lemma umat_mem {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : umat g ∈ UJset ε := g.2
def repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ) :
    UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1
  map_mul' g g' := h.2 _ (umat_mem g) _ (umat_mem g')
end PIW.HCFdeg


