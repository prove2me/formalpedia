-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:36.818361+00:00
-- url     : https://prove2.me/theorems/ddf6d935-1a27-45fe-928c-fe9a9f7f553e
-- title:
--   Extract Free Fill Matrix
-- statement:
--   Definitions and structural lemmas for Extract Free Fill Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnfoldingEquivalence/ExtractFreeFillMatrix.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
def base {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (l : Fin (n + c)) (s : Fin (n' + (c + 1))) : k :=
  if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0
def Q {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ v, x (inX k n' (c + 1) v) = inX k n c (xj v)) ∧ (0 < c → x (eN k (n' + (c + 1)) n') = eN k (n + c) n) ∧
    ∀ j, 1 ≤ j → j < c → x (eN k (n' + (c + 1)) (n' + j)) - eN k (n + c) (n + j) ∈ Ufl k n c j
def fe {n' n c : ℕ} (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : FC n' (c + 1) n c → k :=
  fun p => x (Pi.single p.1.2 1) p.1.1
end PI.UnfoldEquiv.UnitaryGroupMassFormula


