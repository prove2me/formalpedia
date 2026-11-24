-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:14.045619+00:00
-- url     : https://prove2.me/theorems/e0d22511-2b14-40fe-bd43-3803df4bd6af
-- title:
--   Statements Sec Point Separable
-- statement:
--   Definitions and structural lemmas for Statements Sec Point Separable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsSecPointSeparable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
def SecPointSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (L : Type) [Field L] [Algebra k L]
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    [Module.Finite (GenParField k e n) L] (x : Fin n → L),
    Algebra.adjoin (GenParField k e n) (Set.range x) = ⊤ →
    (∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0) →
    ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1 →
    (∀ j₀, x j₀ ≠ 0 →
      Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable (GenParField k e n) L
section Inhabitants
abbrev chartPointInv : Fin 1 → GenParField ℚ 0 1 := fun _ => (genPar ℚ 0 1 (.inr 0))⁻¹
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Vertical


