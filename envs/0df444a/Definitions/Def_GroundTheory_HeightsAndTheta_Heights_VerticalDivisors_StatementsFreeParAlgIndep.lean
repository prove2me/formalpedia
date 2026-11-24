-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:55.554852+00:00
-- url     : https://prove2.me/theorems/42d3f5c6-2cfa-4db5-a8aa-2f5a5130a489
-- title:
--   Statements Free Par Alg Indep
-- statement:
--   Definitions and structural lemmas for Statements Free Par Alg Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsFreeParAlgIndep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
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
def FreeParAlgIndep.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (L : Type) [Field L] [Algebra k L]
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    [Module.Finite (GenParField k e n) L] (x : Fin n → L),
    Algebra.adjoin (GenParField k e n) (Set.range x) = ⊤ →
    (∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0) →
    ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1 →
    ∀ j₀, x j₀ ≠ 0 →
      Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin k (Set.range fun m => x m * (x j₀)⁻¹))
        (fun p : Fin e × {j : Fin n // j ≠ j₀} =>
          algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1))))
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Vertical


