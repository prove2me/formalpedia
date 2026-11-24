-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:42.665305+00:00
-- url     : https://prove2.me/theorems/0b7f646c-7659-48ec-b41b-4a05c30b8b9e
-- title:
--   Statements Pair Cone Lines Indep
-- statement:
--   Definitions and structural lemmas for Statements Pair Cone Lines Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsPairConeLinesIndep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreClosureModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
def PairConeLinesIndep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (Φ : Type) [Field Φ] [Algebra Ω Φ] (K : Type) (N : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E),
    LinearIndependent Ω ψ → ∀ (t : Fin N → Φ), AlgebraicIndependent Ω t → ∀ g : Φ, g ≠ 0 →
      AlgebraicIndependent
        (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
        (Sum.elim (fun i : Fin N => C (∑ j, t j * algebraMap Ω Φ (ψ i (e j))) * X (some none))
          (fun _ : Unit => (C g * X none : MvPolynomial (Option (Option K)) Φ)))
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


