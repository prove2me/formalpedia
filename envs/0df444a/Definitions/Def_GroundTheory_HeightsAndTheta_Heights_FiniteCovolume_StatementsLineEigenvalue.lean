-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineEigenvalue
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineEigenvalue
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:05.563179+00:00
-- url     : https://prove2.me/theorems/5abf69e6-22cb-5421-bfef-fb8060a30b80
-- title:
--   Statements Line Eigenvalue
-- statement:
--   Definitions and structural lemmas for Statements Line Eigenvalue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsLineEigenvalue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
def LineEigenvalue.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → ∃ β : lineStab h v x₀ → (InfinitePlace E → ℂˣ), Continuous β ∧
    ∀ (p : lineStab h v x₀) (w : InfinitePlace E),
      (((p : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
        (β p w : ℂ) • vecAt v x₀ w
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


