-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:59.830677+00:00
-- url     : https://prove2.me/theorems/921af79c-ffbf-47d5-bb62-b958d9e4aa7b
-- title:
--   Pullback Base Change
-- statement:
--   Definitions and structural lemmas for Pullback Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}
def sectionLinearAt {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') (O : X.Opens) :
    Γ(P, O) →ₗ[Γ(X, O)] Γ(P', O) where
  toFun := θ.app O
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul θ
def IsBaseChangeAt (g : T ⟶ U) (N : U.Modules) (O : U.Opens) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(T, g ⁻¹ᵁ O) Q] (ψ : Γ(N, O) →+ Q),
    (∀ (a : Γ(U, O)) (n : Γ(N, O)), ψ (a • n) = g.app O a • ψ n) →
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q,
      ∀ n, ψ' (Etale.pullbackUnitApp g N O n) = ψ n
end
end GroundTheory.Arith.SchemeCoh


