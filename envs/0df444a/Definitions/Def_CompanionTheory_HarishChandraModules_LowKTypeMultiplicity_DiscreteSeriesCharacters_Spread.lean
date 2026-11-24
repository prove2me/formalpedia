-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_Spread
-- name    : CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_Spread
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T16:51:38.750103+00:00
-- url     : https://prove2.me/theorems/6bc872d2-5f1a-454d-8602-aaba008adf30
-- title:
--   Spread
-- statement:
--   Definitions and structural lemmas for Spread, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/DiscreteSeriesCharacters/Spread.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace CompanionTheory.D.DSIC
open Formalism.REAL Formalism.FourierDecayAlt.Q
section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def adjPairs (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Subalgebra ℂ (Pr V) where
  carrier := {p | ∀ x y, ⟪p.1 x, y⟫_ℂ = ⟪x, p.2.unop y⟫_ℂ}
  mul_mem' := fun {p q} hp hq x y => by
    show ⟪p.1 (q.1 x), y⟫_ℂ = ⟪x, q.2.unop (p.2.unop y)⟫_ℂ
    rw [hp, hq]
  add_mem' := fun {p q} hp hq x y => by
    show ⟪p.1 x + q.1 x, y⟫_ℂ = ⟪x, p.2.unop y + q.2.unop y⟫_ℂ
    rw [inner_add_left, inner_add_right, hp, hq]
  algebraMap_mem' := fun c x y => by
    show ⟪c • x, y⟫_ℂ = ⟪x, (starRingEnd ℂ c) • y⟫_ℂ
    rw [inner_smul_left, inner_smul_right]
def fstP (V : Type) [AddCommGroup V] [Module ℂ V] : Pr V →ₐ[ℂ] Module.End ℂ V :=
  { (RingHom.fst (Module.End ℂ V) (Module.End ℂ V)ᵐᵒᵖ : Pr V →+* Module.End ℂ V) with commutes' := fun _ => rfl }
end
end CompanionTheory.D.DSIC


