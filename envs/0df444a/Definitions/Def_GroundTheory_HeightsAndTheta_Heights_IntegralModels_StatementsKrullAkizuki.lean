-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:16.287503+00:00
-- url     : https://prove2.me/theorems/723d3207-8784-4eb9-8f0b-72bfe3b5f3ad
-- title:
--   Statements Krull Akizuki
-- statement:
--   Definitions and structural lemmas for Statements Krull Akizuki, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsKrullAkizuki.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
def TorsionFreeQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (r : ℕ),
      Module.rank R M = r → ∀ a : R, a ≠ 0 →
        Module.length R (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ≤
          (r : ℕ∞) * Module.length R (R ⧸ Ideal.span {a})
def KrullAkizukiQuotientLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L) (b : R), b ≠ 0 →
        IsFiniteLength R (S ⧸ Ideal.span {algebraMap R S b})
end GroundTheory.Heights₂.Heights.Model


