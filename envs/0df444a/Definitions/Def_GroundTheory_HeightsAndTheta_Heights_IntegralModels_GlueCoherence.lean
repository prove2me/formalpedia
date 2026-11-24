-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:57.351008+00:00
-- url     : https://prove2.me/theorems/b97e5072-be96-465f-8332-1954e799b542
-- title:
--   Glue Coherence
-- statement:
--   Definitions and structural lemmas for Glue Coherence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GlueCoherence.lean

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
open CategoryTheory Limits AlgebraicGeometry
noncomputable section
set_option linter.unusedSimpArgs false
universe u
variable {T' T Y Z : Scheme.{u}}
def starIso {W U V O' O N : Scheme.{0}} {t : W ⟶ O'} {h : O' ⟶ O} {k : W ⟶ O} (ek : t ≫ h = k)
    {ρ : O ⟶ N} {τ : O ⟶ V} {jU : W ⟶ U} {ρU : U ⟶ N} {jV : W ⟶ V} (e7 : k ≫ ρ = jU ≫ ρU)
    (e8 : k ≫ τ = jV) {E' : N.Modules} {E₀ : V.Modules}
    (ψ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback ρ).obj E') ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback τ).obj E₀)) :
    (Scheme.Modules.pullback jU).obj ((Scheme.Modules.pullback ρU).obj E') ≅
      (Scheme.Modules.pullback jV).obj E₀ :=
  (pullbackCompIso (rfl : jU ≫ ρU = jU ≫ ρU) (Iso.refl ((Scheme.Modules.pullback ρU).obj E'))).symm ≪≫
    pullbackCompIso e7 (Iso.refl _) ≪≫ pullbackIsoAlong ek ψ ≪≫
    (pullbackCompIso e8 (Iso.refl ((Scheme.Modules.pullback τ).obj E₀))).symm
end
end GroundTheory.Heights₂.Heights.Model


