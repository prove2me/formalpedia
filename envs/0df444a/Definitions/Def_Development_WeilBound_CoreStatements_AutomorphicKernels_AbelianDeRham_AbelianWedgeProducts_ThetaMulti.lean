-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:38.592786+00:00
-- url     : https://prove2.me/theorems/8d2c892b-28df-4bf2-a883-5786aba7f6bf
-- title:
--   Theta Multi
-- statement:
--   Definitions and structural lemmas for Theta Multi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianWedgeProducts/ThetaMulti.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace MainStatements.Hodge.Pf.WedgeProjections
section
variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V)
def theta (g : Fin 2 → Module.Dual K V) : Module.Dual K (⋀[K]^2 W) :=
  exteriorPower.pairingDual K W 2 (exteriorPower.ιMulti K 2 ![g 0 ∘ₗ r₁, g 1 ∘ₗ r₂])
end
end MainStatements.Hodge.Pf.WedgeProjections


