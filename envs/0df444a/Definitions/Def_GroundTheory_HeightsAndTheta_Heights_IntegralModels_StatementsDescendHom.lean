-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:21.831302+00:00
-- url     : https://prove2.me/theorems/be5acce3-5c4e-418a-a076-678d99a42533
-- title:
--   Statements Descend Hom
-- statement:
--   Definitions and structural lemmas for Statements Descend Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsDescendHom.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
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
open CategoryTheory AlgebraicGeometry
noncomputable section
def DescendHom.Statement : Prop :=
  ∀ (T Y Z : Scheme.{0}) (ι : Z ⟶ Y) [IsOpenImmersion ι] (g' : T ⟶ Z) (g : T ⟶ Y) (e : g' ≫ ι = g)
    (F G : Y.Modules)
    (φ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G),
    (∀ V : Y.Opens, V ≤ ι.opensRange → Function.Injective (pullSectionOn g G V)) →
    (∀ V : Y.Opens, V ≤ ι.opensRange → ∀ s : Γ(F, V), ∃ t : Γ(G, V),
      pullSectionOn g G V t = φ.app (g ⁻¹ᵁ V) (pullSectionOn g F V s)) →
    ∃ ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G,
      pullbackHomAlong e ψ = φ
end
end GroundTheory.Heights₂.Heights.Model


