-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_LinEmbedSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:32.851648+00:00
-- url     : https://prove2.me/theorems/eba35ba2-8d9c-4625-8707-47c17aa4bc98
-- title:
--   Lin Embed St
-- statement:
--   Definitions and structural lemmas for Lin Embed St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LinEmbedSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
def blockLinSubst {F : Type*} [Field F] {K K' : Type*} {ι : K → Type*} {ι' : K' → Type*} [∀ k, Fintype (ι k)]
    (e : K' ≃ K) (A : ∀ k', ι' k' → ι (e k') → F) : MRingOver F ι' →ₐ[F] MRingOver F ι :=
  aeval fun q => ∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩
def LinEmbed.Statement : Prop :=
  ∀ (F : Type) [Field F] (K K' : Type) [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type)
    [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] (e : K' ≃ K) (A : ∀ k', ι' k' → ι (e k') → F),
    (∀ k', Function.Injective (Matrix.of (A k')).mulVec) →
    ∀ (I : IFamily F ι) (I' : IFamily F ι'), IsFieldIntersection I → IsFieldIntersection I' →
      ∀ (V : Ideal (MRingOver F ι)) (d : ℕ) (L : Fin d → K → ℤ), IsProjVarF V d →
        I' (V.comap (blockLinSubst e A).toRingHom) d (fun j => L j ∘ e) = I V d L
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


