-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:44.229981+00:00
-- url     : https://prove2.me/theorems/f804b456-c0f1-4724-942f-54ca689cfb62
-- title:
--   Rel Base Change St
-- statement:
--   Definitions and structural lemmas for Rel Base Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RelBaseChangeSt.lean

import Mathlib
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
open MvPolynomial
def RelBaseChange.Statement : Prop :=
  ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (σ τ : Type) (g : σ → MvPolynomial τ F),
    (RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)).map
        (MvPolynomial.map (algebraMap F F')) =
      RingHom.ker (aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) :
        MvPolynomial σ F' →ₐ[F'] MvPolynomial τ F')
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


