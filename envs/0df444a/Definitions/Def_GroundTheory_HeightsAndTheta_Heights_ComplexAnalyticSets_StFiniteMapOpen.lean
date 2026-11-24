-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:10.141086+00:00
-- url     : https://prove2.me/theorems/acbdfcf3-6c6d-490e-ae14-fe6c11fb4c5d
-- title:
--   St Finite Map Open
-- statement:
--   Definitions and structural lemmas for St Finite Map Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteMapOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
def FiniteMapOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    J.IsPrime → Function.Injective ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)) →
    ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite →
    ∀ x ∈ zeroLocus J, ∀ U ∈ 𝓝 x,
      (fun z : Fin n → ℂ => fun i => eval z (p i)) '' (zeroLocus J ∩ U) ∈
        𝓝 (fun i => eval x (p i))
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


