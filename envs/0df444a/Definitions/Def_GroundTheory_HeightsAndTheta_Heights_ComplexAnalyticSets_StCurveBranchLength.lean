-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveBranchLength
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveBranchLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:22.531978+00:00
-- url     : https://prove2.me/theorems/a353623d-3aca-46dc-ac63-69ceac92b3c2
-- title:
--   St Curve Branch Length
-- statement:
--   Definitions and structural lemmas for St Curve Branch Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveBranchLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
def CurveBranchLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (c : Fin m → VarBranch I 1 q) (ord : Fin m → ℕ),
    IsRadicalAt I q →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)) →
      localMult (I ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q)) = ∑ b, ord b
end
end GroundTheory.Heights₂.Heights


