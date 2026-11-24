-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.649877+00:00
-- url     : https://prove2.me/theorems/0b3b1073-b21f-4866-bddb-5a48669316fa
-- title:
--   St Weierstrass Polynomial Division
-- statement:
--   Definitions and structural lemmas for St Weierstrass Polynomial Division, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StWeierstrassPolynomialDivision.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
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
open Topology Filter
noncomputable section
def WeierstrassPolynomialDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (c : Fin d → (σ → ℂ) → ℂ) (g : (Option σ → ℂ) → ℂ),
    (∀ j, AnalyticAt ℂ (c j) 0) → (∀ j, c j 0 = 0) → AnalyticAt ℂ g 0 →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * weierstrassPolynomial c x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


