-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:49.985843+00:00
-- url     : https://prove2.me/theorems/9ab79f78-cfad-4722-94f0-bffa8737fc26
-- title:
--   St Germ Weierstrass Preparation
-- statement:
--   Definitions and structural lemmas for St Germ Weierstrass Preparation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermWeierstrassPreparation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
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
def weierstrassPolynomial {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (x : Option σ → ℂ) : ℂ :=
  x none ^ d + ∑ j : Fin d, c j (fun i => x (some i)) * x none ^ (j : ℕ)
def WeierstrassPreparation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (e : (Option σ → ℂ) → ℂ) (c : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ e 0 ∧ e 0 ≠ 0 ∧ (∀ j, AnalyticAt ℂ (c j) 0) ∧ (∀ j, c j 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = e x * weierstrassPolynomial c x
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


