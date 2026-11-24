-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:17.393095+00:00
-- url     : https://prove2.me/theorems/4bc44b09-7483-4ea6-b6a9-702380584026
-- title:
--   St Germ Weierstrass Division
-- statement:
--   Definitions and structural lemmas for St Germ Weierstrass Division, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermWeierstrassDivision.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
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
def pointWithLast {σ : Type} (z : σ → ℂ) (t : ℂ) : Option σ → ℂ
  | none => t
  | some i => z i
def WeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f g : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * f x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


