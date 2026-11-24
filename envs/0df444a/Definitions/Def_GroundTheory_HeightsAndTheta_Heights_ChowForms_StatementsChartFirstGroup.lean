-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroup
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:14.347807+00:00
-- url     : https://prove2.me/theorems/e5493db2-be96-484d-a5f0-d9d3e37c3d0a
-- title:
--   Statements Chart First Group
-- statement:
--   Definitions and structural lemmas for Statements Chart First Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartFirstGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
open MvPolynomial
noncomputable section
def firstGroup {F : Type*} [Field F] {n e : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F) :=
  aeval (fun ij : Fin (e + 1) × Fin n =>
    Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) f
def ChartFirstGroupPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f →
      Prime (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f))
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


