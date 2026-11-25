-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:22.596479+00:00
-- url     : https://prove2.me/theorems/a363813d-d68b-4ee7-b5e5-d5cba9a24571
-- title:
--   Cay Dens Ex Cay S
-- statement:
--   Definitions and structural lemmas for Cay Dens Ex Cay S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExCayS.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
def cayS {P Q : ℕ} (U : Set (lieU P Q)) : Set (UpqT P Q) :=
  {g | ∃ X ∈ U, UpqT.mat g *
    ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
      (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)}
def CayleyLoc : Prop :=
  ∀ (P Q : ℕ) (m : Measure (UpqT P Q)), m.IsHaarMeasure → ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ⊤ →
  ∀ lam : Measure (lieU P Q), IsOmegaLeb lam →
    Tendsto (fun r : ℝ => m {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c) →
  ∀ ε : ℝ≥0, 0 < ε → ∃ V ∈ 𝓝 (0 : lieU P Q), MeasurableSet V ∧ MeasurableSet (cayS V) ∧
    ∃ ι : UpqT P Q → lieU P Q, Measurable ι ∧
      (∀ (g : UpqT P Q) (X : lieU P Q), X ∈ V →
        (UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
          (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ↔
          g ∈ cayS V ∧ ι g = X)) ∧
      ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧ (∀ X ∈ V, f X ≤ (1 + ε) * c ∧ c ≤ (1 + ε) * f X) ∧
        (m.restrict (cayS V)).map ι = (lam.restrict V).withDensity f
end HcInf


