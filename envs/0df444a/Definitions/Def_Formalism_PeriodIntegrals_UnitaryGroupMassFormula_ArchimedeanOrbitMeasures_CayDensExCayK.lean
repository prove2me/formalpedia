-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayK
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:58.809492+00:00
-- url     : https://prove2.me/theorems/e96f25a3-a01b-4f16-a660-34961d9fb886
-- title:
--   Cay Dens Ex Cay K
-- statement:
--   Definitions and structural lemmas for Cay Dens Ex Cay K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExCayK.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayS
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
section Chart
variable (P Q : ℕ)
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
def cayCand (g : UpqT P Q) : Mat := (1 + 1) * (UpqT.mat g + 1)⁻¹ * (UpqT.mat g - 1)
open Classical in

def cayInv (g : UpqT P Q) : lieU P Q :=
  if h : cayCand P Q g ∈ lieU P Q then ⟨cayCand P Q g, h⟩ else 0
def CayInvMeas : Prop := ∀ P Q : ℕ, Measurable (cayInv P Q)
def CayInvIff : Prop := ∀ (P Q : ℕ) (g : UpqT P Q) (X : lieU P Q),
  UpqT.mat g * ((1 + 1) - ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) =
    (1 + 1) + ((X : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) → cayInv P Q g = X
def CaySUnivMeas : Prop := ∀ P Q : ℕ, MeasurableSet (cayS (Set.univ : Set (lieU P Q)))
end Chart
def CayleyDens : Prop :=
  ∀ (P Q : ℕ) (m : Measure (UpqT P Q)), m.IsHaarMeasure → ∀ c : ℝ≥0∞, c ≠ 0 → c ≠ ⊤ →
  ∀ lam : Measure (lieU P Q), IsOmegaLeb lam →
    Tendsto (fun r : ℝ => m {g | ∃ X ∈ ballU P Q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} /
      lam (ballU P Q r)) (𝓝[>] 0) (𝓝 c) →
  ∃ D ∈ 𝓝 (0 : lieU P Q), MeasurableSet D ∧ ∃ f : lieU P Q → ℝ≥0∞, Measurable f ∧
    Tendsto f (𝓝 0) (𝓝 c) ∧ (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f
end HcInf


