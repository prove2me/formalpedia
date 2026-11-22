-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PhProdConv
-- name    : Formalism_PeriodIntegrals_PhProdConv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:26.766287+00:00
-- url     : https://prove2.me/theorems/0827937c-1273-4e37-87e7-52c88306c9f3
-- title:
--   Ph Prod Conv
-- statement:
--   Definitions and structural lemmas for Ph Prod Conv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PhProdConv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField
open scoped InnerProductSpace
namespace PI.PhProdConv
section Defs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v
def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)
def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ
def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)
def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ
def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T
def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y
end Defs
def ProdConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SecondCountableTopology (G i)] (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsInvInvariant] (ph m : ∀ i, G i → ℂ),
    (∀ i, Integrable (ph i) (μ i)) → (∀ i, PhConv (μ i) (ph i) (m i)) →
      Integrable (fun g : ∀ i, G i => ∏ i, ph i (g i)) (Measure.pi μ) ∧
      PhConv (Measure.pi μ) (fun g => ∏ i, ph i (g i)) (fun g => ∏ i, m i (g i))
end PI.PhProdConv


