-- Prove2me | solution 1 for Auto.carleson_trunc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:57.689892+00:00
-- url     : https://prove2.me/submissions/6d13d7c6-de56-4d30-9f59-1be0dc890bf7

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_measurePreserving_carlesonCoord
public import Theorems.Thm_Auto_carleson_integrand_coord

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ)
    (hint : Integrable (carlesonTrunc a ν g σ ε)) :
    Integrable (fun p : ℝ × ℝ => carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ)) ∧
      ∫ q, carlesonTrunc a ν g σ ε q =
        ∫ p : ℝ × ℝ, carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ) := by
  have hemb := carlesonCoord.toHomeomorph.isClosedEmbedding.measurableEmbedding
  have hc : (fun q => carlesonTrunc a ν g σ ε (carlesonCoord q)) =
      fun q => carlesonH a ν g σ ε q.1 * (carlesonW q.1.2 q.2 : ℂ) :=
    funext (carleson_integrand_coord a ν g σ ε)
  have hi : Integrable (fun q : (ℝ × ℝ) × ℝ => carlesonH a ν g σ ε q.1 *
      (carlesonW q.1.2 q.2 : ℂ)) := by
    rw [← hc]
    exact (measurePreserving_carlesonCoord.integrable_comp_emb hemb).mpr hint
  have hw : ∀ p : ℝ × ℝ, ∫ u, carlesonH a ν g σ ε p * (carlesonW p.2 u : ℂ) =
      carlesonH a ν g σ ε p * (carlesonWeight p.2 : ℂ) := fun p => by
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  rw [Measure.volume_eq_prod] at hi
  refine ⟨hi.integral_prod_left.congr (ae_of_all _ hw), ?_⟩
  rw [← measurePreserving_carlesonCoord.integral_comp hemb, hc, Measure.volume_eq_prod,
    integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ hw)
end Auto
