-- Prove2me | solution 1 for AnosovPlugs.normalCoord_nonneg_of_hasMFDerivWithinAt
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T22:57:54.766086+00:00
-- url     : https://prove2.me/submissions/d446282c-b2d2-4b42-8288-40fd5820317c

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set

open AnosovPlugs

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (γ : ℝ → M) (s : Set ℝ) (t₀ : ℝ) (v : TangentSpace I3 (γ t₀))
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I3 γ s t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hb : γ t₀ ∈ I3.boundary M) (c : ℝ) (hc : c ∈ posTangentConeAt s t₀) :
    0 ≤ c * normalCoord v := by
  have hF : HasFDerivWithinAt (extChartAt I3 (γ t₀) ∘ γ)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v : EuclideanSpace ℝ (Fin 3))) s t₀ := by
    have h2 := hγ.2
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, Function.comp_id, modelWithCornersSelf_coe, range_id, preimage_id,
      inter_univ, id_eq] at h2
    exact h2
  have hg : HasFDerivWithinAt (fun u => (extChartAt I3 (γ t₀) (γ u)) 0)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v : EuclideanSpace ℝ (Fin 3)))) s t₀ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).hasFDerivAt.comp_hasFDerivWithinAt t₀ hF
  have h0 : (extChartAt I3 (γ t₀) (γ t₀)) 0 = 0 := by
    have := (I3.isBoundaryPoint_iff (x := γ t₀)).1 hb
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at this
    exact this.symm
  have hpos : ∀ u, 0 ≤ (extChartAt I3 (γ t₀) (γ u)) 0 := by
    intro u
    have : extChartAt I3 (γ t₀) (γ u) ∈ range I3 := by
      simp only [extChartAt_coe, Function.comp_apply]
      exact mem_range_self _
    rw [range_modelWithCornersEuclideanHalfSpace] at this
    exact this
  have hmin : IsLocalMinOn (fun u => (extChartAt I3 (γ t₀) (γ u)) 0) s t₀ :=
    Filter.Eventually.of_forall (fun u => by simp only [h0]; exact hpos u)
  have key := hmin.hasFDerivWithinAt_nonneg hg hc
  have e : ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v : EuclideanSpace ℝ (Fin 3)))) c = c * normalCoord v := by
    rfl
  rw [← e]
  exact key
