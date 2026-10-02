-- Prove2me | solution 1 for AnosovPlugs.gluing_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-02T10:13:12.778403+00:00
-- url     : https://prove2.me/submissions/c870f7d3-010e-4528-941d-8c2e30f9364f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AnosovPlugs_Section5
import Theorems.Thm_AnosovPlugs_prop_4_2_normal_form
import Theorems.Thm_AnosovPlugs_prop_5_2_return_map_perturbation
import Theorems.Thm_AnosovPlugs_lemma_5_1_cone_field_criterion
import Theorems.Thm_AnosovPlugs_thm_1_5_assembly
import Theorems.Thm_AnosovPlugs_stronglyIsotopic_trans

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

theorem solution {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    (X : (x : U) → TangentSpace I3 x) (φ : U → U)
    (hX : IsFillingHyperbolicPlug X) (hXnoAR : NoAttractorNorRepeller X)
    (hφ : IsStronglyTransverseGluing X φ) :
    ∃ (Y : (x : U) → TangentSpace I3 x) (ψ : U → U),
      IsFillingHyperbolicPlug Y ∧ IsStronglyTransverseGluing Y ψ ∧ StronglyIsotopic X φ Y ψ ∧
      ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
        [IsManifold I3 ∞ N] [T2Space N] [CompactSpace N] [BoundarylessManifold I3 N]
        (Z : (y : N) → TangentSpace I3 y) (q : U → N),
        IsSelfGluing Y ψ Z q → IsHyperbolicSet Z univ := by
  obtain ⟨Y, φ₁, hY, hYnoAR, hφ₁, hiso₁, As, Au, hnf⟩ := prop_4_2_normal_form X φ hX hXnoAR hφ
  have hfam := prop_5_2_return_map_perturbation Y φ₁ As Au hY hYnoAR hφ₁ hnf
  obtain ⟨ψ, hψ, hiso₂, Qs, Qu, hQs, hQu, hcone⟩ :=
    thm_1_5_assembly Y φ₁ As Au hY hYnoAR hφ₁ hnf hfam
  refine ⟨Y, ψ, hY, hψ, stronglyIsotopic_trans hiso₁ hiso₂, ?_⟩
  intro N _ _ _ _ _ _ Z q hq
  exact lemma_5_1_cone_field_criterion Y φ₁ ψ As Au Qs Qu hY hYnoAR hφ₁ hnf hψ hQs hQu hcone N Z q hq
