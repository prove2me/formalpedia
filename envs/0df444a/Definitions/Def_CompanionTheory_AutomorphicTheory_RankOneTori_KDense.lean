-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
-- name    : CompanionTheory_AutomorphicTheory_RankOneTori_KDense
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:05:42.273655+00:00
-- url     : https://prove2.me/theorems/b8cd6ccb-1f5f-4a6c-a410-c6b5b89ec027
-- title:
--   KDense
-- statement:
--   Definitions and structural lemmas for KDense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
namespace Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
section Cpt
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
def tr (a : Γ) : C(Γ, ℝ) →ₐ[ℝ] C(Γ, ℝ) := ContinuousMap.compRightAlgHom ℝ ℝ ⟨fun x => a * x, continuous_const.mul continuous_id⟩
def FinInv (V : Submodule ℝ C(Γ, ℝ)) : Prop := V.FG ∧ ∀ a : Γ, ∀ q ∈ V, tr a q ∈ V
def finAlg (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : Subalgebra ℝ C(Γ, ℝ) where
  carrier := {p | ∃ V, FinInv V ∧ p ∈ V}
  mul_mem' := by
    rintro p q ⟨V, hV, hp⟩ ⟨W, hW, hq⟩
    refine ⟨V * W, ⟨hV.1.mul hW.1, fun a x hx => ?_⟩, Submodule.mul_mem_mul hp hq⟩
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) fun x y hx hy => ?_
    · rw [map_mul]; exact Submodule.mul_mem_mul (hV.2 a m hm) (hW.2 a n hn)
    · rw [map_add]; exact add_mem hx hy
  add_mem' := by
    rintro p q ⟨V, hV, hp⟩ ⟨W, hW, hq⟩
    refine ⟨V ⊔ W, ⟨hV.1.sup hW.1, fun a x hx => ?_⟩, Submodule.add_mem_sup hp hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]; exact Submodule.add_mem_sup (hV.2 a y hy) (hW.2 a z hz)
  algebraMap_mem' c := by
    refine ⟨Submodule.span ℝ {1}, ⟨Submodule.fg_span (finite_singleton _), fun a x hx => ?_⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, map_one]; exact hx
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
variable [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
end Cpt
section Mat
variable {n : ℕ} {K : Set (Mat n)} {hK : IsMatGroup K}
def co (hK : IsMatGroup K) : (Mat n →L[ℝ] ℝ) →ₗ[ℝ] C(MG K hK, ℝ) where
  toFun f := ⟨fun x => f x.mat, f.continuous.comp MG.continuous_mat⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {G : Set (Mat n)}
  {σ : Mat n → (H →L[ℂ] H)} [CompactSpace (MG K hK)]
end Mat
end Formalism.MainStatements.RankOne.KD


