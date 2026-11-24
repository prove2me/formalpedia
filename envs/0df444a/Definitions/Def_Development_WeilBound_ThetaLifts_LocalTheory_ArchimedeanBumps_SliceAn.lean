-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:37.811727+00:00
-- url     : https://prove2.me/theorems/43a119fc-f2b2-4ff9-9b39-d52d4d457d9d
-- title:
--   Slice An
-- statement:
--   Definitions and structural lemmas for Slice An, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
section General
variable {S : Type} [AddCommGroup S] [Module ℂ S]
variable [TopologicalSpace S] [IsTopologicalAddGroup S]
def toCLM (q : Seminorm ℂ S) (hq : Continuous q) (T : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ x, ‖T x‖ ≤ C * q x) : S →L[ℂ] ℂ :=
  ⟨T, continuous_of_continuousAt_zero T (by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm h ?_
    have := (hq.tendsto 0).const_mul C
    simpa using this)⟩
def Sy (_ : Seminorm ℂ S) : Type := S
instance (q : Seminorm ℂ S) : AddCommGroup (Sy q) := inferInstanceAs (AddCommGroup S)
instance (q : Seminorm ℂ S) : Module ℂ (Sy q) := inferInstanceAs (Module ℂ S)
instance (q : Seminorm ℂ S) : SeminormedAddCommGroup (Sy q) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := Sy q) q.toAddGroupSeminorm
instance (q : Seminorm ℂ S) : NormedSpace ℂ (Sy q) := ⟨fun a x => (map_smul_eq_mul q a x).le⟩
end General
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
def derAt (n : ℕ) (x : V) : 𝓢(V, ℂ) →L[ℂ] (V [×n]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => iteratedFDeriv ℝ n f x)
    (fun f g => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      have hg : ContDiff ℝ n g := g.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt)
    (fun a f => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_const_smul_apply hf.contDiffAt)
    ⟨{(0, n)}, 1, zero_le_one, fun f => by simpa using f.norm_iteratedFDeriv_le_seminorm ℂ n x⟩
def evAt (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by simpa using f.norm_le_seminorm ℂ x⟩
end PositivityTheory.ThKG.Loc.Bump
end


