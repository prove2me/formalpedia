-- Prove2me | Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
-- name    : RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:49.517503+00:00
-- url     : https://prove2.me/theorems/5691cb78-c263-4bbc-9da8-b78cd37a969a
-- title:
--   Translation
-- statement:
--   Definitions and structural lemmas for Translation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
set_option autoImplicit true
namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory
section Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def translate {F : Type*} (a : E) (f : E → F) : E → F :=
  fun x => f (x + a)
omit [CompleteSpace E] in
lemma contDiff_translate {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (translate (E := E) a f) := by
  -- `x ↦ x + a` is `C^∞`; compose.
  exact hf.comp (contDiff_id.add contDiff_const)
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_translate {F : Type*} [Zero F] {f : E → F}
    (hf : HasCompactSupport f) (a : E) : HasCompactSupport (translate (E := E) a f) := by
  exact hf.comp_homeomorph (Homeomorph.addRight a)
omit [CompleteSpace E] in
lemma mem_C1c_translate {f : E → ℝ} (hf : f ∈ C1c (E := E)) (a : E) :
    translate (E := E) a f ∈ C1c (E := E) :=
  ⟨contDiff_translate (E := E) hf.1 a, hasCompactSupport_translate (E := E) hf.2 a⟩
noncomputable def translateC1c (a : E) : ↥(C1c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) where
  toFun f := ⟨translate (E := E) a f.1, mem_C1c_translate (E := E) (f := f.1) f.2 a⟩
  map_add' f g := by
    ext x
    simp [translate]
  map_smul' c f := by
    ext x
    simp [translate]
end Topology
section Measure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance
variable (μ : Measure E) [μ.IsAddRightInvariant]
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))
variable [IsFiniteMeasureOnCompacts μ]
end Measure
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov


