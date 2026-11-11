-- Prove2me | Definitions.Def_OAIQ232A008
-- name    : OAIQ232A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:42:24.222111+00:00
-- url     : https://prove2.me/theorems/44342602-f542-4d8a-a65e-d23228b19580
-- title:
--   Definitions bundle OAIQ232A008 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Coordinates_NormalCoordinates2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/NormalCoordinates2.lean).
--
--   **Imports.** It imports the bundle `OAIQ232A001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A013`.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_OAIQ232A001

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
lemma exists_smooth_local_diffeomorphism {f : Y → Y} {S : Set Y}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {a : Y} (ha : a ∈ S)
    (hi : (fderiv ℝ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph Y Y, (e : Y → Y) = f ∧ a ∈ e.source ∧
      e.source ⊆ S ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfa : ContDiffAt ℝ ∞ f a := hf.contDiffAt (hS.mem_nhds ha)
  obtain ⟨L,hL⟩ := hi
  have hder : HasFDerivAt f (L : Y →L[ℝ] Y) a :=
    hL ▸ (hfa.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  let e := hfa.toOpenPartialHomeomorph f hder (by simp)
  have hea : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hder (by simp)
  have hfc : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hS (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) a ha).continuousAt (hS.mem_nhds ha)
  have hev : ∀ᶠ y in 𝓝 a, y ∈ S ∧ (fderiv ℝ f y).IsInvertible :=
    (show ∀ᶠ y in 𝓝 a, y ∈ S from hS.mem_nhds ha).and
      (hfc (isOpen_invertible_endomorphism.mem_nhds ⟨L,hL⟩))
  obtain ⟨U,hUsub,hU,haU⟩ := mem_nhds_iff.mp hev
  let d := e.restrOpen U hU
  have hdf : (d : Y → Y) = f := rfl
  have hdsub : d.source ⊆ S := fun _ hz => (hUsub hz.2).1
  refine ⟨d,hdf,⟨hea,haU⟩,hdsub,?_,?_⟩
  · simpa only [hdf] using hf.mono hdsub
  · intro z hz
    have hy := d.map_target hz
    have hfy : ContDiffAt ℝ ∞ f (d.symm z) := hf.contDiffAt (hS.mem_nhds (hdsub hy))
    obtain ⟨A,hA⟩ := (hUsub hy.2).2
    have hdy : HasFDerivAt d (A : Y →L[ℝ] Y) (d.symm z) := by
      rw [hdf,hA]
      exact (hfy.differentiableAt (by simp)).hasFDerivAt
    exact (d.contDiffAt_symm hz hdy (by simpa only [hdf] using hfy)).contDiffWithinAt

end WeakMTWTransport

end

end OAI
end


