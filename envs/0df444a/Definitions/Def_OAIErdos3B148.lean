-- Prove2me | Definitions.Def_OAIErdos3B148
-- name    : OAIErdos3B148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T19:56:27.481312+00:00
-- url     : https://prove2.me/theorems/a7ede520-6f8e-49f4-88ef-f8e51b745f32
-- title:
--   OpenAI Erdős-3 split, definitions bundle 149 of 168
-- statement:
--   Definitions bundle 149 of 168 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B147`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 149 available.
--
--   Modules: `OAI.Erdos3.IndexedComparableScalarGeometryData`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

structure IndexedComparableScalarGeometryData (d r : ℕ)
    {K I : Type*} [Fintype K] [Fintype I]
    (L W τ : ℝ) (parameters : K → ℕ) (N : I → ℕ) : Prop where
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hL : 1 ≤ L
  hwidth : ∀ z : Option K × I, 0 < trimmedSpatialWidths W τ N z
  hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i
  hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0}
    (trimmedSpatialWidths (K := K) W τ N) z
  hparam : ∀ j, (0 : ℤ) < (parameters j : ℤ)
  sourceGeometry :
    (∀ t : Option K × I, smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 ≤
      canonicalJointFrameWindowConstant (r*d) τ *
        ((jointFrameSourceHi N (trimmedSpatialWidths W τ N) t -
          jointFrameSourceLo (trimmedSpatialWidths W τ N) t : ℤ) : ℝ)) ∧
    (∀ z ∈ Fintype.piFinset (fun t : Option K × I =>
        Finset.Ico (jointFrameSourceLo (trimmedSpatialWidths W τ N) t)
          (jointFrameSourceHi N (trimmedSpatialWidths W τ N) t)), ∀ t,
      |(z t : ℝ) - (0 : ℤ)| ≤ smoothPairCoefficientScale (2 * (N t.2 : ℝ)) L t.1 / 2) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceLo (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L) ∧
    (∀ k : K, ∀ i,
      |(jointFrameSourceHi N (trimmedSpatialWidths W τ N) (some k, i) : ℝ)| ≤
        2 * (N i : ℝ) / L)
  hroot : ∀ i, trimmedSpatialWidths (K := K) W τ N (none, i) ≤
    (spatialTrimMargin τ N i : ℝ)
  hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1 / 2
  hscale : ∀ z : Option K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤
    residueProfileWidth (fun _ : I => 1) (trimmedSpatialWidths W τ N) z
  physicalSize : ∀ i, L * L ^ (d + 1) ≤ 2 * (N i : ℝ)
  parameterBox :
    (∀ j, (0 : ℤ) < (parameters j : ℤ)) ∧
    0 < L ∧
    (∀ j, L ≤ (((parameters j : ℤ) - 0 : ℤ) : ℝ)) ∧
    (∀ j, (parameters j : ℤ) - 0 ≤ (comparableScalarParameterRadius (r : ℝ) L : ℤ)) ∧
    (comparableScalarParameterRadius (r : ℝ) L : ℝ) ≤ ((r : ℝ) + 1) * L ∧
    1 * L ≤ L ∧
    |(0 : ℝ) / L| ≤ r ∧
    (∀ j, |(((parameters j : ℤ) : ℝ)) / L| ≤ r) ∧
    0 ≤ W ∧ L ≤ W ∧ W ≤ (r : ℝ) * d * L

end Erdos3

end

end OAI

end


