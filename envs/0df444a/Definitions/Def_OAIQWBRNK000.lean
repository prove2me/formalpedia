-- Prove2me | Definitions.Def_OAIQWBRNK000
-- name    : OAIQWBRNK000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:21:43.414668+00:00
-- url     : https://prove2.me/theorems/dfb13952-d9f4-443a-9d7b-2267a6333f4d
-- title:
--   Normalized univalent maps as continuous functions on the disk (OpenAI Brennan split)
-- statement:
--   A small definitions bundle from OpenAI's Lean development for *Brennan's conjecture and sharp inverse-square integral means* (OpenAI Math Release, September 24, 2026, result family 072, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It serves the proofs of the two standalone statements `OAI.Brennan.univalent_growth_upper` (Koebe growth upper bound) and `OAI.Brennan.isCompact_univalent_restrictions` (compactness of the class $\mathcal S$), neither of which mentions it.
--
--   Its declarations, all in the namespace `OAI.Brennan`:
--   - `ballNormalize f a R` is the normalized rescaling $z \mapsto \bigl(f(a + Rz) - f(a)\bigr)/\bigl(R\,f'(a)\bigr)$ of $f$ to a disk of radius $R$ about $a$;
--   - `diskExtend g` extends a continuous function $g$ on the unit disk `disk` to $\mathbb C$ by $0$ outside the disk, and `diskExtend_apply` (a `@[simp]` lemma) says it agrees with $g$ on the disk;
--   - `diskSchlichtSet` is the set of continuous $g$ on the disk whose extension `diskExtend g` is `Schlicht`, that is, holomorphic and injective on the disk with value $0$ and derivative $1$ at $0$;
--   - an instance making `disk` a locally compact space (it is open in $\mathbb C$).
--
--   `disk` and `Schlicht` come from the published bundle `Def_Brennan`, which this bundle imports; it imports no other bundle. The definitions bundle of the main Brennan split imports this bundle instead of repeating these declarations.
-- source:
--   OpenAI, Brennan's conjecture and sharp inverse-square integral means, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/IntegralMeans (Distortion.lean, CompactClass.lean) at commit adc7f12

import Mathlib
import Definitions.Def_Brennan

section
-- module Solutions.OAIQW_BrennanCore.Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def ballNormalize (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (f (a+(R : ℂ)*z)-f a)/((R : ℂ)*deriv f a)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_BrennanCore.CompactClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

instance instLocallyCompactSpaceElemComplexDisk : LocallyCompactSpace disk := (show IsOpen disk from Metric.isOpen_ball).locallyCompactSpace

def diskExtend (g : C(disk,ℂ)) (z : ℂ) : ℂ :=
  by classical exact if hz : z ∈ disk then g ⟨z,hz⟩ else 0

@[simp] lemma diskExtend_apply (g : C(disk,ℂ)) (z : disk) : diskExtend g z = g z := by
  simp [diskExtend,z.2]

def diskSchlichtSet : Set C(disk,ℂ) := {g | Schlicht (diskExtend g)}

end Brennan

end

end OAI
end


