-- Prove2me | Definitions.Def_OAIErdos3B110
-- name    : OAIErdos3B110
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:49:53.482636+00:00
-- url     : https://prove2.me/theorems/756a384e-df43-4cf7-a434-6d00cbb4598a
-- title:
--   OpenAI Erdős-3 split, definitions bundle 111 of 132
-- statement:
--   Definitions bundle 111 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B109`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 111 available.
--
--   Modules: `OAI.Erdos3.continuousOn_latticeGaussianMass`, `OAI.Erdos3.continuous_latticeGaussianMass`, `OAI.Erdos3.latticeGaussianTorus`, `OAI.Erdos3.lattice_gaussian_summable`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B117

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem lattice_gaussian_summable (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (x : E) :
    Summable (fun m : Λ => Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2)) := by
  let r : ℝ := -(Module.finrank ℤ Λ : ℝ) - 1
  have hr : r < -(Module.finrank ℤ Λ : ℝ) := by dsimp [r]; linarith
  have hs := ZLattice.summable_norm_sub_rpow Λ r hr x
  have hc : IsClosed (Λ : Set E) := @AddSubgroup.isClosed_of_discrete E _ _ _ _
    Λ.toAddSubgroup (inferInstanceAs (DiscreteTopology Λ))
  have he : Topology.IsClosedEmbedding (fun m : Λ => (m : E) - x) := by
    exact (Homeomorph.subRight x).isClosedEmbedding.comp (Λ.isClosedEmbedding_subtype hc)
  have hn : Tendsto (fun m : Λ => ‖(m : E) - x‖) cofinite atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding he
  have hd := (rexp_neg_quadratic_isLittleO_rpow_atTop
    (show -Real.pi * t < 0 by nlinarith [Real.pi_pos]) 0 r).isBigO.comp_tendsto hn
  have hsum := summable_of_isBigO hs hd
  simpa only [Function.comp_def, zero_mul, add_zero, norm_sub_rev] using hsum

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

theorem continuousOn_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn (latticeGaussianMass Λ t) (Metric.closedBall 0 R) := by
  have hs := (lattice_gaussian_summable Λ (half_pos ht) 0).mul_left
    (Real.exp (Real.pi * t * R ^ 2))
  apply continuousOn_tsum (fun _ => (by fun_prop : Continuous _).continuousOn) hs
  intro m x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
  exact gaussian_translate_bound t R ht.le hR x m (by simpa using hx)

theorem continuous_latticeGaussianMass (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) : Continuous (latticeGaussianMass Λ t) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (continuousOn_latticeGaussianMass Λ ht (‖x‖ + 1) (by positivity)).continuousAt
    (Metric.closedBall_mem_nhds_of_mem (by simp))

end Erdos3

end

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeTorusFourierCoefficient
namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeGaussianTorus (b : Module.Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) :
    C(UnitAddTorus ι, ℂ) where
  toFun := integerPeriodicTorusLift (fun x =>
    (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) : ℂ))
  continuous_toFun := continuous_integerPeriodicTorusLift _
    (Complex.continuous_ofReal.comp ((continuous_latticeGaussianMass Λ ht).comp
      (b.ofZLatticeBasis ℝ Λ).equivFunL.symm.continuous))
    (fun x n => congrArg (fun z : ℝ => (z : ℂ)) (latticeGaussian_integer_periodic Λ b t x n))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

end Erdos3

end

end OAI

end


