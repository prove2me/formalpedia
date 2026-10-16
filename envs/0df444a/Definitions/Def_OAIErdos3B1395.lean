-- Prove2me | Definitions.Def_OAIErdos3B1395
-- name    : OAIErdos3B1395
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T04:38:33.178534+00:00
-- url     : https://prove2.me/theorems/3ff178c7-719b-4a2c-bf03-f7e51df0ca26
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1396 of 1396
-- statement:
--   Definitions bundle 1396 of 1396 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1394`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1396 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateRootBudget_zero_layers`, `OAI.Erdos3.VectorPolynomial.scalarNativeDimension_pos`, `OAI.Erdos3.fixedPathAmbientScalarPrecision_ambient`, `OAI.Erdos3.fixedPathAmbientScalarPrecision_error`, `OAI.Erdos3.fixedPathSlicedAmbientScalarPrecision_error`, `OAI.Erdos3.forecast_ambient_exp_error`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1324
import Definitions.Def_OAIErdos3B1381

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateRootBudget_zero_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [zeroLayerVariables_card]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem scalarNativeDimension_pos (s : ℕ) : 0 < scalarNativeDimension s := by
  unfold scalarNativeDimension
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastAmbientPrecision
namespace OAI

section

namespace Erdos3

theorem forecast_ambient_exp_error {δ M Q A E : ℝ}
    (hδ : δ ≤ Real.exp (-(E + 4))) (hM : M ≤ Real.exp Q)
    (hA : Q + E + 4 ≤ A) :
    2 * δ + M * Real.exp (-A) ≤ Real.exp (-E) := by
  have hterm : M * Real.exp (-A) ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp Q * Real.exp (-A) :=
        mul_le_mul_of_nonneg_right hM (Real.exp_nonneg _)
      _ = Real.exp (Q - A) := by rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp (-(E + 4)) := Real.exp_le_exp.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-(E + 4)) := by linarith
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathAmbientUniformPrecision
namespace OAI

section

namespace Erdos3

theorem fixedPathAmbientScalarPrecision_ambient {Q E M : ℝ}
    (hM : M ≤ Real.exp Q) :
    2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E) ≤
      Real.exp (-fixedPathComparisonPrecision E) := by
  apply forecast_ambient_exp_error (Q := Q)
  · unfold fixedPathForecastTolerance fixedPathComparisonPrecision
    apply Real.exp_le_exp.mpr
    linarith
  · exact hM
  · unfold fixedPathComparisonPrecision fixedPathAmbientPrecision
    linarith

theorem fixedPathAmbientScalarPrecision_error {Q E M sourceError : ℝ}
    (hM : M ≤ Real.exp Q)
    (hsource : sourceError ≤ Real.exp (-fixedPathComparisonPrecision E)) :
    sourceError + Real.exp (-fixedPathComparisonPrecision E) +
      (2 * fixedPathForecastTolerance E + M * Real.exp (-fixedPathAmbientPrecision Q E)) ≤
      Real.exp (-E) := by
  have hambient := fixedPathAmbientScalarPrecision_ambient (E := E) hM
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by
    linarith only [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (-fixedPathComparisonPrecision E) := by
      linarith only [hsource, hambient]
    _ ≤ Real.exp 4 * Real.exp (-fixedPathComparisonPrecision E) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = Real.exp (-E) := by
      rw [← Real.exp_add]
      unfold fixedPathComparisonPrecision
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem fixedPathSlicedAmbientScalarPrecision_error
    (dout dj dc d : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {Pg E Q Mmass sourceError Dgrid L C K δgrid : ℝ}
    (hPg : 0 ≤ Pg) (hE : 0 ≤ E)
    (hsource : sourceError ≤ Real.exp (-(E + 4))) (hM : Mmass ≤ Real.exp Q)
    (hD : 0 ≤ Dgrid) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDP : Dgrid ≤ Real.exp Pg) (hLP : L ≤ Real.exp Pg)
    (hCP : C ≤ Real.exp Pg) (hKP : K ≤ Real.exp Pg)
    (hδ : 0 ≤ δgrid) (hmesh : δgrid ≤ forecastJointGridMesh d Pg (E + 4)) :
    sourceError + (2 * Real.exp (-(E + 8)) + Mmass * Real.exp (-(Q + E + 8))) +
      forecastJointGridError dout dj dc (forecastJointGridCutoff Pg (E + 4))
        Dgrid L C K δgrid ≤ Real.exp (-E) := by
  have hgrid := (forecastJointGridErrorBudget d hPg (show 0 ≤ E + 4 by linarith)).2.2.2.2
    hdout hdj hdc hD hL hC hK hDP hLP hCP hKP hδ hmesh
  have htotal := fixedPathAmbientScalarPrecision_error hM hsource
  dsimp only [fixedPathComparisonPrecision, fixedPathForecastTolerance,
    fixedPathAmbientPrecision] at htotal
  linarith only [hgrid, htotal]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end VectorPolynomial
end Erdos3

end

end OAI

end


