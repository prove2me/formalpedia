-- Prove2me | Definitions.Def_ChapterSpectralDirectSum
-- name    : ChapterSpectralDirectSum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T02:06:59.236226+00:00
-- url     : https://prove2.me/theorems/ee6eeadc-d7f8-46dc-8aeb-fffb6edad78d
-- title:
--   The Lean 4 theorem `cyclicSubspace_eq_closure_range` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSpectralDirectSum.lean`): generated def bundle for ChapterSpectralDirectSum. See BookProof/ChapterSpectralDirectSum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSpectralDirectSum.lean

import Theorems.Thm_BookProof_ChapterCyclicDecomposition_cfcHom_apply_mem_cyclicSubspace

import Definitions.Def_ChapterCyclicDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib


/-!
# The spectral multiplication model without a cyclic vector (plan GAP-2, the assembly)

`ChapterSpectralMultiplication` identifies a normal operator **with a cyclic unit
vector** with multiplication by `z` on `L²(μ)`.  `ChapterCyclicDecomposition` and
`ChapterCyclicDirectSum` split an arbitrary complex Hilbert space into an orthogonal
direct sum of subspaces cyclic for the operator.  This module performs the
**assembly**: the model of a single cyclic summand is built inside the ambient space
(so that no functional calculus of a restricted operator is needed), and the
summand models are then glued over the decomposition.

* `cyclicSubspace_eq_closure_range`, `cfcVecTo`, `denseRange_cfcVecTo` — the
  generating map `f ↦ f(T)ξ` has dense range *in the cyclic subspace of `ξ`*;
* `cyclicUnitary` — since `‖f(T)ξ‖ = ‖f‖_{L²(μ_ξ)}` (`norm_cfcHom_apply`, proved
  with no cyclicity hypothesis), that map extends to a unitary
  `L²(μ_ξ) ≃ₗᵢ[ℂ] cyclicSubspace ξ`;
* `cyclicEmbedding`, `range_cyclicEmbedding`, `cyclicEmbedding_intertwines_cfc`,
  `cyclicEmbedding_intertwines` — read in `H` it is an isometric embedding with range
  the cyclic subspace, carrying multiplication by a continuous symbol `g` into
  `g(T)`, in particular multiplication by `z` into `T`;
* HEADLINE `spectral_multiplication_model_general` — for **every** normal operator on
  a complex Hilbert space there are Borel probability measures `μₓ` on its spectrum
  and isometric embeddings `Vₓ : L²(μₓ) → H` exhibiting `H` as the Hilbert sum of the
  `L²(μₓ)`, with `T` acting on each summand as multiplication by the coordinate
  function.  No cyclic vector and no separability are assumed;
* `countable_orthogonalCyclicFamily` and
  `spectral_multiplication_model_separable` — on a *separable* space the family is
  countable (its members are unit vectors at pairwise distance `√2`), so the model is
  a countable direct sum.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory Complex

namespace BookProof.ChapterSpectralDirectSum

open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

/-! ## 1. The generating map has dense range in the cyclic subspace -/

/-- The cyclic subspace of `ξ` is the closure of the range of `f ↦ f(T)ξ` (that range
is already a linear subspace). -/
theorem cyclicSubspace_eq_closure_range :
    (cyclicSubspace T hT xi : Set H) = closure (Set.range (cfcVec T hT xi)) := by
  have hrange : (Set.range fun g : C(spectrum ℂ T, ℂ) => cfcHom hT g xi)
      = Set.range (cfcVec T hT xi) := rfl
  have hspan : Submodule.span ℂ (Set.range fun g : C(spectrum ℂ T, ℂ) => cfcHom hT g xi)
      = LinearMap.range (cfcVec T hT xi) := by
    rw [hrange, ← LinearMap.coe_range, Submodule.span_eq]
  rw [cyclicSubspace, hspan]
  exact Submodule.topologicalClosure_coe _

/-- The generating map `f ↦ f(T)ξ`, seen as a map into the cyclic subspace of `ξ`. -/
def cfcVecTo : C(spectrum ℂ T, ℂ) →ₗ[ℂ] cyclicSubspace T hT xi :=
  LinearMap.codRestrict _ (cfcVec T hT xi) (cfcHom_apply_mem_cyclicSubspace T hT xi)

@[simp] theorem cfcVecTo_apply (f : C(spectrum ℂ T, ℂ)) :
    (cfcVecTo T hT xi f : H) = cfcHom hT f xi := rfl

theorem denseRange_cfcVecTo : DenseRange (cfcVecTo T hT xi) := by
  change Dense (Set.range (cfcVecTo T hT xi))
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro m
  have hm : (m : H) ∈ closure (Set.range (cfcVec T hT xi)) := by
    rw [← cyclicSubspace_eq_closure_range]
    exact m.2
  refine closure_mono ?_ hm
  rintro _ ⟨f, rfl⟩
  exact ⟨cfcVecTo T hT xi f, ⟨f, rfl⟩, rfl⟩

/-! ## 2. The unitary model of one cyclic summand -/

/-- **The model of a cyclic summand.**  The map `f ↦ f(T)ξ` is an `L²(μ_ξ)`-isometry
onto a dense subspace of the cyclic subspace of `ξ`, hence extends to a unitary
`L²(μ_ξ) ≃ₗᵢ[ℂ] cyclicSubspace ξ`.  Note that no cyclicity hypothesis is needed:
`ξ` is cyclic *for its own cyclic subspace* by construction. -/
def cyclicUnitary : Lp ℂ 2 (spectralMeasure T hT xi) ≃ₗᵢ[ℂ] cyclicSubspace T hT xi :=
  (LinearEquiv.refl ℂ C(spectrum ℂ T, ℂ)).extendOfIsometry
    (ContinuousMap.toLp 2 (spectralMeasure T hT xi) ℂ).toLinearMap
    (cfcVecTo T hT xi)
    (ContinuousMap.toLp_denseRange ℂ _ (μ := spectralMeasure T hT xi) (by simp))
    (denseRange_cfcVecTo T hT xi)
    (fun f => by
      simpa using (norm_cfcHom_apply T hT xi f))

@[simp] theorem cyclicUnitary_toLp (f : C(spectrum ℂ T, ℂ)) :
    cyclicUnitary T hT xi (ContinuousMap.toLp 2 (spectralMeasure T hT xi) ℂ f)
      = cfcVecTo T hT xi f :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-- The model read inside the ambient space: an isometric embedding of `L²(μ_ξ)` into
`H` with range the cyclic subspace of `ξ`. -/
def cyclicEmbedding : Lp ℂ 2 (spectralMeasure T hT xi) →ₗᵢ[ℂ] H :=
  (cyclicSubspace T hT xi).subtypeₗᵢ.comp (cyclicUnitary T hT xi).toLinearIsometry

@[simp] theorem cyclicEmbedding_apply (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi u = (cyclicUnitary T hT xi u : H) := rfl

@[simp] theorem cyclicEmbedding_toLp (f : C(spectrum ℂ T, ℂ)) :
    cyclicEmbedding T hT xi (ContinuousMap.toLp 2 (spectralMeasure T hT xi) ℂ f)
      = cfcHom hT f xi := by
  simp [cyclicEmbedding]









/-! ## 3. Gluing the summand models -/







/-! ## 4. The separable case: countably many summands -/









end BookProof.ChapterSpectralDirectSum

end


