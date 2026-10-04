-- Prove2me | Definitions.Def_ChapterNsFieldMomentumInverse
-- name    : ChapterNsFieldMomentumInverse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:57:04.255142+00:00
-- url     : https://prove2.me/theorems/303675d6-bff6-49ea-977c-e1113db1eda7
-- title:
--   The Lean 4 theorem `continuous_momSymbol` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsFieldMomentumInverse.lean`): generated def bundle for ChapterNsFieldMomentumInverse. See BookProof/ChapterNsFieldMomentumInverse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsFieldMomentumInverse.lean

import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
import Mathlib


/-!
# The inverse field momentum `π^{-1}`

Item 2 of the Navier–Stokes plan items of `CONSOLIDATED_PLAN.md`: *the constraint solved,
`D_j ψ = 0`*.  The field momentum is `π_m = −i ∂_m` in the fibre variable `u`, and the derivative
gauge, solved for the derivative mode, reads `u^{(1)}_j = p_j π^{-1}`.  The item asks for the
inverse `π^{-1}` and flags the domain question as the one genuine analytic residual: `π` is not
boundedly invertible.

Everything here is done in the momentum representation of the fibre variable, where — by
`BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp`, re-exported below as
`isMomInverse_momentumOp` — the field momentum **is** multiplication by the real symbol
`momSymbol m ξ = 2π ⟪ξ, m⟫`.  `IsMomInverse m f g` is the relation `π_m g = f` there, i.e.
`g = π_m^{-1} f`.

What is proved, for a non-zero fibre direction `m`:

* `volume_momSymbol_zero`, `momSymbol_ne_zero_ae` — the symbol vanishes only on a hyperplane, a
  Lebesgue null set;
* `momentum_kernel_trivial` — hence **the kernel of the field momentum is trivial**: the
  `u`-constant mode that the plan flags is not an `L²` state, so no finite-dimensional kernel has
  to be split off, and `π^{-1}` is single valued (`isMomInverse_unique`);
* `isMomInverse_of_memLp` — the inverse exists exactly when the divided symbol is square
  integrable, which is the honest domain of `π^{-1}`;
* `momDomain` is a submodule and `momDomain_dense` — **`π^{-1}` is densely defined**, proved by
  cutting off a neighbourhood of the hyperplane `{σ = 0}`;
* `isMomInverse_smul` — `u^{(1)}_j = p_j π^{-1}`: the solution for the right-hand side `p_j ψ` is
  `p_j` times the inverse, which is the plan's identity on the physical sector;
* `eq_div_of_mul_eq_ae` — its symbol form: a symbol `t` with `σ · t = p` is `t = p / σ` almost
  everywhere, so the derivative mode is determined by the constraint;
* `isMomInverse_momentumOp` — the faithfulness statement: on the Schwartz core the relation
  `IsMomInverse` is satisfied by the `L²` realization of the honest operator `−i ∂_m` and its
  argument.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsFieldMomentumInverse

open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-! ## 1. The symbol of the field momentum, and where it vanishes -/

/-- The real symbol of the field momentum `π_m = −i ∂_m`: `ξ ↦ 2π ⟪ξ, m⟫`. -/
def momSymbol (m : W) (ξ : W) : ℝ := 2 * Real.pi * (inner ℝ ξ m)

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
theorem continuous_momSymbol (m : W) : Continuous (momSymbol m) :=
  continuous_const.mul ((innerSL ℝ).flip m).continuous

omit [FiniteDimensional ℝ W] in
theorem measurable_momSymbol (m : W) : Measurable (momSymbol m) :=
  (continuous_momSymbol m).measurable





/-! ## 2. The inverse field momentum -/

/-- **`g = π_m^{-1} f`**, in the momentum representation of the fibre variable: multiplying `g` by
the symbol of the field momentum returns `f`. -/
def IsMomInverse (m : W) (f g : Lp ℂ 2 (volume : Measure W)) : Prop :=
  (fun ξ => ((momSymbol m ξ : ℝ) : ℂ) * (g : W → ℂ) ξ) =ᵐ[(volume : Measure W)] (f : W → ℂ)







/-- The set of states on which `π^{-1}` is defined, as a submodule. -/
def momDomain (m : W) : Submodule ℂ (Lp ℂ 2 (volume : Measure W)) where
  carrier := {f | ∃ g, IsMomInverse m f g}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure W))]
      with ξ hz
    rw [hz]
    simp
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₁ + g₂, ?_⟩
    filter_upwards [h₁, h₂, MeasureTheory.Lp.coeFn_add g₁ g₂,
      MeasureTheory.Lp.coeFn_add f₁ f₂] with ξ hx₁ hx₂ hg hf
    rw [hg, hf]
    simp only [Pi.add_apply, mul_add]
    rw [hx₁, hx₂]
  smul_mem' := by
    rintro c f ⟨g, h⟩
    refine ⟨c • g, ?_⟩
    filter_upwards [h, MeasureTheory.Lp.coeFn_smul c g, MeasureTheory.Lp.coeFn_smul c f]
      with ξ hx hg hf
    rw [hg, hf]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ c, mul_assoc, hx]



/-! ## 3. `π^{-1}` is densely defined -/

/-- The frequencies where the symbol is bounded away from zero by `1 / (n + 1)`. -/
def cutSet (m : W) (n : ℕ) : Set W := {ξ : W | 1 / ((n : ℝ) + 1) ≤ |momSymbol m ξ|}

omit [FiniteDimensional ℝ W] in
theorem measurableSet_cutSet (m : W) (n : ℕ) : MeasurableSet (cutSet m n) :=
  measurableSet_le measurable_const (measurable_momSymbol m).abs

/-- The cut-off of a state to the frequencies where the symbol is bounded away from zero. -/
def cut (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : Lp ℂ 2 (volume : Measure W) :=
  ((MeasureTheory.Lp.memLp f).indicator (measurableSet_cutSet m n)).toLp







/-! ## 4. The identity of the physical sector, `u^{(1)}_j = p_j π^{-1}` -/





/-! ## 5. Faithfulness: the relation is the honest operator `−i ∂_m` -/



end

end BookProof.NsFieldMomentumInverse


