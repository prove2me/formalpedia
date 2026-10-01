-- Prove2me | Definitions.Def_ChapterScalaronDensitizedTransfer
-- name    : ChapterScalaronDensitizedTransfer
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:01:57.488911+00:00
-- url     : https://prove2.me/theorems/7a00e96e-f32b-48d5-bb22-1db8e35a0b03
-- title:
--   Chapter ScalaronDensitizedTransfer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterScalaronDensitizedTransfer.lean`): generated def bundle for ChapterScalaronDensitizedTransfer. See BookProof/ChapterScalaronDensitizedTransfer.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronDensitizedTransfer.lean

import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# The conformal-mode potential after the densitized change of variables

`BookProof.ChapterStarobinskyPotential` proves the two `R + αR²` potential bounds in the
*physical* variables — `starobinskyV_nonneg` and the completed square
`confV_ge : −M⁴/(16α) ≤ V₃(R_c)` — and runs the essential-self-adjointness and Stone-flow
machinery in the mode (Hermite-basis) realisation.
`BookProof.ChapterQuantumGravityDensitized` performs the densitized change of variables
`y = √e` at the level of symbols, and `BookProof.ChapterQuantumGravityHalfDensity`
constructs the half-density unitary

  `W : L²((0,∞), de) ≃ₗᵢ[ℂ] L²((0,∞), 2y dy)`,  `(W g)(y) = g(y²)`

that makes the point map `e = y²` a Hilbert-space isomorphism.

This module is step 2 of plan item A5: it carries the potential bound *through* that change
of variables, in the continuum (not the mode) realisation, and shows that the resulting
Hamiltonians are unitarily equivalent, so that essential self-adjointness genuinely
*transfers* along `W` rather than being re-proved on each side.

## Contents

* `densConfV M α y = V₃(y²)` — the conformal-mode potential written in the densitized
  coordinate, with `densConfV_comp_densY` identifying it as the pullback of `V₃` along
  `y = √e`;
* `densConfV_ge`, `densConfV_bddBelow` — **the bound survives the change of variables**:
  `−M⁴/(16α) ≤ densConfV M α y` for every `y`, uniformly;
* `densConfV_zero_alpha_tendsto_atBot` — and it survives *because* of `αR²`: at `α = 0` the
  densitized potential still tends to `−∞`, so pure general relativity gains nothing from
  the change of variables;
* `physConfCore` / `physConfOp` and `densConfCore` / `densConfOp` — the multiplication
  operators by `V₃` on `L²((0,∞), de)` and by `densConfV` on `L²((0,∞), 2y dy)`, on their
  bounded-energy cores;
* `halfDensityUnitary_mem_densConfCore`, `halfDensityUnitary_densConfCore_surjective`,
  `halfDensityUnitary_intertwines` — the half-density unitary carries the physical core
  onto the densitized core and intertwines the two operators;
* `densConf_hasZeroDeficiencyOn` and `physConf_hasZeroDeficiencyOn_transfer` — vanishing
  adjoint deficiency of the densitized operator, and its **transfer** to the physical one
  through `BookProof.QuantumGravityHalfDensity.qg_halfDensity_transfer`;
* `densConfOp_quadForm_ge` — the bound at the level of the operator: the quadratic form of
  the densitized Hamiltonian satisfies `⟪f, H f⟫ ≥ −M⁴/(16α)·‖f‖²`, which is the sign every
  relative-bound / commutator-form combination needs;
* `physConf_stone_flow`, `densConf_stone_flow` — the resulting unitary groups.

## Honest boundary

This is the *potential* half of the continuum problem: the operators here are the
multiplication (potential) parts, in one conformal variable, and the change of variables is
the conformal one `e = y²` of `ChapterQuantumGravityDensitized` Part A.  The kinetic
absorption identities (`inv_eq_four_mul_deriv_densY_sq`, `kinetic_absorption`,
`conformal_absorption`) are proved there at the level of symbols; assembling them with the
present transfer into the full continuum `L²(ℝ⁸⁴)` operator still requires the Strichartz
finite-speed / direct-integral input recorded as the standing residue of A1 and A5, and the
gauge/BRST sector remains outside the statement.  No mass gap and no global existence is
claimed.
-/

namespace BookProof.ScalaronDensitized

open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

/-- The physical measure `de` on the nondegenerate branch `(0, ∞)`. -/
abbrev physMeasure : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))

/-! ## The potential in the densitized coordinate -/

/-- **The conformal-mode potential in the densitized coordinate.**  Under the change of
variables `e = y²` of `BookProof.QuantumGravityDensitized` the conformal-mode potential
`V₃(R_c) = −(M²/2)R_c + αR_c²` becomes `y ↦ V₃(y²)`. -/
def densConfV (M alpha y : ℝ) : ℝ := confV M alpha (y ^ 2)











/-! ## Measurability -/

theorem measurable_confV (M alpha : ℝ) : Measurable (confV M alpha) := by
  unfold confV; fun_prop

theorem measurable_densConfV (M alpha : ℝ) : Measurable (densConfV M alpha) := by
  unfold densConfV confV; fun_prop

/-! ## The two multiplication operators -/

variable (M alpha : ℝ)

/-- The bounded-energy core of the physical conformal Hamiltonian on `L²((0,∞), de)`. -/
def physConfCore : Submodule ℂ (Lp ℂ 2 physMeasure) :=
  boundedEnergyCore physMeasure (confV M alpha)

/-- **The physical conformal-mode Hamiltonian**: multiplication by `V₃(e)` on
`L²((0,∞), de)`. -/
def physConfOp : physConfCore M alpha →ₗ[ℂ] physConfCore M alpha :=
  multOp physMeasure (measurable_confV M alpha)

/-- The bounded-energy core of the densitized conformal Hamiltonian on
`L²((0,∞), 2y dy)`. -/
def densConfCore : Submodule ℂ (Lp ℂ 2 qgSrcMeasure) :=
  boundedEnergyCore qgSrcMeasure (densConfV M alpha)

/-- **The densitized conformal-mode Hamiltonian**: multiplication by `V₃(y²)` on
`L²((0,∞), 2y dy)`. -/
def densConfOp : densConfCore M alpha →ₗ[ℂ] densConfCore M alpha :=
  multOp qgSrcMeasure (measurable_densConfV M alpha)









/-! ## The half-density unitary carries one picture to the other -/







/-! ## Essential self-adjointness, and its transfer -/









/-! ## The bound at the level of the operator -/

section QuadForm

variable {X : Type*} [MeasurableSpace X]







end QuadForm





/-! ## The unitary flows -/





end

end BookProof.ScalaronDensitized


