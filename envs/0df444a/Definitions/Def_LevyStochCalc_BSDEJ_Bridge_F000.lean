-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_Bridge_F000
-- name    : LevyStochCalc_BSDEJ_Bridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:38:29.194125+00:00
-- url     : https://prove2.me/theorems/fbecb0fa-f5b0-46d6-beda-8d9895212f6f
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.Bridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.Bridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_CadlagLegs_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From a solution pinned to a Lévy driver to the BSDEJ solution predicate

A `SolvesBSDEJ D f ξ T Y Z U` is a solution of the backward equation over the augmented joint
filtration `augJoint D` of a single Lévy driver, the two stochastic integrals being the canonical
ones for that filtration. `BSDEJ.Definition.IsBSDEJSolution` instead quantifies existentially over
the filtration and over the two martingale legs.

`isBSDEJSolution_of_solvesBSDEJ` transports the former to the latter for the data
`bsdejDataOfGenerator f hf` and any forward process whose terminal value has coordinate `0` equal
to `ξ`, witnessing the existential by `ℱ := augJoint D`, `Filt := (augJoint D).rightCont` and the
càdlàg versions of the two canonical integrals supplied by `exists_cadlag_brownianLeg` and
`exists_cadlag_poissonLeg`.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.isBSDEJSolution_of_solvesBSDEJ` — the transport.
* `LevyStochCalc.BSDEJ.Solves.isBSDEJSolution_of_solvesBSDEJ_const` — its special case for the
  constant forward process `fun _ ω _ => ξ ω`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- An integrand valued in `Fin d → ℝ` whose coordinates are jointly measurable of finite energy
on `[0, T]` has finite total energy on `[0, T]`. -/
theorem lintegral_sum_sq_lt_top_of_energy {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hsq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hp : ∀ i : Fin d, Measurable fun p : Ω × ℝ => (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (((hm i).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun ω =>
    lintegral_finsetSum _ fun i _ => (hp i).comp measurable_prodMk_left
  simp_rw [hinner]
  rw [lintegral_finsetSum _ fun i (_ : i ∈ Finset.univ) => (hp i).lintegral_prod_right']
  exact ENNReal.sum_lt_top.2 fun i _ => lt_top_iff_ne_top.2 (hsq i)
/-- A solution of the backward equation pinned to a Lévy driver is a solution in the sense of
`BSDEJ.Definition.IsBSDEJSolution` for the data `bsdejDataOfGenerator f hf` and any forward
process whose terminal value has coordinate `0` equal to the terminal condition. -/
theorem isBSDEJSolution_of_solvesBSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    {ξ : Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U)
    (X : ℝ → Ω → (Fin 1 → ℝ)) (hX : ∀ ω, X T ω 0 = ξ ω) :
    LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution D.W D.N (bsdejDataOfGenerator f hf)
      X Y Z U T := by
  obtain ⟨MW, hMWa, hMWm, hMWeq, -, hMWmart, -, -⟩ :=
    exists_cadlag_brownianLeg D T hT Z h.Z_meas h.Z_prog h.Z_vanish h.Z_sq
  obtain ⟨MN, hMNa, hMNm, hMNeq, -, hMNmart, -, -⟩ :=
    exists_cadlag_poissonLeg D T hT U h.U_meas h.U_prog h.U_vanish h.U_sq
  refine ⟨h.Y_meas, h.Y_sup, lintegral_sum_sq_lt_top_of_energy h.Z_meas h.Z_sq,
    lt_top_iff_ne_top.2 h.U_sq, Eventually.of_forall h.Y_cadlag, augJoint D,
    D.isBrownianFiltration_aug, D.isPoissonFiltration_aug, (augJoint D).rightCont, rfl,
    h.Y_adapted, Probability.isStronglyProgressive_rightCont_pi h.Z_prog,
    h.U_prog.isStronglyProgressive_rightCont, MW, MN, hMWm, hMNm, hMWa, hMNa,
    ⟨h.Z_meas, h.Z_prog, sq_int_global_of_vanishing h.Z_vanish h.Z_sq, hMWeq⟩,
    ⟨h.U_meas, h.U_prog, marked_sq_int_global_of_vanishing h.U_vanish h.U_sq, hMNeq⟩,
    hMWmart, hMNmart, fun t ht => ?_⟩
  filter_upwards [h.eqn t ht, hMWeq T, hMWeq t, hMNeq T, hMNeq t] with ω heq hWT hWt hNT hNt
  rw [← hWT, ← hWt, ← hNT, ← hNt] at heq
  simp only [bsdejDataOfGenerator, hX ω]
  exact heq
/-- The transport of `isBSDEJSolution_of_solvesBSDEJ` for the constant forward process with value
the terminal condition. -/
theorem isBSDEJSolution_of_solvesBSDEJ_const
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    {ξ : Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U) :
    LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution D.W D.N (bsdejDataOfGenerator f hf)
      (fun _ ω _ => ξ ω) Y Z U T :=
  isBSDEJSolution_of_solvesBSDEJ D hf hT h _ fun _ => rfl
end LevyStochCalc.BSDEJ.Solves


