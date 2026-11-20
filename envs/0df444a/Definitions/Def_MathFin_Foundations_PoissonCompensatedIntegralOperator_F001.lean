-- Prove2me | Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F001
-- name    : MathFin_Foundations_PoissonCompensatedIntegralOperator_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:08:33.112542+00:00
-- url     : https://prove2.me/theorems/2a1c808e-bced-4b89-ac0a-c36a1997e8d9
-- title:
--   Source declarations: MathFin.Foundations.PoissonCompensatedIntegralOperator
-- statement:
--   Source-preserving extracted declarations from MathFin.Foundations.PoissonCompensatedIntegralOperator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F000
import Definitions.Def_SourceProof_e4022c8f2f69eecbce88538a

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated-Poisson integral operator on marked simple integrands

The two linear maps out of the marked simple-integrand module `levySimpleModule`, mirroring the
continuous `ItoIntegralL2.itoAssembly` / `simpleAssembly`:

* `intAssembly : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P` — the elementary compensated integral
  `∑_b φ_b · Ñ(box b)`, viewed in `L²(P)`;
* `emb : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν))` — the integrand
  `∑_b φ_b · 𝟙_{box b}`, viewed in `L²(dP ⊗ dν̂)` (the sibling module).

The `L²` isometry `‖intAssembly V‖ = ‖emb V‖`, obtained by summing the overlapping-box bilinear
pairing `integral_bilinear_pairing`, and the `extendOfNorm` CLM are built on these.

## Provenance

Mirrors the continuous `ItoIntegralL2` assembly; the compensated-integral content is our own.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The elementary compensated integral as a linear map -/

/-! ### The integrand embedding into the predictable `L²(dP ⊗ dν̂)` -/

/-! ### The isometry `‖intAssembly V‖ = ‖emb V‖` (summing the bilinear pairing) -/

/-- **The Itô–Lévy isometry on marked simple integrands** (the identity `extendOfNorm` consumes):
`‖intAssembly V‖ = ‖emb V‖`. Both squared norms expand into the same box-family double sum, equal
term-by-term by `pair_integral_eq` — i.e. the compensated integral into `L²(P)` and the integrand in
`L²(P ⊗ ν̂)` have equal norms. -/
theorem assembly_isometry (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ‖intAssembly N V‖ = ‖emb N V‖ := by
  have hsq : ‖intAssembly N V‖ ^ 2 = ‖emb N V‖ ^ 2 := by
    show ‖(intSumLp N V : Lp ℝ 2 P)‖ ^ 2 = ‖(embLp N V : Lp ℝ 2 (P.prod (referenceIntensity ν)))‖ ^ 2
    rw [lp_two_norm_sq, lp_two_norm_sq]
    rw [show (∫ ω, ((intSumLp N V : Ω → ℝ) ω) ^ 2 ∂P) = ∫ ω, (intSum N V ω) ^ 2 ∂P from
        integral_congr_ae (by
          filter_upwards [(memLp_intSum N V).coeFn_toLp] with ω hω; simp only [intSumLp]; rw [hω]),
      show (∫ p, ((embLp N V : Ω × (ℝ × E) → ℝ) p) ^ 2 ∂(P.prod (referenceIntensity ν)))
          = ∫ p, (embFun N V p) ^ 2 ∂(P.prod (referenceIntensity ν)) from
        integral_congr_ae (by
          filter_upwards [(memLp_embFun N V).coeFn_toLp] with p hp; simp only [embLp]; rw [hp]),
      intSum_sq_integral, embFun_sq_integral]
    exact Finset.sum_congr rfl fun ba hba => Finset.sum_congr rfl fun bb hbb =>
      _root_.Prove2MeSourceProof.h_e4022c8f2f69eecbce88538a N V hba hbb
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
/-! ### The Itô–Lévy integral CLM on the `L²` closure of the simple integrands -/

/-- **The `L²(dP ⊗ dν̂)` closure of the marked simple integrands** — the domain of the extended
Itô–Lévy integral. Concretely the topological closure of `emb`'s range: every element is an `L²`
limit of marked simple integrands `∑_b φ_b · 𝟙_{box b}`. Defining the target *as* this closure makes
the extension's density hypothesis a soft topological fact (`embCorestrict_denseRange`), sidestepping
an explicit marked-predictable `σ`-algebra characterisation. -/
noncomputable def levyClosure (N : PoissonRandomMeasure P ν) :
    Submodule ℝ (Lp ℝ 2 (P.prod (referenceIntensity ν))) :=
  (LinearMap.range (emb N)).topologicalClosure
/-- The integrand embedding `emb`, corestricted to the closure `levyClosure` of its range — the
dense-range map along which the elementary integral extends. -/
noncomputable def embCorestrict (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] levyClosure N :=
  (emb N).codRestrict (levyClosure N)
    (fun V => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (emb N) V))
/-- **Marked simple integrands are dense in their `L²` closure** `levyClosure`. Pushed into the
ambient `L²` the corestricted embedding's range is exactly `emb`'s range, whose closure is
`levyClosure` by construction; so every element of the closure subtype lies in the closure of that
range (`IsInducing.subtypeVal.dense_iff`). -/
theorem embCorestrict_denseRange (N : PoissonRandomMeasure P ν) :
    DenseRange (embCorestrict N) := by
  have hind : Topology.IsInducing ((↑) : levyClosure N → Lp ℝ 2 (P.prod (referenceIntensity ν))) :=
    Topology.IsInducing.subtypeVal
  rw [DenseRange, hind.dense_iff]
  intro x
  have himg : ((↑) : levyClosure N → Lp ℝ 2 (P.prod (referenceIntensity ν)))
        '' Set.range (embCorestrict N)
      = Set.range (emb N) := by
    rw [← Set.range_comp]; rfl
  rw [himg, ← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
  exact x.2
/-- **The Itô–Lévy compensated-Poisson integral as a CLM** on the `L²` closure of the marked simple
integrands: the norm-continuous extension of the elementary integral `intAssembly` along the dense
embedding `embCorestrict` (`LinearMap.extendOfNorm`). -/
noncomputable def itoLevyIntegralL2 (N : PoissonRandomMeasure P ν) :
    levyClosure N →L[ℝ] Lp ℝ 2 P := by
  -- `refine … ?_; exact` rather than a bare `(intAssembly N).extendOfNorm (embCorestrict N)`: the
  -- CLM goal type pins `Eₗ = ↥(levyClosure N)` with its seminormed-group instances, so `exact` bridges
  -- the `Submodule.addCommMonoid` vs seminormed `AddCommMonoid` diamond in one cheap `isDefEq`.
  -- (docs/patterns.md — "extendOfNorm into a submodule".)
  refine LinearMap.extendOfNorm (E := ↥(levySimpleModule N)) (F := Lp ℝ 2 P) (intAssembly N) ?_
  exact embCorestrict N
set_option maxHeartbeats 1000000 in
/-- **The Itô–Lévy `L²` isometry, in full generality** — LevyStochCalc's cited axiom #6: on the whole
`L²` closure `levyClosure`, `‖itoLevyIntegralL2 H‖ = ‖H‖`. The compensated-Poisson stochastic integral
is an `L²` isometry — proven on marked simple integrands (`assembly_isometry`, summing the
overlapping-box bilinear pairing) and extended by continuity to their closure. -/
theorem itoLevyIntegralL2_norm (N : PoissonRandomMeasure P ν) (H : levyClosure N) :
    ‖itoLevyIntegralL2 N H‖ = ‖H‖ := by
  have key : ∀ V : levySimpleModule N, ‖intAssembly N V‖ = ‖embCorestrict N V‖ :=
    fun V => by rw [Submodule.coe_norm]; exact assembly_isometry N V
  -- `unfold` exposes the def's already-bridged `extendOfNorm` term; discharging the isometry kernel
  -- against the submodule codomain re-triggers the instance diamond (a heavy but finite `whnf`), hence
  -- the raised `maxHeartbeats` above. (docs/patterns.md — "extendOfNorm into a submodule".)
  unfold itoLevyIntegralL2
  exact LinearMap.norm_extendOfNorm_eq_of_isometry (embCorestrict_denseRange N) key H
end MathFin


