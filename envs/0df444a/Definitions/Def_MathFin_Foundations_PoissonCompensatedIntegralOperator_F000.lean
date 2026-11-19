-- Prove2me | Definitions.Def_MathFin_Foundations_PoissonCompensatedIntegralOperator_F000
-- name    : MathFin_Foundations_PoissonCompensatedIntegralOperator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:36:50.35229+00:00
-- url     : https://prove2.me/theorems/8810b0ed-d661-4b33-9a56-a5c41b25347c
-- title:
--   Source declarations: MathFin.Foundations.PoissonCompensatedIntegralOperator
-- statement:
--   Source-preserving extracted declarations from MathFin.Foundations.PoissonCompensatedIntegralOperator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_ExtendOfNormIsometry_F000
import Definitions.Def_MathFin_Foundations_PoissonCompensatedSimpleIntegrand_F000
import Definitions.Def_SourceProof_1c3b8c92624b77e806423413

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

/-- A marked simple integrand's coefficient is in `L²(P)`: it is bounded (hence `L^∞`) and
measurable, so on the probability space it is `L²`. -/
lemma IsLevySimple.memLp_coe {N : PoissonRandomMeasure P ν} {V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)}
    (hV : IsLevySimple N V) (b : ℝ × ℝ × Set E) : MemLp (V b) 2 P := by
  obtain ⟨C, _, hC⟩ := hV.bound_coe
  have hm : Measurable (V b) := (show N.AdaptedAt b.1 (V b) from hV.measurable_coe b).measurable
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC b ω)).mono_exponent le_top
/-! ### The elementary compensated integral as a linear map -/

/-- The **elementary compensated integral** `∑_{b} φ_b(·) · Ñ(box b)(·)` of a marked simple
integrand, as a function `Ω → ℝ`. -/
noncomputable def intSum (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) : Ω → ℝ :=
  V.1.sum fun b φ => fun ω => φ ω * N.compensated (indexBox b) ω
/-- The elementary integral is in `L²(P)`: a finite sum of `L²` terms `φ_b · Ñ(box b)`
(`memLp_adapted_mul_compensated`). -/
lemma memLp_intSum (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    MemLp (intSum N V) 2 P := by
  have hrw : intSum N V
      = fun ω => ∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω := by
    funext ω; simp only [intSum, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  exact memLp_finsetSum V.1.support fun b hb =>
    _root_.Prove2MeSourceProof.h_1c3b8c92624b77e806423413 N (V.2.markMeasurable b hb) (V.2.markFinite b hb)
      (V.2.adapted b hb) (V.2.memLp_coe b)
/-- The elementary integral is additive in the integrand. -/
lemma intSum_add (N : PoissonRandomMeasure P ν) (V W : levySimpleModule N) :
    intSum N (V + W) = intSum N V + intSum N W := by
  have key : ((V + W : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) + (W : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [intSum, key]
  exact Finsupp.sum_add_index' (fun b => funext fun ω => by simp)
    (fun b φ ψ => funext fun ω => by simp [add_mul])
/-- The elementary integral is homogeneous in the integrand. -/
lemma intSum_smul (N : PoissonRandomMeasure P ν) (c : ℝ) (V : levySimpleModule N) :
    intSum N (c • V) = c • intSum N V := by
  have key : ((c • V : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = c • (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [intSum, key]
  rw [Finsupp.sum_smul_index' (fun b => funext fun ω => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ => funext fun ω => by simp [smul_eq_mul, mul_assoc]
/-- The elementary integral, in `L²(P)`. -/
noncomputable def intSumLp (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) : Lp ℝ 2 P :=
  (memLp_intSum N V).toLp
/-- **The compensated-Poisson integral as a linear map** `levySimpleModule →ₗ[ℝ] L²(P)`. -/
noncomputable def intAssembly (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P where
  toFun V := intSumLp N V
  map_add' V W := by
    rw [intSumLp, intSumLp, intSumLp,
      ← MemLp.toLp_add (memLp_intSum N V) (memLp_intSum N W)]
    congr 1
    exact intSum_add N V W
  map_smul' c V := by
    rw [intSumLp, intSumLp, RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_intSum N V)]
    congr 1
    exact intSum_smul N c V
/-! ### The integrand embedding into the predictable `L²(dP ⊗ dν̂)` -/

omit [IsProbabilityMeasure P] in
/-- A single box term `φ(ω)·𝟙_{(s,t]×A}(z)` is in `L²(P ⊗ ν̂)`: its square is
`φ(ω)² · 𝟙_box(z)`, an `L¹` product of `φ² ∈ L¹(P)` and the finite-box indicator `∈ L¹(ν̂)`
(`Integrable.mul_prod`). -/
lemma memLp_indicatorTerm {s t : ℝ} {A : Set E}
    (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤) {φ : Ω → ℝ} (hφm : Measurable φ)
    (hφL2 : MemLp φ 2 P) :
    MemLp (fun p : Ω × (ℝ × E) => φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) 2
      (P.prod (referenceIntensity ν)) := by
  haveI : SFinite (referenceIntensity ν) := by unfold referenceIntensity; infer_instance
  have hboxms : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hboxfin : referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := referenceIntensity_box_ne_top hAfin
  have hgm : Measurable
      (fun p : Ω × (ℝ × E) => φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) :=
    (hφm.comp measurable_fst).mul ((measurable_const.indicator hboxms).comp measurable_snd)
  refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
  have hform : (fun p : Ω × (ℝ × E) =>
        (φ p.1 * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) ^ 2)
      = fun p => (φ p.1) ^ 2 * ((Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2
          * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) p.2) := by
    funext p; ring
  rw [hform]
  have hg : Integrable (fun z : ℝ × E => (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z
      * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z) (referenceIntensity ν) := by
    rw [show (fun z : ℝ × E => (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z
          * (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) z)
        = (Set.Ioc s t ×ˢ A).indicator (fun _ => (1 : ℝ)) from by
      funext z; by_cases hz : z ∈ Set.Ioc s t ×ˢ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]]
    exact (integrable_indicator_iff hboxms).mpr (integrableOn_const (hs := hboxfin))
  exact (hφL2.integrable_sq).mul_prod hg
/-- The **integrand** `∑_b φ_b(·) · 𝟙_{box b}(·)` of a marked simple integrand, a function on
`Ω × (ℝ × E)`. -/
noncomputable def embFun (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    Ω × (ℝ × E) → ℝ :=
  V.1.sum fun b φ => fun p => φ p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2
/-- The integrand is in `L²(P ⊗ ν̂)`: a finite sum of `L²` box terms (`memLp_indicatorTerm`). -/
lemma memLp_embFun (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    MemLp (embFun N V) 2 (P.prod (referenceIntensity ν)) := by
  have hrw : embFun N V = fun p => ∑ b ∈ V.1.support,
      V.1 b p.1 * (Set.Ioc b.1 b.2.1 ×ˢ b.2.2).indicator (fun _ => (1 : ℝ)) p.2 := by
    funext p; simp only [embFun, indexBox, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  refine memLp_finsetSum V.1.support ?_
  intro b hb
  exact memLp_indicatorTerm (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    (show N.AdaptedAt b.1 (V.1 b) from V.2.measurable_coe b).measurable (V.2.memLp_coe b)
/-- The integrand embedding is additive in the integrand. -/
lemma embFun_add (N : PoissonRandomMeasure P ν) (V W : levySimpleModule N) :
    embFun N (V + W) = embFun N V + embFun N W := by
  have key : ((V + W : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) + (W : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [embFun, key]
  exact Finsupp.sum_add_index' (fun b => funext fun p => by simp)
    (fun b φ ψ => funext fun p => by simp [add_mul])
/-- The integrand embedding is homogeneous in the integrand. -/
lemma embFun_smul (N : PoissonRandomMeasure P ν) (c : ℝ) (V : levySimpleModule N) :
    embFun N (c • V) = c • embFun N V := by
  have key : ((c • V : levySimpleModule N) : (ℝ × ℝ × Set E) →₀ (Ω → ℝ))
      = c • (V : (ℝ × ℝ × Set E) →₀ (Ω → ℝ)) := rfl
  simp only [embFun, key]
  rw [Finsupp.sum_smul_index' (fun b => funext fun p => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun b _ => funext fun p => by simp [smul_eq_mul, mul_assoc]
/-- The integrand, in `L²(P ⊗ ν̂)`. -/
noncomputable def embLp (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    Lp ℝ 2 (P.prod (referenceIntensity ν)) := (memLp_embFun N V).toLp
/-- **The integrand embedding as a linear map** `levySimpleModule →ₗ[ℝ] L²(dP ⊗ dν̂)`. -/
noncomputable def emb (N : PoissonRandomMeasure P ν) :
    levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν)) where
  toFun V := embLp N V
  map_add' V W := by
    rw [embLp, embLp, embLp, ← MemLp.toLp_add (memLp_embFun N V) (memLp_embFun N W)]
    congr 1
    exact embFun_add N V W
  map_smul' c V := by
    rw [embLp, embLp, RingHom.id_apply, ← MemLp.toLp_const_smul c (memLp_embFun N V)]
    congr 1
    exact embFun_smul N c V
/-! ### The isometry `‖intAssembly V‖ = ‖emb V‖` (summing the bilinear pairing) -/

/-- For `g : Lp ℝ 2 μ`, `‖g‖² = ∫ (g a)² ∂μ`. -/
lemma lp_two_norm_sq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} (g : Lp ℝ 2 μ) :
    ‖g‖ ^ 2 = ∫ a, (g a) ^ 2 ∂μ := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show (g a) * (g a) = (g a) ^ 2
  ring
/-- Each box term of the elementary integral is in `L²(P)`. -/
lemma memLp_intTerm (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {b : ℝ × ℝ × Set E} (hb : b ∈ V.1.support) :
    MemLp (fun ω => V.1 b ω * N.compensated (indexBox b) ω) 2 P :=
  _root_.Prove2MeSourceProof.h_1c3b8c92624b77e806423413 N (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    (V.2.adapted b hb) (V.2.memLp_coe b)
/-- Each box term of the integrand is in `L²(P ⊗ ν̂)`. -/
lemma memLp_embTerm (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {b : ℝ × ℝ × Set E} (hb : b ∈ V.1.support) :
    MemLp (fun p : Ω × (ℝ × E) => V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2) 2
      (P.prod (referenceIntensity ν)) :=
  memLp_indicatorTerm (V.2.markMeasurable b hb) (V.2.markFinite b hb)
    (show N.AdaptedAt b.1 (V.1 b) from V.2.measurable_coe b).measurable (V.2.memLp_coe b)
/-- A pair of elementary-integral box terms has an integrable product (`L² · L²`), in scalar-lambda
form (so the double-sum `∫ = ∑∫` rewrites match). -/
lemma integrable_intPair (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    Integrable (fun ω => (V.1 ba ω * N.compensated (indexBox ba) ω)
      * (V.1 bb ω * N.compensated (indexBox bb) ω)) P :=
  (memLp_intTerm N V hba).integrable_mul (memLp_intTerm N V hbb)
/-- A pair of integrand box terms has an integrable product (`L² · L²`), in scalar-lambda form. -/
lemma integrable_embPair (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    Integrable (fun p : Ω × (ℝ × E) =>
      (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
        * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2))
      (P.prod (referenceIntensity ν)) :=
  (memLp_embTerm N V hba).integrable_mul (memLp_embTerm N V hbb)
/-- **The `L²(P)` second moment as a double sum** over the box family. -/
lemma intSum_sq_integral (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ∫ ω, (intSum N V ω) ^ 2 ∂P
      = ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
                * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P := by
  have hrw : intSum N V
      = fun ω => ∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω := by
    funext ω; simp only [intSum, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  have hsq : (fun ω => (∑ b ∈ V.1.support, V.1 b ω * N.compensated (indexBox b) ω) ^ 2)
      = fun ω => ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          (V.1 ba ω * N.compensated (indexBox ba) ω)
            * (V.1 bb ω * N.compensated (indexBox bb) ω) := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  rw [integral_finsetSum V.1.support fun ba hba => integrable_finsetSum V.1.support fun bb hbb =>
    integrable_intPair N V hba hbb]
  refine Finset.sum_congr rfl fun ba hba => ?_
  exact integral_finsetSum V.1.support fun bb hbb =>
    integrable_intPair N V hba hbb
/-- **The `L²(P ⊗ ν̂)` integrand norm as a double sum** over the box family. -/
lemma embFun_sq_integral (N : PoissonRandomMeasure P ν) (V : levySimpleModule N) :
    ∫ p, (embFun N V p) ^ 2 ∂(P.prod (referenceIntensity ν))
      = ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
                * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
            ∂(P.prod (referenceIntensity ν)) := by
  have hrw : embFun N V = fun p => ∑ b ∈ V.1.support,
      V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2 := by
    funext p; simp only [embFun, Finsupp.sum, Finset.sum_apply]
  rw [hrw]
  have hsq : (fun p : Ω × (ℝ × E) =>
        (∑ b ∈ V.1.support, V.1 b p.1 * (indexBox b).indicator (fun _ => (1 : ℝ)) p.2) ^ 2)
      = fun p => ∑ ba ∈ V.1.support, ∑ bb ∈ V.1.support,
          (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
            * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2) := by
    funext p; rw [sq, Finset.sum_mul_sum]
  rw [hsq]
  rw [integral_finsetSum V.1.support fun ba hba => integrable_finsetSum V.1.support fun bb hbb =>
    integrable_embPair N V hba hbb]
  refine Finset.sum_congr rfl fun ba hba => ?_
  exact integral_finsetSum V.1.support fun bb hbb =>
    integrable_embPair N V hba hbb
/-! ### The Itô–Lévy integral CLM on the `L²` closure of the simple integrands -/

end MathFin


