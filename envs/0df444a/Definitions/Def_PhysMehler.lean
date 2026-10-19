-- Prove2me | Definitions.Def_PhysMehler
-- name    : PhysMehler
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-18T10:18:39.978+00:00
-- url     : https://prove2.me/theorems/d807e4b7-5b53-4183-afcb-3416ab8502e0
-- title:
--   The Lean 4 theorem `substrate_separable` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/PhysMehler.lean`): generated def bundle for PhysMehler. See BookProof/PhysMehler.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/PhysMehler.lean

import Theorems.Thm_PhysFunctionalAnalysis_exists_atomless_sphere_measure

import Theorems.Thm_PhysFunctionalAnalysis_l2_separable


import Definitions.Def_PhysFunctionalAnalysis
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterG3


/-!
# The Kopperman formalism, in Lean

This module assembles, as one explicit object, the formalism of
`Kopperman_Tutorial.p.tex` (after Kopperman's 1967 *"The `L_{ω₁,ω₁}`-Theory of
Hilbert Spaces"*): a **separable real Hilbert space** (the "ontological
substrate"), a **countable dense decidable skeleton** (the computable
approximants), and an **atomless probability prior** (the Mehler "uncertainty"
layer — the Gaussian limit of the uniform measure on the high-dimensional
sphere).

Each component is *already proved* elsewhere in `PnpProof/`; here they are named
and packaged so that statements can be made and checked **about the formalism
itself**. Nothing here is new mathematics and nothing here is an axiom: the file
is `sorry`-free and `axiom`-free, like the rest of the development.

What this formalism supports, and where those statements live:
* the model separation `σ` ("computable selections are prior-null while
  verification is cheap"): `model_P_ne_NP`, `model_P_ne_NP_circuit` (`Main.lean`);
* the relationship to the Clay statement: `model_vs_clay_disjointness`
  (`Main.lean`, T5) — proved *inside* this formalism.

What it does **not** support, and must not be made to via an `axiom`: a bridge
`σ → (P ≠ NP)`. See `PNP_IMPLEMENTATION_PLAN.md` Part 8 / Part 9. The honest way
to test the bridge is to *state it as a theorem and let Lean try to prove it* —
not to assert it as an axiom, which is precisely the act of telling Lean to stop
checking.
-/

namespace PhysHSGaussian

open MeasureTheory Set Filter
open scoped ENNReal Topology
open PhysMeasureBasis

/-! Inlined from `BookProof/PhysHSGaussian/Part3.lean`: the `PhysHSGaussian`
bundle was never published, so this consumer carries the four declarations it
needs (platform-world rule: an unpublished dep cannot be imported). -/

/-- The infinite product of standard Gaussians (the law of an i.i.d. Gaussian
    sequence). -/
noncomputable def gammaMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)



noncomputable instance gammaMeasure_isProbability : IsProbabilityMeasure gammaMeasure := by
  unfold gammaMeasure; infer_instance



/-- Empirical squared norm of the first `k` coordinates. -/
def normSq (k : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range k, (ω i)^2



theorem gaussian_concentration_sphere :
    ∀ᵐ ω ∂gammaMeasure,
      Filter.Tendsto (fun k => normSq k ω / k) Filter.atTop (𝓝 1) := by
  convert ProbabilityTheory.strong_law_ae _ _ _ _ using 1;
  case convert_4 => exact ℝ;
  case convert_10 => exact fun i ω => ( ω i ) ^ 2;
  all_goals try infer_instance;
  · have h_integral : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = 1 := by
      have h_gauss : ∫ x : ℝ, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ←
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      have h_gauss : ∫ x : ℕ → ℝ, x 0 ^ 2 ∂gammaMeasure = ∫ x : ℝ, x ^ 2
        ∂(ProbabilityTheory.gaussianReal 0 1) := by
        have h_map : MeasureTheory.Measure.map (fun x : ℕ → ℝ => x 0) gammaMeasure =
          ProbabilityTheory.gaussianReal 0 1 := by
          convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1
          <;> (first | rfl | infer_instance);
        rw [ ← h_map, MeasureTheory.integral_map ];
        · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      linarith;
    simp_all +decide [ div_eq_inv_mul, normSq ];
  · have h_integrable : MeasureTheory.Integrable (fun x : ℝ => x^2) (ProbabilityTheory.gaussianReal
    0 1) := by
      have h_gauss_integrable : ∫ x, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
        have := @ProbabilityTheory.variance_id_gaussianReal 0 1;
        rw [ ProbabilityTheory.variance, ProbabilityTheory.evariance_eq_lintegral_ofReal, ←
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae ] at this <;> norm_num at *;
        · exact this;
        · exact Filter.Eventually.of_forall fun x => sq_nonneg x;
        · exact Continuous.aestronglyMeasurable ( continuous_pow 2 );
      exact ( by contrapose! h_gauss_integrable; rw [ MeasureTheory.integral_undef
          h_gauss_integrable ] ; norm_num );
    have h_integrable : MeasureTheory.Integrable (fun ω : ℕ → ℝ => ω 0 ^ 2) (Measure.infinitePi (fun
      _ : ℕ => ProbabilityTheory.gaussianReal 0 1)) := by
      have h_map : (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)).map (fun ω
        : ℕ → ℝ => ω 0) = ProbabilityTheory.gaussianReal 0 1 := by
        convert MeasureTheory.Measure.infinitePi_map_eval _ _ using 1;
        exact fun _ => inferInstance
      rw [ ← h_map ] at h_integrable;
      rwa [ MeasureTheory.integrable_map_measure ] at h_integrable;
      · exact h_integrable.1;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
    exact h_integrable;
  · have h_indep : ProbabilityTheory.iIndepFun (fun i : ℕ => fun ω : ℕ → ℝ => ω i) gammaMeasure
    := by
      convert ProbabilityTheory.iIndepFun_infinitePi ( fun i => measurable_id ) using 1
      <;> (first | rfl | infer_instance);
    exact fun i j hij => h_indep.indepFun hij |> fun h => h.comp ( measurable_id.pow_const 2 ) (
      measurable_id.pow_const 2 );
  · intro i
    have h_ident : ProbabilityTheory.IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0)
      gammaMeasure gammaMeasure := by
      constructor;
      · exact measurable_pi_apply i |> Measurable.aemeasurable;
      · exact measurable_pi_apply 0 |> Measurable.aemeasurable;
      · have h_map : ∀ i : ℕ, Measure.map (fun ω : ℕ → ℝ => ω i) gammaMeasure =
        ProbabilityTheory.gaussianReal 0 1 := by
          intro i
          generalize_proofs at *; (
          convert MeasureTheory.Measure.infinitePi_map_eval ( fun _ =>
            ProbabilityTheory.gaussianReal 0 1 ) i using 1 <;> (first | rfl | infer_instance));
        rw [ h_map i, h_map 0 ]
    generalize_proofs at *; (
    exact h_ident.comp ( measurable_id.pow_const 2 ))



end PhysHSGaussian

namespace PhysMehler

open PhysMeasureBasis PhysFunctionalAnalysis PhysHSGaussian
open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The abstract data of a **Kopperman formalism** on a carrier Hilbert space
    `H`: separability, a countable dense decidable skeleton, and an atomless
    probability prior. -/
structure Formalism (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] where
  /-- The substrate is separable (Kopperman's completeness/separability axiom; in
      Lean the standard separable Hilbert space is constructed directly). -/
  separable : TopologicalSpace.SeparableSpace H
  /-- The decidable dense skeleton: the computable approximants. -/
  skeleton : Set H
  skeleton_countable : skeleton.Countable
  skeleton_dense : Dense skeleton
  /-- The Mehler prior. -/
  prior : Measure H
  prior_isProb : IsProbabilityMeasure prior
  /-- "Probability as political choice": the prior is atomless — no single state
      carries positive mass. -/
  prior_atomless : ∀ x : H, prior {x} = 0

/-! ## The substrate: the standard separable Hilbert space -/

/-- The ontological substrate `H`: `L²([0,1])`, the standard separable real
    Hilbert space. (Kopperman uses `L_{ω₁,ω₁}` to pin this down categorically; in
    Lean's type theory it is constructed outright, and `hilbert_classification`
    records that any two such spaces are isometrically isomorphic.) -/
noncomputable abbrev Substrate := Lp ℝ 2 unitMeasure

theorem substrate_separable : TopologicalSpace.SeparableSpace Substrate := l2_separable

/-- The decidable dense skeleton exists: a countable dense subset of the
    substrate (the computable approximants of the tutorial's "decidable dense
    subset"). -/
theorem substrate_decidable_skeleton : ∃ D : Set Substrate, D.Countable ∧ Dense D := by
  haveI := l2_separable
  exact TopologicalSpace.exists_countable_dense Substrate

/-! ## The Mehler measure: the Gaussian limit of the uniform sphere -/

/-- The **Mehler prior**: the infinite-product Gaussian measure on coordinate
    space — Mehler's 1866 limit of the uniform measure on the `√k`-sphere. -/
noncomputable abbrev MehlerPrior : Measure (ℕ → ℝ) := gammaMeasure

theorem mehler_isProbability : IsProbabilityMeasure MehlerPrior :=
  gammaMeasure_isProbability

/-- The Mehler prior "lives on the infinite-dimensional sphere": the normalized
    empirical squared norm concentrates at `1` almost surely (Poincaré–Borel /
    the strong law). -/
theorem mehler_concentrates_on_sphere :
    ∀ᵐ ω ∂MehlerPrior, Tendsto (fun k => normSq k ω / k) atTop (𝓝 1) :=
  gaussian_concentration_sphere

/-! ## The atomless prior layer -/

/-- Every separable inner-product space carrying two orthonormal vectors admits an
    atomless probability prior concentrated on the unit sphere — the abstract
    realization of the Mehler "uncertainty" layer on any Kopperman substrate. -/
theorem admits_atomless_prior (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (e₀ e₁ : E) (h : Orthonormal ℝ ![e₀, e₁]) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧ (∀ x, μ {x} = 0) ∧ ∀ᵐ v ∂μ, ‖v‖ = 1 :=
  exists_atomless_sphere_measure E e₀ e₁ h

/-! ## K-model: "choosing a measure = choosing a model of the formalism"

These results make precise the maintainer's claim that *within the formalism,
choosing a probability measure is choosing a model*. Every model carries an
atomless probability prior (`model_has_prior`); conversely every atomless
probability measure on the substrate is the prior of a model (`formalismOfPrior`,
`prior_surjective_onto_atomless`), so with the substrate (and a canonical
skeleton) fixed the prior-projection is a bijection onto the atomless probability
measures. `koppermanSubstrate` is a concrete witness that the substrate admits a
model.

**Two computational layers — the formalism is not "anti-computable".** The prior
nulls computable *selection* functions (the P-side: `almost_all_not_computable`,
T2). But the formalism *also defines computable NP functions*: the candidate
*verification* is computable (`verifyBits_computable`, M5) — indeed an explicit
`O(k)` Boolean circuit (`model_P_ne_NP_circuit`, N1) — and the decidable dense
skeleton is the layer of *computable approximations* (`pnp.tex` §6/§10: the
verification of a constant output "is in NP", and the formalism rests on a dense
countable basis of computable approximants with computable probabilities). The
separation `model_P_ne_NP` (T3) *is* this coexistence: computable verification with
an a.s.-uncomputable selection. Without the computable layer there would be no NP
side to separate. (Fidelity note: the `skeleton` field here only asserts
`Countable ∧ Dense`; the *computability* of the NP layer is carried by the separate
`Computable`/circuit theorems, not by a field of `Formalism` — see
`PNP_IMPLEMENTATION_PLAN.md` Part 11, "two computational layers".)

**This is sound model theory of the `Formalism` structure — not a Clay bridge.**
"Model" here means a model of *this formalism*, whose decidable skeleton is indexed
by the standard `ℕ`; that is exactly what is needed to *define* the standard
arithmetic statements, and no model *of set theory* is involved or required. The
reason it still does not yield the Clay statement is **arithmetic, not
foundational**: what the measure establishes is the separation `σ` of
`model_P_ne_NP` (computable selections are prior-null), which is a *different*
arithmetic sentence from "SAT ∉ P" — `model_vs_clay_disjointness` (T5) is the proof
that the two are disjoint (`σ` is blind to any individual decidable language). See
`PNP_IMPLEMENTATION_PLAN.md` Part 11 (K-model). -/

/-- **K-model.0** (projection): every model of the formalism carries an atomless
probability measure. (True by construction — `prior` is a field.) -/
theorem model_has_prior {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] (F : Formalism H) :
    IsProbabilityMeasure F.prior ∧ ∀ x, F.prior {x} = 0 :=
  ⟨F.prior_isProb, F.prior_atomless⟩

/-- An explicit orthonormal pair in the substrate `L²([0,1])`: the `√2`-scaled
indicators of the two halves `[0,½]` and `(½,1]`. -/
theorem substrate_orthonormal_pair :
    ∃ e₀ e₁ : Substrate, Orthonormal ℝ ![e₀, e₁] := by
  have hμs : unitMeasure (Icc (0:ℝ) (1/2)) ≠ ∞ := measure_ne_top _ _
  have hμt : unitMeasure (Ioc (1/2:ℝ) 1) ≠ ∞ := measure_ne_top _ _
  have hrestr : unitMeasure = volume.restrict (Icc (0:ℝ) 1) := rfl
  have hsr : unitMeasure.real (Icc (0:ℝ) (1/2)) = 1/2 := by
    have h : unitMeasure (Icc (0:ℝ) (1/2)) = ENNReal.ofReal (1/2) := by
      rw [hrestr, Measure.restrict_apply measurableSet_Icc,
          Set.inter_eq_left.mpr (Set.Icc_subset_Icc le_rfl (by norm_num))]
      norm_num [Real.volume_Icc]
    rw [measureReal_def, h, ENNReal.toReal_ofReal]
    norm_num
  have htr : unitMeasure.real (Ioc (1/2:ℝ) 1) = 1/2 := by
    have h : unitMeasure (Ioc (1/2:ℝ) 1) = ENNReal.ofReal (1/2) := by
      rw [hrestr, Measure.restrict_apply measurableSet_Ioc,
          Set.inter_eq_left.mpr
            (Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc (by norm_num) le_rfl))]
      norm_num [Real.volume_Ioc]
    rw [measureReal_def, h, ENNReal.toReal_ofReal]
    norm_num
  have hempty : (Icc (0:ℝ) (1/2)) ∩ (Ioc (1/2:ℝ) 1) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨_, h1⟩, h2, _⟩; linarith
  have hnorm : ∀ (s : Set ℝ) (hs : MeasurableSet s) (hμ : unitMeasure s ≠ ∞),
      unitMeasure.real s = 1/2 → ‖indicatorConstLp 2 hs hμ (Real.sqrt 2)‖ = 1 := by
    intro s hs hμ hval
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), hval, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), show (1:ℝ) / (2:ℝ≥0∞).toReal = 1/2 by norm_num,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      show (2:ℝ) * (1/2) = 1 by norm_num, Real.sqrt_one]
  set e₀ := indicatorConstLp 2 measurableSet_Icc hμs (Real.sqrt 2) with he₀
  set e₁ := indicatorConstLp 2 measurableSet_Ioc hμt (Real.sqrt 2) with he₁
  have hn0 : ‖e₀‖ = 1 := by rw [he₀]; exact hnorm _ measurableSet_Icc hμs hsr
  have hn1 : ‖e₁‖ = 1 := by rw [he₁]; exact hnorm _ measurableSet_Ioc hμt htr
  have horth : (inner ℝ e₀ e₁ : ℝ) = 0 := by
    rw [he₀, he₁, L2.inner_indicatorConstLp_indicatorConstLp, hempty, measureReal_empty,
      zero_smul]
  exact ⟨e₀, e₁, orthonormal_vecCons_iff.mpr ⟨hn0, fun i => by fin_cases i; simpa using horth,
    orthonormal_vecCons_iff.mpr ⟨hn1, fun i => i.elim0, Orthonormal.of_isEmpty _⟩⟩⟩

section Substrate

/-- Equip the substrate with its Borel σ-algebra so the atomless-prior
construction (H7) applies. -/
noncomputable local instance substrateMeasurableSpace : MeasurableSpace Substrate := borel _

local instance substrateBorelSpace : BorelSpace Substrate := ⟨rfl⟩

/-- The substrate carries an atomless probability measure (from the explicit
orthonormal pair via H7). -/
theorem exists_atomless_prob_substrate :
    ∃ μ : Measure Substrate, IsProbabilityMeasure μ ∧ ∀ x, μ {x} = 0 := by
  obtain ⟨e₀, e₁, h⟩ := substrate_orthonormal_pair
  obtain ⟨μ, hμ1, hμ2, _⟩ := exists_atomless_sphere_measure Substrate e₀ e₁ h
  exact ⟨μ, hμ1, hμ2⟩

/-- **"Choosing a measure is choosing a model":** from any atomless probability
measure on the substrate, build a model of the formalism with that measure as its
prior (substrate fixed, canonical skeleton). -/
noncomputable def formalismOfPrior (μ : Measure Substrate)
    (h1 : IsProbabilityMeasure μ) (h2 : ∀ x, μ {x} = 0) : Formalism Substrate where
  separable := substrate_separable
  skeleton := Classical.choose substrate_decidable_skeleton
  skeleton_countable := (Classical.choose_spec substrate_decidable_skeleton).1
  skeleton_dense := (Classical.choose_spec substrate_decidable_skeleton).2
  prior := μ
  prior_isProb := h1
  prior_atomless := h2

@[simp] theorem prior_formalismOfPrior (μ : Measure Substrate)
    (h1 : IsProbabilityMeasure μ) (h2 : ∀ x, μ {x} = 0) :
    (formalismOfPrior μ h1 h2).prior = μ := rfl

/-- The prior-projection is surjective onto the atomless probability measures:
with the substrate (and a canonical skeleton) fixed, choosing such a measure is
exactly choosing a model. -/
theorem prior_surjective_onto_atomless (μ : Measure Substrate)
    (h1 : IsProbabilityMeasure μ) (h2 : ∀ x, μ {x} = 0) :
    ∃ F : Formalism Substrate, F.prior = μ :=
  ⟨formalismOfPrior μ h1 h2, rfl⟩

/-- **K-ext:** the substrate admits a model of the formalism. -/
theorem nonempty_formalism_substrate : Nonempty (Formalism Substrate) := by
  obtain ⟨μ, h1, h2⟩ := exists_atomless_prob_substrate
  exact ⟨formalismOfPrior μ h1 h2⟩

/-- The canonical atomless probability measure on the Kopperman substrate, used as
the substrate prior of the bounded-prior model.  It is the shared analytic datum
of the decoupled Kopperman–Solovay framework, promoted here so that the generic
`RandomMap2` development does not have to reach into a Riemann-Hypothesis file for
it. -/
noncomputable def rcpPriorOnSubstrate : Measure Substrate := Classical.choose exists_atomless_prob_substrate

instance rcpPriorOnSubstrate_isProb : IsProbabilityMeasure rcpPriorOnSubstrate :=
  (Classical.choose_spec exists_atomless_prob_substrate).1

theorem rcpPriorOnSubstrate_atomless : ∀ x : Substrate, rcpPriorOnSubstrate {x} = 0 :=
  (Classical.choose_spec exists_atomless_prob_substrate).2

/-- A concrete model of the Kopperman formalism on the substrate `L²([0,1])`. -/
noncomputable def koppermanSubstrate : Formalism Substrate :=
  formalismOfPrior (Classical.choose exists_atomless_prob_substrate)
    (Classical.choose_spec exists_atomless_prob_substrate).1
    (Classical.choose_spec exists_atomless_prob_substrate).2

end Substrate

/-! ## T-conserv: arithmetic truth is invariant across formalism and foundation

`Π⁰₂`-invariance / conservativity. The truth value of an arithmetical sentence —
here a `Π⁰₂` sentence `∀ a, ∃ b, p a b` whose matrix `p` is decidable and ranges
over the *standard* naturals — does **not** depend on which `Formalism` is chosen
as the model, nor on any `ZFSet` ("foundation") parameter. This is the
machine-checkable proxy for the maintainer's directive that *"no prior, and no
foundation, moves a first-order arithmetic truth"* (`PNP_IMPLEMENTATION_PLAN.md`
Part 11, queue item **F-min**, step (c)): the `Formalism` and `ZFSet` parameters
genuinely appear in the statement and are proved to drop out.

It is **not** an internal meta-logical provability/independence theorem. Lean has
no theory-comparison or provability predicate in mainline Mathlib, so a literal
"the Kopperman base is PA-incomparable / co-consistent" claim is **not** stated
here (Part 11 fences); the import DAG, the `#print axioms` footprint, and this
`T-conserv` invariance are the honest *proxies* for those meta-claims. The reason
the invariance holds is exactly point 4 of Part 11: a `Π⁰₂` sentence over the
standard `ℕ` is absolute, and Lean's `ℕ` has no nonstandard elements, so the
sentence literally *is* the standard arithmetic sentence — the parameters cannot
move it. -/

/-- A `Π⁰₂` arithmetical sentence over the standard naturals, with decidable
matrix `p` (`∀ a, ∃ b, p a b`). "P ≠ NP" has this shape over an NP-complete
language; see `PNP_IMPLEMENTATION_PLAN.md` Part 11. -/
def Pi02 (p : ℕ → ℕ → Bool) : Prop := ∀ a, ∃ b, p a b = true

/-- The interpretation of a `Π⁰₂` sentence *"inside a formalism `F`, over a
foundation `z`"*. It ignores both the `Formalism` and the `ZFSet` parameter,
because the matrix ranges over the standard `ℕ` — that is the whole content of
`T-conserv` below.

This is the *trivial* wrapper (truth `:= Pi02 p`). A **non-trivial geometric
witness** of the same truth lives in `PnpProof/GeometricTruth.lean`
(`PNP_IMPLEMENTATION_PLAN.md` Part 12): `interpPi02_geom b p F`, defined as the
metric identity `‖Ψ_p − Ψ_true‖ = 0` for the completed vector
`Ψ_p = Σ_x OK_p x /(x+1) · e_x` in `F`'s separable substrate, with
`interpPi02_geom_iff : interpPi02_geom b p F ↔ Pi02 p`. That refinement realizes
the truth *inside the substrate of the chosen model* rather than as the present
`Iff.rfl`; it is a faithful **restatement**, not a decision procedure (its `OK_p`
is noncomputable / `Classical.choice`), and it gives no Clay leverage (Part 12
fences; T5 stands). -/
def interpPi02 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → ℕ → Bool) (_F : Formalism H) (_z : ZFSet) : Prop := Pi02 p

/-- **T-conserv** (`Π⁰₂`-invariance / conservativity, Part 11 step (c)): the
truth of a `Π⁰₂` arithmetical sentence is invariant under any choice of
`Formalism` (the prior/model) **and** under any choice of `ZFSet` foundation —
the parameters drop out. This is the checked core of "no prior, no foundation
moves an arithmetic truth"; it is a proxy for, not an internal proof of, the
meta-logical co-consistency/standardness claims (see the section docstring and
Part 11 fences). -/
theorem arith_truth_invariant {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → ℕ → Bool) (F₁ F₂ : Formalism H) (z₁ z₂ : ZFSet) :
    interpPi02 p F₁ z₁ ↔ interpPi02 p F₂ z₂ := Iff.rfl

/-- Specialisation of `arith_truth_invariant` to a fixed foundation: the truth of
a `Π⁰₂` sentence does not depend on which model (`Formalism`) realises it. -/
theorem pi02_invariant_of_formalism {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → ℕ → Bool) (F₁ F₂ : Formalism H) (z : ZFSet) :
    interpPi02 p F₁ z ↔ interpPi02 p F₂ z :=
  arith_truth_invariant p F₁ F₂ z z

/-- The interpreted truth coincides with the plain arithmetic sentence: the
formalism/foundation wrapping is content-free. (The geometric refinement
`interpPi02_geom_iff` of Part 12 proves the *same* coincidence with a non-trivial
vector-identity witness instead of `Iff.rfl`.) -/
theorem interpPi02_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → ℕ → Bool) (F : Formalism H) (z : ZFSet) :
    interpPi02 p F z ↔ Pi02 p := Iff.rfl

end PhysMehler


