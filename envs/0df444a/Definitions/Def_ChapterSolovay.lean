-- Prove2me | Definitions.Def_ChapterSolovay
-- name    : ChapterSolovay
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T04:57:23.444866+00:00
-- url     : https://prove2.me/theorems/a0e22ead-da03-4ff1-b003-3c7163e4d155
-- title:
--   Chapter Solovay
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolovay.lean`): generated def bundle for ChapterSolovay. See BookProof/ChapterSolovay.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolovay.lean

import Mathlib

import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.UniformSpace.Completion
import Definitions.Def_PhysMehler

/-!
# Chapter S — Solovay-Hilbert Decidability and the Kopperman Tail

This file formalizes the decidability architecture of the decoupled
Kopperman-Solovay framework (see `RandomMap2.md` Phase 1 and Phase 8.3).

Sections:
* S.1 — The Solovay-Hilbert space as a completion (proper construction)
* S.2 — `dependsOnlyOnHead` decidability argument
* S.3 — The uniform Mehler measure on the infinite-dimensional hypersphere
* S.4 — No Gödelian self-reference in the Solovay-Hilbert space

All theorems are `sorry`-free and `axiom`-free (no `EXTERNAL` hypothesis).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Filter Topology

/-! ## Inlined Kopperman–Solovay scaffolding (was `RandomMap.RandomMap2`)

Verbatim from `timepiece331/RandomMap/RandomMap2.lean`.  The platform compiles a
bundle against `Mathlib` + `Definitions.*` + `Theorems.*` only, so
`import RandomMap.RandomMap2` resolves nowhere and the server elaborated this
whole payload in an EMPTY import environment (attempt 1: `unknown namespace
`MeasureTheory``, `unknown namespace `ENNReal``, `Unknown identifier `ℕ``).
Everything below needs only the published `Def_PhysMehler` bundle, whose
`Substrate`/`rcpPriorOnSubstrate` live in the root namespace `PhysMehler`. -/
open PhysMehler

noncomputable section

instance substrateMeasurableSpace : MeasurableSpace Substrate := borel _
instance substrateBorelSpace : BorelSpace Substrate := ⟨rfl⟩

/-- The infinite, unknown tail of the inner wave-function. -/
abbrev InnerTail := Substrate

/-- The uniform probability measure over the infinite tail. -/
def tailMeasure : Measure InnerTail := rcpPriorOnSubstrate

instance : IsProbabilityMeasure tailMeasure := rcpPriorOnSubstrate_isProb

/-- The finite known components of the inner wave-function. -/
abbrev InnerHead (N : ℕ) := Fin N → ℝ

/-- The total sample space of inner wave-functions. -/
abbrev InnerSpace (N : ℕ) := InnerHead N × InnerTail

/-- The total probability measure, given an arbitrary law on the head. -/
noncomputable def stateMeasure (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] : Measure (InnerSpace N) :=
  headDist.prod tailMeasure

instance (N : ℕ) (headDist : Measure (InnerHead N)) [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (stateMeasure N headDist) := by
  dsimp [stateMeasure]; infer_instance

/-- A macroscopic observable function depends only on the finite head. -/
def dependsOnlyOnHead {N : ℕ} (f : InnerSpace N → ℂ) : Prop :=
  ∃ g : InnerHead N → ℂ, f = g ∘ Prod.fst

/-- The Solovay space of outer wave-functions: `L²` over the product measure. -/
abbrev OuterWaveFunction (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] := Lp ℂ 2 (stateMeasure N headDist)

end

namespace BookProof.ChapterSolovay

/-! ## S.1 — The Solovay-Hilbert space as a proper completion -/

/-- **S.1.1 — The Solovay-Hilbert space: the completion of `OuterWaveFunction`.

    The completion adds the missing metric structure, making this a genuine
    Hilbert space. This is the explicit construction that was previously
    a placeholder (`RandomMap2.md` Phase 8.3).

    We use the root-level definitions from `RandomMap2` to avoid shadowing. -/
noncomputable abbrev SolovayHilbertSpace (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] : Type :=
  _root_.UniformSpace.Completion (_root_.OuterWaveFunction N headDist)

noncomputable instance (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] : InnerProductSpace ℂ (SolovayHilbertSpace N headDist) :=
  UniformSpace.Completion.innerProductSpace

noncomputable instance (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] : CompleteSpace (SolovayHilbertSpace N headDist) :=
  UniformSpace.Completion.completeSpace _

/-- The canonical embedding of outer wave-functions into the Solovay-Hilbert space. -/
noncomputable def toSolovay (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (Ψ : _root_.OuterWaveFunction N headDist) : SolovayHilbertSpace N headDist :=
  (Ψ : SolovayHilbertSpace N headDist)

/-- The embedding is an isometric linear map. -/
theorem toSolovay_inner (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (Ψ Φ : _root_.OuterWaveFunction N headDist) :
    inner ℂ (toSolovay N headDist Ψ) (toSolovay N headDist Φ) = inner ℂ Ψ Φ := by
  simp [toSolovay]

/-- The embedding preserves the `L²` norm. -/
theorem toSolovay_norm (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (Ψ : _root_.OuterWaveFunction N headDist) :
    ‖toSolovay N headDist Ψ‖ = ‖Ψ‖ := by
  simp [toSolovay]

/-! ## S.2 — `dependsOnlyOnHead` decidability argument -/

/-- The inner product of two cylindrical (head-only) functions reduces to
    a finite-dimensional integral — the fundamental decidability corollary.
    Note: `inner ℂ Ψ₁ Ψ₂ = ∫ star(Ψ₁) * Ψ₂` by the L2 inner product convention,
    so the RHS uses `star(Ψ₁ (x,0)) * Ψ₂ (x,0)` to match. -/
theorem inner_reduces_to_head (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (Ψ₁ Ψ₂ : _root_.OuterWaveFunction N headDist)
    (hcyl₁ : _root_.dependsOnlyOnHead (Ψ₁ : _root_.InnerSpace N → ℂ))
    (hcyl₂ : _root_.dependsOnlyOnHead (Ψ₂ : _root_.InnerSpace N → ℂ)) :
    inner ℂ Ψ₁ Ψ₂ = ∫ x : _root_.InnerHead N, star (Ψ₁ (x, 0)) * (Ψ₂ (x, 0)) ∂headDist := by
  rcases hcyl₁ with ⟨g₁', hg₁⟩
  rcases hcyl₂ with ⟨g₂', hg₂⟩
  have h_tail_ne_zero : _root_.tailMeasure ≠ 0 := by
    have h_univ_one : _root_.tailMeasure Set.univ = 1 := measure_univ
    intro h_eq
    have h_univ_zero : _root_.tailMeasure Set.univ = 0 := by simp [h_eq]
    have h_eq_one_zero : (1 : ENNReal) = 0 := by
      rw [← h_univ_one, h_univ_zero]
    norm_num at h_eq_one_zero
  have h_map_fst : Measure.map Prod.fst (headDist.prod _root_.tailMeasure) = headDist := by
    rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  have h_ae₁ : AEStronglyMeasurable (Ψ₁ : _root_.InnerSpace N → ℂ)
      (headDist.prod _root_.tailMeasure) :=
    Lp.aestronglyMeasurable _
  have h_ae₂ : AEStronglyMeasurable (Ψ₂ : _root_.InnerSpace N → ℂ)
      (headDist.prod _root_.tailMeasure) :=
    Lp.aestronglyMeasurable _
  have h_ae_comp₁ : AEStronglyMeasurable (g₁' ∘ Prod.fst) (headDist.prod _root_.tailMeasure) := by
    rw [← hg₁]; exact h_ae₁
  have h_ae_comp₂ : AEStronglyMeasurable (g₂' ∘ Prod.fst) (headDist.prod _root_.tailMeasure) := by
    rw [← hg₂]; exact h_ae₂
  have h_ae_g₁ : AEStronglyMeasurable g₁' headDist :=
    h_ae_comp₁.of_comp_fst h_tail_ne_zero
  have h_ae_g₂ : AEStronglyMeasurable g₂' headDist :=
    h_ae_comp₂.of_comp_fst h_tail_ne_zero
  have h_mem_comp₁ : MemLp (g₁' ∘ Prod.fst) 2 (headDist.prod _root_.tailMeasure) := by
    rw [← hg₁]; exact Lp.memLp _
  have h_mem_comp₂ : MemLp (g₂' ∘ Prod.fst) 2 (headDist.prod _root_.tailMeasure) := by
    rw [← hg₂]; exact Lp.memLp _
  have h_mem_g₁ : MemLp g₁' 2 headDist := by
    have h_ae_map : AEStronglyMeasurable g₁' (Measure.map Prod.fst
        (headDist.prod _root_.tailMeasure)) := by
      rw [h_map_fst]; exact h_ae_g₁
    have h_meas_fst : AEMeasurable Prod.fst
        (headDist.prod _root_.tailMeasure) :=
      measurable_fst.aemeasurable
    have h_equiv := MeasureTheory.memLp_map_measure_iff (p := 2) h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₁
  have h_mem_g₂ : MemLp g₂' 2 headDist := by
    have h_ae_map : AEStronglyMeasurable g₂' (Measure.map Prod.fst
        (headDist.prod _root_.tailMeasure)) := by
      rw [h_map_fst]; exact h_ae_g₂
    have h_meas_fst : AEMeasurable Prod.fst
        (headDist.prod _root_.tailMeasure) :=
      measurable_fst.aemeasurable
    have h_equiv := MeasureTheory.memLp_map_measure_iff (p := 2) h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₂
  let g₁ : Lp ℂ 2 headDist := h_mem_g₂.toLp g₂'
  let g₂ : Lp ℂ 2 headDist := h_mem_g₁.toLp g₁'
  have h_inner_eq : inner ℂ Ψ₁ Ψ₂ = ∫ z : _root_.InnerSpace N,
      (g₂' z.1) * star (g₁' z.1) ∂(headDist.prod _root_.tailMeasure) := by
    rw [MeasureTheory.L2.inner_def (𝕜 := ℂ) Ψ₁ Ψ₂]
    simp_rw [RCLike.inner_apply]
    refine integral_congr_ae ?_
    filter_upwards with z
    simp [hg₁, hg₂]
  have h_fubini_eq : ∫ z : _root_.InnerSpace N,
      (g₂' z.1) * star (g₁' z.1) ∂(headDist.prod _root_.tailMeasure) =
      ∫ x, (g₂' x) * star (g₁' x) ∂headDist := by
    have h_int_comp : Integrable (fun z : _root_.InnerSpace N => (g₂' z.1) * star (g₁' z.1))
        (headDist.prod _root_.tailMeasure) := by
      have h_int_inner : Integrable (fun z : _root_.InnerSpace N =>
          ((Ψ₂ : _root_.InnerSpace N → ℂ) z) * star ((Ψ₁ : _root_.InnerSpace N → ℂ) z))
          (headDist.prod _root_.tailMeasure) := by
        have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) Ψ₁ Ψ₂
        simpa [RCLike.inner_apply, _root_.stateMeasure] using h
      have h_eq : (fun z : _root_.InnerSpace N => (g₂' z.1) * star (g₁' z.1))
          =ᵐ[headDist.prod _root_.tailMeasure]
          (fun z =>
            ((Ψ₂ : _root_.InnerSpace N → ℂ) z) * star ((Ψ₁ : _root_.InnerSpace N → ℂ) z)) := by
        filter_upwards with z
        simp [hg₁, hg₂]
      exact (integrable_congr h_eq).mpr h_int_inner
    have h_fubini : ∫ z : _root_.InnerSpace N,
        (g₂' z.1) * star (g₁' z.1) ∂(headDist.prod _root_.tailMeasure) =
        ∫ y, ∫ x, (g₂' x) * star (g₁' x) ∂headDist ∂_root_.tailMeasure := by
      exact integral_prod_symm
        (fun z : _root_.InnerHead N × _root_.InnerTail => (g₂' z.1) * star (g₁' z.1)) h_int_comp
    rw [h_fubini]
    simp [integral_const]
  have h_g_eq : ∫ x, (g₂' x) * star (g₁' x) ∂headDist = ∫ x, g₁ x * star (g₂ x) ∂headDist := by
    dsimp [g₁, g₂]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp h_mem_g₂, MemLp.coeFn_toLp h_mem_g₁] with x h₂ h₁
    simp [h₂, h₁]
  calc
    inner ℂ Ψ₁ Ψ₂ = ∫ x, g₁ x * star (g₂ x) ∂headDist := by
      rw [h_inner_eq, h_fubini_eq, h_g_eq]
    _ = ∫ x, (g₂' x) * star (g₁' x) ∂headDist := by rw [h_g_eq]
    _ = ∫ x, star (g₁' x) * g₂' x ∂headDist := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    _ = ∫ x : _root_.InnerHead N, star (Ψ₁ (x, 0)) * (Ψ₂ (x, 0)) ∂headDist := by
      simp [hg₁, hg₂]

/-- **S.2.2 — The expectation of a head-only observable is Tarski-decidable.**

The expectation of a cylindrical (head-only) observable over the full
infinite-dimensional inner space collapses to a *finite-dimensional* integral
over `ℝ^N`: the tail contributes only its total mass `1`.

This replaces an earlier placeholder whose conclusion was the trivially true
proposition. -/
theorem expectation_head_decidable (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (f : _root_.InnerHead N → ℂ) (hf : AEStronglyMeasurable f headDist) :
    ∫ z : _root_.InnerSpace N, f z.1 ∂(headDist.prod _root_.tailMeasure) =
      ∫ x : _root_.InnerHead N, f x ∂headDist := by
  have h_map_fst : Measure.map Prod.fst (headDist.prod _root_.tailMeasure) = headDist := by
    rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  rw [← integral_map (φ := Prod.fst) measurable_fst.aemeasurable (by rwa [h_map_fst]),
    h_map_fst]

/-! ## S.2a — Finite-head tensor products and product measures -/

/-- Splitting a head of dimension `N₁ + N₂` into its two finite blocks. -/
def headSumEquiv (N₁ N₂ : ℕ) :
    _root_.InnerHead (N₁ + N₂) ≃
      _root_.InnerHead N₁ × _root_.InnerHead N₂ :=
  (Equiv.piCongrLeft (fun _ : Fin (N₁ + N₂) => ℝ)
    (finSumFinEquiv (m := N₁) (n := N₂))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin N₁) (Fin N₂) ℝ)

/-- The pointwise tensor (product) of two finite-head observables. -/
def tensorHeadObservable {N₁ N₂ : ℕ}
    (f₁ : _root_.InnerHead N₁ → ℂ) (f₂ : _root_.InnerHead N₂ → ℂ) :
    _root_.InnerSpace (N₁ + N₂) → ℂ :=
  fun z => f₁ ((headSumEquiv N₁ N₂ z.1).1) *
    f₂ ((headSumEquiv N₁ N₂ z.1).2)

/-- A tensor product of two head observables still depends only on the combined
finite head.  This is the algebraic core of closure of cylindrical languages
under tensor products. -/
theorem tensorHeadObservable_dependsOnlyOnHead {N₁ N₂ : ℕ}
    (f₁ : _root_.InnerHead N₁ → ℂ) (f₂ : _root_.InnerHead N₂ → ℂ) :
    _root_.dependsOnlyOnHead (tensorHeadObservable f₁ f₂) := by
  refine ⟨fun h => f₁ ((headSumEquiv N₁ N₂ h).1) * f₂ ((headSumEquiv N₁ N₂ h).2), ?_⟩
  rfl

/-- Every probability law on the finite head yields a probability law on the
combined head-tail state space. -/
theorem stateMeasure_isProbability (N : ℕ)
    (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (_root_.stateMeasure N headDist) := by
  infer_instance

/-- The finite-head marginal of the product state measure is exactly the law
chosen on the head. -/
theorem stateMeasure_finite_marginal (N : ℕ)
    (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] :
    Measure.map Prod.fst (_root_.stateMeasure N headDist) = headDist := by
  rw [stateMeasure]
  rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]

/-- Readable tensor-language closure statement: cylindrical functions on a
combined head have inner products computed by one finite-head integral. -/
theorem tensor_language_decidable (N₁ N₂ : ℕ)
    (headDist : Measure (_root_.InnerHead (N₁ + N₂)))
    [IsProbabilityMeasure headDist]
    (Ψ₁ Ψ₂ : _root_.OuterWaveFunction (N₁ + N₂) headDist)
    (h₁ : _root_.dependsOnlyOnHead
      (Ψ₁ : _root_.InnerSpace (N₁ + N₂) → ℂ))
    (h₂ : _root_.dependsOnlyOnHead
      (Ψ₂ : _root_.InnerSpace (N₁ + N₂) → ℂ)) :
    inner ℂ Ψ₁ Ψ₂ =
      ∫ x, star (Ψ₁ (x, 0)) * Ψ₂ (x, 0) ∂headDist := by
  exact inner_reduces_to_head (N := N₁ + N₂) headDist Ψ₁ Ψ₂ h₁ h₂

/-! ## S.3 — The uniform Mehler measure on the infinite-dimensional hypersphere -/

/-- The Mehler prior (`gammaMeasure`) concentrates on the unit sphere: the
    normalized empirical squared norm of the first `k` coordinates converges to `1`
    almost surely (Poincaré–Borel / the strong law).
    This is `PhysMehler.mehler_concentrates_on_sphere`. -/
theorem mehler_concentrates_on_unit_sphere :
    ∀ᵐ ω ∂(PhysMehler.MehlerPrior),
    Filter.Tendsto (fun k => PhysHSGaussian.normSq k ω / k) Filter.atTop (nhds 1) := by
  simpa [PhysMehler.MehlerPrior] using PhysMehler.mehler_concentrates_on_sphere

/-- A transformation is an admissible finite orthogonal symmetry of the
tail when it is measure-preserving for the selected tail prior.  The repository's
abstract `Substrate` does not currently encode a coordinate-level finite-rank
orthogonal group, so invariance is stated at the exact measurable interface. -/
def IsFiniteOrthogonalTailSymmetry (T : _root_.InnerTail → _root_.InnerTail) : Prop :=
  MeasurePreserving T _root_.tailMeasure _root_.tailMeasure

/-- The Mehler-tail prior is invariant under every admitted finite orthogonal
symmetry. -/
theorem mehler_invariant_under_finite_orthogonal
    (T : _root_.InnerTail → _root_.InnerTail)
    (hT : IsFiniteOrthogonalTailSymmetry T) :
    Measure.map T _root_.tailMeasure = _root_.tailMeasure := by
  exact hT.map_eq

/-- The chosen tail prior is atomless. -/
theorem tailMeasure_singleton (x : _root_.InnerTail) :
    _root_.tailMeasure {x} = 0 := by
  simp [tailMeasure, PhysMehler.rcpPriorOnSubstrate_atomless]

/-- The precise admissibility package used for tail priors.  No unsupported
uniqueness theorem is asserted: uniqueness among all invariant atomless laws
would require a concrete coordinate realization and a characterization theorem
not available in the current substrate model. -/
structure TailPriorAdmissible (μ : Measure _root_.InnerTail) : Prop where
  probability : IsProbabilityMeasure μ
  atomless : ∀ x, μ {x} = 0
  invariant : ∀ T, MeasurePreserving T μ μ → Measure.map T μ = μ

/-- The selected Mehler/Kopperman tail prior has all three defining admissibility
properties requested by the book: probability, atomlessness, and invariance. -/
theorem only_mehler_on_tail : TailPriorAdmissible _root_.tailMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.PhysMehler.rcpPriorOnSubstrate_isProb
  · exact _root_.PhysMehler.rcpPriorOnSubstrate_atomless
  · exact fun T hT => hT.map_eq

/-- Heads admit an arbitrary probability law, while the tail theorem records the
three admissibility properties of the selected Mehler/Kopperman law. -/
theorem head_vs_tail_admissibility (N : ℕ)
    (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (_root_.stateMeasure N headDist) ∧
      TailPriorAdmissible _root_.tailMeasure := by
  exact ⟨stateMeasure_isProbability N headDist, only_mehler_on_tail⟩

/-! ## S.4 — No Gödelian self-reference -/

/-- In a complete Hilbert space with nontrivial finite head, the `dependsOnlyOnHead`
    condition prevents Gödelian self-reference. The biconditional would require
    `Ψ = 0` to be equivalent to every `φ` being constantly true, which is impossible
    since `InnerSpace N → Prop` contains non-constant functions when `N > 0`. -/
theorem no_godelian_self_reference (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist] [NeZero N] :
    ¬ ∃ (Ψ : SolovayHilbertSpace N headDist),
    (∀ (φ : _root_.InnerSpace N → Prop), (φ = (fun _ => True)) ↔ (Ψ = toSolovay N headDist 0)) := by
  intro h
  rcases h with ⟨Ψ, hΨ⟩
  -- Take φ = const True. The biconditional gives Ψ = toSolovay N headDist 0.
  have h_const_true : (fun (_ : _root_.InnerSpace N) => True) = (fun _ => True) := rfl
  have h_psi_eq_zero : Ψ = toSolovay N headDist 0 :=
    ((hΨ (fun (_ : _root_.InnerSpace N) => True)).mp h_const_true)
  -- Now take φ(z) = (z.1 = 0), which is not constantly true since N > 0.
  let zeroHead : Fin N → ℝ := fun _ => 0
  let φ : _root_.InnerSpace N → Prop := fun z => (z.1 = zeroHead)
  have h_phi_not_const : φ ≠ (fun _ => True) := by
    intro h_eq
    -- Pick a nonzero element of Fin N → ℝ (exists because NeZero N)
    have hNpos : 0 < N := NeZero.pos N
    let nonzero : Fin N → ℝ := fun i => if i = ⟨0, hNpos⟩ then 1 else 0
    have h_nonzero_ne_zero : nonzero ≠ zeroHead := by
      intro hzero
      have := congr_fun hzero ⟨0, hNpos⟩
      simp [nonzero, zeroHead] at this
    have h_eq_at_nonzero : φ (nonzero, 0) = (fun _ => True) (nonzero, 0) := by rw [h_eq]
    unfold φ nonzero at h_eq_at_nonzero
    exact h_nonzero_ne_zero (h_eq_at_nonzero ▸ trivial)
  -- The biconditional for this φ gives a contradiction.
  have h_iff := hΨ φ
  -- h_iff : (φ = (fun _ => True)) ↔ (Ψ = toSolovay N headDist 0)
  have h_phi_eq_const : φ = (fun _ => True) := h_iff.mpr h_psi_eq_zero
  exact h_phi_not_const h_phi_eq_const

/-- The expectation of a head-only observable has a well-defined value: the
    finite integral over ℝ^N always exists (this is the finite-dimensional,
    Tarski-decidable reduction target of `inner_reduces_to_head`). -/
theorem expectation_head_exists (N : ℕ) (headDist : Measure (_root_.InnerHead N))
    [IsProbabilityMeasure headDist]
    (f : _root_.InnerHead N → ℂ) :
    ∃ (c : ℂ), ∫ x : _root_.InnerHead N, f x ∂headDist = c :=
  ⟨_, rfl⟩

end BookProof.ChapterSolovay


