-- Prove2me | Definitions.Def_AutomorphicForm_L2AutomorphicCarrier
-- name    : AutomorphicForm_L2AutomorphicCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5ca2d6a9-75fb-5a47-a58d-768e09144092
-- title:
--   L² carrier for automorphic functions on the upper half-plane
-- statement:
--   For a subset $D$ of the upper half-plane $\mathbb{H}$, `AutomorphicL2 D` is an abbreviation for the complex Hilbert space $L^2$ of the hyperbolic volume measure restricted to $D$, i.e. Mathlib's `Lp ℂ 2 ((volume : Measure ℍ).restrict D)`; its normed group, inner-product and completeness structures are those already attached to `Lp`. The supporting lemmas record that the restricted measure is finite when $\mathrm{vol}(D)<\infty$, and that a function bounded in norm by a constant $C$ (either everywhere, with almost-everywhere strong measurability, or on $D$ only, with continuity and $D$ measurable) lies in $L^2$ of that restricted measure. `boundedToL2` packages the latter into a map sending a continuous $f : \mathbb{H} \to \mathbb{C}$ together with a bound $C$ on $D$ to the corresponding element of `AutomorphicL2 D`; it is shown to be represented almost everywhere by $f$, to be additive in the evident sense (bounds adding), and to send the zero function to $0$.
--
--   Two further groups of results concern the modular situation. First, a continuous $f$ with `IsZeroAtImInfty f` is bounded on Mathlib's fundamental domain `ModularGroup.fd` (compactness of the truncated fundamental domain handles the bounded part, the vanishing hypothesis the cusp), hence lies in $L^2$ of the volume measure restricted to `ModularGroup.fd`, once that set is measurable of finite volume; `FundamentalDomainFiniteVolume` is the predicate naming exactly this conjunction, and `cuspFormMemL2_of_finiteVolume` is the corresponding statement under it. Second, for $g \in \mathrm{GL}_2(\mathbb{R})$ the action $z \mapsto g \cdot z$ preserves the hyperbolic volume, so composition with it gives a linear isometry `rightRegular g` of $L^2(\mathbb{H})$, norm-preserving and contravariant: `rightRegular (g * h)` is `rightRegular g` followed by `rightRegular h`. Finally, the constant function $1$ lies in $L^2$ precisely when the measure is finite (it fails for total mass $\infty$), and `AutomorphicL2 ∅` is trivial.
--
--   **Relation to Mathlib.** Everything is built on Mathlib's $L^p$ spaces (`MemLp.toLp`, `Lp.compMeasurePreservingₗᵢ`), the hyperbolic volume on `ℍ` and its $\mathrm{GL}_2(\mathbb{R})$-invariance, and `ModularGroup.fd`; the project contributes the abbreviation `AutomorphicL2`, the bounded-to-$L^2$ construction, and the named predicate `FundamentalDomainFiniteVolume` packaging measurability and finiteness of the volume of `ModularGroup.fd` as a hypothesis rather than a theorem.
--
--   **Where it is used.** This is the measure-theoretic carrier for the analytic side of the theory of modular forms: $L^2$ of a fundamental domain for the modular group, with the unitary action of $\mathrm{GL}_2(\mathbb{R})$ by Möbius transformations, is the Hilbert space on which Hecke operators and the hyperbolic Laplacian act, and into which continuous cusp forms embed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_L2AutomorphicCarrier.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory UpperHalfPlane Set
open scoped MatrixGroups ENNReal RealInnerProductSpace

noncomputable section

namespace FLT.L2Carrier

abbrev AutomorphicL2 (D : Set ℍ) : Type :=
  Lp ℂ 2 ((volume : Measure ℍ).restrict D)

theorem isFiniteMeasure_restrict_of_lt_top {D : Set ℍ} (hD : volume D < ∞) :
    IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
  ⟨by simpa [Measure.restrict_apply_univ] using hD⟩

example (D : Set ℍ) : NormedAddCommGroup (AutomorphicL2 D) := inferInstance

example (D : Set ℍ) : InnerProductSpace ℂ (AutomorphicL2 D) := inferInstance

example (D : Set ℍ) : CompleteSpace (AutomorphicL2 D) := inferInstance

theorem memLp_two_restrict_of_bound {D : Set ℍ} (hD : volume D < ∞) {f : ℍ → ℂ}
    (hf : AEStronglyMeasurable f ((volume : Measure ℍ).restrict D)) (C : ℝ)
    (hC : ∀ z : ℍ, ‖f z‖ ≤ C) :
    MemLp f 2 ((volume : Measure ℍ).restrict D) :=
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  MemLp.of_bound hf C (Filter.Eventually.of_forall hC)

theorem memLp_two_restrict_of_bound_on {D : Set ℍ} (hD : volume D < ∞)
    (hDm : MeasurableSet D) {f : ℍ → ℂ} (hf : Continuous f) (C : ℝ)
    (hC : ∀ z ∈ D, ‖f z‖ ≤ C) :
    MemLp f 2 ((volume : Measure ℍ).restrict D) := by
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hDm]
  exact Filter.Eventually.of_forall hC

def boundedToL2 {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D) (f : ℍ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ z ∈ D, ‖f z‖ ≤ C) : AutomorphicL2 D :=
  (memLp_two_restrict_of_bound_on hD hDm hf C hC).toLp f

theorem boundedToL2_coeFn {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D)
    (f : ℍ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z ∈ D, ‖f z‖ ≤ C) :
    (boundedToL2 hD hDm f hf C hC : ℍ → ℂ) =ᵐ[(volume : Measure ℍ).restrict D] f :=
  MemLp.coeFn_toLp _

theorem boundedToL2_add {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D)
    (f g : ℍ → ℂ) (hf : Continuous f) (hg : Continuous g) (C C' : ℝ)
    (hC : ∀ z ∈ D, ‖f z‖ ≤ C) (hC' : ∀ z ∈ D, ‖g z‖ ≤ C') :
    boundedToL2 hD hDm (f + g) (hf.add hg) (C + C')
        (fun z hz => (norm_add_le _ _).trans (add_le_add (hC z hz) (hC' z hz))) =
      boundedToL2 hD hDm f hf C hC + boundedToL2 hD hDm g hg C' hC' := by
  simp only [boundedToL2]
  exact MemLp.toLp_add _ _

theorem exists_bound_on_fd_of_isZeroAtImInfty {f : ℍ → ℂ} (hf : Continuous f)
    (hinf : IsZeroAtImInfty f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ModularGroup.fd, ‖f z‖ ≤ C := by

  obtain ⟨A, hA⟩ := (isZeroAtImInfty_iff.mp hinf) 1 one_pos

  have hcpt : IsCompact (ModularGroup.truncatedFundamentalDomain A) :=
    ModularGroup.isCompact_truncatedFundamentalDomain A
  have hbdd : BddAbove ((fun z => ‖f z‖) '' ModularGroup.truncatedFundamentalDomain A) :=
    (hcpt.image (by fun_prop)).bddAbove
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun z hz => ?_⟩
  rcases le_total z.im A with him | him
  ·
    exact le_trans (hB ⟨z, ⟨hz, him⟩, rfl⟩) (le_max_left _ _)
  ·
    exact le_trans (hA z him) (le_max_right _ _)

theorem memLp_two_fd_of_isZeroAtImInfty (hvol : volume ModularGroup.fd < ∞)
    (hmeas : MeasurableSet ModularGroup.fd) {f : ℍ → ℂ} (hf : Continuous f)
    (hinf : IsZeroAtImInfty f) :
    MemLp f 2 ((volume : Measure ℍ).restrict ModularGroup.fd) := by
  obtain ⟨C, _, hC⟩ := exists_bound_on_fd_of_isZeroAtImInfty hf hinf
  exact memLp_two_restrict_of_bound_on hvol hmeas hf C hC

theorem measurePreserving_smul_upperHalfPlane (g : GL (Fin 2) ℝ) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume :=
  MeasureTheory.measurePreserving_smul g (volume : Measure ℍ)

def rightRegular (g : GL (Fin 2) ℝ) :
    Lp ℂ 2 (volume : Measure ℍ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => g • z)
    (measurePreserving_smul_upperHalfPlane g)

theorem norm_rightRegular_apply (g : GL (Fin 2) ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    ‖rightRegular g f‖ = ‖f‖ :=
  (rightRegular g).norm_map f

theorem rightRegular_mul (g h : GL (Fin 2) ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    rightRegular (g * h) f = rightRegular h (rightRegular g f) := by

  show Lp.compMeasurePreserving (fun z : ℍ => (g * h) • z)
      (measurePreserving_smul_upperHalfPlane (g * h)) f =
    Lp.compMeasurePreserving (fun z : ℍ => h • z) (measurePreserving_smul_upperHalfPlane h)
      (Lp.compMeasurePreserving (fun z : ℍ => g • z)
        (measurePreserving_smul_upperHalfPlane g) f)
  rw [← Lp.compMeasurePreserving_comp_apply f]

  congr 1
  congr 1
  exact funext fun z => mul_smul g h z

def FundamentalDomainFiniteVolume : Prop :=
  volume ModularGroup.fd < ∞ ∧ MeasurableSet ModularGroup.fd

theorem cuspFormMemL2_of_finiteVolume (h : FundamentalDomainFiniteVolume)
    {f : ℍ → ℂ} (hf : Continuous f) (hinf : IsZeroAtImInfty f) :
    MemLp f 2 ((volume : Measure ℍ).restrict ModularGroup.fd) :=
  memLp_two_fd_of_isZeroAtImInfty h.1 h.2 hf hinf

theorem gate_const_memLp_of_finite {D : Set ℍ} (hD : volume D < ∞) :
    MemLp (fun _ : ℍ => (1 : ℂ)) 2 ((volume : Measure ℍ).restrict D) :=
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  memLp_const 1

theorem gate_const_not_memLp_of_infinite {μ : Measure ℍ} (hμ : μ univ = ∞) :
    ¬ MemLp (fun _ : ℍ => (1 : ℂ)) 2 μ := by
  intro h
  rcases (memLp_const_iff (by norm_num) (by norm_num)).mp h with h1 | h2
  · exact one_ne_zero h1
  · exact absurd (hμ ▸ h2) (lt_irrefl _)

theorem gate_empty_carrier_subsingleton (f : AutomorphicL2 (∅ : Set ℍ)) : f = 0 := by

  apply Lp.ext_iff.mpr
  have hbot : ae ((volume : Measure ℍ).restrict (∅ : Set ℍ)) = ⊥ :=
    ae_eq_bot.mpr Measure.restrict_empty
  rw [Filter.EventuallyEq, hbot]
  exact Filter.eventually_bot

theorem gate_boundedToL2_zero {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D) :
    boundedToL2 hD hDm (fun _ => (0 : ℂ)) continuous_const 0
      (fun _ _ => by simp) = 0 := by
  simp only [boundedToL2]
  exact MemLp.toLp_zero _

end FLT.L2Carrier
end


