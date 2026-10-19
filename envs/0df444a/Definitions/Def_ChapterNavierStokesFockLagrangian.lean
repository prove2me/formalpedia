-- Prove2me | Definitions.Def_ChapterNavierStokesFockLagrangian
-- name    : ChapterNavierStokesFockLagrangian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-18T11:21:34.470978+00:00
-- url     : https://prove2.me/theorems/dda30e8a-8a74-40cb-815e-de6bfe2833c8
-- title:
--   The Lean 4 theorem `rfl_prime` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesFockLagrangian.lean`): generated def bundle for ChapterNavierStokesFockLagrangian. See BookProof/ChapterNavierStokesFockLagrangian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockLagrangian.lean

import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_boundedEnergyCore_dense

import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hFull_isSymmetricDom
import Mathlib
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_memLp_conj


/-!
# The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation: essential self-adjointness with continuous spectrum

`BookProof.ChapterNavierStokesLagrangianEsa` sets up the untruncated Lagrangian
data `LagrangianFullData` — the parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`,
the force drift generators `Dᵢ` and the volume-preservation constraint `C` — and
proves that the transformed Hamiltonian

`ĥ_full = ½∑ᵢPᵢ² + ν∑ᵢQᵢ² + ∑ᵢfᵢDᵢ + C`

is symmetric with positive second-order part, essentially self-adjoint whenever
the constituents admit a *total family of common eigenvectors*.

That criterion is a discrete-spectrum criterion: it needs eigenvectors.  The
Lagrangian momentum representation of a *continuum* fluid has none — the
constituents are multiplication operators by the momentum coordinates, whose
spectrum is purely continuous.  This module closes that gap.

## What is proved here

* `DominatedOn` and the multiplication operator `mulD` — multiplication by a
  real measurable symbol `h` on the bounded-energy core of a *scale* function
  `g`, available whenever `h` is bounded on the level sets of `g`, with its
  algebra (`mulD_comp`, `mulD_add`, `mulD_sum`, `mulD_real_smul`).
* `mulD_hasZeroDeficiencyOn` — **multiplication by any symbol dominated by the
  scale is essentially self-adjoint on the bounded-energy core of the scale.**
  This generalizes `FockContinuum.multOp_hasZeroDeficiencyOn`, where symbol and
  scale had to coincide, and it is what allows *all four* constituents of the
  transformed Hamiltonian to live on one common core.
* `LagSymbols` — the Lagrangian momentum representation itself: arbitrary
  measurable real symbols `Pᵢ, Qᵢ, Dᵢ, C` on a measure space of momentum
  configurations, with no boundedness assumption whatsoever, and the common
  core `boundedEnergyCore μ S.scale`.
* `LagSymbols.data` — the resulting `LagrangianFullData`, so everything proved
  about the abstract transformed operator (symmetry, positivity of the advective
  and viscous terms, transfer along the change of variables) applies verbatim.
* `LagSymbols.hFull_eq_mulD` — **the transformed Hamiltonian is multiplication
  by the total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.
* `LagSymbols.hFull_hasZeroDeficiencyOn` — **the headline: the untruncated
  transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
  Lagrangian momentum representation**, for arbitrary measurable symbols, with
  in general purely continuous spectrum and no eigenvectors at all.
* `norm_mulD_ge`, `mulD_not_bounded` — the lower bound that makes such an
  operator genuinely unbounded whenever its symbol is.

The second-quantized realization on the continuum Fock space of all
parcel-number sectors — where this criterion is applied to the transformed
Navier–Stokes Hamiltonian itself — is in
`BookProof.ChapterNavierStokesFockParcels`.

## Scope

Nothing here claims global existence for Navier–Stokes, and nothing here claims
essential self-adjointness of the *Eulerian* continuum generator: what is proved
is essential self-adjointness of the transformed operator in the Lagrangian
momentum representation, which by
`NavierStokesFlow.NSFullData.hasZeroDeficiencyOn_of_lagrangian` transports back
along a unitary change of variables only when such a change of variables is
supplied.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockLagrangian

open FullEsa FockContinuum

variable {X : Type*} [MeasurableSpace X]

/-! ## Symbols dominated on the level sets of a scale function -/

/-- The symbol `h` is **dominated on the level sets of the scale `g`**: on the
region where `|g| ≤ n` the symbol `h` is bounded.  This is exactly what is needed
for multiplication by `h` to preserve the bounded-energy core of `g`. -/
def DominatedOn (μ : Measure X) (g h : X → ℝ) : Prop :=
  ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, |g x| ≤ (n : ℝ) → |h x| ≤ M

theorem DominatedOn.rfl' (μ : Measure X) (g : X → ℝ) : DominatedOn μ g g :=
  fun n => ⟨n, Nat.cast_nonneg n, Filter.Eventually.of_forall fun _ hx => hx⟩

theorem DominatedOn.const (μ : Measure X) (g : X → ℝ) (r : ℝ) :
    DominatedOn μ g (fun _ => r) :=
  fun _ => ⟨|r|, abs_nonneg r, Filter.Eventually.of_forall fun _ _ => le_rfl⟩

theorem DominatedOn.add {μ : Measure X} {g h₁ h₂ : X → ℝ} (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) : DominatedOn μ g (fun x => h₁ x + h₂ x) := by
  intro n
  obtain ⟨M₁, hM₁, hx₁⟩ := d₁ n
  obtain ⟨M₂, hM₂, hx₂⟩ := d₂ n
  refine ⟨M₁ + M₂, by linarith, ?_⟩
  filter_upwards [hx₁, hx₂] with x h1 h2 hb
  exact le_trans (abs_add_le _ _) (add_le_add (h1 hb) (h2 hb))

theorem DominatedOn.mul {μ : Measure X} {g h₁ h₂ : X → ℝ} (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) : DominatedOn μ g (fun x => h₁ x * h₂ x) := by
  intro n
  obtain ⟨M₁, hM₁, hx₁⟩ := d₁ n
  obtain ⟨M₂, hM₂, hx₂⟩ := d₂ n
  refine ⟨M₁ * M₂, mul_nonneg hM₁ hM₂, ?_⟩
  filter_upwards [hx₁, hx₂] with x h1 h2 hb
  rw [abs_mul]
  exact mul_le_mul (h1 hb) (h2 hb) (abs_nonneg _) hM₁

theorem DominatedOn.const_mul {μ : Measure X} {g h : X → ℝ} (r : ℝ) (d : DominatedOn μ g h) :
    DominatedOn μ g (fun x => r * h x) :=
  (DominatedOn.const μ g r).mul d

theorem DominatedOn.of_abs_le {μ : Measure X} {g h k : X → ℝ} (d : DominatedOn μ g k)
    (hle : ∀ᵐ x ∂μ, |h x| ≤ |k x|) : DominatedOn μ g h := by
  intro n
  obtain ⟨M, hM, hx⟩ := d n
  refine ⟨M, hM, ?_⟩
  filter_upwards [hx, hle] with x h1 h2 hb
  exact le_trans h2 (h1 hb)

theorem DominatedOn.sum {ι : Type*} {μ : Measure X} {g : X → ℝ} (s : Finset ι)
    {h : ι → X → ℝ} (d : ∀ i ∈ s, DominatedOn μ g (h i)) :
    DominatedOn μ g (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using DominatedOn.const μ g 0
  | insert i s hi ih =>
      have hd : DominatedOn μ g (h i) := d i (Finset.mem_insert_self i s)
      have hrest : DominatedOn μ g (fun x => ∑ j ∈ s, h j x) :=
        ih fun j hj => d j (Finset.mem_insert_of_mem hj)
      have := hd.add hrest
      simpa [Finset.sum_insert hi] using this

/-! ## Multiplication by a dominated symbol on the bounded-energy core -/

/-- Multiplying a bounded-energy state by a dominated symbol stays
square-integrable. -/
theorem memLp_mulD {μ : Measure X} {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {f : Lp ℂ 2 μ} (hf : f ∈ boundedEnergyCore μ g) :
    MemLp (fun x => (h x : ℂ) * (f : X → ℂ) x) 2 μ := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨M, hM, hMx⟩ := hdom n
  have hmeas : AEStronglyMeasurable (fun x => (h x : ℂ) * (f : X → ℂ) x) μ :=
    (Complex.measurable_ofReal.comp hh).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hbound : ∀ᵐ x ∂μ, ‖(h x : ℂ) * (f : X → ℂ) x‖ ≤ M * ‖(f : X → ℂ) x‖ := by
    filter_upwards [hn, hMx] with x hx hMb
    by_cases hb : |g x| ≤ (n : ℝ)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hMb hb) (norm_nonneg _)
    · rw [hx hb]
      simp
  exact MemLp.of_le_mul (Lp.memLp f) hmeas hbound

theorem mulD_mem_core {μ : Measure X} {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {f : Lp ℂ 2 μ} (hf : f ∈ boundedEnergyCore μ g) :
    (memLp_mulD hh hdom hf).toLp _ ∈ boundedEnergyCore μ g := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  filter_upwards [hn, (memLp_mulD hh hdom (⟨n, hn⟩ : f ∈ boundedEnergyCore μ g)).coeFn_toLp]
    with x hx hcoe hbig
  rw [hcoe, hx hbig, mul_zero]

/-- **Multiplication by a dominated real symbol** on the bounded-energy core of
the scale `g`.  Unlike `FockContinuum.multOp` the symbol need not be the scale
itself, so several different symbols act on one and the same core. -/
noncomputable def mulD (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) :
    boundedEnergyCore μ g →ₗ[ℂ] boundedEnergyCore μ g where
  toFun f := ⟨(memLp_mulD hh hdom f.2).toLp _, mulD_mem_core hh hdom f.2⟩
  map_add' f k := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_add]
    filter_upwards [(memLp_mulD hh hdom
        (show ((f : Lp ℂ 2 μ) + (k : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g from (f + k).2)).coeFn_toLp,
      (memLp_mulD hh hdom f.2).coeFn_toLp, (memLp_mulD hh hdom k.2).coeFn_toLp,
      Lp.coeFn_add ((f : Lp ℂ 2 μ)) ((k : Lp ℂ 2 μ)),
      Lp.coeFn_add ((memLp_mulD hh hdom f.2).toLp _)
        ((memLp_mulD hh hdom k.2).toLp _)] with x h1 h2 h3 h4 h5
    rw [h1, h5]
    simp only [Pi.add_apply]
    rw [h2, h3, h4]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    refine Subtype.ext (Lp.ext ?_)
    simp only [Submodule.coe_smul, RingHom.id_apply]
    filter_upwards [(memLp_mulD hh hdom
        (show (c • (f : Lp ℂ 2 μ)) ∈ boundedEnergyCore μ g from (c • f).2)).coeFn_toLp,
      (memLp_mulD hh hdom f.2).coeFn_toLp, Lp.coeFn_smul c ((f : Lp ℂ 2 μ)),
      Lp.coeFn_smul c ((memLp_mulD hh hdom f.2).toLp _)] with x h1 h2 h3 h4
    rw [h1, h4]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem mulD_coeFn (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) (f : boundedEnergyCore μ g) :
    (((mulD μ hh hdom f : boundedEnergyCore μ g) : Lp ℂ 2 μ) : X → ℂ)
      =ᵐ[μ] fun x => (h x : ℂ) * ((f : Lp ℂ 2 μ) : X → ℂ) x :=
  (memLp_mulD hh hdom f.2).coeFn_toLp

/-- Two symbols that agree almost everywhere give the same operator. -/
theorem mulD_congr (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) (hae : h₁ =ᵐ[μ] h₂) :
    mulD μ hh₁ d₁ = mulD μ hh₂ d₂ := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ f, mulD_coeFn μ hh₂ d₂ f, hae] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The multiplication operator is symmetric on the core. -/
theorem mulD_isSymmetricDom (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) : IsSymmetricDom (mulD μ hh hdom) := by
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulD_coeFn μ hh hdom x, mulD_coeFn μ hh hdom y] with a hx hy
  simp only [RCLike.inner_apply, hx, hy, map_mul, Complex.conj_ofReal]
  ring

/-- Composing two multiplication operators multiplies the symbols. -/
theorem mulD_comp (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂)
      = mulD μ (hh₁.mul hh₂) (d₁.mul d₂) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ (mulD μ hh₂ d₂ f), mulD_coeFn μ hh₂ d₂ f,
    mulD_coeFn μ (hh₁.mul hh₂) (d₁.mul d₂) f] with x h1 h2 h3
  simp only [LinearMap.comp_apply]
  rw [h1, h2, h3]
  push_cast
  simp only [Pi.mul_apply, Complex.ofReal_mul]
  ring

/-- Adding two multiplication operators adds the symbols. -/
theorem mulD_add (μ : Measure X) {g h₁ h₂ : X → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (d₁ : DominatedOn μ g h₁) (d₂ : DominatedOn μ g h₂) :
    mulD μ hh₁ d₁ + mulD μ hh₂ d₂ = mulD μ (hh₁.add hh₂) (d₁.add d₂) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh₁ d₁ f, mulD_coeFn μ hh₂ d₂ f,
    mulD_coeFn μ (hh₁.add hh₂) (d₁.add d₂) f,
    Lp.coeFn_add ((mulD μ hh₁ d₁ f : boundedEnergyCore μ g) : Lp ℂ 2 μ)
      ((mulD μ hh₂ d₂ f : boundedEnergyCore μ g) : Lp ℂ 2 μ)] with x h1 h2 h3 h4
  simp only [LinearMap.add_apply, Submodule.coe_add]
  rw [h4]
  simp only [Pi.add_apply]
  rw [h1, h2, h3]
  push_cast
  simp only [Pi.add_apply, Complex.ofReal_add]
  ring

/-- A real multiple of a multiplication operator multiplies the symbol. -/
theorem mulD_real_smul (μ : Measure X) {g h : X → ℝ} (r : ℝ) (hh : Measurable h)
    (hdom : DominatedOn μ g h) :
    ((r : ℝ) : ℂ) • mulD μ hh hdom
      = mulD μ ((measurable_const (a := r)).mul hh) (DominatedOn.const_mul r hdom) := by
  refine LinearMap.ext fun f => Subtype.ext (Lp.ext ?_)
  filter_upwards [mulD_coeFn μ hh hdom f,
    mulD_coeFn μ ((measurable_const (a := r)).mul hh) (DominatedOn.const_mul r hdom) f,
    Lp.coeFn_smul ((r : ℝ) : ℂ) ((mulD μ hh hdom f : boundedEnergyCore μ g) : Lp ℂ 2 μ)]
    with x h1 h2 h3
  simp only [LinearMap.smul_apply, Submodule.coe_smul]
  rw [h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  push_cast
  simp only [Pi.mul_apply, Complex.ofReal_mul]
  ring

/-! ### Flexible forms of the algebra, with the target symbol given explicitly -/

/-- Composition, with the product symbol supplied in whatever form is
convenient. -/
theorem mulD_comp' (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x * h₂ x) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂) = mulD μ hh d := by
  rw [mulD_comp μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.mul hh₂) hh (d₁.mul d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)

/-- Addition, with the sum symbol supplied in whatever form is convenient. -/
theorem mulD_add' (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x + h₂ x) :
    mulD μ hh₁ d₁ + mulD μ hh₂ d₂ = mulD μ hh d := by
  rw [mulD_add μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.add hh₂) hh (d₁.add d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)

/-- Real scaling, with the scaled symbol supplied in whatever form is
convenient. -/
theorem mulD_real_smul' (μ : Measure X) {g h₁ h : X → ℝ} (r : ℝ) (hh₁ : Measurable h₁)
    (hh : Measurable h) (d₁ : DominatedOn μ g h₁) (d : DominatedOn μ g h)
    (heq : ∀ x, h x = r * h₁ x) :
    ((r : ℝ) : ℂ) • mulD μ hh₁ d₁ = mulD μ hh d := by
  rw [mulD_real_smul μ r hh₁ d₁]
  exact mulD_congr μ ((measurable_const (a := r)).mul hh₁) hh
    (DominatedOn.const_mul r d₁) d (Filter.Eventually.of_forall fun x => (heq x).symm)

/-! ## Essential self-adjointness of a dominated multiplication operator -/

/-- **Multiplication by a real symbol dominated by the scale is essentially
self-adjoint on the bounded-energy core.**

This strengthens `FockContinuum.multOp_hasZeroDeficiencyOn`, where the symbol had
to be the scale itself.  The operator has, in general, purely continuous spectrum
and no eigenvector whatsoever; the argument tests the deficiency identity against
the truncations of `(h ∓ i)w`. -/
theorem mulD_hasZeroDeficiencyOn (μ : Measure X) {g h : X → ℝ} (hg : Measurable g)
    (hh : Measurable h) (hdom : DominatedOn μ g h) :
    HasZeroDeficiencyOn (boundedEnergyCore μ g) (mulD μ hh hdom) := by
  have key : ∀ c : ℂ, c.im ≠ 0 → ∀ w : Lp ℂ 2 μ,
      (∀ v : boundedEnergyCore μ g,
        (inner ℂ ((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ) w : ℂ)
          = inner ℂ ((v : boundedEnergyCore μ g) : Lp ℂ 2 μ) (c • w)) → w = 0 := by
    intro c hc w hw
    set W : X → ℂ := fun x => ((h x : ℂ) - c) * ((w : X → ℂ) x) with hW
    have hmeasW : AEStronglyMeasurable W μ :=
      ((Complex.measurable_ofReal.comp hh).aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul (Lp.aestronglyMeasurable w)
    have hzero : ∀ n : ℕ, ∀ᵐ x ∂μ, |g x| ≤ (n : ℝ) → W x = 0 := by
      intro n
      obtain ⟨M, hM, hMx⟩ := hdom n
      have hmeasS : MeasurableSet {x | |g x| ≤ (n : ℝ)} :=
        measurableSet_le hg.abs measurable_const
      set u : X → ℂ := Set.indicator {x | |g x| ≤ (n : ℝ)} W with hu
      have hmeasu : AEStronglyMeasurable u μ := hmeasW.indicator hmeasS
      have hbound : ∀ᵐ x ∂μ, ‖u x‖ ≤ (M + ‖c‖) * ‖(w : X → ℂ) x‖ := by
        filter_upwards [hMx] with x hMb
        by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
        · have hgc : ‖((h x : ℂ) - c)‖ ≤ M + ‖c‖ := by
            refine le_trans (norm_sub_le _ _) ?_
            have h1 : ‖((h x : ℂ))‖ ≤ M := by
              rw [Complex.norm_real, Real.norm_eq_abs]; exact hMb hx
            linarith
          rw [hu, Set.indicator_of_mem hx, hW, norm_mul]
          exact mul_le_mul_of_nonneg_right hgc (norm_nonneg _)
        · rw [hu, Set.indicator_of_notMem hx, norm_zero]
          have : (0 : ℝ) ≤ M + ‖c‖ := by positivity
          positivity
      have humem : MemLp u 2 μ := MemLp.of_le_mul (Lp.memLp w) hmeasu hbound
      have hucore : humem.toLp u ∈ boundedEnergyCore μ g := by
        refine ⟨n, ?_⟩
        filter_upwards [humem.coeFn_toLp] with x hx hbig
        rw [hx, hu, Set.indicator_of_notMem (by simpa using hbig)]
      have hid := hw ⟨humem.toLp u, hucore⟩
      have hleft : (inner ℂ ((mulD μ hh hdom ⟨humem.toLp u, hucore⟩ : boundedEnergyCore μ g) :
          Lp ℂ 2 μ) w : ℂ)
          = ∫ x, (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x ∂μ := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [mulD_coeFn μ hh hdom ⟨humem.toLp u, hucore⟩, humem.coeFn_toLp]
          with x h1 h2
        simp only [RCLike.inner_apply, h1, h2]
        ring
      have hright : (inner ℂ ((⟨humem.toLp u, hucore⟩ : boundedEnergyCore μ g) : Lp ℂ 2 μ)
          (c • w) : ℂ) = ∫ x, (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x) ∂μ := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [humem.coeFn_toLp, Lp.coeFn_smul c w] with x h1 h2
        simp only [RCLike.inner_apply, h1, h2, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hleft, hright] at hid
      have hcombine : ∫ x, ‖u x‖ ^ 2 ∂μ = 0 := by
        have hintegrand : ∀ x, (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
            - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)
            = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
          intro x
          by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
          · have hux : u x = ((h x : ℂ) - c) * ((w : X → ℂ) x) := by
              rw [hu, Set.indicator_of_mem hx]
            have hconj : (starRingEnd ℂ) (u x) * u x = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
              have hmc := Complex.mul_conj' (u x)
              push_cast
              linear_combination hmc
            calc (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
                  - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)
                = (starRingEnd ℂ) (u x) * (((h x : ℂ) - c) * (w : X → ℂ) x) := by
                  simp only [map_mul, Complex.conj_ofReal]
                  ring
              _ = (starRingEnd ℂ) (u x) * u x := by rw [hux]
              _ = ((‖u x‖ ^ 2 : ℝ) : ℂ) := hconj
          · rw [hu, Set.indicator_of_notMem hx]
            simp
        have hzeroint : ∫ x, (((‖u x‖ ^ 2 : ℝ)) : ℂ) ∂μ = 0 := by
          have hint1 : Integrable
              (fun x => (starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x) μ := by
            have h1 : MemLp (fun x => (h x : ℂ) * u x) 2 μ := by
              have hb : ∀ᵐ x ∂μ, ‖(h x : ℂ) * u x‖ ≤ M * ‖u x‖ := by
                filter_upwards [hMx] with x hMb
                by_cases hx : x ∈ {x | |g x| ≤ (n : ℝ)}
                · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                  exact mul_le_mul_of_nonneg_right (hMb hx) (norm_nonneg _)
                · rw [hu, Set.indicator_of_notMem hx]
                  simp
              exact MemLp.of_le_mul humem
                ((Complex.measurable_ofReal.comp hh).aestronglyMeasurable.mul hmeasu) hb
            exact MemLp.integrable_mul (memLp_conj h1) (Lp.memLp w)
          have hint2 : Integrable
              (fun x => (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)) μ := by
            exact MemLp.integrable_mul (memLp_conj humem) ((Lp.memLp w).const_mul c)
          have hsub : ∫ x, ((starRingEnd ℂ) ((h x : ℂ) * u x) * (w : X → ℂ) x
              - (starRingEnd ℂ) (u x) * (c * (w : X → ℂ) x)) ∂μ = 0 := by
            rw [integral_sub hint1 hint2, ← hid, sub_self]
          rw [← hsub]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hintegrand x).symm)
        have hre := congrArg Complex.re hzeroint
        rw [integral_complex_ofReal] at hre
        simpa using hre
      have hnn : 0 ≤ fun x => ‖u x‖ ^ 2 := fun x => by positivity
      have hintu : Integrable (fun x => ‖u x‖ ^ 2) μ := by
        have := humem.integrable_norm_rpow (by norm_num) (by norm_num)
        simpa [Real.rpow_natCast] using this
      have hae := (integral_eq_zero_iff_of_nonneg hnn hintu).1 hcombine
      filter_upwards [hae] with x hx hbig
      have hu0 : u x = 0 := by
        have hnorm : ‖u x‖ ^ 2 = 0 := hx
        simpa [pow_eq_zero_iff] using hnorm
      rw [← hu0, hu, Set.indicator_of_mem (show x ∈ {x | |g x| ≤ (n : ℝ)} from hbig)]
    have hWzero : ∀ᵐ x ∂μ, W x = 0 := by
      have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, |g x| ≤ (n : ℝ) → W x = 0 := ae_all_iff.2 hzero
      filter_upwards [hall] with x hx
      obtain ⟨n, hn⟩ := exists_nat_ge |g x|
      exact hx n hn
    refine Lp.ext ?_
    filter_upwards [hWzero, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hz
    rw [hz]
    have hne : ((h x : ℂ) - c) ≠ 0 := by
      intro hzc
      have him := congrArg Complex.im hzc
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im,
        neg_eq_zero] at him
      exact hc him
    exact (mul_eq_zero.1 hx).resolve_left hne
  refine ⟨fun w hw => key Complex.I (by simp) w ?_, fun w hw => key (-Complex.I) (by simp) w ?_⟩
  · intro v; exact hw v
  · intro v; rw [neg_smul]; exact hw v

/-! ### Lower bounds on the multiplication operator, and unboundedness -/

/-- Where the state lives, the symbol is at least `K`: then the operator
increases the norm by at least the factor `K`. -/
theorem norm_mulD_ge (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) (v : boundedEnergyCore μ g) {K : ℝ} (hK : 0 ≤ K)
    (hge : ∀ᵐ x ∂μ, ((v : Lp ℂ 2 μ) : X → ℂ) x ≠ 0 → K ≤ |h x|) :
    K * ‖((v : Lp ℂ 2 μ))‖ ≤ ‖((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)‖ := by
  have hsmul : ‖((K : ℂ) • (v : Lp ℂ 2 μ))‖ = K * ‖((v : Lp ℂ 2 μ))‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  rw [← hsmul]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hge, mulD_coeFn μ hh hdom v,
    Lp.coeFn_smul ((K : ℂ)) ((v : Lp ℂ 2 μ))] with x hx hmul hsm
  rw [hsm, hmul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hv : ((v : Lp ℂ 2 μ) : X → ℂ) x = 0
  · rw [hv]; simp
  · exact mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hK]; exact hx hv) (norm_nonneg _)

/-- **A multiplication operator with arbitrarily large symbol on unit states is
unbounded.** -/
theorem mulD_not_bounded (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h)
    (H : ∀ K : ℝ, ∃ v : boundedEnergyCore μ g, ‖((v : Lp ℂ 2 μ))‖ = 1 ∧
      ∀ᵐ x ∂μ, ((v : Lp ℂ 2 μ) : X → ℂ) x ≠ 0 → K ≤ |h x|) :
    ¬ ∃ C : ℝ, ∀ v : boundedEnergyCore μ g,
      ‖((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)‖ ≤ C * ‖((v : Lp ℂ 2 μ))‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨v, hv1, hvge⟩ := H (|C| + 1)
  have hlow := norm_mulD_ge μ hh hdom v (by positivity) hvge
  have hup := hC v
  rw [hv1, mul_one] at hlow hup
  have : |C| + 1 ≤ C := le_trans hlow hup
  have hCle : C ≤ |C| := le_abs_self C
  linarith

/-! ### No eigenvectors: continuity of the spectrum -/

/-- **A multiplication operator whose symbol has null level sets has no
eigenvectors.**  If `{x | h x = λ}` is `μ`-null then the only solution of
`h · v = λ v` in the core is `v = 0`. -/
theorem mulD_eq_zero_of_eigen (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {lam : ℂ} (hlevel : μ {x | (h x : ℂ) = lam} = 0)
    (v : boundedEnergyCore μ g)
    (hv : ((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)
        = lam • ((v : Lp ℂ 2 μ))) :
    ((v : Lp ℂ 2 μ)) = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∉ {x | (h x : ℂ) = lam} := measure_eq_zero_iff_ae_notMem.1 hlevel
  have h1 : (((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ) : X → ℂ)
      =ᵐ[μ] ((lam • (v : Lp ℂ 2 μ) : Lp ℂ 2 μ) : X → ℂ) := by rw [hv]
  refine Lp.ext ?_
  filter_upwards [hae, mulD_coeFn μ hh hdom v, Lp.coeFn_smul lam ((v : Lp ℂ 2 μ)), h1,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hmul hsm heq hz
  rw [hz]
  rw [hmul, hsm] at heq
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  by_contra hv0
  exact hx (mul_right_cancel₀ hv0 heq)

/-! ## The Lagrangian momentum representation -/

/-- **The Lagrangian momentum representation of the transformed Navier–Stokes
data.**  The parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`, the force drift
generators `Dᵢ` and the volume-preservation constraint `C` are here *arbitrary
real measurable symbols* on a measure space `X` of momentum configurations —
nothing is assumed bounded, and the resulting operators have in general purely
continuous spectrum. -/
structure LagSymbols (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  /-- The parcel-momentum symbols. -/
  P : Fin 3 → X → ℝ
  /-- The viscous-gradient symbols. -/
  Q : Fin 3 → X → ℝ
  /-- The drift-generator symbols. -/
  Dr : Fin 3 → X → ℝ
  /-- The volume-preservation constraint symbol. -/
  cfun : X → ℝ
  /-- The external force. -/
  force : Fin 3 → ℝ
  /-- The kinematic viscosity. -/
  nu : ℝ
  nu_nonneg : 0 ≤ nu
  P_meas : ∀ i, Measurable (P i)
  Q_meas : ∀ i, Measurable (Q i)
  Dr_meas : ∀ i, Measurable (Dr i)
  c_meas : Measurable cfun

namespace LagSymbols

variable {μ : Measure X} (S : LagSymbols X μ)

/-- The **scale**: the sum of the absolute values of all the symbols.  Its
bounded-energy core is the common domain on which all four constituents of the
transformed Hamiltonian act. -/
def scale : X → ℝ := fun x =>
  (∑ i : Fin 3, |S.P i x|) + (∑ i : Fin 3, |S.Q i x|) + (∑ i : Fin 3, |S.Dr i x|) + |S.cfun x|

theorem scale_nonneg (x : X) : 0 ≤ S.scale x := by
  have h1 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.P i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.Q i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.Dr i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem scale_meas : Measurable S.scale := by
  refine (((Finset.univ.measurable_sum fun i _ => (S.P_meas i).abs).add
    (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).abs)).add
    (Finset.univ.measurable_sum fun i _ => (S.Dr_meas i).abs)).add S.c_meas.abs

/-- Every symbol of the family is dominated by the scale. -/
theorem dominated_of_abs_le {h : X → ℝ} (hle : ∀ x, |h x| ≤ S.scale x) :
    DominatedOn μ S.scale h :=
  (DominatedOn.rfl' μ S.scale).of_abs_le
    (Filter.Eventually.of_forall fun x =>
      le_trans (hle x) (le_abs_self (S.scale x)))

theorem P_dom (i : Fin 3) : DominatedOn μ S.scale (S.P i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.P i x| ≤ ∑ j : Fin 3, |S.P j x| :=
    Finset.single_le_sum (f := fun j => |S.P j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem Q_dom (i : Fin 3) : DominatedOn μ S.scale (S.Q i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.Q i x| ≤ ∑ j : Fin 3, |S.Q j x| :=
    Finset.single_le_sum (f := fun j => |S.Q j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem Dr_dom (i : Fin 3) : DominatedOn μ S.scale (S.Dr i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.Dr i x| ≤ ∑ j : Fin 3, |S.Dr j x| :=
    Finset.single_le_sum (f := fun j => |S.Dr j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem c_dom : DominatedOn μ S.scale S.cfun := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  simp only [scale]
  linarith

/-- The common domain: the bounded-scale core. -/
def core : Submodule ℂ (Lp ℂ 2 μ) := boundedEnergyCore μ S.scale

theorem core_dense : Dense ((S.core : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  boundedEnergyCore_dense μ S.scale_meas

/-- The parcel-momentum operators. -/
noncomputable def Pop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.P_meas i) (S.P_dom i)

/-- The viscous-gradient operators. -/
noncomputable def Qop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.Q_meas i) (S.Q_dom i)

/-- The drift generators. -/
noncomputable def Drop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.Dr_meas i) (S.Dr_dom i)

/-- The volume-preservation constraint operator. -/
noncomputable def Cop : S.core →ₗ[ℂ] S.core := mulD μ S.c_meas S.c_dom

/-- **The Lagrangian momentum representation as untruncated transformed
Navier–Stokes data.**  Everything proved about `LagrangianFullData` — symmetry,
positivity of the advective and viscous quadratic forms, transfer of essential
self-adjointness along the change of variables — applies to it. -/
noncomputable def data : LagrangianEsa.LagrangianFullData (Lp ℂ 2 μ) where
  D := S.core
  P := S.Pop
  Q := S.Qop
  drive := S.Drop
  force := S.force
  constraintOp := S.Cop
  nu := S.nu
  dense := S.core_dense
  P_symm i := mulD_isSymmetricDom μ (S.P_meas i) (S.P_dom i)
  Q_symm i := mulD_isSymmetricDom μ (S.Q_meas i) (S.Q_dom i)
  drive_symm i := mulD_isSymmetricDom μ (S.Dr_meas i) (S.Dr_dom i)
  constraint_symm := mulD_isSymmetricDom μ S.c_meas S.c_dom
  nu_nonneg := S.nu_nonneg

/-- **The total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`: the classical
energy of the transformed Hamiltonian in the momentum representation. -/
noncomputable def total : X → ℝ := fun x =>
  (1 / 2) * (∑ i : Fin 3, (S.P i x) ^ 2) + S.nu * (∑ i : Fin 3, (S.Q i x) ^ 2)
    + (∑ i : Fin 3, S.force i * S.Dr i x) + S.cfun x

theorem total_meas : Measurable S.total := by
  refine ((((measurable_const).mul
    (Finset.univ.measurable_sum fun i _ => (S.P_meas i).pow_const 2)).add
    ((measurable_const).mul
      (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).pow_const 2))).add
    (Finset.univ.measurable_sum fun i _ => (measurable_const).mul (S.Dr_meas i))).add S.c_meas

theorem total_dom : DominatedOn μ S.scale S.total := by
  have hP : DominatedOn μ S.scale (fun x => (1 / 2 : ℝ) * ∑ i : Fin 3, (S.P i x) ^ 2 ) := by
    refine DominatedOn.const_mul _ ?_
    refine DominatedOn.sum Finset.univ fun i _ => ?_
    have := (S.P_dom i).mul (S.P_dom i)
    exact this.of_abs_le (Filter.Eventually.of_forall fun x => by rw [pow_two])
  have hQ : DominatedOn μ S.scale (fun x => S.nu * ∑ i : Fin 3, (S.Q i x) ^ 2) := by
    refine DominatedOn.const_mul _ ?_
    refine DominatedOn.sum Finset.univ fun i _ => ?_
    have := (S.Q_dom i).mul (S.Q_dom i)
    exact this.of_abs_le (Filter.Eventually.of_forall fun x => by rw [pow_two])
  have hD : DominatedOn μ S.scale (fun x => ∑ i : Fin 3, S.force i * S.Dr i x) :=
    DominatedOn.sum Finset.univ fun i _ => DominatedOn.const_mul _ (S.Dr_dom i)
  exact ((hP.add hQ).add hD).add S.c_dom

/-! ### The transformed Hamiltonian is multiplication by the total symbol -/

/-- The symbol of the advective (kinetic) term, `½∑pᵢ²`. -/
noncomputable def kinSym : X → ℝ := fun x => (1 / 2) * (∑ i : Fin 3, (S.P i x) ^ 2)

/-- The symbol of the viscous term, `ν∑qᵢ²`. -/
def visSym : X → ℝ := fun x => S.nu * (∑ i : Fin 3, (S.Q i x) ^ 2)

/-- The symbol of the force drift, `∑fᵢdᵢ`. -/
def driSym : X → ℝ := fun x => ∑ i : Fin 3, S.force i * S.Dr i x

theorem sq_dom (i : Fin 3) : DominatedOn μ S.scale (fun x => (S.P i x) ^ 2) :=
  ((S.P_dom i).mul (S.P_dom i)).of_abs_le
    (Filter.Eventually.of_forall fun x => by rw [pow_two])

theorem sqQ_dom (i : Fin 3) : DominatedOn μ S.scale (fun x => (S.Q i x) ^ 2) :=
  ((S.Q_dom i).mul (S.Q_dom i)).of_abs_le
    (Filter.Eventually.of_forall fun x => by rw [pow_two])

theorem kinSym_meas : Measurable S.kinSym :=
  measurable_const.mul (Finset.univ.measurable_sum fun i _ => (S.P_meas i).pow_const 2)

theorem visSym_meas : Measurable S.visSym :=
  measurable_const.mul (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).pow_const 2)

theorem driSym_meas : Measurable S.driSym :=
  Finset.univ.measurable_sum fun i _ => measurable_const.mul (S.Dr_meas i)

theorem kinSym_dom : DominatedOn μ S.scale S.kinSym :=
  DominatedOn.const_mul _ (DominatedOn.sum Finset.univ fun i _ => S.sq_dom i)

theorem visSym_dom : DominatedOn μ S.scale S.visSym :=
  DominatedOn.const_mul _ (DominatedOn.sum Finset.univ fun i _ => S.sqQ_dom i)

theorem driSym_dom : DominatedOn μ S.scale S.driSym :=
  DominatedOn.sum Finset.univ fun i _ => DominatedOn.const_mul _ (S.Dr_dom i)

/-- The advective term is multiplication by `½∑pᵢ²`. -/
theorem kinetic_eq : S.data.kinetic = mulD μ S.kinSym_meas S.kinSym_dom := by
  have hsq : ∀ i : Fin 3, (S.Pop i).comp (S.Pop i)
      = mulD μ ((S.P_meas i).pow_const 2) (S.sq_dom i) := fun i =>
    mulD_comp' μ (S.P_meas i) (S.P_meas i) ((S.P_meas i).pow_const 2) (S.P_dom i)
      (S.P_dom i) (S.sq_dom i) fun x => by rw [pow_two]
  have hfold : mulD μ ((S.P_meas 0).pow_const 2) (S.sq_dom 0)
      + mulD μ ((S.P_meas 1).pow_const 2) (S.sq_dom 1)
      + mulD μ ((S.P_meas 2).pow_const 2) (S.sq_dom 2)
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.P_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sq_dom i) := by
    rw [mulD_add' μ ((S.P_meas 0).pow_const 2) ((S.P_meas 1).pow_const 2)
        (((S.P_meas 0).pow_const 2).add ((S.P_meas 1).pow_const 2)) (S.sq_dom 0) (S.sq_dom 1)
        ((S.sq_dom 0).add (S.sq_dom 1)) fun _ => rfl]
    exact mulD_add' μ _ _ _ _ _ _ fun x => by
      rw [Fin.sum_univ_three]
      simp [Pi.add_apply]
  have hsum : (∑ i : Fin 3, (S.Pop i).comp (S.Pop i))
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.P_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sq_dom i) := by
    rw [Fin.sum_univ_three, hsq 0, hsq 1, hsq 2]
    exact hfold
  have hkin : S.data.kinetic = ((1 / 2 : ℝ) : ℂ) • (∑ i : Fin 3, (S.Pop i).comp (S.Pop i)) := rfl
  rw [hkin, hsum]
  exact mulD_real_smul' μ (1 / 2 : ℝ) _ _ _ _ fun _ => rfl

/-- The viscous term is multiplication by `ν∑qᵢ²`. -/
theorem viscous_eq : S.data.viscous = mulD μ S.visSym_meas S.visSym_dom := by
  have hsq : ∀ i : Fin 3, (S.Qop i).comp (S.Qop i)
      = mulD μ ((S.Q_meas i).pow_const 2) (S.sqQ_dom i) := fun i =>
    mulD_comp' μ (S.Q_meas i) (S.Q_meas i) ((S.Q_meas i).pow_const 2) (S.Q_dom i)
      (S.Q_dom i) (S.sqQ_dom i) fun x => by rw [pow_two]
  have hfold : mulD μ ((S.Q_meas 0).pow_const 2) (S.sqQ_dom 0)
      + mulD μ ((S.Q_meas 1).pow_const 2) (S.sqQ_dom 1)
      + mulD μ ((S.Q_meas 2).pow_const 2) (S.sqQ_dom 2)
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.Q_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sqQ_dom i) := by
    rw [mulD_add' μ ((S.Q_meas 0).pow_const 2) ((S.Q_meas 1).pow_const 2)
        (((S.Q_meas 0).pow_const 2).add ((S.Q_meas 1).pow_const 2)) (S.sqQ_dom 0) (S.sqQ_dom 1)
        ((S.sqQ_dom 0).add (S.sqQ_dom 1)) fun _ => rfl]
    exact mulD_add' μ _ _ _ _ _ _ fun x => by
      rw [Fin.sum_univ_three]
      simp [Pi.add_apply]
  have hsum : (∑ i : Fin 3, (S.Qop i).comp (S.Qop i))
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.Q_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sqQ_dom i) := by
    rw [Fin.sum_univ_three, hsq 0, hsq 1, hsq 2]
    exact hfold
  have hvis : S.data.viscous = ((S.nu : ℝ) : ℂ) • (∑ i : Fin 3, (S.Qop i).comp (S.Qop i)) := rfl
  rw [hvis, hsum]
  exact mulD_real_smul' μ S.nu _ _ _ _ fun _ => rfl

/-- The force drift is multiplication by `∑fᵢdᵢ`. -/
theorem drift_eq : S.data.drift = mulD μ S.driSym_meas S.driSym_dom := by
  have hterm : ∀ i : Fin 3, ((S.force i : ℝ) : ℂ) • S.Drop i
      = mulD μ (measurable_const.mul (S.Dr_meas i))
          (DominatedOn.const_mul (S.force i) (S.Dr_dom i)) := fun i =>
    mulD_real_smul' μ (S.force i) (S.Dr_meas i) _ (S.Dr_dom i) _ fun _ => rfl
  have hdri : S.data.drift = ∑ i : Fin 3, ((S.force i : ℝ) : ℂ) • S.Drop i := rfl
  have hfold : mulD μ (measurable_const.mul (S.Dr_meas 0))
      (DominatedOn.const_mul (S.force 0) (S.Dr_dom 0))
      + mulD μ (measurable_const.mul (S.Dr_meas 1))
          (DominatedOn.const_mul (S.force 1) (S.Dr_dom 1))
      + mulD μ (measurable_const.mul (S.Dr_meas 2))
          (DominatedOn.const_mul (S.force 2) (S.Dr_dom 2))
      = mulD μ S.driSym_meas S.driSym_dom := by
    rw [mulD_add' μ _ _ ((measurable_const.mul (S.Dr_meas 0)).add
        (measurable_const.mul (S.Dr_meas 1))) _ _
      ((DominatedOn.const_mul (S.force 0) (S.Dr_dom 0)).add
        (DominatedOn.const_mul (S.force 1) (S.Dr_dom 1))) fun _ => rfl]
    exact mulD_add' μ _ _ _ _ _ _ fun x => by
      simp only [driSym]
      rw [Fin.sum_univ_three]
      simp [Pi.add_apply, Pi.mul_apply]
  rw [hdri, Fin.sum_univ_three, hterm 0, hterm 1, hterm 2]
  exact hfold

/-- **The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation is multiplication by the total Lagrangian symbol**
`½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.  The four terms of `ĥ_full` are the four terms of
the classical energy. -/
theorem hFull_eq_mulD : S.data.hFull = mulD μ S.total_meas S.total_dom := by
  have hdec : S.data.hFull
      = S.data.kinetic + S.data.viscous + S.data.drift + S.data.constraintOp := rfl
  have hcon : S.data.constraintOp = mulD μ S.c_meas S.c_dom := rfl
  have hfold1 : mulD μ S.kinSym_meas S.kinSym_dom + mulD μ S.visSym_meas S.visSym_dom
      = mulD μ (S.kinSym_meas.add S.visSym_meas) (S.kinSym_dom.add S.visSym_dom) :=
    mulD_add' μ S.kinSym_meas S.visSym_meas (S.kinSym_meas.add S.visSym_meas) S.kinSym_dom
      S.visSym_dom (S.kinSym_dom.add S.visSym_dom) fun _ => rfl
  have hfold2 : mulD μ (S.kinSym_meas.add S.visSym_meas) (S.kinSym_dom.add S.visSym_dom)
        + mulD μ S.driSym_meas S.driSym_dom
      = mulD μ ((S.kinSym_meas.add S.visSym_meas).add S.driSym_meas)
          ((S.kinSym_dom.add S.visSym_dom).add S.driSym_dom) :=
    mulD_add' μ (S.kinSym_meas.add S.visSym_meas) S.driSym_meas
      ((S.kinSym_meas.add S.visSym_meas).add S.driSym_meas)
      (S.kinSym_dom.add S.visSym_dom) S.driSym_dom
      ((S.kinSym_dom.add S.visSym_dom).add S.driSym_dom) fun _ => rfl
  have hfold3 : mulD μ ((S.kinSym_meas.add S.visSym_meas).add S.driSym_meas)
            ((S.kinSym_dom.add S.visSym_dom).add S.driSym_dom)
        + mulD μ S.c_meas S.c_dom = mulD μ S.total_meas S.total_dom :=
    mulD_add' μ _ _ _ _ _ _ fun _ => rfl
  rw [hdec, S.kinetic_eq, S.viscous_eq, S.drift_eq, hcon]
  exact hfold1 ▸ (hfold2 ▸ hfold3)

/-- **The headline.  The untruncated transformed Navier–Stokes Hamiltonian is
essentially self-adjoint in the Lagrangian momentum representation.**

The symbols are arbitrary measurable real functions: nothing is bounded, and the
operator has in general purely continuous spectrum and no eigenvector at all, so
none of the earlier criteria — bounded realization, complete unitary flow, or a
total family of common eigenvectors — applies. -/
theorem hFull_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn S.data.D S.data.hFull := by
  rw [hFull_eq_mulD]
  exact mulD_hasZeroDeficiencyOn μ S.scale_meas S.total_meas S.total_dom

/-- **No eigenvectors.**  If the total symbol has a null level set at `λ`, then
`ĥ_full v = λ v` forces `v = 0`: the spectrum carries no point mass there. -/
theorem hFull_eq_zero_of_eigen {lam : ℂ} (hlevel : μ {x | (S.total x : ℂ) = lam} = 0)
    (v : S.core) (hv : ((S.data.hFull v : S.core) : Lp ℂ 2 μ) = lam • ((v : Lp ℂ 2 μ))) :
    ((v : Lp ℂ 2 μ)) = 0 := by
  rw [S.hFull_eq_mulD] at hv
  exact mulD_eq_zero_of_eigen μ S.total_meas S.total_dom hlevel v hv

/-- The transformed Hamiltonian is symmetric on its domain (inherited from the
abstract theory). -/
theorem hFull_isSymmetricDom : IsSymmetricDom S.data.hFull :=
  S.data.hFull_isSymmetricDom

end LagSymbols

end FockLagrangian

end BookProof.NavierStokesFlow


