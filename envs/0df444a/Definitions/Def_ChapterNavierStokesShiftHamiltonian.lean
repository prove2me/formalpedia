-- Prove2me | Definitions.Def_ChapterNavierStokesShiftHamiltonian
-- name    : ChapterNavierStokesShiftHamiltonian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:42:04.396046+00:00
-- url     : https://prove2.me/theorems/183f5538-88ee-4b77-a57f-71653f32c364
-- title:
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for the Navier–Stokes fiber H ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesShiftHamiltonian`, source chapter `BookProof/ChapterNavierStokesShiftHamiltonian.lean`).
--
--   `BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine inequalities for the Navier–Stokes fiber Hamiltonian of a *single* degree of freedom, where the Hamiltonian is the `±2`-shift of `ℓ²(ℕ)`. The Fock-space (many-mode) Hamiltonian is a **sum** of such shift operators, one for each field mode, acting on the occupation-number space `ℓ²(ℕᵈ)`. This module isolates the one-mode analysis in a form that does not mention `ℕ` at all, so that it can be applied to each mode of the many-mode problem separately.
--
--   A `ShiftData ι` consists of
--
--   * a symbol `σ ≥ 1` on the index set `ι` (the comparison operator `N` is multiplication by `σ`), * an injective *shift* `s : ι → ι` (for the mode `i` of the Fock space, `s α = α + 2eᵢ`: the creation of two quanta in the mode `i`), * an amplitude `w ≥ 0` with `w β ≤ w (s β)`, dominated by the symbol, `w β ≤ ¼ σ β + K`, * a constant symbol increment along the shift, `σ (s β) = σ β + Δ`.
--
--   The associated Hamiltonian is the antisymmetric hopping operator
--
--   `(H x)_β = i ( w(s⁻¹β) x_{s⁻¹β} − w(β) x_{s β} )`,
--
--   which for the Navier–Stokes fiber is `½(π V + V π) = (iκ/2)(a†² − a²)`.
--
--   * `shiftH_symmetricOn` — `H` is symmetric on the maximal domain of `N`; * `shiftH_relative_bound` — `‖H x‖² ≤ ½‖N x‖² + 8K²‖x‖²`; * `shiftH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼ + K) ⟪x, N x⟫`; * `hasSum_commForm` — the commutator form is the hopping series `2Δ ∑ w(β) Re(x̄_β x_{sβ})`, in general non-zero.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesShiftHamiltonian.lean

import Mathlib
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFreeFieldConstraint
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterU

import Mathlib

import Mathlib

/-!
# Shift Hamiltonians and their Faris–Lavine inequalities

`BookProof.ChapterNavierStokesHermiteFarisLavine` proves the two Faris–Lavine
inequalities for the Navier–Stokes fiber Hamiltonian of a *single* degree of
freedom, where the Hamiltonian is the `±2`-shift of `ℓ²(ℕ)`.  The Fock-space
(many-mode) Hamiltonian is a **sum** of such shift operators, one for each field
mode, acting on the occupation-number space `ℓ²(ℕᵈ)`.  This module isolates the
one-mode analysis in a form that does not mention `ℕ` at all, so that it can be
applied to each mode of the many-mode problem separately.

## The abstract data

A `ShiftData ι` consists of

* a symbol `σ ≥ 1` on the index set `ι` (the comparison operator `N` is
  multiplication by `σ`),
* an injective *shift* `s : ι → ι` (for the mode `i` of the Fock space,
  `s α = α + 2eᵢ`: the creation of two quanta in the mode `i`),
* an amplitude `w ≥ 0` with `w β ≤ w (s β)`, dominated by the symbol,
  `w β ≤ ¼ σ β + K`,
* a constant symbol increment along the shift, `σ (s β) = σ β + Δ`.

The associated Hamiltonian is the antisymmetric hopping operator

`(H x)_β = i ( w(s⁻¹β) x_{s⁻¹β} − w(β) x_{s β} )`,

which for the Navier–Stokes fiber is `½(π V + V π) = (iκ/2)(a†² − a²)`.

## What is proved

* `shiftH_symmetricOn` — `H` is symmetric on the maximal domain of `N`;
* `shiftH_relative_bound` — `‖H x‖² ≤ ½‖N x‖² + 8K²‖x‖²`;
* `shiftH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼ + K) ⟪x, N x⟫`;
* `hasSum_commForm` — the commutator form is the hopping series
  `2Δ ∑ w(β) Re(x̄_β x_{sβ})`, in general non-zero.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace ShiftHamiltonian

open LpNat FarisLavine IkebeKato

/-- The data of an abstract shift Hamiltonian: a comparison symbol `σ ≥ 1`, an
injective shift `s`, and a hopping amplitude `w` dominated by the symbol. -/
structure ShiftData (ι : Type*) where
  /-- The symbol of the comparison operator `N`. -/
  sym : ι → ℝ
  /-- The shift: the hopping `β ↦ s β`. -/
  shift : ι → ι
  /-- The hopping amplitude. -/
  amp : ι → ℝ
  /-- The additive constant in the domination of the amplitude by the symbol. -/
  K : ℝ
  /-- The increment of the symbol along the shift. -/
  step : ℝ
  shift_injective : Function.Injective shift
  amp_nonneg : ∀ β, 0 ≤ amp β
  amp_mono : ∀ β, amp β ≤ amp (shift β)
  K_nonneg : 0 ≤ K
  step_nonneg : 0 ≤ step
  sym_ge_one : ∀ β, 1 ≤ sym β
  amp_le : ∀ β, amp β ≤ (1 / 4) * sym β + K
  sym_step : ∀ β, sym (shift β) = sym β + step

variable {ι : Type*} (S : ShiftData ι)

namespace ShiftData

theorem sym_nonneg (β : ι) : 0 ≤ S.sym β := le_trans zero_le_one (S.sym_ge_one β)



/-! ## Transporting a sequence along the shift -/

/-- `S.hop g` is `g` transported along the shift: it is `g α` at `s α` and `0`
off the range of the shift. -/
noncomputable def hop {M : Type*} [Zero M] (g : ι → M) : ι → M :=
  Function.extend S.shift g 0

@[simp] theorem hop_shift {M : Type*} [Zero M] (g : ι → M) (α : ι) :
    S.hop g (S.shift α) = g α :=
  S.shift_injective.extend_apply g 0 α

theorem hop_eq_zero {M : Type*} [Zero M] (g : ι → M) {β : ι} (h : ¬ ∃ α, S.shift α = β) :
    S.hop g β = 0 := by
  change Function.extend S.shift g (0 : ι → M) β = 0
  rw [Function.extend_apply' g (0 : ι → M) β h]
  rfl

theorem hop_comp {M : Type*} [Zero M] (g : ι → M) : (S.hop g) ∘ S.shift = g :=
  funext fun α => hop_shift S g α

theorem hasSum_hop_iff {M : Type*} [AddCommMonoid M] [TopologicalSpace M] {g : ι → M} {a : M} :
    HasSum (S.hop g) a ↔ HasSum g a := by
  have h := S.shift_injective.hasSum_iff (f := S.hop g) (a := a) (fun β hβ => by
    refine hop_eq_zero S g ?_
    rintro ⟨α, rfl⟩
    exact hβ ⟨α, rfl⟩)
  rw [hop_comp] at h
  exact h.symm

theorem summable_hop {M : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M]
    [CompleteSpace M] {g : ι → M} (h : Summable g) : Summable (S.hop g) :=
  ((hasSum_hop_iff S).mpr h.hasSum).summable

theorem summable_comp_shift {g : ι → ℝ} (h : Summable g) : Summable fun β => g (S.shift β) :=
  h.comp_injective S.shift_injective

theorem hop_nonneg {g : ι → ℝ} (h : ∀ α, 0 ≤ g α) (β : ι) : 0 ≤ S.hop g β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift]
    exact h α
  · rw [hop_eq_zero S g hb]

theorem hop_sq (g : ι → ℝ) (β : ι) : S.hop (fun α => g α ^ 2) β = (S.hop g β) ^ 2 := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S _ hb, hop_eq_zero S g hb]
    ring

theorem norm_hop (g : ι → ℂ) (β : ι) : ‖S.hop g β‖ = S.hop (fun α => ‖g α‖) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, norm_zero]







/-! ## The Hamiltonian -/

/-- The coordinates of the shift Hamiltonian:
`(H x)_β = i ( w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ} )`. -/
noncomputable def hFun (X : ι → ℂ) : ι → ℂ :=
  fun β => Complex.I * (S.hop (fun α => (S.amp α : ℂ) * X α) β - (S.amp β : ℂ) * X (S.shift β))

/-- The sequence of amplitudes weighted by the state. -/
noncomputable def ampSeq (X : ι → ℂ) : ι → ℝ := fun β => S.amp β * ‖X β‖

theorem ampSeq_nonneg (X : ι → ℂ) (β : ι) : 0 ≤ S.ampSeq X β :=
  mul_nonneg (S.amp_nonneg β) (norm_nonneg _)

theorem norm_hFun_le (X : ι → ℂ) (β : ι) :
    ‖S.hFun X β‖ ≤ S.hop (S.ampSeq X) β + S.ampSeq X (S.shift β) := by
  have hnorm1 : ‖S.hop (fun α => (S.amp α : ℂ) * X α) β‖ = S.hop (S.ampSeq X) β := by
    rw [norm_hop]
    congr 1
    funext α
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (S.amp_nonneg α)]
    rfl
  have hnorm2 : ‖(S.amp β : ℂ) * X (S.shift β)‖ ≤ S.ampSeq X (S.shift β) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (S.amp_nonneg β)]
    exact mul_le_mul_of_nonneg_right (S.amp_mono β) (norm_nonneg _)
  calc ‖S.hFun X β‖
      = ‖S.hop (fun α => (S.amp α : ℂ) * X α) β - (S.amp β : ℂ) * X (S.shift β)‖ := by
        simp [hFun]
    _ ≤ ‖S.hop (fun α => (S.amp α : ℂ) * X α) β‖ + ‖(S.amp β : ℂ) * X (S.shift β)‖ :=
        norm_sub_le _ _
    _ ≤ S.hop (S.ampSeq X) β + S.ampSeq X (S.shift β) := by rw [hnorm1]; linarith

/-! ## Square summability -/

/-- The squared norm of an `ℓ²` state is the sum of the squared moduli. -/
theorem hasSum_normSq (f : L2I ι) : HasSum (fun k => ‖(f : ι → ℂ) k‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa [Real.rpow_natCast] using h

theorem norm_diagMax_coe (x : maxDom S.sym) (β : ι) :
    ‖((diagMax S.sym x : L2I ι) : ι → ℂ) β‖ = S.sym β * ‖((x : L2I ι) : ι → ℂ) β‖ := by
  rw [diagMax_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sym_nonneg S β)]

/-- The comparison series that dominates the amplitudes. -/
theorem hasSum_ampBound (x : maxDom S.sym) :
    HasSum (fun β => (1 / 8) * ‖((diagMax S.sym x : L2I ι) : ι → ℂ) β‖ ^ 2
        + (2 * S.K ^ 2) * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2)
      ((1 / 8) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2 + (2 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2) :=
  ((hasSum_normSq _).mul_left _).add ((hasSum_normSq _).mul_left _)

/-- **The amplitude is dominated by the comparison operator**, squared: the
analytic content of the first Faris–Lavine inequality. -/
theorem ampSeq_sq_le (x : maxDom S.sym) (β : ι) :
    (S.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2
      ≤ (1 / 8) * ‖((diagMax S.sym x : L2I ι) : ι → ℂ) β‖ ^ 2
        + (2 * S.K ^ 2) * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2 := by
  have hle := S.amp_le β
  have hamp := S.amp_nonneg β
  have hA2 : S.amp β ^ 2 ≤ (1 / 8) * S.sym β ^ 2 + 2 * S.K ^ 2 := by
    nlinarith [sq_nonneg (S.sym β / 4 - S.K)]
  rw [norm_diagMax_coe S x β]
  simp only [ampSeq]
  nlinarith [hA2, sq_nonneg ‖((x : L2I ι) : ι → ℂ) β‖, norm_nonneg (((x : L2I ι) : ι → ℂ) β)]

theorem summable_ampSeq_sq (x : maxDom S.sym) :
    Summable (fun β => (S.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (ampSeq_sq_le S x)
    (hasSum_ampBound S x).summable



/-- The Hamiltonian maps the maximal domain of the comparison operator into the
Hilbert space. -/
theorem memLp_hFun (x : maxDom S.sym) : Memℓp (S.hFun ((x : L2I ι) : ι → ℂ)) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  have hS := summable_ampSeq_sq S x
  have hshift : Summable (S.hop fun β => (S.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2) :=
    summable_hop S hS
  have htail : Summable (fun β => (S.ampSeq ((x : L2I ι) : ι → ℂ) (S.shift β)) ^ 2) :=
    summable_comp_shift S hS
  refine Summable.of_nonneg_of_le (fun β => sq_nonneg _) ?_
    ((hshift.mul_left 2).add (htail.mul_left 2))
  intro β
  have h1 := norm_hFun_le S ((x : L2I ι) : ι → ℂ) β
  have h2 : 0 ≤ S.hop (S.ampSeq ((x : L2I ι) : ι → ℂ)) β :=
    hop_nonneg S (ampSeq_nonneg S _) β
  have h3 : 0 ≤ S.ampSeq ((x : L2I ι) : ι → ℂ) (S.shift β) := ampSeq_nonneg S _ _
  have h4 := mul_self_le_mul_self (norm_nonneg (S.hFun ((x : L2I ι) : ι → ℂ) β)) h1
  rw [hop_sq]
  nlinarith [h4, sq_nonneg (S.hop (S.ampSeq ((x : L2I ι) : ι → ℂ)) β
    - S.ampSeq ((x : L2I ι) : ι → ℂ) (S.shift β))]

/-- **The shift Hamiltonian**, on the maximal domain of the comparison
operator. -/
noncomputable def shiftH : maxDom S.sym →ₗ[ℂ] L2I ι where
  toFun x := ⟨S.hFun ((x : L2I ι) : ι → ℂ), memLp_hFun S x⟩
  map_add' x y := by
    refine lp.ext (funext fun β => ?_)
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, hFun, hop_shift]
      ring
    · simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, hFun,
        hop_eq_zero S _ hb]
      ring
  map_smul' a x := by
    refine lp.ext (funext fun β => ?_)
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Submodule.coe_smul, hFun, hop_shift]
      ring
    · simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Submodule.coe_smul, hFun, hop_eq_zero S _ hb]
      ring



/-! ## The inner products of the Hamiltonian

`⟪Hx, y⟫` splits into the two hopping series `A` (a hop along the shift) and `B`
(a hop against it).  Both converge absolutely because `2ab ≤ a² + b²`. -/

/-- The hopping series `w(β) x̄_β y_{sβ}`. -/
noncomputable def crossA (X Y : ι → ℂ) : ι → ℂ :=
  fun β => (S.amp β : ℂ) * (starRingEnd ℂ) (X β) * Y (S.shift β)

/-- The hopping series `w(β) x̄_{sβ} y_β`. -/
noncomputable def crossB (X Y : ι → ℂ) : ι → ℂ :=
  fun β => (S.amp β : ℂ) * (starRingEnd ℂ) (X (S.shift β)) * Y β



















/-! ## The first Faris–Lavine inequality: the relative bound -/





/-! ## The second Faris–Lavine inequality: the commutator form -/













end ShiftData

end ShiftHamiltonian

end BookProof.NavierStokesFlow


