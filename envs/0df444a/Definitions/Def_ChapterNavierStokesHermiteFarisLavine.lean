-- Prove2me | Definitions.Def_ChapterNavierStokesHermiteFarisLavine
-- name    : ChapterNavierStokesHermiteFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:51:35.553594+00:00
-- url     : https://prove2.me/theorems/47a2cf41-1898-41f4-b90f-e37446394d0e
-- title:
--   Everywhere else on this route the two Faris–Lavine inequalities
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.NavierStokesHermiteFarisLavine`, source chapter `BookProof/ChapterNavierStokesHermiteFarisLavine.lean`).
--
--   Everywhere else on this route the two Faris–Lavine inequalities
--
--   * the relative bound `‖H x‖² ≤ a‖N x‖² + b‖x‖²`, and * the form-commutator bound `± i[H, N] ≤ c N`,
--
--   are *hypotheses* on the Hamiltonian. Here they are **proved**, for a concrete Hamiltonian in a representation in which the momentum and the fiber coordinate genuinely do **not** commute — so that the commutator `[H, N]` is genuinely non-zero (`commForm_ne_zero_of_pos`), and the Faris–Lavine mechanism (the non-commuting cross terms `π · V` are dominated by the sum of the squares `π² + V²`) is what makes the argument work.
--
--   On the fiber, the one-particle Navier–Stokes transport operator is the symmetric first-order operator `h = ½ (πᵢ Vᵢ + Vᵢ πᵢ)`, with `πᵢ = -i ∂/∂uᵢ` and with the *linear* advection field `Vᵢ(u) = Mᵢⱼuⱼ + Cᵢ`. The comparison operator is built, as Faris–Lavine requires, from the squares of the individual non-commuting pieces: `N = πᵢπᵢ + Vᵢ(u)Vᵢ(u) + I ≥ I`.
--
--   Take one fiber degree of freedom and the linear field `V(u) = κ u` (`κ ≥ 0` the strain rate). In the Hermite (harmonic-oscillator) basis `eₙ` of `L²(du)`, normalised so that `u = (a + a†)/√(2κ)`, `π = i√(κ/2)(a† - a)` — hence `[π, u] = -i`, `nsComm_pu` — one has
--
--   * `N = π² + V² + I = κ(2n̂ + 1) + I`: **diagonal**, multiplication by the symbol `oscSymbol κ n = κ(2n+1) + 1 ≥ 1` (`nsN_core_eq`); * `H = ½(πV + Vπ) = (iκ/2)(a†² - a²)`: the **±2-shift** operator `(Hx)ₘ = i(w(m-2) x(m-2) - w(m) x(m+2))`, `w(n) = (κ/2)√((n+1)(n+2))` (`nsH`, `nsH_core_eq`).
--
--   `H` is *not* diagonal, and `[H, N] = -2iκ²(a² + a†²) ≠ 0`.
--
--   * `nsH_symmetricOn` — `H` is symmetric on the maximal domain of `N`; * `nsH_relative_bound` — **the first Faris–Lavine inequality** `‖Hx‖² ≤ ½‖Nx‖² + 2κ²‖x‖²`; * `nsH_commForm_bound` — **the second Faris–Lavine inequality** `|⟪x, i[H,N]x⟫| ≤ (2κ + 4κ²) ⟪x, Nx⟫`, proved exactly by the mechanism of the theorem: the commutator is the cross term `∝ κ² (a² + a†²)`, and `2ab ≤ a² + b²` dominates it by `π² + V² + I = N`; * `commForm_ne_zero_of_pos` — the commutator form is genuinely non-zero, so the bound is not vacuous; * `nsH_essentiallySelfAdjointOn_core` — consequently, by the Faris–Lavine theorem of `BookProof.ChapterFarisLavine` together with the Ikebe–Kato input of `BookProof.ChapterNavierStokesIkebeKato`, **the Navier–Stokes fiber Hamiltonian is essentially self-adjoint on the finite-mode core**, with no hypothesis left.
--
--   Nothing here claims global regularity for the Navier–Stokes equation.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesHermiteFarisLavine.lean

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
# The two Faris–Lavine inequalities, verified for the Navier–Stokes generator

Everywhere else on this route the two Faris–Lavine inequalities

* the relative bound `‖H x‖² ≤ a‖N x‖² + b‖x‖²`, and
* the form-commutator bound `± i[H, N] ≤ c N`,

are *hypotheses* on the Hamiltonian.  Here they are **proved**, for a concrete
Hamiltonian in a representation in which the momentum and the fiber coordinate
genuinely do **not** commute — so that the commutator `[H, N]` is genuinely
non-zero (`commForm_ne_zero_of_pos`), and the Faris–Lavine mechanism (the
non-commuting cross terms `π · V` are dominated by the sum of the squares
`π² + V²`) is what makes the argument work.

## The model

On the fiber, the one-particle Navier–Stokes transport operator is the symmetric
first-order operator
`h = ½ (πᵢ Vᵢ + Vᵢ πᵢ)`,
with `πᵢ = -i ∂/∂uᵢ` and with the *linear* advection field `Vᵢ(u) = Mᵢⱼuⱼ + Cᵢ`.
The comparison operator is built, as Faris–Lavine requires, from the squares of
the individual non-commuting pieces:
`N = πᵢπᵢ + Vᵢ(u)Vᵢ(u) + I ≥ I`.

Take one fiber degree of freedom and the linear field `V(u) = κ u` (`κ ≥ 0` the
strain rate).  In the Hermite (harmonic-oscillator) basis `eₙ` of `L²(du)`,
normalised so that
`u = (a + a†)/√(2κ)`, `π = i√(κ/2)(a† - a)` — hence `[π, u] = -i`, `nsComm_pu` —
one has

* `N = π² + V² + I = κ(2n̂ + 1) + I`: **diagonal**, multiplication by the symbol
  `oscSymbol κ n = κ(2n+1) + 1 ≥ 1` (`nsN_core_eq`);
* `H = ½(πV + Vπ) = (iκ/2)(a†² - a²)`: the **±2-shift** operator
  `(Hx)ₘ = i(w(m-2) x(m-2) - w(m) x(m+2))`, `w(n) = (κ/2)√((n+1)(n+2))`
  (`nsH`, `nsH_core_eq`).

`H` is *not* diagonal, and `[H, N] = -2iκ²(a² + a†²) ≠ 0`.

## What is proved

* `nsH_symmetricOn` — `H` is symmetric on the maximal domain of `N`;
* `nsH_relative_bound` — **the first Faris–Lavine inequality**
  `‖Hx‖² ≤ ½‖Nx‖² + 2κ²‖x‖²`;
* `nsH_commForm_bound` — **the second Faris–Lavine inequality**
  `|⟪x, i[H,N]x⟫| ≤ (2κ + 4κ²) ⟪x, Nx⟫`, proved exactly by the mechanism of the
  theorem: the commutator is the cross term `∝ κ² (a² + a†²)`, and
  `2ab ≤ a² + b²` dominates it by `π² + V² + I = N`;
* `commForm_ne_zero_of_pos` — the commutator form is genuinely non-zero, so the
  bound is not vacuous;
* `nsH_essentiallySelfAdjointOn_core` — consequently, by the Faris–Lavine theorem
  of `BookProof.ChapterFarisLavine` together with the Ikebe–Kato input of
  `BookProof.ChapterNavierStokesIkebeKato`, **the Navier–Stokes fiber Hamiltonian
  is essentially self-adjoint on the finite-mode core**, with no hypothesis left.

Nothing here claims global regularity for the Navier–Stokes equation.
-/

open scoped ENNReal

namespace BookProof.NavierStokesFlow

namespace HermiteFarisLavine

open LpNat FarisLavine IkebeKato

/-! ## Shifting a sequence by two -/

/-- `shift2 g` is the sequence `g` moved two places up (and `0` on the first two
indices). -/
def shift2 {M : Type*} [Zero M] (g : ℕ → M) : ℕ → M := fun m => if 2 ≤ m then g (m - 2) else 0

@[simp] theorem shift2_add_two {M : Type*} [Zero M] (g : ℕ → M) (n : ℕ) :
    shift2 g (n + 2) = g n := by
  simp [shift2]





theorem hasSum_shift2_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {g : ℕ → M} {s : M} : HasSum (shift2 g) s ↔ HasSum g s := by
  have h := hasSum_nat_add_iff (f := shift2 g) (g := s) 2
  have hfun : (fun n => shift2 g (n + 2)) = g := funext fun n => shift2_add_two g n
  rw [hfun] at h
  have hz : (∑ i ∈ Finset.range 2, shift2 g i) = 0 := by
    simp [Finset.sum_range_succ, shift2]
  rw [hz, add_zero] at h
  exact h.symm

theorem summable_shift2 {M : Type*} [AddCommGroup M] [UniformSpace M] [IsTopologicalAddGroup M]
    [CompleteSpace M] [T2Space M] {g : ℕ → M} (h : Summable g) : Summable (shift2 g) :=
  (hasSum_shift2_iff.mpr h.hasSum).summable

/-- Squaring commutes with the shift. -/
theorem shift2_sq (g : ℕ → ℝ) (m : ℕ) : shift2 (fun n => g n ^ 2) m = (shift2 g m) ^ 2 := by
  by_cases h : 2 ≤ m <;> simp [shift2, h]

/-- A shifted non-negative sequence is non-negative. -/
theorem shift2_nonneg (g : ℕ → ℝ) (h : ∀ n, 0 ≤ g n) (m : ℕ) : 0 ≤ shift2 g m := by
  by_cases hm : 2 ≤ m <;> simp [shift2, hm, h]

/-- The norm of a shifted complex sequence. -/
theorem norm_shift2 (g : ℕ → ℂ) (m : ℕ) : ‖shift2 g m‖ = shift2 (fun n => ‖g n‖) m := by
  by_cases h : 2 ≤ m <;> simp [shift2, h]

/-! ## The symbol and the amplitudes of the Hermite representation -/

/-- The symbol of the comparison operator `N = π² + V² + I = κ(2n̂+1) + I` in the
Hermite basis. -/
def oscSymbol (κ : ℝ) : ℕ → ℝ := fun n => κ * (2 * n + 1) + 1

/-- The off-diagonal amplitude of the Navier–Stokes fiber Hamiltonian
`H = ½(πV + Vπ) = (iκ/2)(a†² - a²)` in the Hermite basis: `H eₙ` has the
component `i w(n)` on `eₙ₊₂` and `-i w(n-2)` on `eₙ₋₂`. -/
noncomputable def amp (κ : ℝ) (n : ℕ) : ℝ := (κ / 2) * Real.sqrt ((n + 1) * (n + 2))

variable {κ : ℝ}

theorem oscSymbol_ge_one (hκ : 0 ≤ κ) (n : ℕ) : 1 ≤ oscSymbol κ n := by
  have : (0 : ℝ) ≤ κ * (2 * n + 1) := by positivity
  simp only [oscSymbol]; linarith

theorem oscSymbol_nonneg (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ oscSymbol κ n :=
  le_trans zero_le_one (oscSymbol_ge_one hκ n)

theorem oscSymbol_step (n : ℕ) : oscSymbol κ (n + 2) = oscSymbol κ n + 4 * κ := by
  simp only [oscSymbol]
  push_cast
  ring



theorem amp_nonneg (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ amp κ n := by
  have : (0 : ℝ) ≤ Real.sqrt ((n + 1) * (n + 2)) := Real.sqrt_nonneg _
  simp only [amp]
  positivity

/-- The amplitude increases along the shift. -/
theorem amp_le_amp_add_two (hκ : 0 ≤ κ) (n : ℕ) : amp κ n ≤ amp κ (n + 2) := by
  have hmono : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2))
      ≤ Real.sqrt ((((n : ℝ) + 2) + 1) * (((n : ℝ) + 2) + 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [amp]
  push_cast
  nlinarith [hmono, Real.sqrt_nonneg (((n : ℝ) + 1) * ((n : ℝ) + 2))]

/-- **The amplitude is dominated by the comparison symbol**: this is the
inequality `w(n) ≤ ¼ N(n) + κ/2` behind both Faris–Lavine bounds. -/
theorem amp_le_quarter (hκ : 0 ≤ κ) (n : ℕ) : amp κ n ≤ (1 / 4) * oscSymbol κ n + κ / 2 := by
  have hs : Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ (n : ℝ) + 3 / 2 := by
    have h1 : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≤ ((n : ℝ) + 3 / 2) ^ 2 := by nlinarith
    have h2 : Real.sqrt (((n : ℝ) + 3 / 2) ^ 2) = (n : ℝ) + 3 / 2 := by
      rw [Real.sqrt_sq (by positivity)]
    calc Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2))
        ≤ Real.sqrt (((n : ℝ) + 3 / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (n : ℝ) + 3 / 2 := h2
  have hmul : (κ / 2) * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ (κ / 2) * ((n : ℝ) + 3 / 2) :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  simp only [amp, oscSymbol]
  linarith



/-! ## The Hamiltonian as a `±2`-shift operator -/

/-- The Navier–Stokes fiber Hamiltonian `H = ½(πV + Vπ) = (iκ/2)(a†² - a²)` acting on
coordinates: `(Hx)ₘ = i(w(m-2) xₘ₋₂ - w(m) xₘ₊₂)`. -/
noncomputable def hFun (κ : ℝ) (X : ℕ → ℂ) : ℕ → ℂ :=
  fun m => Complex.I * (shift2 (fun n => (amp κ n : ℂ) * X n) m - (amp κ m : ℂ) * X (m + 2))

/-- The sequence of amplitudes weighted by the state: `w(n)|xₙ|`. -/
noncomputable def ampSeq (κ : ℝ) (X : ℕ → ℂ) : ℕ → ℝ := fun n => amp κ n * ‖X n‖

theorem ampSeq_nonneg (hκ : 0 ≤ κ) (X : ℕ → ℂ) (n : ℕ) : 0 ≤ ampSeq κ X n :=
  mul_nonneg (amp_nonneg hκ n) (norm_nonneg _)

/-- The pointwise bound on the Hamiltonian: two hops, each weighted by an
amplitude. -/
theorem norm_hFun_le (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) :
    ‖hFun κ X m‖ ≤ shift2 (ampSeq κ X) m + ampSeq κ X (m + 2) := by
  have hnorm1 : ‖shift2 (fun n => (amp κ n : ℂ) * X n) m‖ = shift2 (ampSeq κ X) m := by
    rw [norm_shift2]
    have : (fun n => ‖(amp κ n : ℂ) * X n‖) = ampSeq κ X := by
      funext n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amp_nonneg hκ n)]
      rfl
    rw [this]
  have hnorm2 : ‖(amp κ m : ℂ) * X (m + 2)‖ ≤ ampSeq κ X (m + 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amp_nonneg hκ m)]
    exact mul_le_mul_of_nonneg_right (amp_le_amp_add_two hκ m) (norm_nonneg _)
  calc ‖hFun κ X m‖
      = ‖shift2 (fun n => (amp κ n : ℂ) * X n) m - (amp κ m : ℂ) * X (m + 2)‖ := by
        simp [hFun]
    _ ≤ ‖shift2 (fun n => (amp κ n : ℂ) * X n) m‖ + ‖(amp κ m : ℂ) * X (m + 2)‖ :=
        norm_sub_le _ _
    _ ≤ shift2 (ampSeq κ X) m + ampSeq κ X (m + 2) := by rw [hnorm1]; linarith

/-! ## Square summability -/

/-- The squared norm of an `ℓ²` state is the sum of the squared moduli. -/
theorem hasSum_normSq {ι : Type*} (f : L2I ι) :
    HasSum (fun k => ‖(f : ι → ℂ) k‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa [Real.rpow_natCast] using h

section Domain

variable {x : maxDom (oscSymbol κ)}

theorem norm_diagMax_coe (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (n : ℕ) :
    ‖((diagMax (oscSymbol κ) x : L2I ℕ) : ℕ → ℂ) n‖
      = oscSymbol κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ := by
  rw [diagMax_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (oscSymbol_nonneg hκ n)]

/-- The comparison series that dominates the amplitudes. -/
theorem hasSum_ampBound (x : maxDom (oscSymbol κ)) :
    HasSum (fun n => (1 / 8) * ‖((diagMax (oscSymbol κ) x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
        + (κ ^ 2 / 2) * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
      ((1 / 8) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (κ ^ 2 / 2) * ‖(x : L2I ℕ)‖ ^ 2) :=
  ((hasSum_normSq _).mul_left _).add ((hasSum_normSq _).mul_left _)

/-- **The amplitude is dominated by the comparison operator**, squared: the
analytic content of the first Faris–Lavine inequality. -/
theorem ampSeq_sq_le (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (n : ℕ) :
    (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2
      ≤ (1 / 8) * ‖((diagMax (oscSymbol κ) x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
        + (κ ^ 2 / 2) * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2 := by
  have hle := amp_le_quarter hκ n
  have hnn : 0 ≤ ‖((x : L2I ℕ) : ℕ → ℂ) n‖ := norm_nonneg _
  have hamp : 0 ≤ amp κ n := amp_nonneg hκ n
  have hA2 : amp κ n ^ 2 ≤ (1 / 8) * oscSymbol κ n ^ 2 + κ ^ 2 / 2 := by
    nlinarith [sq_nonneg (oscSymbol κ n / 4 - κ / 2)]
  rw [norm_diagMax_coe hκ x n]
  simp only [ampSeq]
  nlinarith [hA2, sq_nonneg ‖((x : L2I ℕ) : ℕ → ℂ) n‖]

theorem summable_ampSeq_sq (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Summable (fun n => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (ampSeq_sq_le hκ x)
    (hasSum_ampBound x).summable



/-- The Hamiltonian maps the maximal domain of the comparison operator into the
Hilbert space. -/
theorem memLp_hFun (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Memℓp (hFun κ ((x : L2I ℕ) : ℕ → ℂ)) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  have hS := summable_ampSeq_sq hκ x
  have hshift : Summable (shift2 (fun n => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2)) :=
    summable_shift2 hS
  have htail : Summable (fun m => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2)) ^ 2) :=
    (summable_nat_add_iff 2).mpr hS
  refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) ?_
    ((hshift.mul_left 2).add (htail.mul_left 2))
  intro m
  have h1 := norm_hFun_le hκ ((x : L2I ℕ) : ℕ → ℂ) m
  have h2 : 0 ≤ shift2 (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ)) m :=
    shift2_nonneg _ (ampSeq_nonneg hκ _) m
  have h3 : 0 ≤ ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2) := ampSeq_nonneg hκ _ _
  have h4 := mul_self_le_mul_self (norm_nonneg (hFun κ ((x : L2I ℕ) : ℕ → ℂ) m)) h1
  rw [shift2_sq]
  nlinarith [h4, sq_nonneg (shift2 (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ)) m
    - ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2))]

/-- **The Navier–Stokes fiber Hamiltonian** `H = ½(πV + Vπ)`, on the maximal
domain of the comparison operator `N = π² + V² + I`. -/
noncomputable def nsH (κ : ℝ) (hκ : 0 ≤ κ) : maxDom (oscSymbol κ) →ₗ[ℂ] L2I ℕ where
  toFun x := ⟨hFun κ ((x : L2I ℕ) : ℕ → ℂ), memLp_hFun hκ x⟩
  map_add' x y := by
    refine lp.ext (funext fun m => ?_)
    simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, hFun, shift2]
    by_cases h : 2 ≤ m <;> simp [h] <;> ring
  map_smul' a x := by
    refine lp.ext (funext fun m => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul,
      hFun, shift2]
    by_cases h : 2 ≤ m <;> simp [h] <;> ring




/-! ## The inner products of the Hamiltonian

`⟪Hx, y⟫` splits into the two "hopping" series `A` (a particle moves two levels
up) and `B` (two levels down).  Both are absolutely convergent because
`2ab ≤ a² + b²`, and this is the only place where convergence is used. -/

/-- The upward hopping series `w(n) x̄ₙ yₙ₊₂`. -/
noncomputable def crossA (κ : ℝ) (X Y : ℕ → ℂ) : ℕ → ℂ :=
  fun n => (amp κ n : ℂ) * (starRingEnd ℂ) (X n) * Y (n + 2)

/-- The downward hopping series `w(n) x̄ₙ₊₂ yₙ`. -/
noncomputable def crossB (κ : ℝ) (X Y : ℕ → ℂ) : ℕ → ℂ :=
  fun n => (amp κ n : ℂ) * (starRingEnd ℂ) (X (n + 2)) * Y n




















/-! ## The first Faris–Lavine inequality: the relative bound -/







/-! ## The second Faris–Lavine inequality: the commutator form -/











/-! ## Essential self-adjointness, with no hypothesis left -/



/-! ## The commutator is genuinely non-zero

The bound `± i[H, N] ≤ c N` is not the trivial statement `[H, N] = 0`: the
momentum and the advection field do not commute, and already the two-level state
`e₀ + e₂` sees the commutator. -/

/-- The test state `e₀ + e₂`. -/
noncomputable def testState (κ : ℝ) : maxDom (oscSymbol κ) :=
  ⟨(lp.single 2 0 (1 : ℂ) + lp.single 2 2 (1 : ℂ) : L2I ℕ),
    finiteModes_le_maxDom _ (Submodule.add_mem _ (lpSingle_mem_lpFiniteModes 0 (1 : ℂ))
      (lpSingle_mem_lpFiniteModes 2 (1 : ℂ)))⟩







end Domain

end HermiteFarisLavine

end BookProof.NavierStokesFlow


