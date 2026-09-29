-- Prove2me | Definitions.Def_ChapterHashimotoShiftInvert
-- name    : ChapterHashimotoShiftInvert
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:55:19.500953+00:00
-- url     : https://prove2.me/theorems/5f404643-26cf-4332-b4b5-7d82cf315d3c
-- title:
--   `BookProof.ChapterHermiteGalerkinFriedrichs` proves that a Galerkin/Rayleigh–Ritz truncation in a complete (Hermite) bas ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HashimotoShiftInvert`, source chapter `BookProof/ChapterHashimotoShiftInvert.lean`).
--
--   `BookProof.ChapterHermiteGalerkinFriedrichs` proves that a Galerkin/Rayleigh–Ritz truncation in a complete (Hermite) basis converges — strongly, and in the strong resolvent sense — to the positive self-adjoint (Friedrichs) extension of the matrix it is fed, under a standing hypothesis that the operator is **bounded** on its domain.
--
--   That hypothesis is not a restriction on the *physics* the Hashimoto algorithm does, because the algorithm never applies `H` itself: it applies the *shift-inverted* operator `R = (H + γ)⁻¹`. And `R` is bounded — indeed `‖R‖ ≤ 1/γ` — for **every** positive symmetric `H`, however unbounded, purely because of positivity. This module makes that precise and closes the gap:
--
--   * `norm_shiftMap_ge` — the shift bound `‖(A + γ)x‖ ≥ γ‖x‖` for a positive symmetric operator. This is why the *effective* Hamiltonian is bounded even when `H` is not. * `closed_of_selfAdjointCriterion`, `shiftRange_isClosed`, `shiftRange_dense`, `shiftMap_surjective` — for a positive self-adjoint operator (in the sense of `IsPositiveSelfAdjointExtension`) the shifted operator `A + γ` is a bijection of its domain onto the whole space. No boundedness is used. * `IsShiftInvert`, `exists_isShiftInvert` — hence the bounded inverse `R = (A + γ)⁻¹` exists as a genuine element of `F →L[ℂ] F`, with `‖R‖ ≤ γ⁻¹` (`IsShiftInvert.opNorm_le`), self-adjoint (`IsShiftInvert.isSelfAdjoint`), positive and injective. * `IsShiftInvert.dom_eq_range`, `IsShiftInvert.apply_eq`, `shiftInvert_determines` — `R` remembers everything: its range is the domain of `A`, and `A = R⁻¹ − γ` there. Two positive self-adjoint operators with the same shift-invert are the same operator. * `galerkinCompression_shiftInvert_tendsto`, `galerkinResolvent_shiftInvert_tendsto` — the bounded Galerkin theory of `BookProof.ChapterHermiteGalerkinFriedrichs` applies verbatim to `R`. * `hashimoto_shiftInvert_selects_friedrichs` — the headline, **with no boundedness hypothesis anywhere**: for a symmetric positive matrix in a complete basis and any positive self-adjoint extension `A` of it (the Friedrichs extension being one), the shift-inverted operator `R = (A+γ)⁻¹` is bounded, the Galerkin truncations of `R` converge strongly to `R` (this is precisely strong resolvent convergence of the truncations to `A`), and `R` determines `A` uniquely — so the algorithm selects that extension and no other. * `ell2UnboundedExample` and `unbounded_shiftInvert_example` — the hypotheses are satisfied by a genuinely **unbounded** operator: the diagonal operator `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, whose shift-invert at `γ = 1` is the bounded diagonal operator `eₙ ↦ eₙ/(n+1)`. The boundedness hypothesis of `hermiteGalerkin_selects_friedrichs` fails for this `A` (`ell2UnboundedExample_unbounded`), while the theorems here apply.
--
--   This module treats one **real positive** shift `γ`, where invertibility of `A + γ` comes from positivity of `A`. The shifts the Shift-invert Rational Krylov method actually uses are complex with non-zero imaginary part (which makes `γ I − A` invertible for every self-adjoint `A`, positive or not), and they change from step to step; that generalisation, in the same namespace, is `BookProof.ChapterHashimotoComplexShifts`, whose `isShiftInvertC_neg_of_isShiftInvert` relates the two notions.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib

import Mathlib

/-!
# The shift-invert (Hashimoto) trick: the Galerkin/Friedrichs selection theorem
for **unbounded** Hamiltonians

`BookProof.ChapterHermiteGalerkinFriedrichs` proves that a Galerkin/Rayleigh–Ritz
truncation in a complete (Hermite) basis converges — strongly, and in the strong
resolvent sense — to the positive self-adjoint (Friedrichs) extension of the
matrix it is fed, under a standing hypothesis that the operator is **bounded**
on its domain.

That hypothesis is not a restriction on the *physics* the Hashimoto algorithm
does, because the algorithm never applies `H` itself: it applies the
*shift-inverted* operator `R = (H + γ)⁻¹`.  And `R` is bounded — indeed
`‖R‖ ≤ 1/γ` — for **every** positive symmetric `H`, however unbounded, purely
because of positivity.  This module makes that precise and closes the gap:

* `norm_shiftMap_ge` — the shift bound `‖(A + γ)x‖ ≥ γ‖x‖` for a positive
  symmetric operator.  This is why the *effective* Hamiltonian is bounded even
  when `H` is not.
* `closed_of_selfAdjointCriterion`, `shiftRange_isClosed`, `shiftRange_dense`,
  `shiftMap_surjective` — for a positive self-adjoint operator (in the sense of
  `IsPositiveSelfAdjointExtension`) the shifted operator `A + γ` is a bijection
  of its domain onto the whole space.  No boundedness is used.
* `IsShiftInvert`, `exists_isShiftInvert` — hence the bounded inverse
  `R = (A + γ)⁻¹` exists as a genuine element of `F →L[ℂ] F`, with
  `‖R‖ ≤ γ⁻¹` (`IsShiftInvert.opNorm_le`), self-adjoint
  (`IsShiftInvert.isSelfAdjoint`), positive and injective.
* `IsShiftInvert.dom_eq_range`, `IsShiftInvert.apply_eq`,
  `shiftInvert_determines` — `R` remembers everything: its range is the domain
  of `A`, and `A = R⁻¹ − γ` there.  Two positive self-adjoint operators with the
  same shift-invert are the same operator.
* `galerkinCompression_shiftInvert_tendsto`,
  `galerkinResolvent_shiftInvert_tendsto` — the bounded Galerkin theory of
  `BookProof.ChapterHermiteGalerkinFriedrichs` applies verbatim to `R`.
* `hashimoto_shiftInvert_selects_friedrichs` — the headline, **with no
  boundedness hypothesis anywhere**: for a symmetric positive matrix in a
  complete basis and any positive self-adjoint extension `A` of it (the
  Friedrichs extension being one), the shift-inverted operator `R = (A+γ)⁻¹` is
  bounded, the Galerkin truncations of `R` converge strongly to `R` (this is
  precisely strong resolvent convergence of the truncations to `A`), and `R`
  determines `A` uniquely — so the algorithm selects that extension and no
  other.
* `ell2UnboundedExample` and `unbounded_shiftInvert_example` — the hypotheses
  are satisfied by a genuinely **unbounded** operator: the diagonal operator
  `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`, whose shift-invert at `γ = 1` is the bounded
  diagonal operator `eₙ ↦ eₙ/(n+1)`.  The boundedness hypothesis of
  `hermiteGalerkin_selects_friedrichs` fails for this `A`
  (`ell2UnboundedExample_unbounded`), while the theorems here apply.

This module treats one **real positive** shift `γ`, where invertibility of
`A + γ` comes from positivity of `A`.  The shifts the Shift-invert Rational
Krylov method actually uses are complex with non-zero imaginary part (which
makes `γ I − A` invertible for every self-adjoint `A`, positive or not), and
they change from step to step; that generalisation, in the same namespace, is
`BookProof.ChapterHashimotoComplexShifts`, whose
`isShiftInvertC_neg_of_isShiftInvert` relates the two notions.
-/

namespace BookProof.HashimotoShiftInvert

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology
open scoped lp

/-! ## Part 1 — the shift bound: why the effective Hamiltonian is bounded -/

section Bound

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

/-- The shifted operator `A + γ` on the domain of `A`. -/
noncomputable def shiftMap (A : Dom →ₗ[ℂ] F) (γ : ℝ) : Dom →ₗ[ℂ] F :=
  A + (γ : ℂ) • Dom.subtype







end Bound

/-! ## Part 2 — for a positive self-adjoint operator the shift is a bijection -/

section Surjective

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}


/-- The range of the shifted operator, as a submodule. -/
noncomputable def shiftRange (A : Dom →ₗ[ℂ] F) (γ : ℝ) : Submodule ℂ F :=
  LinearMap.range (shiftMap A γ)







end Surjective

/-! ## Part 3 — the shift-inverted operator `R = (A + γ)⁻¹` -/

section ShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

/-- `R` is the **shift-invert** of `A` at shift `γ`: a bounded everywhere-defined
operator that inverts `A + γ` in both directions.  This is the operator the
Hashimoto/SIRK algorithm actually applies — the "effective Hamiltonian". -/
def IsShiftInvert (A : Dom →ₗ[ℂ] F) (γ : ℝ) (R : F →L[ℂ] F) : Prop :=
  (∀ x : Dom, R (shiftMap A γ x) = (x : F)) ∧
    ∀ u : F, ∃ h : R u ∈ Dom, shiftMap A γ ⟨R u, h⟩ = u

























end ShiftInvert

/-! ## Part 3b — the converse: the operator defined by a bounded shift-invert

Running the construction backwards turns a bounded, injective, positive
self-adjoint `R` into the (generally unbounded) operator `A = R⁻¹ − γ` of which
it is the shift-invert.  This is how one exhibits genuinely unbounded examples,
and it shows the notion `IsShiftInvert` is not vacuous. -/

section Converse

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A preimage under an operator, chosen on its range. -/
noncomputable def preim (R : F →L[ℂ] F) (y : LinearMap.range (R : F →ₗ[ℂ] F)) : F :=
  (LinearMap.mem_range.mp y.2).choose

omit [CompleteSpace F] in
@[simp] theorem preim_spec (R : F →L[ℂ] F) (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    R (preim R y) = (y : F) := (LinearMap.mem_range.mp y.2).choose_spec



/-- **The operator whose shift-invert is `R`**: `A = R⁻¹ − γ`, defined on the
range of `R`. -/
noncomputable def invShiftOperator (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ) :
    LinearMap.range (R : F →ₗ[ℂ] F) →ₗ[ℂ] F where
  toFun y := preim R y - (γ : ℂ) • (y : F)
  map_add' y z := by
    have h : preim R (y + z) = preim R y + preim R z := by
      apply hinj
      rw [preim_spec, map_add, preim_spec, preim_spec]
      rfl
    rw [h]
    push_cast [Submodule.coe_add]
    module
  map_smul' a y := by
    have h : preim R (a • y) = a • preim R y := by
      apply hinj
      rw [preim_spec, map_smul, preim_spec]
      rfl
    simp only [RingHom.id_apply, h]
    push_cast [Submodule.coe_smul]
    module













end Converse

/-! ## Part 4 — the Galerkin theory applies to the effective Hamiltonian -/

section Galerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}





end Galerkin

/-! ## Part 5 — the headline: no boundedness hypothesis -/

section Headline

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



end Headline

/-! ## Part 6 — a genuinely unbounded example -/

section Example

open scoped InnerProductSpace ENNReal

/-! ### The diagonal operator on `ℓ²(ℕ, ℂ)` -/

theorem memlp_diagFun {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    Memℓp (fun n => (c n : ℂ) * x n) 2 := by
  have hx : Summable fun n => ‖(x : ℕ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp x).summable (by norm_num)
  refine memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx)
  have h1 : ‖(c n : ℂ) * (x : ℕ → ℂ) n‖ = |c n| * ‖(x : ℕ → ℂ) n‖ := by
    simp [Complex.norm_real]
  have hle : |c n| * ‖(x : ℕ → ℂ) n‖ ≤ ‖(x : ℕ → ℂ) n‖ := by
    nlinarith [abs_nonneg (c n), hc n, norm_nonneg ((x : ℕ → ℂ) n)]
  rw [h1, show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  exact Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- The diagonal (multiplication) operator on `ℓ²(ℕ, ℂ)` with real coefficients
bounded by one, as a linear map. -/
noncomputable def diagLin {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun x := ⟨fun n => (c n : ℂ) * x n, memlp_diagFun hc x⟩
  map_add' x y := by
    apply lp.ext; funext n
    simp only [lp.coeFn_add]
    dsimp [PreLp]
    rw [mul_add]
  map_smul' a x := by
    apply lp.ext; funext n
    simp only [lp.coeFn_smul]
    dsimp [PreLp]
    ring

@[simp] theorem diagLin_apply {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagLin hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (c n : ℂ) * x n := rfl

theorem diagLin_norm_le {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) :
    ‖diagLin hc x‖ ≤ ‖x‖ := by
  refine lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg x) ?_
  rw [lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((memlp_diagFun hc x).summable (by norm_num)) ((lp.memℓp x).summable (by norm_num))
  have h1 : ‖((diagLin hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n‖ = |c n| * ‖(x : ℕ → ℂ) n‖ := by
    rw [diagLin_apply]; simp [Complex.norm_real]
  have hle : |c n| * ‖(x : ℕ → ℂ) n‖ ≤ ‖(x : ℕ → ℂ) n‖ := by
    nlinarith [abs_nonneg (c n), hc n, norm_nonneg ((x : ℕ → ℂ) n)]
  rw [h1, show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  exact Real.rpow_le_rpow (by positivity) hle (by norm_num)

/-- The diagonal operator as a bounded operator, of norm at most one. -/
noncomputable def diagCLM {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  (diagLin hc).mkContinuous 1 (by simpa using diagLin_norm_le hc)

@[simp] theorem diagCLM_apply {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    ((diagCLM hc x : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (c n : ℂ) * x n := rfl







theorem diagCLM_injective {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) (hne : ∀ n, c n ≠ 0) :
    Function.Injective (diagCLM hc) := by
  intro x y hxy
  apply lp.ext
  funext n
  have h := congrArg (fun z : ℓ²(ℕ, ℂ) => (z : ℕ → ℂ) n) hxy
  simp only [diagCLM_apply] at h
  have hc0 : (c n : ℂ) ≠ 0 := by exact_mod_cast hne n
  exact mul_left_cancel₀ hc0 h

/-! ### The unbounded example: `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)` -/

/-- The coefficients `1/(n+1)` of the shift-inverted operator. -/
noncomputable def invCoeff (n : ℕ) : ℝ := 1 / (n + 1)

theorem invCoeff_pos (n : ℕ) : 0 < invCoeff n := by
  have : (0:ℝ) < (n : ℝ) + 1 := by positivity
  simpa [invCoeff] using this

theorem invCoeff_le_one (n : ℕ) : invCoeff n ≤ 1 := by
  have h1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [invCoeff, div_le_one (by positivity)]
  exact h1

theorem invCoeff_abs_le_one (n : ℕ) : |invCoeff n| ≤ 1 := by
  rw [abs_of_pos (invCoeff_pos n)]
  exact invCoeff_le_one n

theorem invCoeff_ne_zero (n : ℕ) : invCoeff n ≠ 0 := ne_of_gt (invCoeff_pos n)

/-- **The effective (shift-inverted) Hamiltonian of the example**: the bounded
diagonal operator `eₙ ↦ eₙ/(n+1)`. -/
noncomputable def ell2ShiftInvert : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) := diagCLM invCoeff_abs_le_one

theorem ell2ShiftInvert_injective : Function.Injective ell2ShiftInvert :=
  diagCLM_injective invCoeff_abs_le_one invCoeff_ne_zero



/-- The square root coefficients, used to see that `R ≤ 1`. -/
noncomputable def sqrtInvCoeff (n : ℕ) : ℝ := Real.sqrt (invCoeff n)







/-- **The unbounded Hamiltonian of the example**: `A = R⁻¹ − 1`, i.e. `A eₙ = n eₙ`,
on the domain `range R = {x : ∑ (n+1)²|xₙ|² < ∞}`. -/
noncomputable def ell2UnboundedExample :
    LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  invShiftOperator ell2ShiftInvert ell2ShiftInvert_injective 1



/-- The `k`-th basis vector of `ℓ²(ℕ, ℂ)` is in the range of `R`: indeed
`R ((k+1) eₖ) = eₖ`. -/
theorem ell2ShiftInvert_smul_single (k : ℕ) :
    ell2ShiftInvert (((k : ℂ) + 1) • lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℂ) := by
  apply lp.ext
  funext n
  rw [ell2ShiftInvert, diagCLM_apply]
  by_cases hn : n = k
  · subst hn
    have hne : ((n : ℂ) + 1) ≠ 0 := by
      rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring]
      exact_mod_cast Nat.succ_ne_zero n
    have hcoe : ((invCoeff n : ℝ) : ℂ) = ((n : ℂ) + 1)⁻¹ := by
      rw [invCoeff]
      push_cast
      rw [one_div]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_eq_same, hcoe,
      smul_eq_mul, mul_one]
    field_simp
  · simp [lp.single_apply, Pi.single_eq_of_ne hn]

theorem ell2Basis_apply (k : ℕ) : (ell2Basis k : ℓ²(ℕ, ℂ)) = lp.single 2 k (1 : ℂ) :=
  lp.ext_iff.mpr (congrArg Subtype.val (HilbertBasis.repr_self ell2Basis k))

theorem ell2Basis_mem_range (k : ℕ) :
    (ell2Basis k : ℓ²(ℕ, ℂ))
      ∈ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) :=
  ⟨((k : ℂ) + 1) • lp.single 2 k (1 : ℂ), by
    rw [ell2Basis_apply]; exact ell2ShiftInvert_smul_single k⟩

/-- The finite-mode (Hermite-type) domain sits inside the domain of the
unbounded operator, so the algorithm's matrix elements are all defined. -/
theorem finiteModeDomain_le_range :
    finiteModeDomain ell2Basis
      ≤ LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ)) := by
  rw [finiteModeDomain, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact ell2Basis_mem_range k

/-- **The matrix the algorithm is given**: the unbounded operator restricted to
finite linear combinations of basis vectors. -/
noncomputable def ell2ExampleMatrix : finiteModeDomain ell2Basis →ₗ[ℂ] ℓ²(ℕ, ℂ) :=
  ell2UnboundedExample.comp (Submodule.inclusion finiteModeDomain_le_range)









end Example

end BookProof.HashimotoShiftInvert


