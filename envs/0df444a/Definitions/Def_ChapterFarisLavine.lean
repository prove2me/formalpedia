-- Prove2me | Definitions.Def_ChapterFarisLavine
-- name    : ChapterFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:38:41.10898+00:00
-- url     : https://prove2.me/theorems/2574cf07-0870-418c-90d0-fd9cd38d4a12
-- title:
--   The abstract Faris–Lavine theory — `SymmetricOn`, `DeficiencyTrivialAt`, `EssentiallySelfAdjointOn`, `quadForm`, `commFo ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FarisLavine`, source chapter `BookProof/ChapterFarisLavine.lean`).
--
--   The abstract Faris–Lavine theory — `SymmetricOn`, `DeficiencyTrivialAt`, `EssentiallySelfAdjointOn`, `quadForm`, `commForm` and the criterion `essentiallySelfAdjointOn_of_farisLavine` — lives in `BookProof.ChapterFarisLavineCore`, which depends on Mathlib alone. This module adds the parts that talk to the concrete operators of the Navier–Stokes chapters: the refutation of the criterion without positivity of `N`, the multiplication operators on `ℓ²(ℕ)`, and the tie-in with `BookProof.NavierStokesFlow.HasZeroDeficiencyOn`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

import Mathlib

/-!
# Faris–Lavine: the concrete companions of the abstract criterion

The abstract Faris–Lavine theory — `SymmetricOn`, `DeficiencyTrivialAt`,
`EssentiallySelfAdjointOn`, `quadForm`, `commForm` and the criterion
`essentiallySelfAdjointOn_of_farisLavine` — lives in
`BookProof.ChapterFarisLavineCore`, which depends on Mathlib alone.  This module
adds the parts that talk to the concrete operators of the Navier–Stokes chapters:
the refutation of the criterion without positivity of `N`, the multiplication
operators on `ℓ²(ℕ)`, and the tie-in with
`BookProof.NavierStokesFlow.HasZeroDeficiencyOn`.
-/

namespace BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}


/-! ## The hypotheses cannot be weakened to a mere relative bound

The Navier–Stokes chapters of this project carry the Faris–Lavine criterion as a
named hypothesis in the form: *`H` symmetric on a dense domain, `‖H v‖ ≤ a ‖N v‖`,
and `|⟪v, [H, N] v⟫| ≤ b |⟪v, N v⟫|` imply vanishing adjoint deficiency*, with no
positivity and no self-adjointness required of `N`.  That form of the statement
is **false**, and the theorem below refutes it: for the limit-circle Jacobi
operator of `BookProof.ChapterNavierStokesDeficiency` the choice `N = H` verifies
both inequalities (with `a = 1`, `b = 0`) while essential self-adjointness fails.
The positivity of `N` and the surjectivity of `N + 1` in
`essentiallySelfAdjointOn_of_farisLavine` are therefore not decorative. -/



/-! ## An unbounded application: multiplication operators on `ℓ²(ℕ)`

The multiplication operator by an arbitrary real sequence `lam`, on its maximal
domain, satisfies the hypotheses of Theorem 1 with `N = |lam|` and `c = 0`: the
two operators commute, so the commutator form vanishes identically, and `N + 1`
is surjective because `1 + |lam n| ≥ 1`.  Hence it is essentially self-adjoint —
an unbounded instance of the criterion. -/

section Multiplication

open scoped ENNReal

/-- The Hilbert space `ℓ²(ℕ)`. -/
noncomputable abbrev L2Nat := lp (fun _ : ℕ => ℂ) 2

/-- Coefficientwise multiplication by a real symbol. -/
def mulSymbolFun (s : ℕ → ℝ) (f : ℕ → ℂ) : ℕ → ℂ := fun n => (s n : ℂ) * f n

theorem memLpTwo_of_norm_le {f g : ℕ → ℂ} (hg : Memℓp g 2) (h : ∀ n, ‖f n‖ ≤ ‖g n‖) :
    Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num)] at hg ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
  gcongr
  exact h n

/-- The maximal domain of multiplication by `lam`. -/
def mulSymbolDomain (lam : ℕ → ℝ) : Submodule ℂ L2Nat where
  carrier := {f : L2Nat | Memℓp (mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ)) 2}
  add_mem' := by
    intro f g hf hg
    have heq : mulSymbolFun lam ((f + g : L2Nat) : ℕ → ℂ)
        = mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ) + mulSymbolFun lam ((g : L2Nat) : ℕ → ℂ) := by
      funext n; simp [mulSymbolFun]; ring
    simp only [Set.mem_setOf_eq, heq]
    exact hf.add hg
  zero_mem' := by
    have heq : mulSymbolFun lam ((0 : L2Nat) : ℕ → ℂ) = 0 := by
      funext n; simp [mulSymbolFun]
    simp only [Set.mem_setOf_eq, heq]
    exact zero_memℓp
  smul_mem' := by
    intro c f hf
    have heq : mulSymbolFun lam ((c • f : L2Nat) : ℕ → ℂ)
        = c • mulSymbolFun lam ((f : L2Nat) : ℕ → ℂ) := by
      funext n; simp [mulSymbolFun]; ring
    simp only [Set.mem_setOf_eq, heq]
    exact hf.const_smul c

/-- Multiplication by a symbol `s` dominated by `lam`, on the maximal domain of
`lam`. -/
noncomputable def mulSymbolOp (lam s : ℕ → ℝ) (hs : ∀ n, |s n| ≤ |lam n|) :
    mulSymbolDomain lam →ₗ[ℂ] L2Nat where
  toFun f := ⟨mulSymbolFun s ((f : L2Nat) : ℕ → ℂ), by
    refine memLpTwo_of_norm_le f.2 fun n => ?_
    simp only [mulSymbolFun, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hs n) (norm_nonneg _)⟩
  map_add' f g := by
    ext n
    simp only [Submodule.coe_add, lp.coeFn_add, mulSymbolFun, Pi.add_apply]
    ring
  map_smul' c f := by ext n; simp [mulSymbolFun]; ring



theorem abs_abs_le (lam : ℕ → ℝ) : ∀ n, |(|lam n|)| ≤ |lam n| := fun n => by simp

/-- The comparison operator `N = |lam|`. -/
noncomputable def mulComparison (lam : ℕ → ℝ) : mulSymbolDomain lam →ₗ[ℂ] L2Nat :=
  mulSymbolOp lam (fun n => |lam n|) (abs_abs_le lam)

/-- The operator itself, multiplication by `lam`. -/
noncomputable def mulHamiltonian (lam : ℕ → ℝ) : mulSymbolDomain lam →ₗ[ℂ] L2Nat :=
  mulSymbolOp lam lam (fun _ => le_rfl)















/-- The basis state `e n`, which lies in every maximal domain. -/
noncomputable def mulBasis (lam : ℕ → ℝ) (n : ℕ) : mulSymbolDomain lam :=
  ⟨lp.single 2 n 1, by
    have hval : mulSymbolFun lam ((lp.single 2 n (1 : ℂ) : L2Nat) : ℕ → ℂ)
        = (lam n : ℂ) • ((lp.single 2 n (1 : ℂ) : L2Nat) : ℕ → ℂ) := by
      funext m
      by_cases hmn : m = n
      · subst hmn; simp [mulSymbolFun, lp.single_apply]
      · simp [mulSymbolFun, lp.single_apply, Pi.single_eq_of_ne hmn]
    change Memℓp (mulSymbolFun lam ((lp.single 2 n (1 : ℂ) : L2Nat) : ℕ → ℂ)) 2
    rw [hval]
    exact (lp.memℓp _).const_smul _⟩



end Multiplication

/-! ## Discharging the named hypothesis of the Navier–Stokes chapter

`BookProof.ChapterNavierStokesFlow` carries essential self-adjointness on a dense
domain in its own predicate `HasZeroDeficiencyOn`, and obtains it from a
Faris–Lavine criterion supplied as a *named hypothesis*.  The predicate is
literally the conjunction of the two deficiency conditions used here, so the
theorem proved above discharges that hypothesis — in the corrected form, with `N`
positive and `N + 1` surjective (the unrestricted relative-bound form being false
by `not_farisLavine_criterion_of_relative_bound`). -/

section NavierStokesTieIn






end NavierStokesTieIn

end BookProof.FarisLavine


