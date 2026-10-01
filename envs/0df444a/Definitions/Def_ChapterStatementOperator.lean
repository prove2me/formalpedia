-- Prove2me | Definitions.Def_ChapterStatementOperator
-- name    : ChapterStatementOperator
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:55:37.998052+00:00
-- url     : https://prove2.me/theorems/dfe26ebd-6297-4fa9-b6da-33c0b84452b6
-- title:
--   Chapter StatementOperator
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterStatementOperator.lean`): generated def bundle for ChapterStatementOperator. See BookProof/ChapterStatementOperator.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStatementOperator.lean

import Mathlib


/-!
# Statements as operators on the Hilbert space of models

`book.tex`, chapter *Statistical Model Theory and Bayesian priors where the Riemann
Hypothesis is true*, §*Statistical Model Theory*:

> Then, we can represent statements (theorems if proven so) as operators in a Hilbert
> space.  This allows to deal with undecidable statements as projection operators, which
> project the Hilbert space of models to a smaller subspace.  Statements become more than
> true/false/undecidable … We can even consider uncertain statements, that are operators
> but not projections. … an undecidable statement also has a proof and "approximated"
> proofs (which evaluate incorrectly for a small subspace of the models).

This chapter formalizes that calculus.  `H` is the Hilbert space of models; a
`ModelStatement` is an orthogonal projection on it, and its *truth value* on a model
vector `ψ` is the expectation `Re ⟪ψ, Pψ⟫`.

Main results.

* `ModelStatement.truthValue_eq_norm_sq`, `truthValue_nonneg`, `truthValue_le_norm_sq`,
  `truthValue_mem_unitInterval` — the truth value is a real number between `0` and
  `‖ψ‖²`, so on unit model vectors it is a number in `[0,1]`: "statements become more
  than true/false/undecidable".
* `ModelStatement.truthValue_not` — negation `1 - P` complements the truth value.
* `ModelStatement.and` — the conjunction of two *commuting* statements is again a
  statement, and it is weaker than each conjunct (`truthValue_and_le_left`/`_right`).
* `ModelStatement.truthValue_eq_zero_iff` and `truthValue_eq_norm_sq_iff` — the models
  of extreme truth value are exactly those killed by, respectively fixed by, the
  projection.
* `ModelStatement.undecidable_iff` — a statement is undecidable (`P ≠ 0` and `P ≠ 1`)
  exactly when there is a nonzero model where it holds outright and a nonzero model
  where it fails outright: the projection has a proper nonzero range.
* `UncertainStatement` — the weaker notion the book asks for: a self-adjoint operator
  with truth values in `[0, ‖ψ‖²]`, not required to be a projection.
  `ModelStatement.toUncertain` embeds the projections and
  `halfUncertain_not_idempotent` exhibits an uncertain statement that is genuinely not a
  projection.
* `approximate_proof_error` — an "approximated proof": an operator within `ε` of the
  statement evaluates every model to within `ε‖ψ‖²` of the true value.
-/

namespace BookProof.ChapterStatementOperator

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **statement** about the models collected in the Hilbert space `H`: an orthogonal
projection, i.e. a self-adjoint idempotent bounded operator.  Its range is the subspace
of models in which the statement holds. -/
structure ModelStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The operator representing the statement. -/
  op : H →L[ℂ] H
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint op
  /-- The operator is idempotent. -/
  isIdempotent : op ∘L op = op

namespace ModelStatement

variable (S : ModelStatement H) (ψ : H)

/-- The **truth value** of the statement on the model vector `ψ`: the expectation
`Re ⟪ψ, Pψ⟫`. -/
noncomputable def truthValue : ℝ := RCLike.re (inner ℂ ψ (S.op ψ))

/-- The truth value is the squared norm of the projected model. -/
@[simp] theorem truthValue_eq_norm_sq : S.truthValue ψ = ‖S.op ψ‖ ^ 2 := by
  have h1 : (inner ℂ ψ (S.op ψ) : ℂ) = inner ℂ ψ (S.op (S.op ψ)) := by
    rw [← ContinuousLinearMap.comp_apply, S.isIdempotent]
  rw [truthValue, h1, ← ContinuousLinearMap.adjoint_inner_left, S.isSelfAdjoint.adjoint_eq,
    inner_self_eq_norm_sq]

theorem truthValue_nonneg : 0 ≤ S.truthValue ψ := by
  rw [S.truthValue_eq_norm_sq]; positivity

/-- A projection does not increase norms. -/
theorem norm_op_le : ‖S.op ψ‖ ≤ ‖ψ‖ := by
  have hb : ‖S.op ψ‖ ^ 2 = RCLike.re (inner ℂ ψ (S.op ψ)) := (S.truthValue_eq_norm_sq ψ).symm
  have h1 : RCLike.re (inner ℂ ψ (S.op ψ)) ≤ ‖(inner ℂ ψ (S.op ψ) : ℂ)‖ :=
    le_trans (le_abs_self _) (RCLike.abs_re_le_norm _)
  have h2 : ‖(inner ℂ ψ (S.op ψ) : ℂ)‖ ≤ ‖ψ‖ * ‖S.op ψ‖ := norm_inner_le_norm ψ (S.op ψ)
  rcases eq_or_lt_of_le (norm_nonneg (S.op ψ)) with h | h
  · rw [← h]; exact norm_nonneg ψ
  · have hsq : ‖S.op ψ‖ ^ 2 ≤ ‖ψ‖ * ‖S.op ψ‖ := hb ▸ (h1.trans h2)
    nlinarith

theorem truthValue_le_norm_sq : S.truthValue ψ ≤ ‖ψ‖ ^ 2 := by
  rw [S.truthValue_eq_norm_sq]
  have := S.norm_op_le ψ
  nlinarith [norm_nonneg (S.op ψ), norm_nonneg ψ]



/-- The **negation** of a statement. -/
def not (S : ModelStatement H) : ModelStatement H where
  op := 1 - S.op
  isSelfAdjoint := by
    simpa using (IsSelfAdjoint.one (R := H →L[ℂ] H)).sub S.isSelfAdjoint
  isIdempotent := by
    have hmul : S.op * S.op = S.op := S.isIdempotent
    change (1 - S.op) * (1 - S.op) = 1 - S.op
    have h : (1 - S.op) * (1 - S.op) = 1 - S.op - S.op + S.op * S.op := by noncomm_ring
    rw [h, hmul]; abel





/-- The **conjunction** of two commuting statements. -/
def and (S T : ModelStatement H) (hcomm : S.op ∘L T.op = T.op ∘L S.op) :
    ModelStatement H where
  op := S.op ∘L T.op
  isSelfAdjoint := by
    have hadj : adjoint (S.op ∘L T.op) = T.op ∘L S.op := by
      rw [ContinuousLinearMap.adjoint_comp, S.isSelfAdjoint.adjoint_eq,
        T.isSelfAdjoint.adjoint_eq]
    rw [IsSelfAdjoint, star_eq_adjoint, hadj, ← hcomm]
  isIdempotent := by
    have hS : S.op * S.op = S.op := S.isIdempotent
    have hT : T.op * T.op = T.op := T.isIdempotent
    have hc : S.op * T.op = T.op * S.op := hcomm
    change (S.op * T.op) * (S.op * T.op) = S.op * T.op
    calc (S.op * T.op) * (S.op * T.op) = S.op * (T.op * S.op) * T.op := by noncomm_ring
      _ = S.op * (S.op * T.op) * T.op := by rw [← hc]
      _ = (S.op * S.op) * (T.op * T.op) := by noncomm_ring
      _ = S.op * T.op := by rw [hS, hT]











/-- A statement is **undecidable** when its operator is neither `0` nor `1`: it projects
the space of models onto a proper nonzero subspace. -/
def Undecidable (S : ModelStatement H) : Prop := S.op ≠ 0 ∧ S.op ≠ 1



end ModelStatement

/-- An **uncertain statement**: the book's weakening — a self-adjoint operator whose
expectation on every model lies between `0` and `‖ψ‖²`, but which need not be a
projection. -/
structure UncertainStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The operator representing the uncertain statement. -/
  op : H →L[ℂ] H
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint op
  /-- Expectations are nonnegative. -/
  nonneg : ∀ ψ : H, 0 ≤ RCLike.re (inner ℂ ψ (op ψ))
  /-- Expectations are bounded by the squared norm. -/
  le_norm_sq : ∀ ψ : H, RCLike.re (inner ℂ ψ (op ψ)) ≤ ‖ψ‖ ^ 2

/-- Every statement is in particular an uncertain statement. -/
noncomputable def ModelStatement.toUncertain (S : ModelStatement H) :
    UncertainStatement H where
  op := S.op
  isSelfAdjoint := S.isSelfAdjoint
  nonneg := fun ψ => S.truthValue_nonneg ψ
  le_norm_sq := fun ψ => S.truthValue_le_norm_sq ψ

omit [CompleteSpace H] in
/-- The expectation of `½ · 1` is half the squared norm. -/
theorem half_inner_eq (ψ : H) :
    RCLike.re (inner ℂ ψ (((1 / 2 : ℂ) • (1 : H →L[ℂ] H)) ψ)) = ‖ψ‖ ^ 2 / 2 := by
  simp [inner_smul_right, ← Complex.ofReal_pow]
  ring

/-- The "half true" statement `½ · 1`: an uncertain statement. -/
noncomputable def halfUncertain : UncertainStatement H where
  op := (1 / 2 : ℂ) • (1 : H →L[ℂ] H)
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_smul, star_one]
    norm_num
  nonneg := fun ψ => by rw [half_inner_eq]; positivity
  le_norm_sq := fun ψ => by
    rw [half_inner_eq]
    nlinarith [sq_nonneg ‖ψ‖]







end BookProof.ChapterStatementOperator


