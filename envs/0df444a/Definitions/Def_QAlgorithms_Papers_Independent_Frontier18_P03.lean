-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03
-- name    : QAlgorithms_Papers_Independent_Frontier18_P03
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:29:59.479462+00:00
-- url     : https://prove2.me/theorems/ca11722a-71f0-44b3-912a-fcf7034fe7e4
-- title:
--   Definitions for General formulas for capacity of classical-quantum channels
-- statement:
--   The objects the formalized statements of *General formulas for capacity of classical-quantum channels* (arXiv:quant-ph/0206186) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FunctionChoices`: PDF p.8: sequences choosing one function from each nonempty family. Index `n : Nat` denotes the source's term numbered `n+1`.
--   - `minusCutoff`: PDF p.8: the minus cutoff. Both the inner limsup and outer supremum are extended-real, including empty and unbounded threshold sets.
--   - `plusCutoff`: PDF p.8: the plus cutoff, with extended-real liminf and infimum.
--   - `OperatorPositive`: PDF p.9: positivity of a bounded complex Hilbert-space operator, written as reality and nonnegativity of every quadratic form.
--   - `regularizedSandwich`: PDF pp.9–10: bounded regularization of the generalized-inverse sandwich. The regularizer is `1/(k+1)>0`; its strong limit is the support extension of `(sqrt(S+T))^{-1} S (sqrt(S+T))^{-1}`. Each factor here is bounded, even when the generalized inverse itself is unbounded.
--   - `DensityPresentation`: PDF pp.4,23: a normalized positive trace-class state, represented by `rho = sum_k |v_k><v_k|` with `sum_k ||v_k||^2 = 1`. Zero vectors allow finite rank. Every positive trace-class state has such a presentation, even on a nonseparable Hilbert space, since its support is separable. The representation is not required to be unique or orthogonal.
--   - `densityAction`: PDF p.23: action of the represented density operator. Square-norm summability guarantees absolute convergence of this vector series.
--   - `traceAgainst`: PDF p.23: real trace `Tr[rho A]`. For every bounded A the series is absolutely summable, bounded termwise by `||A|| ||v_k||^2`, so no divergent real-tsum default is used.
--   - `IsOrthogonalProjection`: PDF p.23: an orthogonal projection is idempotent and self-adjoint. No commutation of two such projections is implicit.
--   - `purePresentation`: Rank-one state presentation, a small case of the PDF p.4 state convention.
--   - `IsFiniteLaw`: PDF p.6: a finitely supported real array is a probability law precisely when all weights are nonnegative and sum to one.
--   - `meanCost`: PDF p.25: the expected cost, always a finite sum. Costs may be negative.
--   - `feasibleLaws`: PDF pp.25,28: feasible finite-support laws, as a subset of the real vector space of finitely supported arrays.
-- source:
--   General formulas for capacity of classical-quantum channels, arXiv:quant-ph/0206186v4, https://arxiv.org/abs/quant-ph/0206186v4

import Mathlib

/-!
Statements from Hayashi–Nagaoka, arXiv:quant-ph/0206186v4.
Only Lemmas 1, 2, 6 and Appendix II are stated here. The other planned nodes
are explicitly deferred in the unit's HARD.md and GAPS.json.
No finite-dimensional specialization stands in for a general-channel theorem.
-/

noncomputable section

open Filter

namespace QAlgorithms.Papers.Independent.Frontier18.P03

/-- PDF p.8: sequences choosing one function from each nonempty family.
Index `n : Nat` denotes the source's term numbered `n+1`. -/
abbrev FunctionChoices (F : ℕ → Set (ℝ → ℝ)) :=
  {f : ℕ → ℝ → ℝ // ∀ n, f n ∈ F n}

/-- PDF p.8: the minus cutoff. Both the inner limsup and outer supremum
are extended-real, including empty and unbounded threshold sets. -/
def minusCutoff (f : ℕ → ℝ → ℝ) (x : ℝ) : EReal :=
  sSup {r : EReal | ∃ a : ℝ, r = (a : EReal) ∧
    Filter.limsup (fun n => (f n a : EReal)) atTop ≤ (x : EReal)}

/-- PDF p.8: the plus cutoff, with extended-real liminf and infimum. -/
def plusCutoff (f : ℕ → ℝ → ℝ) (x : ℝ) : EReal :=
  sInf {r : EReal | ∃ a : ℝ, r = (a : EReal) ∧
    (x : EReal) ≤ Filter.liminf (fun n => (f n a : EReal)) atTop}

example : minusCutoff (fun _ _ => 0) (-1) = ⊥ := by
  simp [minusCutoff]

example : plusCutoff (fun _ _ => 0) 1 = ⊤ := by
  simp [plusCutoff]

/-- PDF p.9: positivity of a bounded complex Hilbert-space operator, written
as reality and nonnegativity of every quadratic form. -/
def OperatorPositive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) : Prop :=
  ∀ v, (inner ℂ v (A v)).im = 0 ∧ 0 ≤ (inner ℂ v (A v)).re

/-- PDF pp.9–10: bounded regularization of the generalized-inverse sandwich.
The regularizer is `1/(k+1)>0`; its strong limit is the support extension of
`(sqrt(S+T))^{-1} S (sqrt(S+T))^{-1}`. Each factor here is bounded, even
when the generalized inverse itself is unbounded. -/
def regularizedSandwich {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S T : H →L[ℂ] H) (k : ℕ) : H →L[ℂ] H :=
  let R : H →L[ℂ] H :=
    cfc (fun t : ℝ => (Real.sqrt (t + ((k : ℝ) + 1)⁻¹))⁻¹) (S + T)
  R.comp (S.comp R)

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    OperatorPositive (0 : H →L[ℂ] H) := by
  intro v
  simp

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (k : ℕ) : regularizedSandwich 0 T k = 0 := by
  simp [regularizedSandwich]

/-- PDF pp.4,23: a normalized positive trace-class state, represented by
`rho = sum_k |v_k><v_k|` with `sum_k ||v_k||^2 = 1`. Zero vectors allow finite
rank. Every positive trace-class state has such a presentation, even on a
nonseparable Hilbert space, since its support is separable. The representation
is not required to be unique or orthogonal. -/
structure DensityPresentation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  vectors : ℕ → H
  mass : HasSum (fun k => ‖vectors k‖ ^ 2) 1

/-- PDF p.23: action of the represented density operator. Square-norm
summability guarantees absolute convergence of this vector series. -/
def densityAction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (rho : DensityPresentation H) (v : H) : H :=
  ∑' k : ℕ, (inner ℂ (rho.vectors k) v) • rho.vectors k

/-- PDF p.23: real trace `Tr[rho A]`. For every bounded A the series is
absolutely summable, bounded termwise by `||A|| ||v_k||^2`, so no divergent
real-tsum default is used. -/
def traceAgainst {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (rho : DensityPresentation H) (A : H →L[ℂ] H) : ℝ :=
  ∑' k : ℕ, (inner ℂ (rho.vectors k) (A (rho.vectors k))).re

/-- PDF p.23: an orthogonal projection is idempotent and self-adjoint.
No commutation of two such projections is implicit. -/
def IsOrthogonalProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : H →L[ℂ] H) : Prop :=
  (∀ v, P (P v) = P v) ∧
    ∀ u v, inner ℂ (P u) v = inner ℂ u (P v)

/-- Rank-one state presentation, a small case of the PDF p.4 state convention. -/
def purePresentation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) (hv : ‖v‖ = 1) : DensityPresentation H where
  vectors := fun k => if k = 0 then v else 0
  mass := by
    refine (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun ?_
    intro k
    by_cases hk : k = 0 <;> simp [hk, hv]

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (rho : DensityPresentation H) : traceAgainst rho (0 : H →L[ℂ] H) = 0 := by
  simp [traceAgainst]

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : H) (hv : ‖v‖ = 1) (A : H →L[ℂ] H) :
    traceAgainst (purePresentation v hv) A = (inner ℂ v (A v)).re := by
  unfold traceAgainst
  apply HasSum.tsum_eq
  refine (hasSum_ite_eq (0 : ℕ) ((inner ℂ v (A v)).re)).congr_fun ?_
  intro k
  by_cases hk : k = 0 <;> simp [purePresentation, hk]

example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IsOrthogonalProjection (0 : H →L[ℂ] H) := by
  constructor <;> intros <;> simp

/-- PDF p.6: a finitely supported real array is a probability law precisely
when all weights are nonnegative and sum to one. -/
def IsFiniteLaw {X : Type*} (p : X →₀ ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ p.sum (fun _ w => w) = 1

/-- PDF p.25: the expected cost, always a finite sum. Costs may be negative. -/
def meanCost {X : Type*} (c : X → ℝ) (p : X →₀ ℝ) : ℝ :=
  p.sum (fun x w => w * c x)

/-- PDF pp.25,28: feasible finite-support laws, as a subset of the real
vector space of finitely supported arrays. -/
def feasibleLaws {X : Type*} (c : X → ℝ) (gamma : ℝ) : Set (X →₀ ℝ) :=
  {p | IsFiniteLaw p ∧ meanCost c p ≤ gamma}

example {X : Type*} (c : X → ℝ) : meanCost c (0 : X →₀ ℝ) = 0 := by
  simp [meanCost]

example {X : Type*} : ¬ IsFiniteLaw (0 : X →₀ ℝ) := by
  simp [IsFiniteLaw]

example {X : Type*} (c : X → ℝ) (gamma : ℝ) (x : X) :
    Finsupp.single x (1 : ℝ) ∈ feasibleLaws c gamma ↔ c x ≤ gamma := by
  classical
  constructor
  · intro h
    simpa [meanCost] using h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro y
      by_cases hxy : x = y <;> simp [Finsupp.single_apply, hxy]
    · simp
    · simpa [meanCost] using h

end QAlgorithms.Papers.Independent.Frontier18.P03


