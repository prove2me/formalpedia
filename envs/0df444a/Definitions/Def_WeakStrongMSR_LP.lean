-- Prove2me | Definitions.Def_WeakStrongMSR_LP
-- name    : WeakStrongMSR_LP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:41.49007+00:00
-- url     : https://prove2.me/theorems/d313ef8f-d67d-4b8a-bb36-8f5a821cafd9
-- title:
--   Candidates and the packing LP (1)
-- statement:
--   A **candidate** is a triple $(A(s,R),s,R)$ with a strongly queried centre $s$, a radius $R$ and a set $A(s,R)$ of unqueried points. The record also keeps the witness set $W_s$ from which $A$ was computed. For a strong set $S$, candidate family $\mathcal C$, guess $\lambda$ and witness count $h$, the **packing LP (1)** is
--   $$\max\sum_{x\in X\setminus S}y_x\quad\text{s.t.}\quad y(A(s,R))\le R+\lambda\ \ ((A(s,R),s,R)\in\mathcal C),\qquad 0\le y_x\le \lambda/h\ \ (x\in X\setminus S).$$
--   $\mathrm{OPT}_{LP}$ denotes its optimum. An **LP routine** returns a vector for every instance. It **selects optimal solutions** if, on every instance with $\lambda>0$ and nonnegative radii, its vector is feasible and attains $\mathrm{OPT}_{LP}$.
--
--   **Formalization Note** The LP routine is a parameter of the algorithm ("solve (1) to obtain $y$"). The run-level milestones hold for every routine that selects optimal solutions. On those instances $y=0$ is feasible and the feasible set is bounded, so an optimum exists.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3.1, p.7 (PDF 8), LP (1)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# Candidates and the packing LP (1)

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), §3.1, p.7: "A candidate is a triple (A(s, R), s, R), with
s ∈ S and A(s, R) ⊆ X \ S", and LP (1):
`max ∑_{x ∈ X∖S} y_x` s.t. `y(A(s, R)) ≤ R + λ` for every candidate and `0 ≤ y_x ≤ λ/h` for
`x ∈ X ∖ S`.

**Formalization Note.**
* A candidate also records the witness set `W` of its centre (from which `A` was computed); it is
  bookkeeping used to name the set `E_s` of points corrupt for `W_s`, and is not read by the LP.
* The LP variables are the points of `X ∖ S`: a feasible `y` vanishes on `S`.
* `lpOpt` is the supremum of the objective over the feasible set; when every candidate has
  `R ≥ 0` and `λ > 0` the feasible set contains `0` and is bounded, so this is the maximum.
* "Solve (1) to obtain y" (R10): an `LPSelector` returns a vector for each `(S, C, λ, h)`;
  `SelectsOptimal` says it returns an optimal solution on every instance with `λ > 0` and
  nonnegative radii (every instance the algorithm produces). -/

/-- A candidate `(A(s, R), s, R)` together with the witness set `W` of its centre. -/
structure Cand (n : ℕ) where
  /-- The point set `A(s, R)`. -/
  A : Finset (Fin n)
  /-- The centre `s`. -/
  s : Fin n
  /-- The radius `R`. -/
  R : ℝ
  /-- The witness set `W_s` used to compute `A`. -/
  W : Finset (Fin n)

/-- Feasibility for LP (1) with strong set `S`, candidates `Cs`, guess `λ` and cap `λ/h`. -/
def LPFeasible {n : ℕ} (S : Finset (Fin n)) (Cs : List (Cand n)) (lam : ℝ) (h : ℕ)
    (y : Fin n → ℝ) : Prop :=
  (∀ x ∈ S, y x = 0) ∧ (∀ x, x ∉ S → 0 ≤ y x ∧ y x ≤ lam / h) ∧
    ∀ c ∈ Cs, ∑ x ∈ c.A, y x ≤ c.R + lam

/-- The objective `∑_x y_x` of LP (1). -/
noncomputable def lpValue {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ x, y x

/-- `OPT_LP`: the optimum of LP (1). -/
noncomputable def lpOpt {n : ℕ} (S : Finset (Fin n)) (Cs : List (Cand n)) (lam : ℝ) (h : ℕ) : ℝ :=
  sSup (lpValue '' {y | LPFeasible S Cs lam h y})

/-- An LP routine: a vector for every strong set, candidate family, guess and cap parameter. -/
abbrev LPSelector (n : ℕ) : Type := Finset (Fin n) → List (Cand n) → ℝ → ℕ → (Fin n → ℝ)

/-- The routine returns an optimal solution of LP (1) whenever `λ > 0` and all radii are
nonnegative. -/
def SelectsOptimal {n : ℕ} (sel : LPSelector n) : Prop :=
  ∀ (S : Finset (Fin n)) (Cs : List (Cand n)) (lam : ℝ) (h : ℕ), 0 < lam →
    (∀ c ∈ Cs, 0 ≤ c.R) →
    LPFeasible S Cs lam h (sel S Cs lam h) ∧ lpValue (sel S Cs lam h) = lpOpt S Cs lam h

end WeakStrongMSR


