-- Prove2me | Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp
-- name    : Disjunctive_GeneralDisjunctions_Cglp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:58:44.463052+00:00
-- url     : https://prove2.me/theorems/fb30106c-2b89-4e33-ad45-b2ea59322b80
-- title:
--   The CGLP (11.6), Theorem 11.9's coefficients, and domination
-- statement:
--   This definition sets up the cut-generating-LP apparatus Theorems 11.9 and 11.11 need.
--
--   The **CGLP (11.6)**, `IsCGLP116Feasible`, is the cut-generating LP for the disjunction
--   $D(P,S)$: multipliers $(u^t)_{t\in T}$, $(u^t_0)_{t\in T}$ reconstruct $\alpha:=u^t\tilde A +
--   u^t_0 d^t$ and $\beta:=u^t\tilde b + u^t_0 d^t_0$ for every $t$, normalized by
--   $\sum_t(u^te+u^t_0)=1$. `piCoef`/`IntersectionCutFromS` build Theorem 11.9's intersection-cut
--   coefficients $\pi_j:=\max_t \pi^t_j$ and the resulting cut, expressed via the surplus values
--   at a chosen cobasis $\iota$. `SatisfiesThm119Condition` packages Theorem 11.9's sufficient
--   condition (a common nonsingular cobasis supporting every $u^t$).
--   `IsEquivalentToIntersectionCutFromS` says a halfspace coincides with some such cut for some
--   cobasis. `Dominates` and `IsCGLP116UniqueMin` give Theorem 11.11's domination and
--   unique-optimality notions.
--
--   **Formalization Note.** `Ahat`/`Bhat`/`Abar`/`Abar0`/`SurplusM` restate
--   `08-cut-correspondence`'s/`09-simplex-tableau`'s/`10-split-closure`'s tableau apparatus
--   unchanged, generalized where needed from a fixed row `k` to a general row `i`, matching how
--   Chapter 11 itself reuses Chapter 9's tableau coefficients for a general row (not just the
--   disjunction row `k`).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 153, 159-162, Section 11.4-11.5

import Mathlib

namespace Disjunctive.GeneralDisjunctions

/-- `Â`, the `n×n` submatrix of `Ã` whose rows are `ι 0, …, ι (n-1)` (restated from
`08-cut-correspondence`/`09-simplex-tableau`/`10-split-closure`). -/
def Ahat {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Atil (ι i) j

/-- `b̂`, the subvector of `b̃` corresponding to `Â` (restated locally). -/
def Bhat {n : ℕ} {M : Type*} (btil : M → ℝ) (ι : Fin n → M) : Fin n → ℝ :=
  fun i => btil (ι i)

/-- `ā_i0 := e_i Â⁻¹ b̂`, the tableau's constant column at row `i` (restated locally, generalized
from a single fixed row `k` to a general row `i`). -/
noncomputable def Abar0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (i : Fin n) : ℝ :=
  (Ahat Atil ι)⁻¹.mulVec (Bhat btil ι) i

/-- `ā_ij := -(Â⁻¹)_{ij}` (restated locally, generalized to a general row `i`). -/
noncomputable def Abar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (i j : Fin n) : ℝ :=
  -((Ahat Atil ι)⁻¹) i j

/-- The surplus (slack) value at an arbitrary row `i : M` (restated from `09-simplex-tableau`'s
`SurplusM`). -/
def SurplusM {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (i : M)
    (x : Fin n → ℝ) : ℝ :=
  dotProduct (Atil i) x - btil i

/-- The CGLP constraint set (11.6) (Balas §11.4, p. 153) corresponding to the disjunction
`D(P,S) = {x : ∨_{t∈T} (Ãx≥b̃ ∧ dᵗx≥dᵗ₀)}`: `α - uᵗÃ - uᵗ₀dᵗ = 0`, `-β + uᵗb̃ + uᵗ₀dᵗ₀ = 0` for
`t ∈ T`, `∑ₜ(uᵗe + uᵗ₀) = 1`, `uᵗ, uᵗ₀ ≥ 0`. -/
def IsCGLP116Feasible {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (u : T → M → ℝ) (u0 : T → ℝ) (β : ℝ) : Prop :=
  (∀ t, α = Matrix.vecMul (u t) Atil + u0 t • d t) ∧
    (∀ t, β = dotProduct (u t) btil + u0 t * d0 t) ∧
    (∑ t, ((∑ i, u t i) + u0 t)) = 1 ∧
    (∀ t i, 0 ≤ u t i) ∧ (∀ t, 0 ≤ u0 t)

/-- `π^t_j`, Theorem 11.9's per-disjunct intersection-cut coefficient (Balas §11.5, p. 160, in
the theorem's own proof): `d^t(-ā_j) / (d^t_0 - d^t·ā_0)`. -/
noncomputable def piT {n : ℕ} {M T : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (d : T → Fin n → ℝ) (d0 : T → ℝ) (t : T) (j : Fin n) : ℝ :=
  dotProduct (d t) (fun i => -(Abar Atil ι i j)) /
    (d0 t - dotProduct (d t) (fun i => Abar0 Atil btil ι i))

/-- `π_j := max_{t∈T} π^t_j`, the intersection-cut coefficient of Theorem 11.9 (Balas §11.5,
p. 159-160). -/
noncomputable def piCoef {n : ℕ} {M T : Type*} [Fintype T] [Nonempty T] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (j : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun t => piT Atil btil ι d d0 t j)

/-- The intersection cut `πx_J ≥ 1` from `S := {x : dᵗx ≤ dᵗ₀, t∈T}` and the LP simplex tableau
with nonbasic (row) set `ι` (Balas §11.5, p. 155-159), expressed via the surplus values at the
cobasis rows (matching `09-simplex-tableau`'s identification of nonbasic structural variables
with their corresponding surplus values). -/
noncomputable def IntersectionCutFromS {n : ℕ} {M T : Type*} [Fintype T] [Nonempty T]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M)
    (d : T → Fin n → ℝ) (d0 : T → ℝ) : Set (Fin n → ℝ) :=
  {x | 1 ≤ ∑ j, piCoef Atil btil ι d d0 j * SurplusM Atil btil (ι j) x}

/-- `w` (a CGLP-(11.6) solution's multipliers `u`) satisfies the sufficient condition of Theorem
11.9 (Balas §11.5, p. 162): there is an injective, nonsingular-tableau cobasis `ι` on whose image
every `uᵗ` is entirely supported. -/
def SatisfiesThm119Condition {n : ℕ} {M T : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (u : T → M → ℝ) : Prop :=
  ∃ ι : Fin n → M, Function.Injective ι ∧ IsUnit (Ahat Atil ι).det ∧
    ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0

/-- `(α,β)` is equivalent to some standard intersection cut from `S` (Balas §11.5, p. 161-162,
"there exists no intersection cut from `S` equivalent to..."): the halfspace `{β≤αx}` coincides,
for some cobasis `ι`, with `IntersectionCutFromS` at `ι`. -/
noncomputable def IsEquivalentToIntersectionCutFromS {n : ℕ} {M T : Type*} [Fintype T]
    [Nonempty T] [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (d : T → Fin n → ℝ) (d0 : T → ℝ) (α : Fin n → ℝ) (β : ℝ) : Prop :=
  ∃ ι : Fin n → M, {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0

/-- `γ¹x≥γ¹₀` dominates `γ²x≥γ²₀` on `P` (Balas §11.5, p. 161): every `x∈P` satisfying the first
also satisfies the second. -/
def Dominates {n : ℕ} (P : Set (Fin n → ℝ)) (gamma1 : Fin n → ℝ) (gamma10 : ℝ)
    (gamma2 : Fin n → ℝ) (gamma20 : ℝ) : Prop :=
  ∀ x ∈ P, gamma10 ≤ dotProduct gamma1 x → gamma20 ≤ dotProduct gamma2 x

/-- `(α,β)` uniquely minimizes `αx̄_N - β` over (11.6) (Balas §11.5, p. 161-162): feasible,
optimal, and the unique `(α,β)`-pair achieving the optimum. -/
def IsCGLP116UniqueMin {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (xbarN : Fin n → ℝ) (α : Fin n → ℝ) (β : ℝ) : Prop :=
  (∃ u u0, IsCGLP116Feasible Atil btil d d0 α u u0 β) ∧
    (∀ α' β' u' u0', IsCGLP116Feasible Atil btil d d0 α' u' u0' β' →
      dotProduct α xbarN - β ≤ dotProduct α' xbarN - β') ∧
    (∀ α' β' u' u0', IsCGLP116Feasible Atil btil d d0 α' u' u0' β' →
      dotProduct α' xbarN - β' = dotProduct α xbarN - β → α' = α ∧ β' = β)

end Disjunctive.GeneralDisjunctions


