-- Prove2me | Definitions.Def_Disjunctive_LiftProject_Basic
-- name    : Disjunctive_LiftProject_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:34:56.572501+00:00
-- url     : https://prove2.me/theorems/3ded9a0b-5f50-4b62-99a8-3966aca02329
-- title:
--   The cut-generating LP, its restriction, and the mixed 0-1 disjunctive set
-- statement:
--   This definition fixes the vocabulary of Chapter 6: the split disjunction on a 0-1 variable,
--   the cut-generating LP `(CGLP)` and its row-restricted version `(CGLP)^R`, and the mixed 0-1
--   program's disjunctive feasible set.
--
--   For a polyhedron $P$ and coordinate $i$, $\mathrm{SplitConvexify}(P,i) := \mathrm{conv}(P \cap
--   \{x : x_i \in \{0,1\}\})$, one step of sequential convexification. The **cut-generating LP**
--   system (Balas' `(CGLP)`) asks for $(\alpha,\beta)$ together with multipliers $u,v \ge 0$ and
--   scalars $u_0,v_0$ satisfying
--
--   $$
--   \alpha - u\tilde A + u_0 e_j = 0, \quad \alpha - v\tilde A - v_0 e_j = 0, \quad \beta - u
--   \tilde b = 0, \quad \beta - v\tilde b - v_0 = 0, \quad u,v \ge 0
--   $$
--
--   for the disjunction on coordinate $j$; `(CGLP)^R` is the same system with the row set restricted
--   to $M_R$ and the column (variable) set restricted to $R$. $\alpha^1_i := u\tilde A_i$ (`Alpha1`)
--   and $\alpha^2_i := v\tilde A_i$ (`Alpha2`) are the row-restricted dot products used by Corollary
--   6.3; $\alpha^1_i$/$\alpha^2_i$ as in eq. (6.4) (`Alpha1_64`/`Alpha2_64`) instead add/subtract
--   $u_0$/$v_0$ at the disjunction coordinate $j$ — a different pair of formulas, used by Theorem 6.4.
--   The **mixed 0-1 program's feasible set** imposes $x_k \in \{0,1\}$ for every $k$ in the 0-1
--   index set $N'$.
--
--   **Formalization Note.** `Alpha1`/`Alpha2` and `Alpha1_64`/`Alpha2_64` are kept as separate
--   definitions, per `BRIEF.md`'s explicit warning that Corollary 6.3's and Theorem 6.4's `α¹,α²` are
--   different expressions despite the shared notation.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 79-86, Section 6

import Mathlib

namespace Disjunctive.LiftProject

/-- The polyhedron `{x : A x ≥ b}` (restated locally, as in earlier chunks of the series). -/
def Poly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, b i ≤ (A.mulVec x) i}

/-- `{x : x_i ∈ {0,1}}`, the split disjunction on coordinate `i` (Balas §6, eq. (6.1)). -/
def ZeroOneSet {n : ℕ} (i : Fin n) : Set (Fin n → ℝ) := {x | x i = 0 ∨ x i = 1}

/-- The sequential-convexification step `conv(S ∩ {x_i ∈ {0,1}})` (Balas §6, p. 79). -/
def SplitConvexify {n : ℕ} (S : Set (Fin n → ℝ)) (i : Fin n) : Set (Fin n → ℝ) :=
  convexHull ℝ (S ∩ ZeroOneSet i)

/-- The cut-generating LP's feasibility system (6.3): `(α,β)` together with multipliers
`u,v ≥ 0` and scalars `u₀,v₀` satisfying `α - uÃ + u₀e_j = 0`, `α - vÃ - v₀e_j = 0`,
`β - u b̃ = 0`, `β - v b̃ - v₀ = 0` (Balas §6, p. 80, for the disjunction on coordinate `j`). -/
def IsCGLPFeasible {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (j : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) : Prop :=
  (∀ i, α i - (∑ ρ, u ρ * Atil ρ i) + (if i = j then u0 else 0) = 0) ∧
    (∀ i, α i - (∑ ρ, v ρ * Atil ρ i) - (if i = j then v0 else 0) = 0) ∧
    β - ∑ ρ, u ρ * btil ρ = 0 ∧ β - (∑ ρ, v ρ * btil ρ) - v0 = 0 ∧ 0 ≤ u ∧ 0 ≤ v

/-- The reduced cut-generating LP's feasibility system `(CGLP)^R` (Balas §6.4, p. 84): the same
system, restricted to the row set `MR` and the column (variable) set `R`. -/
def IsCGLPRFeasible {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (MR : Finset M) (R : Finset (Fin n)) (j : Fin n) (αR : Fin n → ℝ) (uR : M → ℝ) (u0R : ℝ)
    (vR : M → ℝ) (v0R : ℝ) (β : ℝ) : Prop :=
  (∀ i ∈ R, αR i - (∑ ρ ∈ MR, uR ρ * Atil ρ i) + (if i = j then u0R else 0) = 0) ∧
    (∀ i ∈ R, αR i - (∑ ρ ∈ MR, vR ρ * Atil ρ i) - (if i = j then v0R else 0) = 0) ∧
    β - ∑ ρ ∈ MR, uR ρ * btil ρ = 0 ∧ β - (∑ ρ ∈ MR, vR ρ * btil ρ) - v0R = 0 ∧
    0 ≤ uR ∧ 0 ≤ vR

/-- `α¹_i := u^R Ã^R_i`, the restricted dot product of a row-restricted multiplier against
column `i` of `Ã` over the reduced row set (Balas §6.4-6.5, p. 84-86, eq. (6.4) and Corollary
6.3). -/
def Alpha1 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (uR : M → ℝ)
    (MR : Finset M) (i : Fin n) : ℝ :=
  ∑ ρ ∈ MR, uR ρ * Atil ρ i

/-- `α²_i := v^R Ã^R_i` (Balas §6.4-6.5, p. 84-86, eq. (6.4) and Corollary 6.3). -/
def Alpha2 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (vR : M → ℝ)
    (MR : Finset M) (i : Fin n) : ℝ :=
  ∑ ρ ∈ MR, vR ρ * Atil ρ i

/-- The row space of `(CGLP)` extended from the reduced problem's row space `M`: one fresh
unit-coefficient row per variable `i`, matching the role of the deleted bound-constraint rows
(each of which has a single nonzero, unit, coefficient) that the reduced problem discarded
(Balas §6.4, p. 84, the rows indexed `m+i`, `m+n+i`; see `MODERATION_NOTES.md`). `M ⊕ Fin n` is
used directly (a fresh row per variable), rather than a named abbreviation, to keep Mathlib's
`Fintype`/`DecidableEq` instances for sums resolving without a custom unfolding step. -/
def AtilExt {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) :
    Matrix (M ⊕ Fin n) (Fin n) ℝ :=
  Sum.elim Atil (fun k i => if k = i then (1 : ℝ) else 0)

/-- The extended right-hand side: `b̃` on `M`-rows, `0` on the fresh rows (so the fresh rows
never affect the `β`-equations, matching Corollary 6.3's unchanged `β`). -/
def BtilExt {n : ℕ} {M : Type*} [Fintype M] (btil : M → ℝ) : M ⊕ Fin n → ℝ :=
  Sum.elim btil (fun _ => 0)

/-- `α¹_i` as in eq. (6.4) (Balas §6.4, p. 85): `u Ã_i`, minus `u₀` at the disjunction coordinate
`j`. Distinct from `Alpha1` (Corollary 6.3's row-restricted version). -/
def Alpha1_64 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (u : M → ℝ) (u0 : ℝ)
    (j i : Fin n) : ℝ :=
  (∑ ρ, u ρ * Atil ρ i) - (if i = j then u0 else 0)

/-- `α²_i` as in eq. (6.4) (Balas §6.4, p. 85): `v Ã_i`, plus `v₀` at the disjunction coordinate
`j`. Distinct from `Alpha2` (Corollary 6.3's row-restricted version). The signs at `i = j` are
those of (6.3) (`α - uÃ + u₀e_j = 0`, `α - vÃ - v₀e_j = 0`), which `IsCGLPFeasible` also encodes;
the display (6.4) prints them the other way round, contradicting (6.3) on the same pages. -/
def Alpha2_64 {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (v : M → ℝ) (v0 : ℝ)
    (j i : Fin n) : ℝ :=
  (∑ ρ, v ρ * Atil ρ i) + (if i = j then v0 else 0)

/-- The feasible set of the mixed 0-1 program `(MIP)` (Balas §6, eq. (6.1)): the disjunctive set
imposing `x_k ∈ {0,1}` for every `k` in the 0-1 index set `N'`. -/
def MIPDisjunctiveSet {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ) (btil : Fin m → ℝ)
    (Nprime : Finset (Fin n)) : Set (Fin n → ℝ) :=
  Poly Atil btil ∩ ⋂ k ∈ Nprime, ZeroOneSet k

end Disjunctive.LiftProject


