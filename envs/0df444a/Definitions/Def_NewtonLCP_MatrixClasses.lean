-- Prove2me | Definitions.Def_NewtonLCP_MatrixClasses
-- name    : NewtonLCP_MatrixClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:56.839726+00:00
-- url     : https://prove2.me/theorems/c8363d34-08fd-4921-8646-34449a7a62bf
-- title:
--   Column sufficient, row sufficient and $P_0$ matrices
-- statement:
--   Let $M\in\mathbb R^{n\times n}$, and write $x(Mx)$ for the entrywise product of $x$ and $Mx$.
--
--   1. $M$ is **column sufficient** if for all $x\in\mathbb R^n$, $x(Mx)\le 0_n$ implies $x(Mx)=0_n$.
--   2. $M$ is **row sufficient** if $M^\top$ is column sufficient.
--   3. $M\in P_0$ if every principal minor $\det M_{SS}$, $S\subseteq[n]$, is nonnegative.
--
--   Väliaho's theorem identifies the sufficient (column and row sufficient) matrices with $\mathcal P_\star$; $P_0$ is the class in which $I_n+DMD$ is always nonsingular (Corollary 2.5).
--
--   **Formalization Note** The principal minor of the empty index set is $1$.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), §1, p.2; §2.2, p.7

import Mathlib

open Matrix

namespace NewtonLCP

/-!
# Column sufficient, row sufficient and P₀ matrices

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), §1, p.2 (sufficiency and `P₀`); restated §2.2,
p.7.

**Formalization Note.** The product `x(Mx)` is entrywise. A principal minor is the determinant of
the principal submatrix on an index subset `S`; the empty minor is `1`, so the quantifier over all
`S : Finset ι` is the paper's "all principal minors".
-/

variable {ι : Type*} [Fintype ι]

/-- `M` is column sufficient: for all `x`, `x(Mx) ≤ 0ₙ` implies `x(Mx) = 0ₙ` (p.2). -/
def IsColSufficient (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, (∀ i, x i * (M *ᵥ x) i ≤ 0) → ∀ i, x i * (M *ᵥ x) i = 0

/-- `M` is row sufficient: `Mᵀ` is column sufficient (p.2). -/
def IsRowSufficient (M : Matrix ι ι ℝ) : Prop :=
  IsColSufficient Mᵀ

/-- `M ∈ P₀`: every principal minor of `M` is nonnegative (p.2). -/
def IsP0 [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ S : Finset ι, 0 ≤ (M.submatrix (fun i : S => (i : ι)) (fun i : S => (i : ι))).det

end NewtonLCP


