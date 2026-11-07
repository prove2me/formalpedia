-- Prove2me | Definitions.Def_RandOrderCSP_fourierCoeff
-- name    : RandOrderCSP_fourierCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:21.811124+00:00
-- url     : https://prove2.me/theorems/3a943a6f-004f-4e54-8445-bb2a0a7c2405
-- title:
--   Fourier analysis on $\mathbb Z_q^U$
-- statement:
--   For $A,X\in\mathbb Z_q^U$ put $\chi_A(X)=\exp(2\pi i\langle A,X\rangle/q)$, and for $f:\mathbb Z_q^U\to\mathbb C$
--
--   $$\hat f(A)=\mathbb E_{X}\,f(X)\chi_A(X).$$
--
--   The density of a distribution $D$ on a finite set $S$ is $\mu_D=|S|\,D$. $\mathrm{supp}(A)$ is the set of nonzero coordinates and $\mathrm{wt}(A)=|\mathrm{supp}(A)|$. $\mathcal F_U(s)$ is the class of $g$ with $\|g\|_1\le1$ and $\|g\|_\infty\le q^s$, under uniform-average norms.
--
--   The sign and normalization match the paper, since the constants of the level inequality depend on them.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3, pp.10–11; §5.1, p.22

import Mathlib

namespace RandOrderCSP

variable {U : Type} {q : ℕ}

/-- `χ_A(X) := exp(2πi⟨A, X⟩/q)` (§5.1, p.22). `ZMod.stdAddChar a = exp(2πi a/q)`. -/
noncomputable def chi [Fintype U] [NeZero q] (A X : U → ZMod q) : ℂ :=
  ZMod.stdAddChar (∑ i, A i * X i)

/-- **Fourier coefficient on `ℤ_q^U`** (§5.1, p.22).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.22: "For A, X ∈ Z_q^d, write
χ_A(X) := exp(2πi⟨A, X⟩/q) and, for f : Z_q^d → ℂ, f̂(A) := E_{X∈Z_q^d} f(X)χ_A(X)."

**Formalization Note.** The expectation is the uniform average and the character carries a plus sign,
with no conjugate, as printed. The index set `[d]` is any finite type `U`. -/
noncomputable def fourierCoeff [Fintype U] [DecidableEq U] [NeZero q]
    (f : (U → ZMod q) → ℂ) (A : U → ZMod q) : ℂ :=
  (1 / (Fintype.card (U → ZMod q) : ℂ)) * ∑ X, f X * chi A X

/-- The density `μ_D(X) = |S| D(X)` of a distribution `D` on a finite set `S` (§3, p.10). -/
noncomputable def density {S : Type} [Fintype S] (D : S → ℝ) (X : S) : ℝ :=
  (Fintype.card S : ℝ) * D X

/-- `supp(A)`: the set of nonzero coordinates of `A` (§5.1, p.22). -/
def vsupp [Fintype U] (A : U → ZMod q) : Finset U := by
  classical
  exact Finset.univ.filter fun i => A i ≠ 0

/-- `wt(A) := |supp(A)|` (§5.1, p.22). -/
def wt [Fintype U] (A : U → ZMod q) : ℕ := (vsupp A).card

/-- `f ∈ ℱ_U(s)` (3.3), p.11: `‖f‖₁ ≤ 1` and `‖f‖_∞ ≤ q^s`, with the uniform-average `L¹` norm. -/
def InFamilyF [Fintype U] [DecidableEq U] [NeZero q] (s : ℝ) (f : (U → ZMod q) → ℂ) : Prop :=
  (1 / (Fintype.card (U → ZMod q) : ℝ)) * ∑ X, ‖f X‖ ≤ 1 ∧ ∀ X, ‖f X‖ ≤ (q : ℝ) ^ s

end RandOrderCSP


