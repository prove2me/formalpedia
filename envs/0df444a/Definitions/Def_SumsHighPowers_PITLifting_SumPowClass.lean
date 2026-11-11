-- Prove2me | Definitions.Def_SumsHighPowers_PITLifting_SumPowClass
-- name    : SumsHighPowers_PITLifting_SumPowClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:09:47.8622+00:00
-- url     : https://prove2.me/theorems/9b853322-e850-434d-91e6-81d20b0a5ef2
-- title:
--   The degree-bounded class $C_\Delta$ and sums of $r$ $d$-th powers $\Sigma^r\wedge^d C$ (pp. 4, 12)
-- statement:
--   Let $F$ be a field and let $C\subseteq F[x_1,\dots,x_n]$ be a class of polynomials (any set).
--
--   **Degree-bounded class (§1.5, p. 12).** For $\Delta\in\mathbb N$, $C_\Delta$ is the set of polynomials of $C$ of total degree at most $\Delta$:
--   $$C_\Delta=\{f\in C:\ \deg f\le \Delta\}.$$
--
--   **Sums of powers (§1, p. 4).** For $r,d\in\mathbb N$,
--   $$\Sigma^r\wedge^d C=\Big\{\sum_{i=1}^r \alpha_i f_i^{\,d}\ :\ \alpha_i\in F,\ f_i\in C\Big\}.$$
--   The scalars $\alpha_i$ may be $0$, so sums of fewer than $r$ powers are included, and $f^0=1$. The class $\Sigma^2 C$ used for hitting sets is the case $r=2$, $d=1$: $\{\alpha_1g_1+\alpha_2g_2: g_i\in C\}$; it contains every scalar multiple of an element of $C$.
--
--   **Formalization Note.** `degBounded C Δ` uses `MvPolynomial.totalDegree`; `sumPowClass r d C` indexes the summands by `Fin r` and writes $\alpha_i f_i^d$ as `α i • f i ^ d`. Variables are `Fin n`.
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 4, display defining Σ^r ∧^d C (Eq. (1)); p. 12, §1.5 (C_Δ)

import Mathlib

namespace SumsHighPowers.PITLifting

/-- **The degree-bounded subclass `C_Δ`** (Kaplan–Shpilka–Tal, *PIT and Reconstruction for Sums of
High Powers*, §1.5, p. 12): the polynomials of the class `C ⊆ F[x₁, …, xₙ]` of (total) degree at
most `Δ`.

**Formalization Note.** A class is a `Set` of polynomials in the variables `Fin n`; degree is
`MvPolynomial.totalDegree` (total degree, not individual degree). -/
def degBounded {F : Type*} [Field F] {n : ℕ} (C : Set (MvPolynomial (Fin n) F)) (Δ : ℕ) :
    Set (MvPolynomial (Fin n) F) :=
  {f | f ∈ C ∧ f.totalDegree ≤ Δ}

/-- **Sums of `r` `d`-th powers from a class, `Σ^r ∧^d C`** (§1, p. 4):
`Σ^r ∧^d C := { ∑_{i=1}^r αᵢ fᵢ^d : fᵢ ∈ C }`, with scalars `αᵢ ∈ F` (Eq. (1)).

`Σ²C` (used for hitting sets) is the case `r = 2`, `d = 1`: `{α₁ g₁ + α₂ g₂ : gᵢ ∈ C}`.

**Formalization Note.** The summands are indexed by `Fin r`; `αᵢ = 0` is allowed, so sums of fewer
than `r` powers are included; `f ^ 0 = 1`. -/
def sumPowClass {F : Type*} [Field F] {n : ℕ} (r d : ℕ) (C : Set (MvPolynomial (Fin n) F)) :
    Set (MvPolynomial (Fin n) F) :=
  {P | ∃ (α : Fin r → F) (f : Fin r → MvPolynomial (Fin n) F),
      (∀ i, f i ∈ C) ∧ P = ∑ i, α i • f i ^ d}

end SumsHighPowers.PITLifting


