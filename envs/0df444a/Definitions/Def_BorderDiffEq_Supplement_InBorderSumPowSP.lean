-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_InBorderSumPowSP
-- name    : BorderDiffEq_Supplement_InBorderSumPowSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:51:15.622855+00:00
-- url     : https://prove2.me/theorems/76ed5499-1612-4053-a17d-e6c60ed0b0e7
-- title:
--   The border of $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$
-- statement:
--   $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$ is the set of sums $\sum_{i=1}^kP_i^{e_i}$ of powers of polynomials of degree at most $\delta$ given as sums of monomials, with
--   $$
--   \sum_{i=1}^k\bigl(\mathrm{size}(P_i)+e_i\bigr)\le s ,
--   $$
--   so that the exponents contribute to the size. A polynomial $f\in F[x_1,\dots,x_n]$ is in its **border** if at most $k$ polynomials $P_i\in F((\epsilon))[x]$ of total degree at most $\delta$ and exponents $e_i\ge1$ with $\sum_i(\mathrm{size}(P_i)+e_i)\le s$ satisfy $\sum_iP_i^{e_i}=f+\epsilon S$ with $S\in F[[\epsilon]][x]$.
--
--   This is the class of Theorems 2.4 and 2.7.
--
--   **Formalization Note** $\mathrm{size}$ is `spSize`. "$k$ summands" is read as "at most $k$", which can only enlarge the class. The border relation is the published `BorderDiffEq.IsEpsApprox`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.2, p.8, item 1; §4, p.23

import Mathlib
import Definitions.Def_BorderDiffEq_IsEpsApprox
import Definitions.Def_BorderDiffEq_Supplement_spSize

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **The border of sums of powers of low-degree polynomials, `f ∈ cl(Σ^{[k]} ∧ ΣΠ^{[δ]}(s))`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), §2.2, p.8, item 1: "We write
`Σ^{[k]} ∧ ΣΠ^{[δ]}(s)` for the set of sums `∑_{i=1}^k Pᵢ^{eᵢ}` with `deg Pᵢ ≤ δ` and
`∑_{i=1}^k (size(Pᵢ) + eᵢ) ≤ s`; thus the exponents contribute to the size"; border as in §4,
p.23): `f ∈ F[x₁, …, xₙ]` is in the border if there are at most `k` polynomials
`Pᵢ ∈ F((ε))[x]` of total degree at most `δ`, given as sums of monomials, and exponents `eᵢ ≥ 1`
with `∑ᵢ (size(Pᵢ) + eᵢ) ≤ s` and `∑ᵢ Pᵢ^{eᵢ} = f + ε·S`, `S ∈ F[[ε]][x]`.

**Formalization Note.** `size(Pᵢ)` is `spSize` (one per monomial plus one per variable it uses;
the paper leaves it undefined). "`k` summands" is read as "at most `k`", which can only enlarge
the class. Constants in `F((ε))` and `IsEpsApprox` are the base mission's border convention. -/
def InBorderSumPowSP (F : Type) [Field F] (n k δ s : ℕ) (f : MvPolynomial (Fin n) F) : Prop :=
  ∃ (t : ℕ) (P : Fin t → MvPolynomial (Fin n) (LaurentSeries F)) (e : Fin t → ℕ),
    t ≤ k ∧ (∀ i, 1 ≤ e i) ∧ (∀ i, (P i).totalDegree ≤ δ) ∧
    ∑ i, (spSize (P i) + e i) ≤ s ∧ IsEpsApprox (∑ i, P i ^ e i) f

end BorderDiffEq.Supplement


