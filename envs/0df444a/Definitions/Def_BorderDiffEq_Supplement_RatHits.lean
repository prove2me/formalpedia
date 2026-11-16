-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_RatHits
-- name    : BorderDiffEq_Supplement_RatHits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:16.625196+00:00
-- url     : https://prove2.me/theorems/83dd1dd1-8637-4625-8d74-abfbf252e2c0
-- title:
--   A list of rational points hits a class of polynomials
-- statement:
--   Let $F$ be a field of characteristic zero, so that $\mathbb Q\subseteq F$. A list $H$ of points of $\mathbb Q^n$ is a **hitting set** for a class $\mathcal C\subseteq F[x_1,\dots,x_n]$ if every nonzero $f\in\mathcal C$ has a point $h\in H$ with $f(h)\ne0$.
--
--   Taking the points in $\mathbb Q^n$ lets one point set serve every field of characteristic zero, as the explicit constructions of the paper do.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorems 2.2 and 2.6, pp.7 and 9; Fact 7.4, p.54

import Mathlib

namespace BorderDiffEq.Supplement

/-- **A list of rational points is a hitting set for a class of polynomials over `F`**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Theorems 2.2 and 2.6, pp.7 and 9;
Fact 7.4, p.54; standard notion): `H ⊆ ℚⁿ ⊆ Fⁿ` hits the class `C ⊆ F[x₁, …, xₙ]` if every nonzero
`f ∈ C` is nonzero at some point of `H`.

**Formalization Note.** `F` is a field of characteristic zero in every use, so `ℚ ⊆ F` and the
points are mapped into `Fⁿ` by `Rat.cast`. Taking the points in `ℚⁿ` makes one point set serve
every such field, as the explicit constructions of the paper do. -/
def RatHits (F : Type) [Field F] {n : ℕ} (H : List (Fin n → ℚ))
    (C : MvPolynomial (Fin n) F → Prop) : Prop :=
  ∀ f, C f → f ≠ 0 → ∃ h ∈ H, MvPolynomial.eval (fun i => (h i : F)) f ≠ 0

end BorderDiffEq.Supplement


