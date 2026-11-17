-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_bdeg
-- name    : ApproxDegComp_Supplement_bdeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:58:44.098556+00:00
-- url     : https://prove2.me/theorems/7f276b4c-ead5-4a24-a7ad-f423d8cd7d49
-- title:
--   Bounded approximate degree $\widetilde{\mathrm{bdeg}}(f)$ of a partial Boolean function
-- statement:
--   Let $f:D\subseteq\{0,1\}^n\to\{0,1\}$ be a possibly partial Boolean function and $\varepsilon\ge0$. A real polynomial $p:\mathbb R^n\to\mathbb R$ is a **bounded $\varepsilon$-approximation** of $f$ if
--
--   $$|p(x)-f(x)|\le\varepsilon\ \text{ for every }x\in D\qquad\text{and}\qquad 0\le p(x)\le1\ \text{ for every }x\in\{0,1\}^n .$$
--
--   The **bounded $\varepsilon$-approximate degree** $\mathrm{bdeg}_\varepsilon(f)$ is the minimum total degree of such a polynomial, and $\widetilde{\mathrm{bdeg}}(f)=\mathrm{bdeg}_{1/3}(f)$.
--
--   The approximation is required only on the domain, while boundedness is required on the whole cube. This is the measure in which Theorem 19 is stated for the partial inner function $\mathrm{PrTH}^t_m$.
--
--   **Formalization Note** Polynomials are arbitrary real multivariate polynomials, evaluated at 0/1 points, and degree is total degree. The minimum is the infimum of a set of natural numbers, which is nonempty for every $f$ and every $\varepsilon\ge0$ (the multilinear interpolant of $f$ is exact and $\{0,1\}$-valued on the cube; this is proved in a sanity file), so the infimum is attained.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 3, p.11

import Mathlib
import Definitions.Def_ApproxDegComp_cubePt
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace ApproxDegComp

namespace Supplement

/-- **Bounded ε-approximate degree** `bdeg_ε(f)` and `b̃deg(f) = bdeg_{1/3}(f)` (Definition 3,
p.11). Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 3,
p.11: "Let f : D ⊆ {0,1}ⁿ → {0,1} be a Boolean function. For 0 ≤ ϵ < 1/2, a real polynomial
p : ℝⁿ → ℝ is said to approximate f if |p(x) − f(x)| ≤ ϵ, for every x ∈ D and 0 ≤ p(x) ≤ 1, for
every x ∈ {0,1}ⁿ. The bounded ϵ-approximate degree of f, denoted by bdeg_ϵ(f) is the minimum
degree of all such bounded ϵ-approximating polynomials of f."

`bdegEps ε f` is the least `d` such that some real polynomial of total degree at most `d` is
within `ε` of `f` on the domain of `f` and takes values in `[0, 1]` on the whole cube.

**Formalization Note** `f` is a `NoPerfectRandComp.PartialFn` (domain `f.dom ⊆ {0,1}^ι`, value
`f.val` read on the domain only). Polynomials are `MvPolynomial ι ℝ` of any shape, evaluated at
0/1 points (`cubePt`, `true ↦ 1`); degree is `totalDegree`. The minimum is `sInf` over `ℕ`; the set
is nonempty for every `f` and every `ε ≥ 0` (the multilinear interpolant of `f.val` takes values in
`{0,1}` on the cube; checked in `Solutions/verification/ApproxDegComp_Supplement_sanity.lean`). The
range `0 ≤ ε < 1/2` is not bundled; the statements use `ε = 1/3`. -/
noncomputable def bdegEps {ι : Type} [Fintype ι] (ε : ℝ) (f : NoPerfectRandComp.PartialFn ι) : ℕ :=
  sInf {d : ℕ | ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧
    (∀ x ∈ f.dom, |MvPolynomial.eval (cubePt x) p - boolToReal (f.val x)| ≤ ε) ∧
    ∀ x : ι → Bool, 0 ≤ MvPolynomial.eval (cubePt x) p ∧ MvPolynomial.eval (cubePt x) p ≤ 1}

/-- **Bounded approximate degree** `b̃deg(f) = bdeg_{1/3}(f)` (Definition 3, p.11: "In particular,
b̃deg(f) = bdeg_{1/3}(f)"). -/
noncomputable def bdeg {ι : Type} [Fintype ι] (f : NoPerfectRandComp.PartialFn ι) : ℕ :=
  bdegEps (1 / 3) f

end Supplement

end ApproxDegComp


