-- Prove2me | Definitions.Def_ApproxDegComp_approxDeg
-- name    : ApproxDegComp_approxDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:38.305162+00:00
-- url     : https://prove2.me/theorems/644646d1-7eb2-47eb-887e-7575252cf7d7
-- title:
--   $\varepsilon$-approximate degree $\deg_\varepsilon(f)$ and approximate degree $\widetilde{\deg}(f)$
-- statement:
--   For a Boolean function $f:\{0,1\}^n\to\{0,1\}$ and $\varepsilon\ge0$, the **$\varepsilon$-approximate degree** $\deg_\varepsilon(f)$ is the minimum total degree of a real polynomial that $\varepsilon$-approximates $f$ on $\{0,1\}^n$. The **approximate degree** is
--
--   $$\widetilde{\deg}(f)=\deg_{1/3}(f).$$
--
--   For $\varepsilon=0$ this is the exact degree. Approximate degree lower-bounds bounded-error quantum query complexity and is the measure whose behaviour under composition this mission is about.
--
--   **Formalization Note** The minimum is the infimum of a set of natural numbers. That set is nonempty for every $f$ and every $\varepsilon\ge0$ because the exact multilinear representation of $f$ has degree at most $n$, so the infimum is attained and is never the empty-set default. Degree means total degree.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 2, p.11

import Mathlib
import Definitions.Def_ApproxDegComp_IsApprox

namespace ApproxDegComp

/-- **ε-approximate degree** `deg_ε(f)` (Definition 2, p.11).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 2, p.11: "The ϵ-approximate degree of f, denoted by deg_ϵ(f) is the minimum
degree of all such ϵ-approximating polynomials of f."

`approxDegEps ε f` is the least `d` such that some real polynomial of total degree at most `d`
`ε`-approximates `f` on the cube.

**Formalization Note** The minimum is `sInf` of a set of natural numbers. For `ε ≥ 0` and finite
`ι` the set is nonempty (the exact multilinear representation of `f` has degree at most
`card ι`; checked in `Solutions/verification/ApproxDegComp_sanity.lean`), so `sInf` is the
minimum and never the junk value of the empty set. Degree is `MvPolynomial.totalDegree`. -/
noncomputable def approxDegEps {ι : Type} [Fintype ι] (ε : ℝ) (f : (ι → Bool) → Bool) : ℕ :=
  sInf {d : ℕ | ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ IsApprox ε f p}

/-- **Approximate degree** `d̃eg(f) = deg_{1/3}(f)` (Definition 2, p.11: "In particular,
d̃eg(f) = deg_{1/3}(f)"). -/
noncomputable def approxDeg {ι : Type} [Fintype ι] (f : (ι → Bool) → Bool) : ℕ :=
  approxDegEps (1 / 3) f

end ApproxDegComp


