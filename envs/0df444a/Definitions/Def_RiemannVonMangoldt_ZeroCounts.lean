-- Prove2me | Definitions.Def_RiemannVonMangoldt_ZeroCounts
-- name    : RiemannVonMangoldt_ZeroCounts
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T02:10:04.950576+00:00
-- url     : https://prove2.me/theorems/6e00e685-a716-48b3-b245-c1d6406c8f76
-- title:
--   Zero-counting functions $N(T)$, $N(T,\chi)$ and the Lindelöf hypothesis
-- statement:
--   This file fixes the three objects in terms of which the Riemann–von Mangoldt formula and its refinements are stated.
--
--   1. **The zero-counting function of $\zeta$.** For real $T$, let
--   $$N(T)=\sum_{\substack{\rho:\ \zeta(\rho)=0\\ 0<\operatorname{Re}\rho<1,\ 0<\operatorname{Im}\rho\le T}} m_\rho ,$$
--   where $m_\rho\ge 1$ is the multiplicity (order of vanishing) of the zero $\rho$ of the Riemann zeta function. Thus $N(T)$ is the number of zeros of $\zeta$ in the critical strip with imaginary part in $(0,T]$, counted with multiplicity; $N(T)=0$ for $T\le 0$.
--
--   2. **The zero-counting function of a Dirichlet $L$-function.** For a positive integer $q$, a Dirichlet character $\chi$ modulo $q$ and real $T$, let
--   $$N(T,\chi)=\sum_{\substack{\rho:\ L(\rho,\chi)=0\\ 0<\operatorname{Re}\rho<1,\ -T\le\operatorname{Im}\rho\le T}} m_\rho ,$$
--   the number of zeros of $L(s,\chi)$ in the critical strip with imaginary part between $-T$ and $T$, counted with multiplicity.
--
--   3. **The Lindelöf hypothesis.** The statement that for every $\varepsilon>0$,
--   $$\zeta\!\left(\tfrac12+it\right)=O\!\left(t^{\varepsilon}\right)\qquad (t\to+\infty).$$
--
--   These are the standard definitions used by Titchmarsh (*The Theory of the Riemann Zeta-Function*, §9.2 and §13) and Davenport (*Multiplicative Number Theory*, Ch. 16).
--
--   **Formalization Note** $\zeta$ is Mathlib's `riemannZeta` and $L(s,\chi)$ is `DirichletCharacter.LFunction` (the analytic continuation of $\sum\chi(n)n^{-s}$). The multiplicity is `analyticOrderNatAt`, and each count is a `finsum` over the zero set, which is finite for every $T$ (zeros of a nonzero meromorphic function in a bounded region); this finiteness is a fact a solver must establish, not an assumption. Every zero of $\zeta$ with positive imaginary part lies in the open strip $0<\operatorname{Re}s<1$, so restricting to the strip in item 1 agrees with the source's "zeros with imaginary part greater than 0 and at most $T$". In item 2 the open strip excludes the trivial zero at $s=0$ of an even nonprincipal character. Since $\zeta(\bar s)=\overline{\zeta(s)}$, the one-sided bound in item 3 is equivalent to the usual two-sided form $\zeta(\tfrac12+it)=O((1+|t|)^{\varepsilon})$.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), first displayed formula (definition of $N(T)$), the paragraph "Under the Lindelöf and Riemann hypotheses", and the final paragraph (definition of $N(T,\chi)$). Standard conventions: Titchmarsh (1986) §9.2; Davenport, Multiplicative Number Theory, Ch. 16.

import Mathlib

/-!
# Zero-counting functions for the Riemann–von Mangoldt formula

* `zetaZeroCount T` is `N(T)`: the number of zeros `ρ` of the Riemann zeta function with
  `0 < Re ρ < 1` and `0 < Im ρ ≤ T`, counted with multiplicity.
* `dirichletZeroCount χ T` is `N(T, χ)`: the number of zeros `ρ` of the Dirichlet
  `L`-function `L(s, χ)` with `0 < Re ρ < 1` and `-T ≤ Im ρ ≤ T`, counted with multiplicity.
* `LindelofHypothesis` is the Lindelöf hypothesis `ζ(1/2 + it) = O(t^ε)` for every `ε > 0`.
-/

namespace RiemannVonMangoldt

open Complex Filter Asymptotics

/-- `N(T)`: the number of zeros of `ζ` in the critical strip with imaginary part in `(0, T]`,
counted with multiplicity. -/
noncomputable def zetaZeroCount (T : ℝ) : ℝ :=
  ∑ᶠ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0},
    (analyticOrderNatAt riemannZeta s : ℝ)

/-- `N(T, χ)`: the number of zeros of `L(s, χ)` in the critical strip with imaginary part in
`[-T, T]`, counted with multiplicity. -/
noncomputable def dirichletZeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (T : ℝ) : ℝ :=
  ∑ᶠ s ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ χ.LFunction s = 0},
    (analyticOrderNatAt χ.LFunction s : ℝ)

/-- The Lindelöf hypothesis: for every `ε > 0`, `ζ(1/2 + it) = O(t^ε)` as `t → +∞`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =O[atTop] (fun t : ℝ => t ^ ε)

end RiemannVonMangoldt


