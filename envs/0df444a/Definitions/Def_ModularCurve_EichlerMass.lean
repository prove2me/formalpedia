-- Prove2me | Definitions.Def_ModularCurve_EichlerMass
-- name    : ModularCurve_EichlerMass
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a7235bee-ffe4-515e-a6b0-eb4d4b606297
-- title:
--   Eichler mass and supersingular count as rational functions
-- statement:
--   Two rational-valued arithmetic functions of a pair of natural numbers $N,q$ are introduced.
--
--   The first, [`ModularCurve.eichlerMass N q`](../def/ModularCurve_EichlerMass.html#L8), is $\bigl((q-1)\,\psi(N)\bigr)/12$, where $\psi(N)$ denotes [`ModularCurve.dedekindPsi N`](../def/ModularCurve_X0.html#L201), itself defined as the divisor sum $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (so $\psi(1)=1$, and for $N \geq 1$ this is the usual $N\prod_{p \mid N}(1+p^{-1})$); the natural number $\psi(N)$ is cast into $\mathbb{Q}$, and the division is division in $\mathbb{Q}$.
--
--   The second, [`ModularCurve.ssCountFormula N q`](../def/ModularCurve_EichlerMass.html#L11), adds to the Eichler mass the two correction terms
--   $$\frac{(2-\nu_2(q))\,\nu_2(N)}{4} + \frac{(2-\nu_3(q))\,\nu_3(N)}{3},$$
--   again with all counts cast into $\mathbb{Q}$. Here $\nu_2(M)$ is [`ModularCurve.nuTwo M`](../def/ModularCurve_GenusNumerics.html#L9), the cardinality of the subtype of $\mathbb{Z}/M$ cut out by $x^2+1=0$, and $\nu_3(M)$ is [`ModularCurve.nuThree M`](../def/ModularCurve_GenusNumerics.html#L11), the cardinality of the subtype cut out by $x^2+x+1=0$; these are the counts of solutions of the two quadratic congruences modulo $M$ that govern the elliptic points of order $2$ and $3$ on $X_0(M)$.
--
--   Both declarations are arithmetic functions pure and simple: $N$ and $q$ are arbitrary natural numbers, with no primality of $q$, no coprimality $\gcd(N,q)=1$ and no positivity assumed, and neither definition asserts anything about an actual supersingular locus or a quaternionic class number. The interpretation of $\nu_2,\nu_3$ as elliptic-point counts and of $\mathrm{ssCountFormula}$ as a count of supersingular points weighted by automorphisms is supplied elsewhere, by identities relating these expressions to [`ModularCurve.genusFormula`](../def/ModularCurve_GenusNumerics.html#L20).
--
--   **Relation to Mathlib.** Mathlib provides no Dedekind psi function, no elliptic-point counts $\nu_2,\nu_3$ and no Eichler mass formula; these, together with [`ModularCurve.dedekindPsi`](../def/ModularCurve_X0.html#L201), [`ModularCurve.nuTwo`](../def/ModularCurve_GenusNumerics.html#L9), [`ModularCurve.nuThree`](../def/ModularCurve_GenusNumerics.html#L11) and [`ModularCurve.genusFormula`](../def/ModularCurve_GenusNumerics.html#L20) from the imported modules, are the project's own numerical definitions.
--
--   **Where it is used.** These expressions are the general-level form of the numerical count attached to the special fibre of $X_0(Nq)$ at $q$, compared with the genus expression [`ModularCurve.genusFormula`](../def/ModularCurve_GenusNumerics.html#L20) through the identity $\mathrm{ssCountFormula}(N,q) = g(Nq) - 2g(N) + 1$. They feed the computations of character-group and component-group ranks across levels used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EichlerMass.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

noncomputable def eichlerMass (N q : ℕ) : ℚ :=
  ((q : ℚ) - 1) * (dedekindPsi N : ℚ) / 12

noncomputable def ssCountFormula (N q : ℕ) : ℚ :=
  eichlerMass N q
    + (2 - (nuTwo q : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree q : ℚ)) * (nuThree N : ℚ) / 3

end ModularCurve


