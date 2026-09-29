-- Prove2me | Definitions.Def_BlackbodyRadiation_planck
-- name    : BlackbodyRadiation_planck
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T18:26:59.118987+00:00
-- url     : https://prove2.me/theorems/e24c8ddc-3030-437c-b8c0-326b1e01fe46
-- title:
--   Planck spectral radiance $B_\nu$, $B_\lambda$ and the shape function $x^n/(e^x-1)$
-- statement:
--   Planck's law gives the **spectral radiance** of a black body in thermodynamic equilibrium
--   at absolute temperature $T$: the power emitted per unit area, per unit solid angle, per
--   unit of the spectral variable. The three physical parameters are the Planck constant $h$,
--   the speed of light $c$, and the Boltzmann constant $k_B$; they are kept as real variables
--   so that the definitions are unit-agnostic.
--
--   Per unit **frequency** $\nu$,
--
--   $$B_\nu(\nu, T) \;=\; \frac{2h\nu^3/c^2}{\exp\!\left(\dfrac{h\nu}{k_B T}\right) - 1},$$
--
--   and per unit **wavelength** $\lambda$,
--
--   $$B_\lambda(\lambda, T) \;=\; \frac{2hc^2/\lambda^5}{\exp\!\left(\dfrac{hc}{\lambda k_B T}\right) - 1}.$$
--
--   These are deliberately given as two separate definitions rather than one: spectral radiance
--   is measured per increment of its own spectral variable, so $B_\lambda$ is *not* obtained
--   from $B_\nu$ by the substitution $\nu = c/\lambda$ alone — the Jacobian $c/\lambda^2$ also
--   enters, which is why the two curves peak at different places.
--
--   The third definition is the dimensionless **shape function**
--
--   $$g_n(x) \;=\; \frac{x^n}{e^x - 1},$$
--
--   indexed by a natural number $n$. Both parameterizations of Planck's law reduce to a
--   positive temperature-dependent prefactor times $g_n$ evaluated at a dimensionless argument
--   — $n = 5$ and $x = hc/(\lambda k_B T)$ for the wavelength form, $n = 3$ and
--   $x = h\nu/(k_B T)$ for the frequency form. This reduction is the strong form of Wien's
--   displacement law: the shape of the spectrum does not depend on the temperature.
--
--   All three are total real-valued functions, so they take junk values where the denominator
--   vanishes or an argument leaves the physical range; theorems built on them carry explicit
--   positivity hypotheses.
--
--   ---
--
--   ## Read-back (non-blind — written by the same agent that drafted this definition)
--
--   The platform normally attaches a read-back to a *draft* proposal item; this bundle is a published definition referenced by the proposal, and a reference item carries no read-back field, so the read-back is reproduced here instead.
--
--   > **Disclosure — non-blind read-back.** This read-back was *not* written by an independent blind auditor. It was written by the same agent that drafted the Lean statement it describes, with full knowledge of the intended meaning and of the source material. It is therefore self-testimony, not independent testimony, and it cannot be relied on to catch a mismatch between intent and formalization in the way a blind read-back is designed to. Please read it as a convenience rendering only, and audit the Lean statement directly.
--
--   This bundle introduces three real-valued functions of real arguments. No hypotheses are
--   imposed on any argument: each is a total function, defined for every real input, with
--   whatever value the real-number operations produce — including the convention that division
--   by zero yields $0$.
--
--   The first, written here $B_\nu$, takes five real numbers $h$, $c$, $k_B$, $T$, $\nu$ and
--   returns
--
--   $$B_\nu \;=\; \left.\left(\frac{2h\nu^{3}}{c^{2}}\right)\middle/\left(\exp\!\left(\frac{h\nu}{k_B T}\right)-1\right)\right.$$
--
--   evaluated left-to-right as $\bigl((2h\nu^{3})/c^{2}\bigr)$ divided by
--   $\bigl(\exp(h\nu/(k_BT))-1\bigr)$. The exponent $3$ on $\nu$ is a natural-number power.
--   Degenerate inputs are included: if $c = 0$ the first quotient is $0$; if $k_B T = 0$ the
--   inner quotient $h\nu/(k_BT)$ is $0$, so the exponential is $1$ and the outer denominator is
--   $0$, making the whole expression $0$; the same happens whenever
--   $\exp(h\nu/(k_BT)) = 1$, i.e. whenever $h\nu = 0$ with $k_BT \neq 0$. Negative or zero
--   values of any argument are permitted.
--
--   The second, written here $B_\lambda$, takes five real numbers $h$, $c$, $k_B$, $T$,
--   $\lambda$ (the last named `lam` in the code) and returns
--
--   $$B_\lambda \;=\; \left.\left(\frac{2hc^{2}}{\lambda^{5}}\right)\middle/\left(\exp\!\left(\frac{hc}{\lambda k_B T}\right)-1\right),\right.$$
--
--   again evaluated as $\bigl((2hc^{2})/\lambda^{5}\bigr)$ divided by
--   $\bigl(\exp(hc/(\lambda k_BT))-1\bigr)$, with $\lambda^{5}$ a natural-number power and the
--   product in the exponent's denominator associated as $(\lambda k_B) T$. Note that this is a
--   separate function from the first: it is not defined in terms of $B_\nu$, and no relation
--   between the two is asserted anywhere in this bundle. Degenerate inputs behave as above:
--   $\lambda = 0$ makes the first quotient $0$; $\lambda k_B T = 0$ makes the exponent $0$, the
--   exponential $1$, the outer denominator $0$, and the value $0$.
--
--   The third, written here $g_n$, takes a natural number $n$ and a real number $x$ and returns
--
--   $$g_n(x) \;=\; \frac{x^{n}}{e^{x}-1},$$
--
--   with $x^{n}$ the natural-number power (so $g_0(x) = 1/(e^x-1)$, and $0^0 = 1$ at
--   $n = x = 0$). At $x = 0$ the denominator is $0$, so $g_n(0) = 0$ for every $n$. For $x < 0$
--   the denominator is negative, so $g_n$ takes negative values there when $x^n > 0$. The value
--   $5$ or $3$ for $n$ is not built in; $n$ ranges over all natural numbers.
--
--   These are definitions only: nothing is asserted or proved about them here. In particular,
--   the bundle does not claim that either function is positive, continuous, differentiable, or
--   bounded, and does not relate $B_\nu$ or $B_\lambda$ to $g_n$.
-- source:
--   Planck's law, Wikipedia, https://en.wikipedia.org/wiki/Planck%27s_law , sections "The law" (frequency form and wavelength form of the spectral radiance B_nu and B_lambda) and "Properties / Peaks".

import Mathlib

namespace BlackbodyRadiation

/-- Planck's law, frequency parameterisation: the spectral radiance of a black body
at absolute temperature `T` per unit frequency `ν`,

  `B_ν(ν, T) = (2 h ν³ / c²) / (exp (h ν / (k_B T)) - 1)`. -/
noncomputable def planckFreq (h c kB T ν : ℝ) : ℝ :=
  2 * h * ν ^ 3 / c ^ 2 / (Real.exp (h * ν / (kB * T)) - 1)

/-- Planck's law, wavelength parameterisation: the spectral radiance of a black body
at absolute temperature `T` per unit wavelength `lam`,

  `B_λ(λ, T) = (2 h c² / λ⁵) / (exp (h c / (λ k_B T)) - 1)`. -/
noncomputable def planckWave (h c kB T lam : ℝ) : ℝ :=
  2 * h * c ^ 2 / lam ^ 5 / (Real.exp (h * c / (lam * kB * T)) - 1)

/-- The temperature-independent shape function `x ↦ xⁿ / (exp x - 1)` of the Planck
spectrum: `n = 5` for the wavelength parameterisation, `n = 3` for the frequency one. -/
noncomputable def planckShape (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n / (Real.exp x - 1)

end BlackbodyRadiation


