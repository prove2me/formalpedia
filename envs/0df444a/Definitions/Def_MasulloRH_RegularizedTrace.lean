-- Prove2me | Definitions.Def_MasulloRH_RegularizedTrace
-- name    : MasulloRH_RegularizedTrace
-- status  : Definition
-- author  : @davidloeffler
-- created : 2026-11-20T21:35:22.127375+00:00
-- url     : https://prove2.me/theorems/bcb9a5ab-1b4b-473b-86a1-cd5bc2827c5a
-- title:
--   Explicit regularized cutoff family and trace continuation expressions
-- statement:
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For each nonnegative integer $n$ (including $n=0$), set $N=n+1$, let $g(x)=0$ for $x≤0$ and $g(x)=e^{-1/x}$ for $x>0$, and set $H(x)=g(x)/(g(x)+g(1-x))$. Define $χ_n(t)=H(N log(t)-1)(1-H(log(t)/N-1))$ when $t>1$, and $χ_n(t)=0$ otherwise; define $f_{n,s}(t)=χ_n(t)(t^{1/2-s}-t^{-2})$ when $t>1$, and $f_{n,s}(t)=0$ otherwise, using complex powers of the positive real number $t$. Let $Z_α$ be the set of complex numbers $ρ$ such that $ζ(ρ)=0$, $0<Re(ρ)<1$, and $|Re(ρ)-1/2|<α$, where $ζ$ is the actual Riemann zeta function; each distinct location is an index. Write $m(ρ)$ for its natural-number analytic order at $ρ$: the local vanishing order when analytic and not identically zero nearby, with value zero if nonanalytic or identically zero nearby. Write $M(f,w)=∫_{0}^{∞}t^{w-1}f(t) dt$, with additive real Lebesgue measure and complex powers. Let $L(z)=ζ′(z)/ζ(z)$, where the derivative is the totalized complex derivative (zero where differentiability fails), and complex division by zero is zero. For every complex $s$ define $A(s)=∫_1^∞(t^{1/2-s}-t^{-2})√t/(t^2-1) dt$ using additive Lebesgue measure on $(1,∞)$, and $P(s)=(1/(s-1)-1/(5/2-1))+(1/s-1/(5/2))$. For every real $α$, complex $s$, and $ρ∈Z_α$, define $R_α(s,ρ)=m(ρ)(1/(s-ρ)-1/(5/2-ρ))$, $S_α(s)=Σ_{ρ∈Z_α}R_α(s,ρ)$, and $T_α(s)=L(5/2)+A(s)-P(s)+S_α(s)$. The predicate on $(α,s)$ called the continuation domain means exactly $1/2+α<Re(s)$ and $s≠1$. Define $A_n(s)=∫_1^∞(f_{n,s}(t)+f_{n,s}(t^{-1}))√t/(t^2-1) dt$, $Q_n(s)=Σ_{(p,k)}(log(p)/√(p^{k+1}))(f_{n,s}(p^{k+1})+f_{n,s}((p^{k+1})^{-1}))$, with $p$ a natural prime and $k$ any nonnegative integer, $P_n(s)=M(f_{n,s},1/2)+M(f_{n,s},-1/2)$, $S_{α,n}(s)=Σ_{ρ∈Z_α}m(ρ)M(f_{n,s},ρ-1/2)$, and $W_α(ρ)=m(ρ)/(1+Im(ρ)^2)$. These are definitions for all displayed parameters, without assumptions on $α$ or $s$; all real scalar factors are embedded in $ℂ$ where required, all complex reciprocal expressions use zero inverse at zero, and all integrals and sums have the totalized conventions. Integrals are the totalized complex Bochner integrals (zero for a nonintegrable integrand); unordered sums are totalized sums (zero when the family is not summable).
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

/-- The actual totalized logarithmic derivative, not a proposed extension. -/
noncomputable def zetaLogDeriv (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

/-- A fixed smooth cutoff in log coordinates. With N=n+1 it vanishes for
log t ≤ 1/N and log t ≥ 2N. This is a reconstruction, not a definition in the source. -/
noncomputable def traceLogCutoff (n : ℕ) (t : ℝ) : ℝ :=
  if 1 < t then
    Real.smoothTransition (((n : ℝ) + 1) * Real.log t - 1) *
      (1 - Real.smoothTransition (Real.log t / ((n : ℝ) + 1) - 1))
  else 0

/-- Subtraction at the fixed exponent 2 removes the endpoint divergence at t=1.
Here s is the unshifted zeta argument, so the variable exponent is 1/2-s. -/
noncomputable def regularizedTraceTest (n : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  if 1 < t then
    (traceLogCutoff n t : ℂ) * ((t : ℂ) ^ (1 / 2 - s) - (t : ℂ) ^ (-2 : ℂ))
  else 0

noncomputable def regularizedArch (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ),
    ((t : ℂ) ^ (1 / 2 - s) - (t : ℂ) ^ (-2 : ℂ)) *
      ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)

noncomputable def regularizedPolar (s : ℂ) : ℂ :=
  (1 / (s - 1) - 1 / ((5 / 2 : ℂ) - 1)) + (1 / s - 1 / (5 / 2 : ℂ))

noncomputable def zeroResolventTerm (α : ℝ) (s : ℂ)
    (ρ : ZetaZerosInTraceStrip α) : ℂ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) *
    (1 / (s - (ρ : ℂ)) - 1 / ((5 / 2 : ℂ) - (ρ : ℂ)))

noncomputable def regularizedSpectral (α : ℝ) (s : ℂ) : ℂ :=
  ∑' ρ : ZetaZerosInTraceStrip α, zeroResolventTerm α s ρ

noncomputable def regularizedTraceRHS (α : ℝ) (s : ℂ) : ℂ :=
  zetaLogDeriv (5 / 2) + regularizedArch s - regularizedPolar s + regularizedSpectral α s

/-- A half-plane with the zeta pole removed. -/
def InTraceContinuationDomain (α : ℝ) (s : ℂ) : Prop :=
  1 / 2 + α < s.re ∧ s ≠ 1

noncomputable def cutoffArch (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), realTraceIntegrand (regularizedTraceTest n s) t

noncomputable def cutoffPrime (n : ℕ) (s : ℂ) : ℂ :=
  ∑' i : Nat.Primes × ℕ, primePowerTraceTerm (regularizedTraceTest n s) i

noncomputable def cutoffPolar (n : ℕ) (s : ℂ) : ℂ :=
  mellin (regularizedTraceTest n s) (1 / 2) +
    mellin (regularizedTraceTest n s) (-1 / 2)

noncomputable def cutoffSpectral (α : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm (regularizedTraceTest n s) α ρ

noncomputable def zeroDecayWeight (α : ℝ) (ρ : ZetaZerosInTraceStrip α) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)

end MasulloRH


