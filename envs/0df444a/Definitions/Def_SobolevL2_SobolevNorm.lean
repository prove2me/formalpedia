-- Prove2me | Definitions.Def_SobolevL2_SobolevNorm
-- name    : SobolevL2_SobolevNorm
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T17:00:41.575842+00:00
-- url     : https://prove2.me/theorems/578b4f8e-6059-4113-9415-7cb24d0cff88
-- title:
--   The $L^2$-Sobolev norm $\|u\|_{H^s}=\|J^s u\|_{L^2}\in[0,\infty]$ of a tempered distribution on $\mathbb R^n$ (Bessel potential $J^s$, any real order $s$)
-- statement:
--   **The $L^2$-Sobolev (Bessel potential) norm of order $s\in\mathbb R$.** Let $E$ be a finite-dimensional real inner product space (a model of $\mathbb R^n$) with Lebesgue measure, $F$ a complex Banach space, and $u\in\mathcal S'(E,F)$ a tempered distribution. With the Fourier transform $\widehat f(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$, the Bessel potential of order $s$ is the Fourier multiplier
--   $$J^s u=\mathcal F^{-1}\big((1+|\xi|^2)^{s/2}\,\widehat u\big).$$
--   The Sobolev space $H^s(E,F)$ consists of those $u$ for which $J^s u$ is (represented by) a function in $L^2(E,F)$, and we define
--   $$\|u\|_{H^s}=\|J^s u\|_{L^2(E,F)}\quad\text{if }u\in H^s(E,F),\qquad \|u\|_{H^s}=\infty\ \text{otherwise}.$$
--   For $F$ a Hilbert space Plancherel's theorem gives $\|u\|_{H^s}^2=\int_E(1+|\xi|^2)^s\,\|\widehat u(\xi)\|_F^2\,d\xi$ (theorems `SobolevL2.sobolevNorm_eq_iInf_fourier`, `SobolevL2.sobolevNorm_schwartz_eq_lintegral_fourier`), which is the weighted Fourier-side norm (9.1.1.3) of Definition 9.1.1.1 of the source for the group $G=\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$. In the paper's normalization (9.1.1.3) the squared norm carries the weight $(1+w^2)^{s/2}$ (not $(1+w^2)^{s}$); for $G=\mathbb R^n$, $\widehat G\cong\mathbb R^n$ and the Sobolev weight $w(\xi)=|\xi|$ (which satisfies (9.1.1.2) with $C_w=1$), the paper's $H^s_w$ is therefore the classical $H^{s/2}$ used here.
--
--   The norm is the basic quantity of the $L^2$ Sobolev theory recalled in §9.1 of the source. The Hilbert space structure, the density of test functions, the monotonicity in $s$, the duality $H^{-s}=(H^s)'$ and the characterization by derivatives are stated in terms of it in the theorems `SobolevL2.*`; the Sobolev embedding `SobolevL2.lca_sobolev_embedding` is formulated on the Fourier side of a general locally compact abelian group and does not use it.
--
--   **Formalization Note.** Mathlib provides `TemperedDistribution.besselPotential E F s` and the predicate `TemperedDistribution.MemSobolev s 2 u`, but no norm. `SobolevL2.sobolevNorm s u` is the infimum of `‖f‖ₑ` over all `f : Lp F 2 volume` with `besselPotential E F s u = f` (as tempered distributions). Since `Lp → 𝓢'` is injective, there is at most one such `f`, so the value is $\|J^s u\|_{L^2}$ when `MemSobolev s 2 u` holds and $\infty$ (empty infimum) otherwise.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 396, Definition 9.1.1.1 (norm (9.1.1.3)), specialized to $G=\mathbb R^n$ with the weight $w(\xi)=|\xi|$; classical reference: P. Górka and E. G. Reyes, Sobolev spaces on locally compact abelian groups, arXiv:1208.3053v1 (2012), §§1–2, as cited by the paper at Definition 9.1.1.1

import Mathlib

/-!
# The `L²`-Sobolev norm of a tempered distribution

For a finite-dimensional real inner product space `E` (a model of `ℝⁿ` with Lebesgue measure)
and a complex Banach space `F`, Mathlib defines the Bessel potential
`J^s = TemperedDistribution.besselPotential E F s`, the Fourier multiplier with symbol
`ξ ↦ (1 + ‖ξ‖²)^{s/2}` on tempered distributions, and the membership predicate
`TemperedDistribution.MemSobolev s 2 u` (`J^s u` is represented by an `L²` function).

This file adds the corresponding norm `‖u‖_{H^s} = ‖J^s u‖_{L²}`, valued in `[0, ∞]`.
-/

namespace SobolevL2

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap

/-- The `L²`-Sobolev (Bessel potential) norm of order `s ∈ ℝ` of a tempered distribution
`u ∈ 𝓢'(E, F)`: `‖u‖_{H^s} = ‖J^s u‖_{L²(E, F)}`, where `J^s = besselPotential E F s` is the
Fourier multiplier with symbol `(1 + ‖ξ‖²)^{s/2}`.

It is the infimum of `‖f‖ₑ` over all `f ∈ L²(E, F)` with `J^s u = f` (as tempered
distributions). Such an `f` is unique when it exists, so the value is `‖J^s u‖_{L²}` when
`u ∈ H^s(E, F)` (i.e. `MemSobolev s 2 u`) and `∞` otherwise. -/
noncomputable def sobolevNorm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (s : ℝ) (u : 𝓢'(E, F)) : ℝ≥0∞ :=
  ⨅ (f : Lp F 2 (volume : Measure E)) (_ : besselPotential E F s u = f), ‖f‖ₑ

end SobolevL2


