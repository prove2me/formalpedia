-- Prove2me | Definitions.Def_mm_continuous
-- name    : mm_continuous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:39:04.62237+00:00
-- url     : https://prove2.me/theorems/5d8ab27f-e5d5-42f2-adca-460dc1e30249
-- title:
--   Heat kernels and product chains
-- statement:
--   This file defines continuous-time chains by Poissonization, following Chapter 20 of Levin–Peres–Wilmer.
--
--   **The heat kernel.** For a chain $P$ on a finite state space and a real time $t\ge0$, the **heat kernel** is
--   $$H_t(x,y)=\sum_{k=0}^{\infty}e^{-t}\,\frac{t^k}{k!}\;P^k(x,y):$$
--   run the discrete chain, but take its jumps at the arrival times of a rate-one Poisson clock, so the number of jumps completed by time $t$ is Poisson with mean $t$. This agrees with the matrix exponential $e^{t(P-I)}$; the series presentation keeps everything inside elementary real analysis.
--
--   **Continuous-time mixing.** With $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ the total variation distance of Mission II, the continuous distance to stationarity and mixing time are
--   $$d^{\mathrm{cont}}(t)=\max_{x}\bigl\|H_t(x,\cdot)-\pi\bigr\|_{TV},\qquad t^{\mathrm{cont}}_{\mathrm{mix}}(\varepsilon)=\inf\{t\ge0:\ d^{\mathrm{cont}}(t)\le\varepsilon\},$$
--   the latter a real number rather than an integer — one dividend of continuous time.
--
--   **Product chains.** For coordinate chains $P_1,\dots,P_n$ on factor spaces, the chain updating only coordinate $i$ leaves the other coordinates fixed and moves coordinate $i$ by $P_i$; the **product chain** picks a uniformly random coordinate and updates it:
--   $$P=\frac1n\sum_{i=1}^n\widetilde P_i.$$
--   Its continuous-time mixing exhibits the $n\log n$ phenomenon (Theorem 20.7, a milestone of this mission), the template for the hypercube.
--
--   **Conventions.** The heat-kernel series is a `tsum` (its summability under stochasticity is provable, and non-summable families would sum to the junk value $0$); the continuous mixing time is an `sInf` over reals, junk $0$ on an empty set — excluded under the theorems' hypotheses.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 20, Sections 20.1-20.4, pp. 265-269

import Definitions.Def_mm_mixing
import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Continuous-time chains, following Levin–Peres–Wilmer, *Markov Chains and
Mixing Times*, Chapter 20.

The heat kernel is defined by Poissonization (LPW Eq. (20.5)):
`H_t(x,y) = ∑_k e^{-t} t^k/k! · P^k(x,y)`, which agrees with the matrix
exponential `e^{t(P−I)}`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **heat kernel** `H_t = e^{t(P−I)}`, via the Poissonization formula
(LPW §20.1, Eq. (20.5)). -/
def heatKernel (P : Matrix V V ℝ) (t : ℝ) : Matrix V V ℝ :=
  fun x y => ∑' k : ℕ, Real.exp (-t) * t ^ k / (Nat.factorial k) * (P ^ k) x y

/-- `d^{cont}(t) = max_x ‖H_t(x,·) − π‖_TV` (LPW §20.2). -/
def contDistStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℝ) : ℝ :=
  ⨆ x : V, tvDist (fun y => heatKernel P t x y) π

/-- The continuous mixing time
`t^{cont}_mix(ε) = inf {t ≥ 0 : d^{cont}(t) ≤ ε}` (LPW §20.2,
Eq. (20.7)). -/
def contMixingTime (P : Matrix V V ℝ) (π : V → ℝ) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ contDistStationary P π t ≤ ε}

/-- The chain updating only coordinate `i` with the matrix `P i`
(LPW §20.4, Eq. (20.14)). -/
def coordChain {n : ℕ} {W : Fin n → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] (P : ∀ i, Matrix (W i) (W i) ℝ) (i : Fin n) :
    Matrix (∀ j, W j) (∀ j, W j) ℝ :=
  fun x y => if ∀ j : Fin n, j ≠ i → y j = x j then P i (x i) (y i) else 0

/-- The **product chain** `P = n⁻¹ ∑ᵢ P̃ᵢ`: pick a coordinate uniformly at
random and update it (LPW §20.4). -/
def productChain {n : ℕ} {W : Fin n → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] (P : ∀ i, Matrix (W i) (W i) ℝ) :
    Matrix (∀ j, W j) (∀ j, W j) ℝ :=
  fun x y => (n : ℝ)⁻¹ * ∑ i : Fin n, coordChain P i x y

end

end MarkovMixing


