-- Prove2me | Definitions.Def_ModularCurve_UVCrossingDominantIndices
-- name    : ModularCurve_UVCrossingDominantIndices
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/8b774e11-66b6-5fe6-a514-c36901e7dcfa
-- title:
--   Dominant indices and circle index drop for crossing-model normal forms
-- statement:
--   Throughout, $W$ is a commutative ring. A pair $(a,b)$ of one-variable power series over $W$ is read as the normal form $a(U)+b(V)$ of an element of the crossing model $W[[U,V]]/(UV-\pi)$, and the module indexes the terms of such a pair by a single integer.
--
--   `nfCoeff` sends $n \ge 0$ to the $n$-th coefficient of $a$ and $n = -(j+1) < 0$ to the $(j+1)$-st coefficient of $b$. `nfExponent` sends $n \ge 0$ to the exponent vector $\mathrm{Finsupp.single}\ 0\ n$, i.e. the monomial $U^{n}$, and $n = -(j+1)$ to $\mathrm{Finsupp.single}\ 1\ (j+1)$, i.e. $V^{j+1}$.
--
--   Given an arbitrary function $v : W \to \mathbb{N}\cup\{\infty\}$ (no valuation axioms are imposed) and natural numbers $E, t$, `termOrder` is
--   $$v(\mathrm{nfCoeff}(a,b)(n)) + \mathrm{annulusWeight}\,E\,t\,(\mathrm{nfExponent}\,n),$$
--   where $\mathrm{annulusWeight}\,E\,t\,d = d(0)\,t + d(1)\,(E - t)$ with truncated subtraction in $\mathbb{N}$; thus the weight is $nt$ for $n \ge 0$ and $(-n)(E-t)$ for $n < 0$.
--
--   `dominantIndices` is the set of $n \in \mathbb{Z}$ at which `termOrder` attains the value $\mathrm{repGaussOrder}\,v\,E\,t$ of the multivariable series $\mathrm{inU}\,a + \mathrm{inV}\,b$, that is the infimum over all exponent vectors $d$ of $v(\text{coeff}_d) + \mathrm{annulusWeight}\,E\,t\,d$. Note that this is equality with the infimum over the whole two-variable series, not merely over the indices $n$.
--
--   `circleIndexDrop` is $(\sup - \inf)$ of that set of integers, coerced to $\mathbb{N}$; the conditionally complete lattice structure on $\mathbb{Z}$ supplies default values when the set is empty or unbounded, so the value is then $0$.
--
--   All the definitions are keyed on the pair $(a,b)$, i.e. on a chosen presentation, rather than on the element of the quotient ring it represents.
--
--   **Relation to Mathlib.** Mathlib has no notion of Gauss order on a crossing model, nor of dominant indices; these are the project's own. The suprema and infima are Mathlib's `sSup`/`sInf` for the conditionally complete lattice $\mathbb{Z}$, so unbounded or empty index sets receive Mathlib's default values.
--
--   **Where it is used.** These notions provide the vocabulary for the slope analysis of the Gauss order $t \mapsto \mathrm{gaussOrder}\,v\,\pi\,E\,t\,x$ on the crossing model $W[[U,V]]/(UV-\pi)$: the extreme dominant indices act as the one-sided slopes of this piecewise-linear function of the depth $t$, and their difference counts, with multiplicity, the zeros of $x$ on the circle of radius $t$. They are the local input to the study of the crossing model as a model of a modular curve near a supersingular point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_UVCrossingDominantIndices.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]

def nfCoeff (ab : PowerSeries W × PowerSeries W) : ℤ → W
  | Int.ofNat i => PowerSeries.coeff i ab.1
  | Int.negSucc j => PowerSeries.coeff (j + 1) ab.2

def nfExponent : ℤ → (Fin 2 →₀ ℕ)
  | Int.ofNat i => Finsupp.single 0 i
  | Int.negSucc j => Finsupp.single 1 (j + 1)

def termOrder (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) : ℕ∞ :=
  v (nfCoeff ab n) + (annulusWeight E t (nfExponent n) : ℕ∞)

def dominantIndices (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) : Set ℤ :=
  {n | termOrder v E t ab n = repGaussOrder v E t (inU ab.1 + inV ab.2)}

def circleIndexDrop (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) : ℕ :=
  (sSup (dominantIndices v E t ab) - sInf (dominantIndices v E t ab)).toNat

end

end ModularCurve.UVCrossingModel


