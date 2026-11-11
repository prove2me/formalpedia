-- Prove2me | Definitions.Def_IntegerRootsFN_Main_Representations
-- name    : IntegerRootsFN_Main_Representations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:34.911327+00:00
-- url     : https://prove2.me/theorems/748becb1-b951-436b-b4e1-e5c73587943a
-- title:
--   Signed magnitude lengths and represented Gaussian rationals
-- statement:
--   For an integer $u$, put $\ell(u)=\lceil\log_2(|u|+1)\rceil$, with $\ell(0)=0$. A represented Gaussian rational consists of integers $u,v$ and a positive natural denominator $w$, with value
--
--   $$z=(u+iv)/w,\qquad \operatorname{size}(z)=\ell(u)+\ell(v)+\ell(w).$$
--
--   Dyadic numbers reuse the published Gaussian-dyadic triple and its complex value; their source size is $\ell(u)+\ell(v)+\ell(k)$ for denominator $2^k$. The other published definition's size including three overhead bits is deliberately not used as this paper's mathematical size. Evaluation points instead have length $\lceil\log_2(2+|c|)\rceil$, and a list's point size is the sum of those lengths, including repetitions. All logarithms are base two.
--
--   These finite representations distinguish semantic values from storage, and ensure positive rational denominators. Binary signs and separators are charged separately by the machine interface.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 7, §3.1; p. 10, Lemma 3.5

import Mathlib
import Definitions.Def_ApproxGKR_dyadicVal

set_option autoImplicit false

namespace IntegerRootsFN.Main

def magnitudeLength (z : ℤ) : ℕ := Nat.clog 2 (z.natAbs + 1)

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Evaluation-point size differs from magnitudeLength: its argument is `2+|z|`. -/
noncomputable def pointLength (z : ℤ) : ℕ :=
  ⌈logTwo (2 + |(z : ℝ)|)⌉₊

noncomputable def pointSize (cs : List ℤ) : ℕ := (cs.map pointLength).sum

/-- General Gaussian rationals are finite, possibly unreduced, representations. -/
structure GaussianRational where
  re : ℤ
  im : ℤ
  den : ℕ
  den_pos : 0 < den

noncomputable def GaussianRational.value (z : GaussianRational) : ℂ :=
  ((z.re : ℂ) + (z.im : ℂ) * Complex.I) / (z.den : ℂ)

def GaussianRational.bitSize (z : GaussianRational) : ℕ :=
  magnitudeLength z.re + magnitudeLength z.im + magnitudeLength (z.den : ℤ)

def dyadicSize (z : ApproxGKR.GaussDyadic) : ℕ :=
  magnitudeLength z.1 + magnitudeLength z.2.1 + magnitudeLength (z.2.2 : ℤ)

end IntegerRootsFN.Main


