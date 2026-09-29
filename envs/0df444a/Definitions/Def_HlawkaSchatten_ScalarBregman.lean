-- Prove2me | Definitions.Def_HlawkaSchatten_ScalarBregman
-- name    : HlawkaSchatten_ScalarBregman
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T06:44:28.89256+00:00
-- url     : https://prove2.me/theorems/1b9cb1ee-7a56-4524-af30-3cbf7a1017ce
-- title:
--   The scalar power potential, its gradient, and the scalar Bregman divergence
-- statement:
--   For real $p,x$:
--
--   - `signedPower q x` $:= \mathrm{sign}(x)\,|x|^q$ — the signed real power (Lean totalizes it at $x=0$ and for every real exponent $q$, via `Real.rpow` and `SignType.sign`).
--   - `powerPotential p x` $:= |x|^p/p =: F_p(x)$ — the scalar potential. The division by $p$ is deliberate and load-bearing: it is $F_p$, not $|x|^p$, whose derivative (for $p>1$) is the plain signed $(p-1)$-power with no extra factor of $p$.
--   - `powerGradient p x` $:= |x|^{p-2}x =: G_p(x)$ — the signed power that is the gradient of $F_p$ when $p>1$.
--   - `scalarMazur p x` $:=$ `signedPower (p/2) x` $=: \psi_p(x)$ — the scalar Mazur map, used to compare the power geometry of $F_p$ with an ordinary (squared-distance) Hilbert geometry.
--   - `scalarBregman p a b` $:= F_p(a)-F_p(b)-G_p(b)(a-b) =: \beta_p(a,b)$ — the Bregman divergence of $F_p$, written with its explicit gradient term.
--
--   All five definitions are total in $p$ and in their real arguments; no positivity or size hypothesis on $p$ is imposed here.
--
--   The bundle also proves several elementary algebraic facts used throughout the rest of the construction: `signedPower`/`scalarMazur` vanish at $0$ and are odd ($\mathrm{signedPower}\,q\,(-x)=-\mathrm{signedPower}\,q\,x$, and likewise for `scalarMazur`); $\mathrm{signedPower}\,1\,x=x$; composing signed powers multiplies their exponents, $\mathrm{signedPower}\,q\,(\mathrm{signedPower}\,r\,x)=\mathrm{signedPower}\,(qr)\,x$; $|x|^p=(x^2)^{p/2}$, so $F_p(x)=(x^2)^{p/2}/p$ is manifestly even; and $F_p$ is homogeneous under positive scaling, $F_p(cx)=c^pF_p(x)$ for $c>0$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarBregman.lean#L26-L328

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Scalar power Bregman data

These are the scalar objects used in the first layer of the audited
Bregman--Mazur proof. The normalization of `powerPotential` is important:
its derivative is the signed `(p - 1)`-power with no extra factor of `p`.
-/

namespace HlawkaSchatten

open Filter
open scoped Topology

/-- The signed real power `sign(x) * |x| ^ q`. -/
noncomputable def signedPower (q x : ℝ) : ℝ :=
  (SignType.sign x : ℝ) * |x| ^ q

/-- The convex scalar potential `|x| ^ p / p`. -/
noncomputable def powerPotential (p x : ℝ) : ℝ :=
  |x| ^ p / p

/-- The signed power that is the gradient of `powerPotential` for `p > 1`. -/
noncomputable def powerGradient (p x : ℝ) : ℝ :=
  |x| ^ (p - 2) * x

/-- The scalar Mazur map used to compare a power geometry with a Hilbert geometry. -/
noncomputable def scalarMazur (p x : ℝ) : ℝ :=
  signedPower (p / 2) x

/-- The Bregman divergence of `powerPotential`, written with its explicit gradient. -/
noncomputable def scalarBregman (p a b : ℝ) : ℝ :=
  powerPotential p a - powerPotential p b - powerGradient p b * (a - b)

@[simp]
theorem signedPower_zero (q : ℝ) : signedPower q 0 = 0 := by
  simp [signedPower]







@[simp]
theorem scalarMazur_zero (p : ℝ) : scalarMazur p 0 = 0 := by
  simp [scalarMazur]



@[simp]
theorem signedPower_one (x : ℝ) : signedPower 1 x = x := by
  simp [signedPower]

@[simp]
theorem signedPower_neg (q x : ℝ) : signedPower q (-x) = -signedPower q x := by
  simp [signedPower, Left.sign_neg]

/-- Composition of signed real powers multiplies their exponents. -/
theorem signedPower_comp (q r x : ℝ) :
    signedPower q (signedPower r x) = signedPower (q * r) x := by
  by_cases hx : x = 0
  · subst x
    simp
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have habs : 0 < |x| := abs_pos.mpr hx
    have hpow : 0 < |x| ^ r := Real.rpow_pos_of_pos habs r
    simp only [signedPower, sign_neg hxneg, SignType.coe_neg,
      SignType.coe_one, neg_mul, one_mul]
    rw [sign_neg (neg_lt_zero.mpr hpow), SignType.coe_neg,
      SignType.coe_one, neg_mul, one_mul, abs_neg, abs_of_pos hpow,
      ← Real.rpow_mul habs.le]
    congr 2
    ring
  · have hpow : 0 < |x| ^ r :=
      Real.rpow_pos_of_pos (abs_pos.mpr hx) r
    simp only [signedPower, sign_pos hxpos, SignType.coe_one, one_mul]
    rw [sign_pos hpow, SignType.coe_one, one_mul, abs_of_pos hpow,
      ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring





@[simp]
theorem scalarMazur_neg (p x : ℝ) : scalarMazur p (-x) = -scalarMazur p x := by
  simp [scalarMazur]













/-- An absolute real power factors through the square of its argument. -/
theorem sq_rpow_div_two (p x : ℝ) :
    (x ^ 2) ^ (p / 2) = |x| ^ p := by
  rw [Real.rpow_div_two_eq_sqrt p (sq_nonneg x), Real.sqrt_sq_eq_abs]

/-- The power potential is an even function expressed through a nonnegative
square. -/
theorem powerPotential_eq_sq_rpow_div_two (p x : ℝ) :
    powerPotential p x = (x ^ 2) ^ (p / 2) / p := by
  rw [powerPotential, sq_rpow_div_two]













/-- The power potential is homogeneous under positive scalar multiplication. -/
theorem powerPotential_mul_of_pos (p x : ℝ) {c : ℝ} (hc : 0 < c) :
    powerPotential p (c * x) = c ^ p * powerPotential p x := by
  simp only [powerPotential, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg x)]
  ring













end HlawkaSchatten


