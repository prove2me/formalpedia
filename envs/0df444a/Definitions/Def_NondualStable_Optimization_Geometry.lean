-- Prove2me | Definitions.Def_NondualStable_Optimization_Geometry
-- name    : NondualStable_Optimization_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:34.48296+00:00
-- url     : https://prove2.me/theorems/38e20b3f-9ff1-4c53-862f-ad16b356be1c
-- title:
--   Coordinate geometry, nested requests and uniform complexity profiles
-- statement:
--   Let $d$ be the dimension, let $a\in[1,\infty]$ be a norm exponent, and let $R\ge0$ be a radius. The coordinate space is $\mathbb R^d$, with its usual finite-dimensional topology and the standard $\ell_a$ norm. The closed feasible ball and movement of a path $z^0,\ldots,z^H$ are
--   $$X=\{x:\|x\|_p\le R\},\qquad \operatorname{Mov}_q(z)=\sum_{t<H}\|z^{t+1}-z^t\|_q.$$
--   Requests are nonempty compact convex subsets of $X$ and are nested. An objective is globally convex and globally $G$-Lipschitz in $\ell_q$. A minimum is represented by an attained value together with the lower-bound inequality against every feasible point. The rate is $\rho=1/p-(1/q-1/2)_+$. Threshold heads and the radii $R H^{1/a-1/p}$ are computed from their inputs.
--
--   These interfaces separate the general geometry from the source-specific center and algorithm. The uniform logarithmic profiles use $D(d,u)=1+\log(2d+2)+\log(2+u)$; no polynomial factor in dimension occurs in the error profile.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 5/PDF p. 6, Section 2; printed p. 9/PDF p. 10, Lemma 8; printed pp. 27–28/PDF pp. 28–29, Appendices F–G

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Local notation for the published, Mathlib-based finite-dimensional lp norm.
Only exponents at least one occur in source statements. -/
noncomputable abbrev lpNorm {d : ℕ} (p : ℝ≥0∞) (x : Vec d) : ℝ :=
  RegimeDRCVaR.normM p x

noncomputable def recip (p : ℝ≥0∞) : ℝ := p⁻¹.toReal

noncomputable def dual (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

def ball {d : ℕ} (p : ℝ≥0∞) (R : ℝ) : Set (Vec d) :=
  {x | lpNorm p x ≤ R}

def admissible (p q : ℝ≥0∞) : Prop := 1 ≤ p ∧ p ≤ q ∧ p ≤ 2 ∧ 1 < q

noncomputable def rate (p q : ℝ≥0∞) : ℝ :=
  recip p - max (recip q - 1 / 2) 0

def Objective {d : ℕ} (q : ℝ≥0∞) (G : ℝ) (f : Vec d → ℝ) : Prop :=
  ConvexOn ℝ Set.univ f ∧ ∀ x y, |f x - f y| ≤ G * lpNorm q (x - y)

def Body {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (K : Set (Vec d)) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧ K ⊆ ball p R

def Nested {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : ℕ → Set (Vec d)) : Prop :=
  (∀ t ≤ H, Body p R (K t)) ∧ ∀ t < H, K (t + 1) ⊆ K t

noncomputable def movement {d : ℕ} (q : ℝ≥0∞) (H : ℕ) (z : ℕ → Vec d) : ℝ :=
  ∑ t ∈ Finset.range H, lpNorm q (z (t + 1) - z t)

/-- An attained-minimum relation avoids a real infimum's value on bad input. -/
def Minimum {d : ℕ} (X : Set (Vec d)) (f : Vec d → ℝ) (v : ℝ) : Prop :=
  (∃ x ∈ X, f x = v) ∧ ∀ x ∈ X, v ≤ f x

noncomputable def head {d : ℕ} (p : ℝ≥0∞) (R : ℝ) (H : ℕ) (x : Vec d) : Vec d :=
  fun i => if R * (H : ℝ) ^ (-recip p) < |x i| then x i else 0

noncomputable def radius (p s : ℝ≥0∞) (R : ℝ) (H : ℕ) : ℝ :=
  R * (H : ℝ) ^ (recip s - recip p)

noncomputable def logFactor (d : ℕ) (a : ℝ) : ℝ :=
  1 + Real.log (2 * (d : ℝ) + 2) + Real.log (2 + a)

noncomputable def oracleBudget (B : ℝ) (j : ℕ) (ρ : ℝ)
    (d : ℕ) (G R ε : ℝ) : ℝ :=
  B * (1 + (G * R / ε) ^ (1 / ρ)) * (logFactor d (G * R / ε)) ^ j

noncomputable def errorBudget (B : ℝ) (j : ℕ) (ρ : ℝ)
    (d T : ℕ) (G R : ℝ) : ℝ :=
  B * G * R * (T : ℝ) ^ (-ρ) * (logFactor d T) ^ j

end NondualStable.Optimization


