-- Prove2me | Definitions.Def_NondualStable_Optimization_GaussianCenter
-- name    : NondualStable_Optimization_GaussianCenter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:10.963369+00:00
-- url     : https://prove2.me/theorems/940ff5f5-0840-4a95-8560-27a5bac15bfb
-- title:
--   Lifted Gaussian center and quantitative movement and sample profiles
-- statement:
--   Fix $1\le p\le\min\{q,2\}$ with $q>1$, a positive radius $R$, a positive integer horizon $H$, and a nonempty compact convex body $K\subseteq R B_p^d$. Put $r=\min\{q,2\}$, $L_d=\lceil\log(2d+2)\rceil$, $s=1+1/L_d$, $R_a=R H^{1/a-1/p}$, $\mu=R_r^2/R_1^2$, and $\eta=R_r^2/(R_1\sqrt{L_d})$. Define
--   $$\mathcal L(K)=\{(u,v):u+v\in K,\ \|u\|_1\le R_1,\ \|v\|_r\le R_r\},\quad F^g(u,v)=\tfrac12\|v\|_r^2+\tfrac\mu2\|u\|_s^2-\eta\langle g,u\rangle.$$
--   The sample is the sum of the minimizing components; the reference center is its standard Gaussian expectation. Value increments are differences between the computed optimal values on consecutive requests. Existence, uniqueness, measurability, integrability and center feasibility form an explicit conclusion predicate; none is assumed by a data structure.
--
--   The module also defines the movement profile, sample threshold and sufficient objective tolerance from (17), (36) and (39). The selected optimizer defaults to zero only when no optimizer exists. The mathematical theorems establish that this branch is unavailable on valid inputs. The reference minimizer and expectation are analysis objects, with no machine instruction granting them unit cost.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed pp. 9–10/PDF pp. 10–11, equations (10)–(14); printed p. 11/PDF p. 12, (17); printed pp. 20–22/PDF pp. 21–23, (27)–(33); printed pp. 25,27/PDF pp. 26,28, (36),(39)

import Definitions.Def_NondualStable_Optimization_Geometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

noncomputable def gaussian (d : ℕ) : Measure (Vec d) :=
  Measure.pi (fun _ => gaussianReal 0 1)

noncomputable def L (d : ℕ) : ℝ := ⌈Real.log (2 * (d : ℝ) + 2)⌉₊

noncomputable def tailExponent (q : ℝ≥0∞) : ℝ≥0∞ := min q 2

noncomputable def headExponent (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 + 1 / L d)

noncomputable def mu (p q : ℝ≥0∞) (R : ℝ) (H : ℕ) : ℝ :=
  (radius p (tailExponent q) R H) ^ 2 / (radius p 1 R H) ^ 2

noncomputable def eta (p q : ℝ≥0∞) (d : ℕ) (R : ℝ) (H : ℕ) : ℝ :=
  (radius p (tailExponent q) R H) ^ 2 / (radius p 1 R H * Real.sqrt (L d))

def lift {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) : Set (Vec d × Vec d) :=
  {w | w.1 + w.2 ∈ K ∧ lpNorm 1 w.1 ≤ radius p 1 R H ∧
    lpNorm (tailExponent q) w.2 ≤ radius p (tailExponent q) R H}

noncomputable def potential {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (g : Vec d) (w : Vec d × Vec d) : ℝ :=
  (lpNorm (tailExponent q) w.2) ^ 2 / 2 +
    mu p q R H / 2 * (lpNorm (headExponent d) w.1) ^ 2 - eta p q d R H * dotProduct g w.1

def Optimizer {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) (g : Vec d) (w : Vec d × Vec d) : Prop :=
  w ∈ lift p q R H K ∧ ∀ w' ∈ lift p q R H K,
    potential p q R H g w ≤ potential p q R H g w'

/-- A minimizer is selected only if one exists; zero is the off-domain default.
Uniqueness, measurability and integrability are theorem conclusions, never fields. -/
noncomputable def optimizer {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) (g : Vec d) : Vec d × Vec d := by
  classical
  exact if h : ∃ w, Optimizer p q R H K g w then Classical.choose h else (0, 0)

noncomputable def sample {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) (g : Vec d) : Vec d :=
  (optimizer p q R H K g).1 + (optimizer p q R H K g).2

noncomputable def center {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) : Vec d := ∫ g, sample p q R H K g ∂gaussian d

def CenterWellDefined {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) : Prop :=
  (lift p q R H K).Nonempty ∧
  (∀ g, ∃! w, Optimizer p q R H K g w) ∧
  Measurable (optimizer p q R H K) ∧
  Integrable (sample p q R H K) (gaussian d) ∧ center p q R H K ∈ K

noncomputable def value {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : Set (Vec d)) (g : Vec d) : ℝ :=
  potential p q R H g (optimizer p q R H K g)

noncomputable def increment {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : ℕ → Set (Vec d)) (t : ℕ) (g : Vec d) : ℝ :=
  value p q R H (K (t + 1)) g - value p q R H (K t) g

noncomputable def totalIncrement {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H : ℕ)
    (K : ℕ → Set (Vec d)) (g : Vec d) : ℝ :=
  ∑ t ∈ Finset.range H, increment p q R H K t g

noncomputable def movementProfile (C : ℝ) (p q : ℝ≥0∞) (d : ℕ) (R : ℝ) (H : ℕ) : ℝ :=
  C * R * (H : ℝ) ^ (1 - rate p q) *
    (1 + Real.sqrt (L d) * (Real.log (2 * (H : ℝ))) ^ (1 - recip (tailExponent q)))

noncomputable def sampleCount (q : ℝ≥0∞) (R E : ℝ) (H : ℕ) (δ : ℝ) : ℝ :=
  let r := (tailExponent q).toReal
  max ((4 : ℝ) ^ (r / (r - 1))) 8 *
    ((R / E) ^ (r / (r - 1)) + (R / E) ^ 2 * Real.log ((H + 1 : ℕ) / δ))

noncomputable def solverTolerance (p q : ℝ≥0∞) (d : ℕ) (R E : ℝ) (H : ℕ) : ℝ :=
  E ^ 2 * min ((Real.exp (-2) / 2) * mu p q R H / (4 * L d))
    (((tailExponent q).toReal - 1) / 8)

end NondualStable.Optimization


