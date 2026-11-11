-- Prove2me | Definitions.Def_TsybakovLearning_OptimalERM_Bounds
-- name    : TsybakovLearning_OptimalERM_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:54.738281+00:00
-- url     : https://prove2.me/theorems/075c4eb8-7ffb-4ff5-9ccc-815f4b2a8926
-- title:
--   Clipped logarithm, exact bounds, and simultaneous failure events
-- statement:
--   Throughout the upper-bound results use $L(x)=\log_2(\max\{x,2\})$, so $L(0)=L(1)=1$. For dimension $d$, sample size $m>0$, region mass $p$, disagreement mass $q$, and $0<\delta<1$, set
--
--   $$A=dL\!\left(\frac pq\wedge\frac{mp}d\right)+L(1/\delta),\qquad B_2=c\sqrt{qA/m}+cA/m.$$
--
--   The undefined ratios in the printed display are read with the finite-cap limiting convention: at $d=0$ the entire $dL$ term is zero; at $d>0,q=0$ it is $dL(mp/d)$. In particular, when $p=q=0$ it is $d$, and the square-root term is zero.
--
--   The other exact numerical expressions are
--
--   $$B_3=16c\left[\sqrt{\frac{a\gamma^\alpha(d+L(1/\delta))}{(1-\alpha)m}}+\frac{d+L(1/\delta)}{(1-\alpha)m}\bigl(1+L(a)+(1-\alpha)L(1/\gamma)\bigr)^2\right],$$
--   $$B_1=C\left[\frac{a(d+L(1/\delta))}{(1-\alpha)n}\right]^{1/(2-\alpha)},\qquad C(c)=4096c^2+192c+1.$$
--
--   A Bernstein failure sample admits some pair $f,g\in H$ whose absolute restricted population-minus-empirical difference exceeds $B_2$. A small-excess failure sample admits some $h\in H$ with population excess at most $\gamma$ and empirical-minus-population excess deviation greater than $B_3$. An ERM failure sample admits some actual empirical minimizer with excess greater than $B_1$. Each is a single event, retaining all pairs or hypotheses simultaneously. Tail events with arbitrary thresholds are also named so measurability can be stipulated independently of the numerical witnesses.
--
--   These definitions abbreviate expressions and events; they assert no probability estimates. Real powers and square roots are used only with the theorem's positive denominators and nonnegative probability masses.
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), §2 and Theorem 1, p. 5 (PDF p. 5); Lemmas 2–3, pp. 5–6 (PDF pp. 5–6); Theorem 2, p. 9 (PDF p. 9)

import Definitions.Def_TsybakovLearning_OptimalERM_NoiseModel

open MeasureTheory

namespace TsybakovLearning.OptimalERM

/-- The upper-bound convention on p. 5, including L(0)=L(1)=1. -/
noncomputable def clippedLog (x : ℝ) : ℝ := Real.log (max x 2) / Real.log 2

/-- The capped extended-ratio reading, without ever dividing by q=0 or d=0. -/
noncomputable def complexity (d m : ℕ) (p q δ : ℝ) : ℝ :=
  (if d = 0 then 0 else
    (d : ℝ) * clippedLog (if q = 0 then (m : ℝ) * p / d
      else min (p / q) ((m : ℝ) * p / d))) + clippedLog (1 / δ)

noncomputable def bernsteinBound (c : ℝ) (d m : ℕ) (p q δ : ℝ) : ℝ :=
  c * Real.sqrt (q * complexity d m p q δ / m) + c * complexity d m p q δ / m

noncomputable def smallExcessBound (c a α γ δ : ℝ) (d m : ℕ) : ℝ :=
  16 * c * (Real.sqrt (a * γ ^ α * ((d : ℝ) + clippedLog (1 / δ)) / ((1 - α) * m)) +
    (((d : ℝ) + clippedLog (1 / δ)) / ((1 - α) * m)) *
      (1 + clippedLog a + (1 - α) * clippedLog (1 / γ)) ^ 2)

noncomputable def ermBound (C a α δ : ℝ) (d n : ℕ) : ℝ :=
  C * (a * ((d : ℝ) + clippedLog (1 / δ)) / ((1 - α) * n)) ^ (1 / (2 - α))

/-- Theorem 2's constant provenance; the goal only asserts the numerical existence of C. -/
def explicitConstant (c : ℝ) : ℝ := 4096 * c ^ 2 + 192 * c + 1

variable {X : Type*} [MeasurableSpace X]

def bernsteinFailure (c : ℝ) (H : Set (X → Bool)) (D : Measure (X × Bool))
    (Δ : Set X) (d m : ℕ) (δ : ℝ) : Set (Fin m → X × Bool) :=
  {S | ∃ f ∈ H, ∃ g ∈ H,
    bernsteinBound c d m (regionMass D Δ) (disagreement D Δ f g) δ <
      |(restrictedRisk D Δ f - restrictedRisk D Δ g) -
        (restrictedEmpRisk Δ S f - restrictedEmpRisk Δ S g)|}

def smallExcessTail (H : Set (X → Bool)) (D : Measure (X × Bool))
    (R : Regression D) (γ : ℝ) (m : ℕ) (t : ℝ) : Set (Fin m → X × Bool) :=
  {S | ∃ h ∈ H, risk D h - risk D (bayes R) ≤ γ ∧
    t < |empRisk S h - empRisk S (bayes R) - risk D h + risk D (bayes R)|}

def smallExcessFailure (c : ℝ) (H : Set (X → Bool)) (D : Measure (X × Bool))
    (R : Regression D) (a α γ δ : ℝ) (d m : ℕ) : Set (Fin m → X × Bool) :=
  smallExcessTail H D R γ m (smallExcessBound c a α γ δ d m)

def ermTail (H : Set (X → Bool)) (D : Measure (X × Bool))
    (R : Regression D) (n : ℕ) (t : ℝ) : Set (Fin n → X × Bool) :=
  {S | ∃ h : X → Bool, IsERM H S h ∧ t < risk D h - risk D (bayes R)}

def ermFailure (C : ℝ) (H : Set (X → Bool)) (D : Measure (X × Bool))
    (R : Regression D) (a α δ : ℝ) (d n : ℕ) : Set (Fin n → X × Bool) :=
  ermTail H D R n (ermBound C a α δ d n)

end TsybakovLearning.OptimalERM


