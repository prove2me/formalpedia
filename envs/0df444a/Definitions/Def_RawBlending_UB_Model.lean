-- Prove2me | Definitions.Def_RawBlending_UB_Model
-- name    : RawBlending_UB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:26.164549+00:00
-- url     : https://prove2.me/theorems/18651d9d-0877-4679-984e-03fb760d49d0
-- title:
--   §3 model: two-material dynamic program and standing assumptions
-- statement:
--   The model has two raw materials, periods $t=1,\ldots,T$, conversion rates $0<a^1<a^2$, and finite laws for demand and capacity $(D_t,R_t)$ and the two independent material availabilities $q_t^1,q_t^2$. Availability may be infinite. For inventory $y\in\mathbb R_+^2$, the feasible postproduction set is
--   $$
--   E_2(y,D,R)=\{w\in\mathbb R_+^2: w\le y,\ a^1w^1+a^2w^2\ge a^1y^1+a^2y^2-D,\ w^1+w^2\ge y^1+y^2-R\}.
--   $$
--   The cost recursion defines $J_t$ from $V_{t+1}$, minimizes $J_t$ over $E_2$ to obtain $U_t$, averages it in $\bar G_t$ and $G_t$, and minimizes over orders to obtain $V_t$. The terminal cost is $V_{T+1}(x)=c^1_{T+1}x^1+c^2_{T+1}x^2$. The predicate $H_t$ records convexity, continuity, supermodularity, and coordinatewise lower growth of $V_{t+1}$.
--
--   This file fixes the model shared by the main theorem and its dynamic-programming milestones.
--
--   **Formalization Note** Expectations are finite sums. Minima are written as real infima before attainment is proved. The standing predicate makes explicit nonnegative revenues and holding and purchase costs, strictly positive $c_t^j+h_t^j$, positive conversion rates, and $T>0$.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), §3, pp. 6–10 (PDF 6–10), equations (1)–(7), H_t

import Mathlib
import Definitions.Def_RawBlending_UB_FinLaw
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

noncomputable section
open Filter

namespace RawBlending.UB

abbrev Vec := ℝ × ℝ
def orthant : Set Vec := {x | 0 ≤ x}

/-- All deterministic data and period laws of the two-material model. -/
structure Data where
  T : ℕ
  a1 : ℝ
  a2 : ℝ
  e : ℕ → ℝ
  σ : ℕ → ℝ
  h1 : ℕ → ℝ
  h2 : ℕ → ℝ
  c1 : ℕ → ℝ
  c2 : ℕ → ℝ
  DR : ℕ → FinLaw (ℝ × ℝ)
  qq1 : ℕ → FinLaw (WithTop ℝ)
  qq2 : ℕ → FinLaw (WithTop ℝ)

def Data.Standing (d : Data) : Prop :=
  0 < d.T ∧ 0 < d.a1 ∧ d.a1 < d.a2 ∧
  (∀ t, 1 ≤ t → t ≤ d.T →
    0 < d.σ t ∧ 0 ≤ d.e t ∧ 0 ≤ d.h1 t ∧ 0 ≤ d.h2 t ∧
    0 < d.c1 t + d.h1 t ∧ 0 < d.c2 t + d.h2 t ∧
    (d.DR t).IsProb ∧
    (∀ z ∈ (d.DR t).supp, 0 ≤ z.1 ∧ 0 ≤ z.2) ∧
    (d.qq1 t).IsProb ∧ (d.qq2 t).IsProb ∧
    (∀ q ∈ (d.qq1 t).supp, (0 : WithTop ℝ) ≤ q) ∧
    (∀ q ∈ (d.qq2 t).supp, (0 : WithTop ℝ) ≤ q)) ∧
  (∀ t, 1 ≤ t → t ≤ d.T + 1 → 0 ≤ d.c1 t ∧ 0 ≤ d.c2 t)

def p (d : Data) (t : ℕ) : ℝ := d.e t + d.σ t

/-- Delivered inventory, allowing unlimited availability. -/
def capAt (y x : ℝ) : WithTop ℝ → ℝ
  | ⊤ => y
  | (r : ℝ) => min y (x + r)

def E1 (x : Vec) (M : ℝ) : Set Vec :=
  {y | 0 ≤ y ∧ x ≤ y ∧ y.1 ≤ max x.1 M ∧ y.2 ≤ max x.2 M}

def E2 (a1 a2 : ℝ) (y : Vec) (D R : ℝ) : Set Vec :=
  {w | 0 ≤ w ∧ w ≤ y ∧
    a1 * y.1 + a2 * y.2 - D ≤ a1 * w.1 + a2 * w.2 ∧
    y.1 + y.2 - R ≤ w.1 + w.2}

def Minimizes (f : Vec → ℝ) (S : Set Vec) (x : Vec) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

def Jstep (d : Data) (t : ℕ) (Vnext : Vec → ℝ) (w : Vec) : ℝ :=
  (d.a1 * p d t + d.h1 t - d.c1 (t+1)) * w.1 +
  (d.a2 * p d t + d.h2 t - d.c2 (t+1)) * w.2 + Vnext w

def Ustep (d : Data) (t : ℕ) (Vnext : Vec → ℝ) (y : Vec) (D R : ℝ) : ℝ :=
  sInf (Jstep d t Vnext '' E2 d.a1 d.a2 y D R)

def Gbarstep (d : Data) (t : ℕ) (Vnext : Vec → ℝ) (y : Vec) : ℝ :=
  (d.c1 t - d.a1 * p d t) * y.1 + (d.c2 t - d.a2 * p d t) * y.2 +
  (d.DR t).expect (fun z => Ustep d t Vnext y z.1 z.2 + d.σ t * z.1)

def Gstep (d : Data) (t : ℕ) (Vnext : Vec → ℝ) (y x : Vec) : ℝ :=
  (d.qq1 t).expect (fun q1 =>
    (d.qq2 t).expect (fun q2 =>
      Gbarstep d t Vnext (capAt y.1 x.1 q1, capAt y.2 x.2 q2)))

def Vstep (d : Data) (t : ℕ) (Vnext : Vec → ℝ) (x : Vec) : ℝ :=
  sInf ((fun y => Gstep d t Vnext y x) '' {y : Vec | x ≤ y})

def boundary (d : Data) (x : Vec) : ℝ :=
  d.c1 (d.T+1) * x.1 + d.c2 (d.T+1) * x.2

/-- Backward recursion indexed by the number of periods remaining. -/
def Vtg (d : Data) : ℕ → Vec → ℝ
  | 0 => boundary d
  | k+1 => Vstep d (d.T-k) (Vtg d k)

def V (d : Data) (t : ℕ) : Vec → ℝ := Vtg d (d.T+1-t)
def J (d : Data) (t : ℕ) : Vec → ℝ := Jstep d t (V d (t+1))
def U (d : Data) (t : ℕ) (y : Vec) (D R : ℝ) : ℝ := Ustep d t (V d (t+1)) y D R
def Gbar (d : Data) (t : ℕ) : Vec → ℝ := Gbarstep d t (V d (t+1))
def G (d : Data) (t : ℕ) (y x : Vec) : ℝ := Gstep d t (V d (t+1)) y x

/-- The two coordinatewise lower growth bounds used in H_t. -/
def LowerGrowth (f : Vec → ℝ) (b1 b2 : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∀ v : ℝ, 0 ≤ v →
    ∀ᶠ s : ℝ in atTop, b1 - ε ≤ f (s, v) / s) ∧
  (∀ ε : ℝ, 0 < ε → ∀ v : ℝ, 0 ≤ v →
    ∀ᶠ s : ℝ in atTop, b2 - ε ≤ f (v, s) / s)

def Shape (f : Vec → ℝ) : Prop :=
  ConvexOn ℝ orthant f ∧ ContinuousOn f orthant ∧
  Supermodularity.Monotonicity.SupermodularOn f orthant

def H (d : Data) (t : ℕ) : Prop :=
  Shape (V d (t+1)) ∧ LowerGrowth (V d (t+1)) (d.c1 (t+1)) (d.c2 (t+1))

def IsJClass (f : Vec → ℝ) : Prop :=
  Shape f ∧
  (∀ v : ℝ, 0 ≤ v → Tendsto (fun s : ℝ => f (s, v)) atTop atTop) ∧
  (∀ v : ℝ, 0 ≤ v → Tendsto (fun s : ℝ => f (v, s)) atTop atTop)

end RawBlending.UB


