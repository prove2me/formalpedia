-- Prove2me | Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm
-- name    : ZonotopeContainment_AdaptiveSampling_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:17.695449+00:00
-- url     : https://prove2.me/theorems/e2807d0c-f98c-4044-84b7-a300f69a4fbf
-- title:
--   Algorithm 1 and its independent Gaussian tapes
-- statement:
--   Fix a real constant $C$ and dimension $d$. Write $q(t)=1/\max\{1,|t|\}$, $\lambda_j=\log(d)/2^j$, and let $R$ be the first index with $\lambda_R<1$. For the theorem's $d\ge3$, a run executes exactly $j=0,\ldots,R-1$.
--
--   Given generators $w$ and a map $T$, start at $v_i=Tw_i$ and $A=T^{-1}$. At a draw $z$ and current scale $\lambda$, set
--   $$t_i=\frac{\langle z,v_i\rangle}{C\lambda\|v_i\|},\quad r_i=q(t_i),\quad S=\sum_i\frac{r_i v_i v_i^\top}{\|v_i\|},\quad x=\sum_i t_i r_i v_i.$$
--   Record $x_{\mathrm{orig}}=Ax$ before updating $v_i\leftarrow r_iS^{-1/2}v_i$ and $A\leftarrow AS^{1/2}$. Here $S^{1/2}$ is the canonical positive semidefinite matrix square root and $S^{-1/2}$ its inverse. A zero generator has $t_i=0$ and $r_i=1$ and remains zero.
--
--   A run is a deterministic recursion in its $R$ draws. The one-run law is the product of $R$ standard Gaussian vector laws, and the $N$-run law is the product of $N$ one-run laws; every run uses the same $T$. Both laws are registered as probability measures (instances proved in the file). The containment test reports inclusion exactly when every recorded point of every run belongs to $Q$.
--
--   The definitions assume neither matrix invertibility at later steps nor output feasibility: these are the feasibility theorem's conclusions. Outside the executed indices the state is frozen, which supplies a total state function without recording additional points.
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), §2.1 and Algorithm 1, pp. 5–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Geometry

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder Pointwise

namespace ZonotopeContainment.AdaptiveSampling

/-- The specific weight in §2.1, not a variant from §2.3. -/
def q (t : ℝ) : ℝ := 1 / max 1 |t|

def scale (d j : ℕ) : ℝ := Real.log d / (2 : ℝ) ^ j

/-- First j for which lam_j < 1; thus the executed indices are precisely j < rounds d. -/
def rounds (d : ℕ) : ℕ := Nat.find (show ∃ j : ℕ, scale d j < 1 from by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (Real.log d) (by norm_num : (1 : ℝ) < 2)
  exact ⟨j, (div_lt_one (by positivity : 0 < (2 : ℝ) ^ j)).2 hj⟩)

structure State (d n : ℕ) where
  v : Fin n → E d
  A : Mat d

def projections {d n : ℕ} (C lam : ℝ) (v : Fin n → E d) (z : E d) (i : Fin n) : ℝ :=
  inner ℝ z (v i) / (C * lam * ‖v i‖)

def weights {d n : ℕ} (C lam : ℝ) (v : Fin n → E d) (z : E d) (i : Fin n) : ℝ :=
  q (projections C lam v z i)

/-- Weighted Lewis matrix S, with the weights evaluated before the update. -/
def weightedMatrix {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) : Mat d :=
  ∑ i, (r i / ‖v i‖) • rankOne (v i)

def localPoint {d n : ℕ} (C lam : ℝ) (v : Fin n → E d) (z : E d) : E d :=
  ∑ i, (projections C lam v z i * weights C lam v z i) • v i

/-- S^{-1/2} is the inverse of the canonical PSD square root, not a chosen factorization. -/
def updatedGenerators {d n : ℕ} (v : Fin n → E d) (r : Fin n → ℝ) : Fin n → E d :=
  fun i => r i • act ((CFC.sqrt (weightedMatrix v r))⁻¹) (v i)

def step {d n : ℕ} (C lam : ℝ) (s : State d n) (z : E d) : State d n :=
  let r := weights C lam s.v z
  { v := updatedGenerators s.v r
    A := s.A * CFC.sqrt (weightedMatrix s.v r) }

abbrev Tape (d : ℕ) := Fin (rounds d) → E d

/-- The state at j, frozen once the while loop terminates. -/
def runState {d n : ℕ} (C : ℝ) (w : Fin n → E d) (T : Mat d) (z : Tape d) :
    ℕ → State d n
  | 0 => { v := fun i => act T (w i), A := T⁻¹ }
  | j + 1 => if h : j < rounds d then
      step C (scale d j) (runState C w T z j) (z ⟨j, h⟩)
    else runState C w T z j

/-- Record using the current A and v, before step is applied. -/
def recorded {d n : ℕ} (C : ℝ) (w : Fin n → E d) (T : Mat d) (z : Tape d)
    (j : Fin (rounds d)) : E d :=
  let s := runState C w T z j
  act s.A (localPoint C (scale d j) s.v (z j))

def runLaw (d : ℕ) : Measure (Tape d) :=
  Measure.pi (fun _ : Fin (rounds d) => stdGaussian (E d))

instance runLaw_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (runLaw d) := by
  unfold runLaw; infer_instance

abbrev Tapes (d N : ℕ) := Fin N → Tape d

def runsLaw (d N : ℕ) : Measure (Tapes d N) :=
  Measure.pi (fun _ : Fin N => runLaw d)

instance runsLaw_isProbabilityMeasure (d N : ℕ) : IsProbabilityMeasure (runsLaw d N) := by
  unfold runsLaw; infer_instance

/-- Exact membership testing: inclusion is reported iff all recorded points are accepted. -/
def reportsInclusion {d n N : ℕ} (C : ℝ) (w : Fin n → E d) (T : Mat d)
    (Q : Set (E d)) (z : Tapes d N) : Prop :=
  ∀ k j, recorded C w T (z k) j ∈ Q

end ZonotopeContainment.AdaptiveSampling


