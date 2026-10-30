-- Prove2me | Definitions.Def_BSSSampleRobust_Asymptotic_Policy
-- name    : BSSSampleRobust_Asymptotic_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:26:01.790833+00:00
-- url     : https://prove2.me/theorems/5234b9d3-8e2f-4939-b4e8-e97072b6474a
-- title:
--   Measurable multistage mixed-integer history policies
-- statement:
--   A finite horizon $T\ge1$ has stage uncertainty dimensions $d_t$ with positive total dimension, real decision dimensions $n_t$, and integer suffix sizes $0\le p_t\le n_t$. Trajectories are finite $\ell_p$ coordinate spaces, with coordinates labeled by stage and within-stage index. The history at stage $t$ contains precisely the coordinates at stages strictly before $t$. A policy is an arbitrary Borel measurable map at each stage from this history to the real decision space, with its last $p_t$ coordinates equal to integers. The integral suffix is the embedded $\mathbb Z^{p_t}$ block. First-stage histories are singletons; zero-sized stage uncertainty or decision blocks are allowed. This general policy object contains no affine data, distribution assumptions, or optimization guarantees.
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; §§1.2–2, PDF/printed 6–7

import Mathlib

open MeasureTheory

open scoped ENNReal Classical

namespace BSSSampleRobust.Asymptotic

/-- A finite real coordinate space with its chosen lp norm and Borel sigma algebra. -/
abbrev Vec (p : ℝ≥0∞) (ι : Type) := PiLp p (fun _ : ι => ℝ)

instance vecMeasurableSpace (p : ℝ≥0∞) (ι : Type) : MeasurableSpace (Vec p ι) :=
  borel (Vec p ι)

instance vecBorelSpace (p : ℝ≥0∞) (ι : Type) : BorelSpace (Vec p ι) := ⟨rfl⟩

/-- Dimensions for a finite horizon, including the integer suffix of each decision. -/
structure Layout where
  T : ℕ
  positive_horizon : 0 < T
  d : Fin T → ℕ
  n : Fin T → ℕ
  integerCount : Fin T → ℕ
  integer_le : ∀ t, integerCount t ≤ n t
  positive_dimension : 0 < ∑ t, d t

abbrev Coord (D : Layout) := (t : Fin D.T) × Fin (D.d t)
abbrev Path (p : ℝ≥0∞) (D : Layout) := Vec p (Coord D)
abbrev History (D : Layout) (t : Fin D.T) :=
  {i : Coord D // i.1 < t} → ℝ
abbrev Decision (p : ℝ≥0∞) (D : Layout) (t : Fin D.T) := Vec p (Fin (D.n t))

def historyOf {p : ℝ≥0∞} {D : Layout} (t : Fin D.T) (z : Path p D) : History D t :=
  fun i => z i.1

/-- All Borel measurable history policies, with the last integerCount coordinates integral. -/
structure Policy (p : ℝ≥0∞) (D : Layout) where
  act : (t : Fin D.T) → History D t → Decision p D t
  measurable_act : ∀ t, Measurable (act t)
  integer_act : ∀ t h (i : Fin (D.n t)),
    D.n t - D.integerCount t ≤ i.val → ∃ k : ℤ, act t h i = (k : ℝ)

end BSSSampleRobust.Asymptotic


