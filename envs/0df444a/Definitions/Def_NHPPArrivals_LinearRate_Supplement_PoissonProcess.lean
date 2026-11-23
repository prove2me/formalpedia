-- Prove2me | Definitions.Def_NHPPArrivals_LinearRate_Supplement_PoissonProcess
-- name    : NHPPArrivals_LinearRate_Supplement_PoissonProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:05:26.133461+00:00
-- url     : https://prove2.me/theorems/b4087ea9-5dd7-4c1a-baa3-96461cdea6fd
-- title:
--   Finite simple arrival processes and independent Poisson increments (§3.2)
-- statement:
--   On a probability space $(\Omega,\mathcal F,P)$, a finite arrival process on $[0,T]$ consists of counts $N(t)$ and measurable epochs $X_1,X_2,\ldots$. On one common event of probability one, the observed epochs are strictly increasing in $(0,T]$, and
--   $$N(t)=\#\{j\le N(T):X_j\le t\},\qquad 0\le t\le T.$$
--   It is a nonhomogeneous Poisson process of rate $\lambda$ when the increments over every finite collection of disjoint intervals $(u_i,v_i]\subseteq[0,T]$ have joint law
--   $$P\{N(v_i)-N(u_i)=q_i\text{ for all }i\}=\prod_i e^{-m_i}m_i^{q_i}/q_i!,\qquad m_i=\int_{u_i}^{v_i}\lambda(s)\,ds.$$
--   This definition is independent of the paper's regularity assumptions and does not assume any conditional arrival law. Those assumptions are supplied separately by AdmissibleRate. The epochs are indexed from zero in Lean; unused epochs are immaterial.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, §3.2, standing NHPP model before (4)

import Mathlib

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory ProbabilityTheory

/-- A finite simple arrival process on [0,T], with its epochs indexed from zero.
Unused epochs after the last arrival have no effect. The path identities hold on one
common full-measure set, not on a time-dependent exceptional set. -/
def IsArrivalProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ℝ) (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (N t)) ∧
  (∀ j, Measurable (X j)) ∧
  ∀ᵐ ω ∂P,
    (∀ i j : ℕ, i < j → j < N T ω → X i ω < X j ω) ∧
    (∀ i : ℕ, i < N T ω → X i ω ∈ Set.Ioc (0 : ℝ) T) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      N t ω = ((Finset.range (N T ω)).filter (fun j => X j ω ≤ t)).card)

/-- NHPP: the counting paths above and the independent Poisson increment laws
on every finite family of disjoint intervals (u_i,v_i] inside [0,T].
No conditional arrival law is postulated here. -/
def IsNHPP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : ℝ → ℝ) (T : ℝ) (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  IsArrivalProcess P T N X ∧
  ∀ (m : ℕ) (u v : Fin m → ℝ) (q : Fin m → ℕ),
    (∀ i, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ T) →
    (∀ i j, i ≠ j → v i ≤ u j ∨ v j ≤ u i) →
    P {ω | ∀ i, N (v i) ω - N (u i) ω = q i} =
      ∏ i, poissonMeasure (Real.toNNReal (∫ s in u i..v i, lam s)) {q i}

end NHPPArrivals.LinearRate.Supplement


