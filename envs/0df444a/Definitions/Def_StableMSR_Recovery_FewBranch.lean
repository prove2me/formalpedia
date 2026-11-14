-- Prove2me | Definitions.Def_StableMSR_Recovery_FewBranch
-- name    : StableMSR_Recovery_FewBranch
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T15:09:41.446218+00:00
-- url     : https://prove2.me/theorems/357e2fdf-2dbc-4ec1-8b70-aca3949db44c
-- title:
--   Bounded large-cluster enumeration and feasibility-checked selection
-- statement:
--   Fix a metric array $d$, a stability parameter $1<\gamma<2$, and a bound $B$ on the number of large clusters. For each guessed radius $R=d(c,x)$, represent a candidate by an input-distance ball $C=B_d(a,d(a,b))$. Retain it precisely when its represented radius and its optimal discrete-center radius both lie in $[(\gamma-1)R/4,R]$ and expanding the represented radius by $\gamma$ preserves the ball.
--
--   Enumerate pairwise disjoint families of at most $B$ retained representations. Complete a family with all global threshold components at distance threshold $(\gamma-1)R/2$ that are disjoint from its union. Take the union of these completed outputs over all input-distance guesses. Starting with a feasible partition, scan these outputs and replace the current answer only when the candidate is feasible and has strictly smaller sum of radii.
--
--   The global-component completion is a feasibility-checked variant of the paper's residual-component computation. At the true family of large clusters, Lemma 3.8 makes the two completions equal. Other enumerated outputs may be infeasible and are explicitly rejected.
--
--   These are finite algorithm specifications. The powerset filter denotes the bounded family; a separate theorem supplies an equivalent enumeration by fixed-length option tuples. No interpreter runtime is asserted by this definition.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Equation (1), Algorithm 1 Branch A, and Appendix A.5. The feasibility-checked global-component variant has the same true-family completion by Lemma 3.8.

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.CandidateAux

noncomputable def represented {n : ℕ} (d : Point n → Point n → ℝ)
    (q : Point n × Point n) : Cluster n := ball d q.1 (d q.1 q.2)

noncomputable def representations {n : ℕ} (d : Point n → Point n → ℝ)
    (γ R : ℝ) : Finset (Point n × Point n) :=
  Finset.univ.filter (fun q =>
    (γ - 1) * R / 4 ≤ d q.1 q.2 ∧ d q.1 q.2 ≤ R ∧
    (γ - 1) * R / 4 ≤ radius d (represented d q) ∧
    radius d (represented d q) ≤ R ∧
    represented d q = ball d q.1 (γ * d q.1 q.2))

noncomputable def families {n : ℕ} (d : Point n → Point n → ℝ)
    (γ R : ℝ) (budget : ℕ) : Finset (Finset (Point n × Point n)) :=
  (representations d γ R).powerset.filter (fun Q => Q.card ≤ budget ∧
    (Q : Set (Point n × Point n)).Pairwise (fun p q => Disjoint (represented d p) (represented d q)))

noncomputable def completeFamily {n : ℕ} (d : Point n → Point n → ℝ)
    (γ R : ℝ) (Q : Finset (Point n × Point n)) : Partition n :=
  Q.image (represented d) ∪
    (components d (2 * ((γ - 1) * R / 4)) Finset.univ).filter
      (fun K => Disjoint K ((Q.image (represented d)).biUnion id))

noncomputable def improve {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (current candidate : Partition n) : Partition n :=
  if Feasible Finset.univ k candidate ∧ cost d candidate < cost d current
  then candidate else current

noncomputable def select {n : ℕ} (d : Point n → Point n → ℝ) (k : ℕ)
    (initial : Partition n) (candidates : List (Partition n)) : Partition n :=
  candidates.foldl (improve d k) initial

noncomputable def fewOutputs {n : ℕ} (d : Point n → Point n → ℝ)
    (γ : ℝ) (budget : ℕ) : Finset (Partition n) :=
  Finset.univ.biUnion (fun p : Point n × Point n =>
    (families d γ (d p.1 p.2) budget).image (completeFamily d γ (d p.1 p.2)))

end StableMSR.Recovery.CandidateAux


