-- Prove2me | Definitions.Def_FairShareAlmostAll_Slack_ConfigurationPolytope
-- name    : FairShareAlmostAll_Slack_ConfigurationPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:09.578814+00:00
-- url     : https://prove2.me/theorems/a48cde31-7ab3-4d5c-add5-7247265a5b44
-- title:
--   Conditioned certificates, configuration polytope and fractional agents
-- statement:
--   For $c=1/(32q^2\log q)$, the Section 3 construction uses entitlements at most $c$. A certificate is conditioned on avoiding $C_1$ by dividing its surviving weights by that event's probability. The support $\mathcal P_i$ consists exactly of positive conditional weights.
--
--   The polytope has nonnegative coordinates, agent sums one and capacities
--   $$\sum_{i\in N_+}\sum_{P\in\mathcal P_i}d_{j,iP}x_{iP}\le |S_{j-1}|\quad(2\le j\le H).$$
--   Unused coordinates are fixed to zero. A vertex is a feasible point that is not the midpoint of distinct feasible points. Integral agents have a support coordinate equal to one; the other active agents form $F$. For $z>0$, $F_z=\{i\in F:b_i\ge z\}$ and $h(z)=1+\lceil\log(1/z)/\log(1+1/q)\rceil$.
--
--   The auxiliary slack predicate allows $W\le1-15/(2q)$; the paper assumes $W\le1-8/q$. This explicitly declared extension supplies the integer rounding detail for real epsilon. It does not assume conditioning is defined or that a vertex exists.
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 9 (PDF p. 10), §3–§3.2, printed pp. 9–11 (PDF pp. 10–12); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack

noncomputable def cap (q : ℕ) : ℝ := 1 / (32 * (q : ℝ)^2 * Real.log (q : ℝ))

/-- Relaxed slack suffices for floor(8/epsilon), retaining the printed goal constant. -/
noncomputable def SlackAssumptions {n m : ℕ} (X : Instance n m) (q : ℕ) : Prop :=
  ConstructionAssumptions X q ∧ (∀ i, X.entitlement i ≤ cap q) ∧
    totalEntitlement X ≤ 1 - 15 / (2 * (q : ℝ))

noncomputable def avoidanceMass {m : ℕ} (q : ℕ)
    (D : FiniteLaw (Finset (Fin m))) : ℝ :=
  probability D (fun P => Disjoint P (bucket q m 1))

noncomputable def conditionedWeight {m : ℕ} (q : ℕ)
    (D : FiniteLaw (Finset (Fin m))) (P : Finset (Fin m)) : ℝ := by
  classical
  exact if Disjoint P (bucket q m 1) then D.weight P / avoidanceMass q D else 0

noncomputable def configurationSupport {m : ℕ} (q : ℕ)
    (D : FiniteLaw (Finset (Fin m))) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (fun P => 0 < conditionedWeight q D P)

noncomputable def conditionedPoint {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m))) (i : Fin n) (P : Finset (Fin m)) : ℝ := by
  classical
  exact if i ∈ active X then conditionedWeight q (D i) P else 0

/-- Zero extension gives precisely the source polytope, without free unused coordinates. -/
noncomputable def Feasible {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (x : Fin n → Finset (Fin m) → ℝ) : Prop :=
  (∀ i P, 0 ≤ x i P) ∧
  (∀ i P, i ∉ active X ∨ P ∉ configurationSupport q (D i) → x i P = 0) ∧
  (∀ i ∈ active X, ∑ P ∈ configurationSupport q (D i), x i P = 1) ∧
  ∀ j ∈ Finset.Icc 2 (bucketCount q m),
    ∑ i ∈ active X, ∑ P ∈ configurationSupport q (D i), request X q j i P * x i P ≤
      (ordinaryBucket q m (j - 1)).card

noncomputable def Vertex {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m))) (x : Fin n → Finset (Fin m) → ℝ) : Prop :=
  Feasible X q D x ∧ ∀ y z, Feasible X q D y → Feasible X q D z →
    (∀ i P, x i P = (y i P + z i P) / 2) → y = z

noncomputable def integralAgents {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (x : Fin n → Finset (Fin m) → ℝ) : Finset (Fin n) := by
  classical
  exact (active X).filter (fun i => ∃ P ∈ configurationSupport q (D i), x i P = 1)

noncomputable def fractionalAgents {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (x : Fin n → Finset (Fin m) → ℝ) : Finset (Fin n) := by
  classical
  exact active X \ integralAgents X q D x

noncomputable def fractionalAbove {n m : ℕ} (X : Instance n m) (q : ℕ)
    (D : Fin n → FiniteLaw (Finset (Fin m)))
    (x : Fin n → Finset (Fin m) → ℝ) (z : ℝ) : Finset (Fin n) := by
  classical
  exact (fractionalAgents X q D x).filter (fun i => z ≤ X.entitlement i)

noncomputable def thresholdIndex (q : ℕ) (z : ℝ) : ℕ :=
  1 + ⌈Real.log (1 / z) / Real.log (1 + 1 / (q : ℝ))⌉₊

end FairShareAlmostAll.Slack


