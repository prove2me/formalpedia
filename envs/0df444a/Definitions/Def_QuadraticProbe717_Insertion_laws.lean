-- Prove2me | Definitions.Def_QuadraticProbe717_Insertion_laws
-- name    : QuadraticProbe717_Insertion_laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:01.121757+00:00
-- url     : https://prove2.me/theorems/3fec34a9-28d6-4953-af0d-2b925d723f86
-- title:
--   Uniform fixed-load and Poissonized algorithm laws
-- statement:
--   Fix $n>0$ and a completion permutation $\pi$. Let $H_0,\ldots,H_m$ be independent uniform residues modulo $n$, and run the insertion process on these hashes. The fixed-load tail and expectation are the exact finite averages
--   $$
--   p_{n,m,\pi}(k)=n^{-(m+1)}\#\{H:T_m(H)>k\},\qquad E_{n,m,\pi}=n^{-(m+1)}\sum_H T_m(H).
--   $$
--   For $\lambda\ge0$, the occupied-set law is the mixture of the algorithm's $r$-insertion occupied-set laws with weights $e^{-\lambda}\lambda^r/r!$. The Poissonized tail is $\int p_{n,r,\pi}(k)\,d\operatorname{Poisson}(\lambda)(r)$. No event $r\ge n$ is removed. Each conditional hash sequence has its full product uniform law.
--
--   For an occupied set $A$, put $F_i(A)=1$ when $i\notin A$ and zero otherwise, $Z(A)=n-|A|$, and
--   $$C(r)=\operatorname{Cov}(F_0,F_r).$$
--   The rate $(1-\varepsilon)n$ is represented by its nonnegative-real value; every statement using that rate requires $0<\varepsilon<1$. The state space has the full discrete σ-algebra. All costs are bounded by $2n$ and the vacancy coordinates by one, so the displayed expectations have their ordinary probabilistic meaning.
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Section 3, equation (2); Section 7, p. 15, p. 6 (PDF p. 6)

import Definitions.Def_QuadraticProbe717_Insertion_probing
import Definitions.Def_QuadraticProbe717_Insertion_association

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuadraticProbe717.Insertion

noncomputable def poissonRate (n : ℕ) (ε : ℝ) : ℝ≥0 := ((1 - ε) * n).toNNReal

noncomputable def uniformHashes (n m : ℕ) [NeZero n] : PMF (Fin m → ZMod n) :=
  PMF.uniformOfFintype _

noncomputable def fixedTail (n m : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun h : Fin (m + 1) → ZMod n => k < fixedTime n m π h)).card : ℝ) /
    (n : ℝ) ^ (m + 1)

noncomputable def expectedCost (n m : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) : ℝ :=
  ∑ h : Fin (m + 1) → ZMod n, (fixedTime n m π h : ℝ) / (n : ℝ) ^ (m + 1)

/-- The Poissonized tail is the mixture of the actual fixed-load insertion laws. -/
noncomputable def poissonTail (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (rate : ℝ≥0) (k : ℕ) : ℝ :=
  ∫ r : ℕ, fixedTail n r π k ∂poissonMeasure rate

/-- Occupied-set probability mass function obtained by running the algorithm on uniform hashes. -/
noncomputable def occupiedPMF (n m : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) :
    PMF (Finset (ZMod n)) :=
  (uniformHashes n m).map (fun h => occupied n π (List.ofFn h))

instance stateMeasurableSpace (n : ℕ) [NeZero n] : MeasurableSpace (Finset (ZMod n)) := ⊤

/-- A discrete mixture; Poisson count and conditional uniform hash sequence are sampled independently. -/
noncomputable def poissonState (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (rate : ℝ≥0) : Measure (Finset (ZMod n)) :=
  Measure.sum (fun r : ℕ => (poissonMeasure rate {r}) • (occupiedPMF n r π).toMeasure)

def vacancy (n : ℕ) [NeZero n] (i : ZMod n) (A : Finset (ZMod n)) : ℝ :=
  if i ∈ A then 0 else 1

def vacantCount (n : ℕ) [NeZero n] (A : Finset (ZMod n)) : ℕ := n - A.card

noncomputable def vacancyCovariance (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (rate : ℝ≥0) (r : ZMod n) : ℝ :=
  covariance (vacancy n 0) (vacancy n r) (poissonState n π rate)

end QuadraticProbe717.Insertion


