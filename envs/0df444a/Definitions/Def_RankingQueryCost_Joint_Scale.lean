-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Scale
-- name    : RankingQueryCost_Joint_Scale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:01.22202+00:00
-- url     : https://prove2.me/theorems/85d29e77-42e2-4781-bb5c-d8c768848848
-- title:
--   Finite graph extremum and exact information scale
-- statement:
--   For $s$ faulty identities, let $U_{AK}(n,s)$ be the maximum sum of squared degrees over all simple graphs on the $n$ labels with exactly $s$ edges. Define
--
--   $$B_s=s\min\{s+1,n\},\quad u=s\min\{s,n-1\},\quad U=\min\{B_s,U_{AK}(n,s)\},\quad\kappa=u/n^3.$$
--
--   The exact near-threshold target is $(1+\delta)U/n^3$. For positive $x$, $A_x=n\log_2\min\{n,x^{-1/2}\}$, and $A_0=n\log_2n$. The module also computes the quasi-complete and quasi-star expressions in §5.1 by finite maximal core sizes. Their equality with the graph extremum is a theorem, rather than a defining assumption.
--
--   **Formalization Note** The graph maximum is a finite maximum over edge subsets. It is zero for an impossible edge cardinality; admissibility excludes that case. At $s=0$ all three energy values are zero.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §2.2, equation (2), p. 4, PDF p. 5; §5.1, p. 25, PDF p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Domain

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

/-- A graph is the finite set of its unordered edges. -/
noncomputable def supportDegree {n : ℕ} (E : Finset (Pair n)) (i : Fin n) : ℕ :=
  (E.filter fun e => e.1.1 = i ∨ e.1.2 = i).card

noncomputable def degreeSquareSum {n : ℕ} (E : Finset (Pair n)) : ℕ :=
  ∑ i, supportDegree E i ^ 2

/-- Genuine finite maximization over graphs with exactly `s` edges. `sup ∅ = 0` only
arises outside the admissible edge range; admissibility always supplies such graphs. -/
noncomputable def extremalDegreeEnergy (n s : ℕ) : ℕ :=
  ((Finset.univ : Finset (Pair n)).powersetCard s).sup degreeSquareSum

def incidenceCap (n s : ℕ) : ℕ := s * min (s + 1) n

def crudeScale (n s : ℕ) : ℕ := s * min s (n - 1)

noncomputable def errorScale (n s : ℕ) : ℕ :=
  min (incidenceCap n s) (extremalDegreeEnergy n s)

def kappa (n s : ℕ) : ℝ := (crudeScale n s : ℝ) / (n : ℝ) ^ 3

noncomputable def threshold (n s : ℕ) (δ : ℝ) : ℝ :=
  (1 + δ) * (errorScale n s : ℝ) / (n : ℝ) ^ 3

noncomputable def resolutionCost (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then n * Real.logb 2 n
  else n * Real.logb 2 (min (n : ℝ) (1 / Real.sqrt x))

/-- Quasi-complete formula, with A maximal subject to binom(A,2) ≤ s. -/
noncomputable def cliqueCore (n s : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun A => A.choose 2 ≤ s).sup id

noncomputable def quasiCompleteEnergy (n s : ℕ) : ℕ :=
  let A := cliqueCore n s
  let R := s - A.choose 2
  R * A ^ 2 + (A - R) * (A - 1) ^ 2 + R ^ 2

noncomputable def starCore (n s : ℕ) : ℕ :=
  ((Finset.range n).filter fun H => H * n - H * (H + 1) / 2 ≤ s).sup id

noncomputable def quasiStarEnergy (n s : ℕ) : ℕ :=
  let H := starCore n s
  let R := s - (H * n - H * (H + 1) / 2)
  H * (n - 1) ^ 2 + (H + R) ^ 2 + R * (H + 1) ^ 2 + (n - H - 1 - R) * H ^ 2

end RankingQueryCost.Joint


