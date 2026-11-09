-- Prove2me | Definitions.Def_CoordBoundaries_Throughput_Pricing
-- name    : CoordBoundaries_Throughput_Pricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:25.113611+00:00
-- url     : https://prove2.me/theorems/b3e3804c-5a7f-43b1-8da1-7b0e6894a9a4
-- title:
--   Inputs of the pricing problem (2) with a tracked set and required jobs
-- statement:
--   For a candidate $(\mathcal B,\mathcal S,K)$, a block $B$, a set $H_B$ of jobs with $|H_B|\le 8K$, rational weights $w_j$ and a rational table $\alpha(A)$ for $A\subseteq H_B$ (both possibly negative), the **pricing problem (2)** is
--   $$\max_{C\in\mathcal C(B)}\Big\{\sum_{j\in C}w_j+\alpha(C\cap H_B)\Big\}.$$
--   Rationals are given as an integer numerator and a positive natural denominator. The encoding of an input lists the instance, the partition, the block index, $K$, the elements of $H_B$, the weights and the table (indexed by the subsets of $H_B$); the bit size of the weights and table is $\Lambda$.
--
--   This is the separation problem that makes the stage LPs of §4.2–§4.3 solvable without listing configurations.
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 24–25, §4.4, problem (2)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Partition

open Classical

namespace CoordBoundaries.Throughput

/-! # Pricing with required jobs, problem (2) (Tong–Xu, §4.4, pp. 24–25)

For a block `B` of a candidate partition, a tracked set `H_B` with `|H_B| ≤ 8K`, rational job
weights `w_j` and a rational table `α(A)` for `A ⊆ H_B` (either may be negative), problem (2) asks
for `max_{C ∈ 𝒞(B)} {Σ_{j ∈ C} w_j + α(C ∩ H_B)}`. Rationals are given as an integer numerator and a
positive natural denominator. -/

/-- An input of the pricing problem (2). -/
structure PricingInput (I : Instance) where
  P : Partition I.T
  k : Fin P.len
  K : ℕ
  H : Finset (Fin I.n)
  wNum : Fin I.n → ℤ
  wDen : Fin I.n → ℕ
  αNum : Finset (Fin I.n) → ℤ
  αDen : Finset (Fin I.n) → ℕ

namespace PricingInput

variable {I : Instance} (X : PricingInput I)

/-- Well-formed input: positive denominators and `|H_B| ≤ 8K`. -/
def Valid : Prop :=
  (∀ j, 0 < X.wDen j) ∧ (∀ A ⊆ X.H, 0 < X.αDen A) ∧ X.H.card ≤ 8 * X.K

/-- `w_j`. -/
noncomputable def w (j : Fin I.n) : ℝ := (X.wNum j : ℝ) / X.wDen j

/-- `α(A)`. -/
noncomputable def α (A : Finset (Fin I.n)) : ℝ := (X.αNum A : ℝ) / X.αDen A

/-- The objective of (2): `Σ_{j ∈ C} w_j + α(C ∩ H_B)`. -/
noncomputable def objective (C : Finset (Fin I.n)) : ℝ :=
  (∑ j ∈ C, X.w j) + X.α (C ∩ X.H)

/-- The elements of `H_B` in increasing order. -/
def Hlist : List (Fin I.n) := X.H.sort (· ≤ ·)

/-- Encoding of the coefficients: `(w_j)_j` as numerator/denominator pairs, then `α(A)` for all
subsets `A ⊆ H_B` (listed as sublists of `Hlist`). Its bit size is `Λ`. -/
def encCoeffs : List ℤ :=
  (List.finRange I.n).flatMap (fun j => [X.wNum j, (X.wDen j : ℤ)]) ++
    X.Hlist.sublists.flatMap fun l => [X.αNum l.toFinset, (X.αDen l.toFinset : ℤ)]

/-- Encoding of the whole pricing input: instance, partition, block index, `K`, `H_B`,
coefficients. -/
def encode : List ℤ :=
  enc I ++ encPartition X.P ++ [(X.k : ℤ), (X.K : ℤ), (X.H.card : ℤ)] ++
    X.Hlist.map (fun j => ((j : ℕ) : ℤ)) ++ X.encCoeffs

end PricingInput

end CoordBoundaries.Throughput


