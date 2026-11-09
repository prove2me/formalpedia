-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_Mechanism
-- name    : HouseAllocLT_LowerBound_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:42.819778+00:00
-- url     : https://prove2.me/theorems/776fdf69-a44b-400d-91e6-65b39dde1f6a
-- title:
--   Feasible randomized mechanisms, LT and approximation ratios
-- statement:
--   A randomized mechanism assigns a lottery over feasible matchings to every reported profile. Write $\phi_{i,a}(R)$ for its assignment marginal. For a true report $P_i$, evaluate both truthful and deviating outcomes using the true classes:
--
--   $$\Phi^{P_i}_{i,j}(R)=\sum_{a\in C_j^i(P_i)}\phi_{i,a}(R).$$
--
--   Lexicographic truthfulness requires the truthful true-class vector to be lexicographically at least the deviating vector, for every agent, profile and alternative report. Restricted LT applies this same condition only when all reports lie in a specified domain.
--
--   Let $X_h^\phi(P)$ be the expected count within the first $h$ ranks. The ratios are
--
--   $$\alpha_{n,m}(\phi)=\sup_P\max_{1\le h\le r(P),\ R_h^*(P)>0}\frac{R_h^*(P)}{X_h^\phi(P)},\qquad \alpha(\phi)=\sup_{n,m\ge1}\alpha_{n,m}(\phi).$$
--
--   These quantities compare a mechanism to the rank-maximal signature at each prefix.
--
--   **Formalization Note** Lotteries are arbitrary real nonnegative weights summing to one on a finite carrier, supported on matchings feasible for the report. Ratios lie in the extended nonnegative reals, so a positive numerator divided by zero is infinity. Empty inner index sets contribute zero. Families are total also at zero market sizes, which are omitted from the uniform supremum.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §2, truthfulness and equation (1), PDF p. 7 (printed p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_RankMaximal

open scoped BigOperators
open Classical

open scoped ENNReal

namespace HouseAllocLT.LowerBound
noncomputable section

/-- §2, PDF pp.6–7: a real probability vector over finite edge sets, supported
on matchings feasible for the reported profile. No anonymity or PO is required. -/
structure Mechanism (n m : ℕ) where
  prob : Profile n m → Assignment n m → ℝ
  nonneg : ∀ P μ, 0 ≤ prob P μ
  total : ∀ P, ∑ μ, prob P μ = 1
  supported : ∀ P μ, prob P μ ≠ 0 → Feasible P μ

def marginal {n m : ℕ} (φ : Mechanism n m) (P : Profile n m)
    (i : Fin n) (a : Fin m) : ℝ :=
  ∑ μ, if (i, a) ∈ μ then φ.prob P μ else 0

def trueClassProb {n m : ℕ} (φ : Mechanism n m) (i : Fin n)
    (truth : Preference m) (R : Profile n m) (j : ℕ) : ℝ :=
  ∑ a ∈ truth.classes j, marginal φ R i a

/-- Both vectors are evaluated on the true classes of P i; reports are unrestricted. -/
def IsLT {n m : ℕ} (φ : Mechanism n m) : Prop :=
  ∀ (P : Profile n m) (i : Fin n) (R : Preference m),
    LexGE (P i).length (trueClassProb φ i (P i) P)
      (trueClassProb φ i (P i) (Function.update P i R))

/-- LT only for true types, alternative reports, and other agents in D. -/
def IsLTOn {n m : ℕ} (φ : Mechanism n m) (D : Set (Preference m)) : Prop :=
  ∀ (P : Profile n m), (∀ i, P i ∈ D) → ∀ (i : Fin n) (R : Preference m), R ∈ D →
    LexGE (P i).length (trueClassProb φ i (P i) P)
      (trueClassProb φ i (P i) (Function.update P i R))

def expectedSize {n m : ℕ} (φ : Mechanism n m) (P : Profile n m) : ℝ :=
  ∑ μ, φ.prob P μ * (μ.card : ℝ)

def expectedPrefix {n m : ℕ} (φ : Mechanism n m) (P : Profile n m) (h : ℕ) : ℝ :=
  ∑ μ, φ.prob P μ * (prefixCount P μ h : ℝ)

/-- Equation (1): every profile and nonzero rank-maximal prefix. ENNReal preserves
positive numerator / zero denominator = infinity; empty prefix sets contribute zero. -/
def approximationRatio {n m : ℕ} (φ : Mechanism n m) : ℝ≥0∞ :=
  ⨆ P : Profile n m, ⨆ h : ℕ, ⨆ (_ : 1 ≤ h ∧ h ≤ rankLength P ∧ 0 < benchmarkPrefix P h),
    (benchmarkPrefix P h : ℝ≥0∞) / ENNReal.ofReal (expectedPrefix φ P h)

abbrev MechanismFamily := ∀ n m : ℕ, Mechanism n m

def uniformRatio (φ : MechanismFamily) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ m : ℕ, ⨆ (_ : 1 ≤ n ∧ 1 ≤ m), approximationRatio (φ n m)

end
end HouseAllocLT.LowerBound


