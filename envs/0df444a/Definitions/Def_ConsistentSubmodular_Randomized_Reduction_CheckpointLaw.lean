-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointLaw
-- name    : ConsistentSubmodular_Randomized_Reduction_CheckpointLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:16.571759+00:00
-- url     : https://prove2.me/theorems/0700b448-717b-4119-b3fa-6043022ec8fc
-- title:
--   Finite probability laws: expectation, point mass, uniform, product, pushforward to trajectories
-- statement:
--   A finite probability law is handled by explicit weights.
--
--   - `Law Ω` (for a finite type $\Omega$) is a structure with a weight function $\mu:\Omega\to\mathbb{R}$ such that $\mu(\omega)\ge 0$ for all $\omega$ and $\sum_{\omega}\mu(\omega)=1$.
--   - `Law.expect μ X` is the expectation $\mathbb{E}_\mu[X]=\sum_{\omega}\mu(\omega)X(\omega)$ of a function $X:\Omega\to\mathbb{R}$.
--   - `Law.dirac ω₀` is the point mass at $\omega_0$: weight $1$ at $\omega_0$ and $0$ elsewhere.
--   - `Law.uniform h hh` (for $h\ge 1$) is the uniform law on $\{0,\dots,h-1\}$, each point having weight $1/h$.
--   - `Law.pi μ` takes a family of laws $\mu_i$ on a finite type $X$, indexed by a finite type $\iota$, and returns the law of independent coordinates on functions $x:\iota\to X$ with weight $\prod_{i}\mu_i(x_i)$.
--   - `Law.prod μ ν` is the law of two independent components on $\Omega\times Y$, with weight $\mu(\omega)\,\nu(y)$.
--   - `Law.trajectory μ τ`, for a map $\tau$ from $\Omega$ to trajectories $(\tau(\omega)_t)_{0\le t\le n}$ of subsets of $\{0,\dots,n-1\}$, is the pushforward law on trajectories (a `RandomTrajectory n`): the probability of a trajectory $S$ is $\sum_{\omega:\ \tau(\omega)=S}\mu(\omega)$.
--
--   The proofs that the weights are nonnegative and sum to one are part of the definitions.
--
--   These laws are the probabilistic vocabulary of the reduction from clairvoyant addition robustness to consistency (Lemma 1): the randomness of the checkpoint algorithm is a product of independent checkpoint samples and uniform subblock choices, and the algorithm's randomized trajectory is its pushforward.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointLaw.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

/-- A probability law on a finite type: nonnegative weights summing to one. -/
structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  sum_one : ∑ ω, weight ω = 1

namespace Law

variable {Ω : Type*} [Fintype Ω]

/-- The expectation `E[X]`. -/
def expect (μ : Law Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * X ω

/-- The point mass at `ω₀`. -/
def dirac [DecidableEq Ω] (ω₀ : Ω) : Law Ω where
  weight ω := if ω = ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_one := by simp

/-- The uniform law on `Fin h`, for `h ≥ 1`. -/
def uniform (h : ℕ) (hh : 0 < h) : Law (Fin h) where
  weight _ := 1 / h
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Independent coordinates: the product of laws `μ i` on `X`, indexed by a
finite type `ι`. -/
def pi {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] (μ : ι → Law X) :
    Law (ι → X) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (μ i).nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
    simp only [(μ _).sum_one, Finset.prod_const_one]

variable {Y : Type*} [Fintype Y]

/-- Two independent components. -/
def prod (μ : Law Ω) (ν : Law Y) : Law (Ω × Y) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  sum_one := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, μ.sum_one, ν.sum_one, one_mul]

/-- The law of the trajectory `τ ω`, the pushforward of `μ` under `τ`. -/
def trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n)) :
    RandomTrajectory n := by
  classical
  exact
    { prob := fun S => ∑ ω ∈ Finset.univ.filter (fun ω => τ ω = S), μ.weight ω
      prob_nonneg := fun S => Finset.sum_nonneg fun ω _ => μ.nonneg ω
      prob_sum := by rw [Finset.sum_fiberwise Finset.univ τ μ.weight]; exact μ.sum_one }

end Law

end ConsistentSubmodular.Checkpoints

end


