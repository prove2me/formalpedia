-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints
-- name    : ConsistentSubmodular_Randomized_Reduction_Checkpoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:52.588957+00:00
-- url     : https://prove2.me/theorems/dbe5e1f3-a29b-4d55-ab23-3d006777bec5
-- title:
--   Checkpoint reduction for Lemma 1: parameters, consistency bound, random choices, law
-- statement:
--   Let $\gamma>0$ be the slack and $k$ the budget; $\alpha$ is the addition-robustness ratio and `hadm` is a hypothesis that every single-arrival window instance admits an $\alpha$-addition-robust distribution.
--
--   - `params γ k` is the parameter record of Algorithm 1 with $\ell=\lfloor\gamma k\rfloor$, $\kappa=k-2\ell$, $h=\lceil1/\gamma\rceil$ and $s=\lfloor k/d\rfloor+1\ge\lceil k/d\rceil$ operations per update, where $d=\lfloor \ell/h\rfloor$ is the minimum subblock length.
--   - `consistency γ` $=\lceil16/\gamma^2\rceil+3$ is the consistency bound of Lemma 1.
--   - `Sample n h` is the type of random choices on a stream of length $n$: a checkpoint sample $a_i\subseteq\{0,\dots,n-1\}$ and a subblock $b_i\in\{0,\dots,h-1\}$ for each of the blocks $i=0,\dots,n$.
--   - `samplesOf a i` and `choicesOf b i` read these choices as functions of a natural-number block index (value $\emptyset$, respectively $0$, outside $0,\dots,n$).
--   - `robustWeights hadm f κ c` is a chosen $\alpha$-addition-robust distribution (a weight function on subsets) for the window instance `window f κ c` at checkpoint $c$; `robustLaw` packages it as a `Law` on subsets.
--   - `sampleLaw hadm f P hh` is the law of the random choices: independent checkpoint samples, the one of block $i$ drawn from `robustLaw` at checkpoint $c=i\ell$ with budget $\kappa$, and independent uniform subblocks on $\{0,\dots,h-1\}$.
--   - `optimum f k t` $=$ `optimalCore f X_t ∅ k`, an exact optimum of at most $k$ arrived elements, recomputed after every arrival; it serves small budgets.
--
--   The file also proves that the chosen distribution is addition robust and, in particular, a valid law.
--
--   These definitions assemble Algorithm 1 and its randomness for the reduction of Lemma 1 (Appendix A.3), which turns an $\alpha$-addition-robust routine into a randomized $O(\gamma^{-2})$-consistent $(\alpha-3\gamma)$-approximation.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/Checkpoints.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointLaw
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

/-- The parameters of Algorithm 1 for the slack `γ` and the budget `k`:
`ℓ = ⌊γk⌋`, `κ = k - 2ℓ`, `h = ⌈1/γ⌉`, and `s = ⌊k/d⌋ + 1 ≥ ⌈k/d⌉` operations per
update, where `d = ⌊ℓ/h⌋` is the minimum subblock length. -/
def params (γ : ℝ) (k : ℕ) : Params where
  ℓ := ⌊γ * k⌋₊
  κ := k - 2 * ⌊γ * k⌋₊
  h := ⌈1 / γ⌉₊
  s := k / (⌊γ * k⌋₊ / ⌈1 / γ⌉₊) + 1

/-- The consistency bound of Lemma 1. -/
def consistency (γ : ℝ) : ℕ := ⌈16 / γ ^ 2⌉₊ + 3

/-- The random choices of Algorithm 1 on a stream of length `n`: a checkpoint
sample and a subblock for each of the blocks `0, ..., n`. -/
abbrev Sample (n h : ℕ) := (Fin (n + 1) → Finset (Fin n)) × (Fin (n + 1) → Fin h)

/-- The checkpoint samples, indexed by block. -/
def samplesOf {n : ℕ} (a : Fin (n + 1) → Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  if hi : i < n + 1 then a ⟨i, hi⟩ else ∅

/-- The selected subblocks, indexed by block. -/
def choicesOf {n h : ℕ} (b : Fin (n + 1) → Fin h) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then (b ⟨i, hi⟩).val else 0

variable {n : ℕ} {α : ℝ}

/-- The `α`-addition-robust distribution returned at the checkpoint `c`. -/
def robustWeights (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    Finset (Fin n) → ℝ :=
  Classical.choose (hadm n (window f κ c) (window_singleArrivals f κ c))

theorem robustWeights_spec (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    (window f κ c).IsAdditionRobust α (robustWeights hadm f κ c) :=
  Classical.choose_spec (hadm n (window f κ c) (window_singleArrivals f κ c))

/-- The law of the checkpoint sample at `c`. -/
def robustLaw (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    Law (Finset (Fin n)) where
  weight := robustWeights hadm f κ c
  nonneg := (robustWeights_spec hadm f κ c).1
  sum_one := (robustWeights_spec hadm f κ c).2.1

/-- The law of the random choices: independent checkpoint samples, the one of
block `i` at the checkpoint `τ = iℓ`, and independent uniform subblocks. -/
def sampleLaw (hadm : AdmitsAdditionRobust α) (f : Objective n) (P : Params) (hh : 0 < P.h) :
    Law (Sample n P.h) :=
  (Law.pi fun i : Fin (n + 1) => robustLaw hadm f P.κ (i.val * P.ℓ)).prod
    (Law.pi fun _ : Fin (n + 1) => Law.uniform P.h hh)

/-- Small budgets: recompute an exact optimum after every arrival. -/
def optimum (f : Objective n) (k t : ℕ) : Finset (Fin n) :=
  optimalCore f (arrivedPrefix n t) ∅ k

end ConsistentSubmodular.Checkpoints

end


