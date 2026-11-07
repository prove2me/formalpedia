-- Prove2me | Definitions.Def_EffRobustLearn_IsAlg1Trajectory
-- name    : EffRobustLearn_IsAlg1Trajectory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:00.877627+00:00
-- url     : https://prove2.me/theorems/756529fe-44db-4292-ae81-a40264bab087
-- title:
--   A trajectory of Algorithm 1
-- statement:
--   A sequence of concepts $c_t$ from $c_0\in C$ is a trajectory if for every $t\in[T]$, $c_t\in C$ and
--   $$\langle\nabla F_t(\bar\mu_t[S]),c_t[S]\rangle\ge\max_{v\in K}\langle\nabla F_t(\bar\mu_t[S]),v\rangle-\frac{\gamma_t}{25}.$$
--
--   This is the hypothesis of Lemma 3.10. It separates the optimization analysis from how the concepts were found.
--
--   **Formalization Note** The maximum is written as a bound against every $v\in K$; $K$ is compact, so this is equivalent.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Algorithm 1, line 7, p.14 (PDF p.15); Lemma 3.10, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_EffRobustLearn_gradF

namespace EffRobustLearn

/-- A trajectory of Algorithm 1, independent of how the concepts `c_t` were found: `μ̄_1 = c0 ∈ C` and, in every round
`t = 1, …, T`, `c_t ∈ C` and line 7's guarantee, Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.14,
`⟨∇F_t(μ̄_t[S]), c_t[S]⟩ ≥ max_{v∈K} ⟨∇F_t(μ̄_t[S]), v⟩ - γ_t/25`, holds. The iterates are `muSeq c0 c`.

**Formalization Note.** `max_{v∈K}` is written as a bound against every `v ∈ K`, which is equivalent since `K` is
compact (Lemma 3.5). This is the hypothesis of Lemma 3.10: "every Frank–Wolfe optimization step satisfies Eq. (3.3)", read after the normalization of
p.33, where `D_2 = 2` makes the accuracy `D_2²γ_t/100 = γ_t/25`. -/
def IsAlg1Trajectory {X : Type*} {n m : ℕ} (C : Set (X → Bool)) (ε : ℝ) (c0 : X → Bool)
    (c : ℕ → X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) : Prop :=
  c0 ∈ C ∧ ∀ t ∈ Finset.Icc 1 (numRounds ε), c t ∈ C ∧ ∀ v ∈ feasibleSet C Sinp Sref,
    inner ℝ (gradAtIterate ε c0 c Sinp Sref t) v - stepSize t / 25 ≤
      inner ℝ (gradAtIterate ε c0 c Sinp Sref t) (evalVec (toPM (c t)) Sinp Sref)

end EffRobustLearn


