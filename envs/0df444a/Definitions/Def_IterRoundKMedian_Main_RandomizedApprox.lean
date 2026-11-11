-- Prove2me | Definitions.Def_IterRoundKMedian_Main_RandomizedApprox
-- name    : IterRoundKMedian_Main_RandomizedApprox
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:27:08.625101+00:00
-- url     : https://prove2.me/theorems/bd52e89c-39dd-47a2-b255-d1151d4bf44c
-- title:
--   Randomized polynomial-time α-approximation algorithms for metric k-median (seeded TM2 machines)
-- statement:
--   A **randomized algorithm** is modelled as a deterministic function $\mathcal A$ that maps a pair (encoded instance, seed) of bit strings to an output bit string, together with a polynomial $q$: on instance $I$ the seed is a uniformly random bit string of length $m=q(|\mathrm{enc}(I)|)$.
--
--   $\mathcal A$ is a **randomized polynomial-time $\alpha$-approximation algorithm for metric k-median** if
--
--   1. $\mathcal A$ is computed in polynomial time (worst case, in the length of its input) by a Turing machine with finitely many stacks and finite alphabets: `FinitePolyTime encodePair id A` from the published `KMedianThreshold` definition, where the input is the pair code of $(\mathrm{enc}(I),\text{seed})$;
--   2. for every instance $I$ and **every** seed $s\in\{0,1\}^m$, the output is the membership mask of a set $S_s\subseteq F$ with $S_s\neq\emptyset$ and $|S_s|\le k$;
--   3. for every instance $I$, the expected cost under a uniform seed is at most $\alpha$ times the optimum:
--   $$\frac{1}{2^m}\sum_{s\in\{0,1\}^m}\mathrm{cost}(S_s)\ \le\ \alpha\cdot \mathrm{OPT}(I).$$
--
--   **Formalization Note.** `IsRandomizedApprox α alg q`. The output word is decoded by `outputSet` (bit $i$ set iff point $i$ is opened); clause 2 forces it to be exactly `mask I S`. This is the worst-case-time, fair-coin reading of “randomized polynomial-time”; it implies the expected-polynomial-time (Las Vegas) reading.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 3 and p. 5, §1 and Theorem 1.1

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_IterRoundKMedian_Main_Instance

namespace IterRoundKMedian.Main

/-- The membership mask of a facility set: bit `i` is `true` iff point `i` is in `S`. -/
def mask (I : Instance) (S : Finset (Fin I.n)) : List Bool :=
  List.ofFn (fun i : Fin I.n => decide (i ∈ S))

/-- The set of points whose bit is `true` in an output word. -/
def outputSet (I : Instance) (w : List Bool) : Finset (Fin I.n) :=
  Finset.univ.filter (fun i : Fin I.n => w.getD i.val false = true)

/-- An output word is feasible: it is the mask of a nonempty set of at most `k`
facilities. -/
def FeasibleOutput (I : Instance) (w : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ w = mask I S

/-- Expected cost of a seeded algorithm `alg` with seed-length polynomial `q` on `I`:
the average of `cost(outputSet)` over all `2^m` seeds of length `m = q(|enc I|)`,
i.e. the expectation under a uniformly random seed. -/
noncomputable def expectedCost (alg : List Bool × List Bool → List Bool)
    (q : Polynomial ℕ) (I : Instance) : ℝ :=
  (∑ s : Fin (q.eval (encodeInstance I).length) → Bool,
      cost I (outputSet I (alg (encodeInstance I, List.ofFn s)))) /
    2 ^ (q.eval (encodeInstance I).length)

/-- A randomized polynomial-time `α`-approximation algorithm for metric k-median:
`alg` maps (encoded instance, seed) to an output word and is computed in polynomial time
by a finite-alphabet TM2 machine (`FinitePolyTime`, on the input `encodePair (enc I, seed)`);
the seed is a uniformly random word of length `q(|enc I|)`; on every instance and every
seed the output is a nonempty set of at most `k` facilities; and the expected cost is at
most `α · OPT`. -/
def IsRandomizedApprox (α : ℝ) (alg : List Bool × List Bool → List Bool)
    (q : Polynomial ℕ) : Prop :=
  OAI.MetricKMedian.Complexity.FinitePolyTime OAI.MetricKMedian.Complexity.encodePair id alg ∧
    ∀ I : Instance,
      (∀ s : Fin (q.eval (encodeInstance I).length) → Bool,
          FeasibleOutput I (alg (encodeInstance I, List.ofFn s))) ∧
        expectedCost alg q I ≤ α * optimum I

end IterRoundKMedian.Main


