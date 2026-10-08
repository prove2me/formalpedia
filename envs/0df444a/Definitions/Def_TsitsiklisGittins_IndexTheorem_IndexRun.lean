-- Prove2me | Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun
-- name    : TsitsiklisGittins_IndexTheorem_IndexRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:04.84026+00:00
-- url     : https://prove2.me/theorems/458d6f80-29ac-4c90-af9d-6f96d4414d0f
-- title:
--   A run of the index algorithm and the indices γ it assigns
-- statement:
--   This module defines the INDEX ALGORITHM of Tsitsiklis (1994), pp. 197–198, which associates with every state $x\in\mathcal X$ a number $\gamma(x)$, its **index**:
--
--   1. (a) Pick a state $s^*$ such that $r(s^*)=\max_{x\in\mathcal X}r(x)$ and let $\gamma(s^*)=r(s^*)$. Let $i^*$ be such that $s^*\in\mathcal X_{i^*}$.
--   2. (b) If $\mathcal X_{i^*}$ is a singleton, remove bandit $i^*$. Else, reduce bandit $i^*$ by removing state $s^*$. Go back to (a).
--
--   A **run** of the algorithm is a list $s_0,s_1,\dots$ of the states of $\mathcal X$, each exactly once, together with a function $\gamma$ on $\mathcal X$, such that for every $k$, at the stage obtained from the initial stage by removing $s_0,\dots,s_{k-1}$ in turn,
--   $$
--   s_k\ \text{is present},\qquad \operatorname{rate}_k(s_k)=\max_{q\ \text{present}}\operatorname{rate}_k(q),\qquad \gamma(s_k)=\operatorname{rate}_k(s_k).
--   $$
--   Here $\operatorname{rate}_0=r$ of (2.1), and the later rates are the reduced rates (2.3).
--
--   The indices are the input of Theorem 2.2, the Gittins index theorem in the form proved in the paper.
--
--   **Formalization Note** When several states attain the maximum in step (a), the paper does not say which one is picked; every choice is a run, and statements about "the index determined by the index algorithm" quantify over all runs. The removal of a whole bandit in step (b) is the reduction of its last present state, which leaves the other bandits unchanged.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), pp. 197–198 (PDF pp. 4–5), Section 2, INDEX ALGORITHM

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_Reduction

namespace TsitsiklisGittins.IndexTheorem

namespace SemiMarkovBandit

variable {n : ℕ} {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- A run of the INDEX ALGORITHM (pp. 197–198) on `B`, picking the states in the order `seq` and
assigning the indices `γ`: `seq` lists every state of `𝒳` exactly once, and for every `k`, at the
stage obtained from the initial one by removing `seq[0], …, seq[k-1]` in turn,
(a) `seq[k]` is still present and its rate is the maximum of the rates of all present states,
and `γ(seq[k])` is that rate; (b) the next stage removes `seq[k]` (reduction of its bandit).
Ties in step (a) may be broken arbitrarily: every such choice is a run. -/
def IsIndexRun (B : SemiMarkovBandit n X) (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) : Prop :=
  seq.Nodup ∧ (∀ q, q ∈ seq) ∧
    ∀ (k : ℕ) (hk : k < seq.length),
      seq[k] ∈ (B.stageAfter (seq.take k)).alive ∧
      (∀ q ∈ (B.stageAfter (seq.take k)).alive,
        (B.stageAfter (seq.take k)).rate q ≤ (B.stageAfter (seq.take k)).rate seq[k]) ∧
      γ seq[k] = (B.stageAfter (seq.take k)).rate seq[k]

end SemiMarkovBandit

end TsitsiklisGittins.IndexTheorem


