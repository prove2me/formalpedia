-- Prove2me | Definitions.Def_GarberOLO_Alg3_expectedRegret
-- name    : GarberOLO_Alg3_expectedRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:01:13.843879+00:00
-- url     : https://prove2.me/theorems/015ef524-5fdc-43d4-b29a-895ecefffeae
-- title:
--   Expected $\alpha$-regret of Algorithm 3
-- statement:
--   Algorithm 3 plays $s_1$ in round $1$ and, for $t = 1, \dots, T-1$, plays in round $t+1$ the point $s_{t+1} = s_i^{(t)}$ with probability $a_i^{(t)}$, where $(a^{(t)}, (v_i^{(t)}, s_i^{(t)})_i)$ is the output of round $t$'s Algorithm 2 call; the draws are independent across rounds, and the adversary's vectors $f_1, \dots, f_T$ are fixed in advance. The **expected α-regret** is
--   $$\mathbb E\big[\alpha\text{-regret}(\{(s_t, f_t)\}_{t\in[T]})\big] = \sum_{\sigma} \Big(\prod_{t=1}^{T-1} a^{(t)}_{\sigma_t}\Big)\ \alpha\text{-regret}\big(s_1, s^{(1)}_{\sigma_1}, \dots, s^{(T-1)}_{\sigma_{T-1}};\ f_1, \dots, f_T\big),$$
--   the sum running over all index sequences $\sigma = (\sigma_1, \dots, \sigma_{T-1})$.
--
--   This is the left-hand side of Theorem 1.
--
--   **Formalization Note** The law of $(s_1, \dots, s_T)$ is the product of the per-round finite distributions, so the expectation is written as this finite weighted sum over sample paths rather than as an integral against a product measure. The sampled points are the $s$-components (points of $K$).
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, §2.1, p. 4; §2.1.1, p. 5; Algorithm 3, line 9, p. 14; Theorem 1, p. 14

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_alphaRegret
import Definitions.Def_GarberOLO_Alg3_alg3Call

namespace GarberOLO.Alg3

/-- **The expected α-regret of Algorithm 3 over T rounds** (Theorem 1, Reading 4).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, §2.1, p. 4: "when the sequence {x_t}_{t∈[T]} is randomized we will use E[α − regret] to
denote the expected α-regret"; §2.1.1, p. 5: "the sequence of losses/payoffs f₁, …, f_T is chosen
in advance"; Algorithm 3, line 9, p. 14: "sample s_{t+1} ∈ {s₁, …, s_N} according to distribution
(a₁, …, a_N)".

The played points are s₁ (deterministic) and, for `t = 1, …, T − 1`, s_{t+1} = the second
component `(vs i).2` of an index `i` drawn with probability `a i` from the output of the round-t
Algorithm 2 call (`alg3Call … t`), independently across rounds. A sample path is a choice
`σ u ∈ Fin N` of index for each of the `T − 1` sampling rounds (`u = 0, …, T − 2` is round
`u + 1`); its probability is `∏_u a^{(u+1)}(σ u)`. `expectedRegret … T` is
`Σ_σ (∏_u a^{(u+1)}(σ u)) · alphaRegret S (s₁, s₂(σ), …, s_T(σ)) f T`.

**Formalization Note.** (Reading 4.) The expectation is over the algorithm's sampling only (the
adversary is oblivious and the ỹ-sequence does not depend on the samples). The law of
`(s₁, …, s_T)` is the product of the per-round finite distributions, so the expectation is this
finite weighted sum over sample paths, written out instead of as an integral against a product
measure; the two coincide whenever the weights are probability vectors, which they are under
`IsOptimalSelector` and termination. The sampled points are the s-components (points of K), not
the v-components. -/
noncomputable def expectedRegret {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ)
    (c : ℝ) (s₁ : EuclideanSpace ℝ (Fin d)) (η ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ σ : ((u : Fin (T - 1)) → Fin (alg3Call S OK sel c s₁ η ε f (u.val + 1)).N),
    (∏ u : Fin (T - 1), (alg3Call S OK sel c s₁ η ε f (u.val + 1)).a (σ u)) *
      alphaRegret S
        (fun t => match t with
          | 0 => 0
          | 1 => s₁
          | u + 2 => if h : u < T - 1 then
              ((alg3Call S OK sel c s₁ η ε f (u + 1)).vs (σ ⟨u, h⟩)).2 else 0)
        f T

end GarberOLO.Alg3


