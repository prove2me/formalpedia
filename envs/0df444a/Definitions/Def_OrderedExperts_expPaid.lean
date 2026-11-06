-- Prove2me | Definitions.Def_OrderedExperts_expPaid
-- name    : OrderedExperts_expPaid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:49.096809+00:00
-- url     : https://prove2.me/theorems/4d4ba375-6080-4d17-a4dd-acd241415e25
-- title:
--   Expected cumulative paid loss of Algorithm 2
-- statement:
--   Fix an oblivious instance: recommendations $a_{t,f}$ and loss components $\ell^\uparrow_t,\ell^\downarrow_t$ for every round. Run Algorithm 2 with learning rate $\eta$ and horizon $T$. On each round $t$ the only randomness is the pair, drawn with probability
--   $$
--   \mathbb P(A_t=a,B_t=b\mid\text{past})=\pi_t(a)\,\kappa_t(a,b),
--   $$
--   where $\pi_t$ is the smoothed distribution and $\kappa_t$ the pair kernel with $m=m_t$, $\xi=1/T$, both computed from the past estimates. The **expected cumulative paid loss** $\mathbb E\sum_{t=1}^T\frac12(\ell_t(x_{t,A_t})+\ell_t(x_{t,B_t}))$ is computed exactly by the backward recursion: with $k$ rounds remaining at round $t$ and past estimate vectors $v$,
--   $$
--   E_0(t,v)=0,\qquad E_{k+1}(t,v)=\sum_{a,b=1}^{m_t}\pi_t(a)\kappa_t(a,b)\Bigl[\tfrac12\bigl(\ell_t(x_{t,a})+\ell_t(x_{t,b})\bigr)+E_k\bigl(t+1,\,v\text{ with round }t\text{ set to }\hat\ell_t\bigr)\Bigr],
--   $$
--   and the algorithm's expected cumulative paid loss is $E_T(0,0)$.
--
--   **Formalization Note** Rounds are $0$-based. The adversary is oblivious, so this finite recursion over the drawn pairs is the expectation exactly.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Algorithm 2, p.11; Algorithm 1 (Pair), p.9; Sec. 2.2, pp.5–6

import Definitions.Def_OrderedExperts_kappa
import Definitions.Def_OrderedExperts_roundEst
import Definitions.Def_OrderedExperts_paidLoss

namespace OrderedExperts

/-- **Expected cumulative paid loss of Algorithm 2.**
Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Algorithm 2, p.11, with Pair of Algorithm 1, p.9 ("Draw `A ∼ π` and then `B ∼ κ(A, ·)`"),
and Sec. 2.2, pp.5–6: "We bound the expected regret `ERegT(F)`, where the expectation is over learner
randomness."

`expPaid η T rec up down k t v` is the expected paid loss of the `k` rounds `t, t+1, …, t+k−1` of
Algorithm 2 (learning rate `η`, horizon `T`) when the past estimate vectors are `v s` (`s < t`): on
round `t` the pair `(a, b)` of active ranks is drawn with probability `πt(a) κt(a, b)` (`πt` the
smoothed distribution, `κt` the kernel with `m = mt`, `ξ = 1/T`), the learner pays
`½(ℓt(xt,a) + ℓt(xt,b))`, and the estimate vector of the round is recorded at index `t`. The
algorithm's expected cumulative paid loss is `expPaid η T rec up down T 0 0`.

**Formalization Note.** The adversary is oblivious (`rec`, `up`, `down` are fixed functions) and
the only randomness is the pair drawn each round given the past, so this finite recursion is the
expectation exactly; rounds are 0-based. -/
noncomputable def expPaid {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ} (η : ℝ) (T : ℕ)
    (rec : ℕ → Fin n → A) (up down : ℕ → A → ℝ) : ℕ → ℕ → (ℕ → Fin n → ℝ) → ℝ
  | 0, _, _ => 0
  | k + 1, t, v =>
      ∑ a ∈ Finset.Icc 1 (chainSize rec t), ∑ b ∈ Finset.Icc 1 (chainSize rec t),
        roundPi η T rec v t a * kappa (chainSize rec t) (1 / (T : ℝ)) (roundPi η T rec v t) a b *
          (paidLoss rec up down t a b +
            expPaid η T rec up down k (t + 1)
              (Function.update v t (roundEst η T rec up down v t a b)))

end OrderedExperts


