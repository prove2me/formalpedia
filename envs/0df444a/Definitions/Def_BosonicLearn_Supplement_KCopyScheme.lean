-- Prove2me | Definitions.Def_BosonicLearn_Supplement_KCopyScheme
-- name    : BosonicLearn_Supplement_KCopyScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:00:34.269925+00:00
-- url     : https://prove2.me/theorems/e20bfb7d-f994-4dd7-be43-d6c7d460a162
-- title:
--   Adaptive $k$-copy measurement protocol on $n$ bosonic modes with a budget of $N$ copies
-- statement:
--   Fix $n$ bosonic modes, with Fock space $\ell^2(\mathbb N^n)$, a block bound $k$, a number of rounds $R$, a copy budget $N$ and a measurable outcome space $\mathcal O$. An **adaptive $k$-copy protocol** processes fresh copies of an unknown state $\rho$ in rounds $t=0,1,\dots,R-1$. In round $t$, after the earlier classical outcomes $x_{<t}=(x_0,\dots,x_{t-1})$, it
--
--   1. chooses a block size $b_t(x_{<t})\in\{0,1,\dots,k\}$, a measurable function of $x_{<t}$;
--   2. applies a POVM $M^{(t,x_{<t})}$ on $\ell^2\big((\mathbb N^n)^{b_t}\big)$, with outcomes in $\mathcal O$, to $b_t$ fresh copies, i.e. to $\rho^{\otimes b_t}$, and records the outcome $x_t$.
--
--   No quantum system is kept between rounds, so the protocol is adaptive only through classical information. The total number of copies is bounded on every transcript:
--
--   $$\sum_{t=0}^{R-1} b_t(x_{<t})\le N .$$
--
--   The outcome law of round $t$ is a Markov kernel in $x_{<t}$ which, on a density operator $\rho$, is the Born law of $M^{(t,x_{<t})}$ on $\rho^{\otimes b_t}$.
--
--   This is the $k$-copy model of quantum state tomography of Chen–Li–Liu and of Kim–Lu–Mele–Rouzé, used by the paper's Theorem 4; at $k=1$ it is the adaptive single-copy model.
--
--   **Formalization Note** A round with $b_t=0$ measures the one-dimensional space $\rho^{\otimes0}$ and only draws classical randomness: this is how stopping early and internal randomness are expressed. The number of rounds $R$ is free. A protocol of the paper makes at most $N$ requests of sizes between $1$ and $k$, chosen from earlier outcomes and internal randomness, and is one of these, with such rounds drawing the randomness before each request. A budget that holds only almost surely can be made to hold on every transcript by stopping when the next block would exceed it, which changes no transcript law. As in the base `AdaptiveScheme`, the round laws are carried as kernels tied to the POVMs by the Born rule on densities.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §4, p. 19 (k-copy model of [CLL24], [KLMR26, Definition 1.1]); proof of Theorem 4, p. 26 ("1 ≤ b_i ≤ k, and ∑_i b_i ≤ N on every run")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open MeasureTheory ProbabilityTheory

namespace BosonicLearn.Supplement

/-- **Adaptive `k`-copy measurement protocol in `R` rounds with a total budget of `N` copies of an `n`-mode state.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705,
§4, p. 19: "The input copies are processed in blocks of at most k fresh copies. At each round, the protocol applies
a POVM to the current block, and the choice of POVM may depend on all previous classical outcomes. No quantum system
is retained from one round to the next." (the model of [CLL24, Theorem 1.2] and [KLMR26, Definition 1.1]); p. 26:
"every request actually made satisfies 1 ≤ b_i ≤ k, and ∑_i b_i ≤ N on every run. In particular, A makes at most N
requests."

A `KCopyScheme n k R N O` runs `R` rounds. In round `t`, after the earlier outcomes `x : Fin t → O`, it
1. chooses a block size `block t x ∈ {0, …, k}` (a measurable function of the earlier outcomes);
2. applies the POVM `povm t x`, on `ℓ²((ℕⁿ)^{block t x})` with outcomes in the measurable space `O`, to
   `block t x` fresh copies, i.e. to `ρ^{⊗ block t x}` (`WildeQIT.Schumacher.tensorPow`, as in
   `BosonicLearn.collectiveSuccess`).
The total number of copies used, `∑_{t<R} block t (x₀,…,x_{t−1})`, is at most `N` on every transcript. `round ρ t` is the
round-`t` outcome law as a Markov kernel in the earlier outcomes; on a density `ρ` it is the Born law of `povm t x`
on `ρ^{⊗ block t x}`.

**Formalization Note.** A round with `block t x = 0` measures the one-dimensional space `ρ^{⊗0}` and only draws
classical randomness; this is how stopping and internal randomness are expressed (including randomness used to
choose the first block, p. 27: "The size b_i may depend on previous outcomes and internal randomness"). The
number of rounds `R` is a free parameter, so every protocol of the paper (at most `N` requests, each of size
between `1` and `k`, with internal randomness before each request) is one of these, e.g. with `R = 2N` rounds
alternating randomness rounds and requests, padded with size-`0` rounds. The copy
budget is required on every transcript; a protocol whose budget holds only almost surely becomes one of these by
stopping as soon as the next block would exceed the budget, which changes no transcript law. As in
`BosonicLearn.AdaptiveScheme`, the round laws are carried as kernels tied to the POVMs by the Born rule on densities
(arrays that are not densities are unconstrained), and `O` is an arbitrary measurable space. -/
structure KCopyScheme (n k R N : ℕ) (O : Type) [MeasurableSpace O] where
  /-- the number of fresh copies measured in round `t` after the earlier outcomes `x` -/
  block : (t : Fin R) → (Fin t → O) → ℕ
  /-- each block has at most `k` copies -/
  block_le : ∀ (t : Fin R) (x : Fin t → O), block t x ≤ k
  /-- the block size is a measurable function of the earlier outcomes -/
  block_measurable : ∀ t : Fin R, Measurable (block t)
  /-- at most `N` copies are used in total, on every transcript -/
  budget : ∀ x : Fin R → O, ∑ t : Fin R, block t (fun i => x (Fin.castLE t.isLt.le i)) ≤ N
  /-- the POVM of round `t`, on `block t x` copies, after the earlier outcomes `x` -/
  povm : (t : Fin R) → (x : Fin t → O) → FockPOVM (Fin (block t x) → Occupation (Fin n)) O
  /-- the round-`t` outcome law on the state `ρ`, as a kernel in the earlier outcomes -/
  round : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ → (t : Fin R) → Kernel (Fin t → O) O
  /-- each round kernel is Markov -/
  round_markov : ∀ ρ t, IsMarkovKernel (round ρ t)
  /-- on densities the round law is the Born law of the chosen POVM on `ρ^{⊗ block t x}` -/
  round_born : ∀ ρ, IsDensity ρ → ∀ (t : Fin R) (x : Fin t → O),
    round ρ t x = (povm t x).law (WildeQIT.Schumacher.tensorPow (block t x) ρ)

end BosonicLearn.Supplement


