-- Prove2me | Definitions.Def_DoublyEffIP_IsSoundIP
-- name    : DoublyEffIP_IsSoundIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:07.262841+00:00
-- url     : https://prove2.me/theorems/2b46d4eb-ae43-4cff-b480-629e1e9ced44
-- title:
--   A $2^{-\sigma}$-sound $(\ell,a,\mathrm{Ptime},\mathrm{Vtime})$-IP at input length $n$
-- statement:
--   Let $\Pi$ be a public-coin protocol, $L\subseteq\{0,1\}^*$ a language, $n,T,S,\sigma\in\mathbb N$, $\mathrm{pp}=(n,T,S,\sigma)$, and let $\ell$, $a$ be the protocol's round count and message length at $\mathrm{pp}$. Given real bounds $\bar\ell,\bar a,\overline{P},\overline{V}$, the protocol $\Pi$ is a **$2^{-\sigma}$-sound $(\bar\ell,\bar a,\overline P,\overline V)$-IP for $L$ at length $n$** if
--
--   1. on $\mathrm{pp}$ the parameter machine outputs $\langle\ell\rangle\langle a\rangle$ within $\overline V$ steps, and $\ell\le\bar\ell$, $a\le\bar a$;
--
--   and for every input $x$ of length $n$:
--
--   2. **verifier time:** for every query sequence and every answer sequence ($\ell$ messages of $a$ bits each), the verifier halts within $\overline V$ steps;
--   3. **prover time:** for every query sequence $q$, the prover machine outputs an $a$-bit answer in every round, and its running times over the $\ell$ rounds sum to at most $\overline P$;
--   4. **completeness:** if $x\in L$, the verifier accepts on every $q$ together with the prover machine's answers, i.e. $\Pr_q[\langle P(x),V(x;q)\rangle\neq\bot]=1$;
--   5. **soundness:** if $x\notin L$, then for every prover strategy $P^*$ (an arbitrary function from the queries received so far to an $a$-bit answer)
--
--   $$
--   \Pr_{q}\big[\langle P^*(x),V(x;q)\rangle\neq\bot\big]\le 2^{-\sigma},
--   $$
--
--   where $q$ is uniform over $(\{0,1\}^a)^\ell$.
--
--   This is the paper's Definition 7 with $\epsilon=2^{-\sigma}$, specialized to one input length, with machine running times.
--
--   **Formalization Note** Probabilities over the uniform coins are counts: probability $1$ means "for every $q$", and the soundness bound is $\#\{q\mid V\text{ accepts}\}\cdot2^\sigma\le2^{\ell a}$. The completeness prover is the protocol's own deterministic prover machine, which "runs in time Ptime" (p.10); its time is the total of its next-message computations over the rounds, required on every input of length $n$. The verifier's bound holds on every coin and answer sequence, not only honest ones. A cheating prover is chosen after $x$ and $\mathrm{pp}$ and sees the queries so far.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Definition 7, p.11; Section 3.4, pp.10–11

import Mathlib
import Definitions.Def_DoublyEffIP_ppCode
import Definitions.Def_DoublyEffIP_HaltsAt
import Definitions.Def_DoublyEffIP_ComputesIn
import Definitions.Def_DoublyEffIP_Accepts
import Definitions.Def_DoublyEffIP_Protocol
import Definitions.Def_DoublyEffIP_msgs
import Definitions.Def_DoublyEffIP_proverInput
import Definitions.Def_DoublyEffIP_verifierInput

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP

/-- **A `2^{-σ}`-sound `(ℓ, a, Ptime, Vtime)`-IP for `L` at input length `n`** — Definition 7
(ǫ-Sound (ℓ, a, Ptime, Vtime)-IP) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*,
arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), p.11, with the protocol of
Section 3.4, pp.10–11, and `ǫ = 2^{-σ}`.

Write `pp` for the public parameters `(n, T, S, σ)` and `ℓ`, `a` for `prot.rounds` and
`prot.msgLen` at `(n, T, S, σ)`. Then:
1. (parameters) on `pp` the machine `paramM` outputs `ℓ` and `a` in binary within `VB` steps, and
   `ℓ ≤ ℓB`, `a ≤ aB`;

and for every input `x` of length `n`:

2. (verifier time) for every query sequence `q` and every answer sequence, each of `ℓ` messages
   of `a` bits, the verifier halts within `VB` steps;
3. (prover time) for every `q`, the prover machine outputs, in each round `j`, an `a`-bit answer
   `a_j = P(x, j, (q_0, …, q_j))`, and the total number of steps over the `ℓ` rounds is at most
   `PB`;
4. (completeness) if `x ∈ L`, the verifier accepts on every `q` together with the prover
   machine's answers to it;
5. (soundness) if `x ∉ L`, then for every prover strategy `P*` (any function from the queries so
   far to an `a`-bit answer) the verifier accepts on at most a `2^{-σ}` fraction of the `2^{ℓa}`
   query sequences.

**Formalization Note.**
* Probabilities over the uniform coins `q ∈ ({0,1}^a)^ℓ` are counts: "probability 1" is "for
  every `q`", and `Pr ≤ 2^{-σ}` is `#{q | accept} · 2^σ ≤ 2^{ℓa}`.
* The completeness prover is the protocol's own machine `P`, whose running time is `Ptime`
  (p.10: "The machine P is deterministic and runs in time Ptime"); otherwise `Ptime` would bound
  nothing. Its time is the total over the rounds of its next-message machine, on every input `x`.
* The verifier's time bound holds on every coin and answer sequence, not only honest ones.
* A cheating prover sees the queries so far; `x` and `pp` are fixed before it is chosen, and it is
  computationally unbounded, so this loses nothing.
* `ℓ` and `a` are computed by `paramM` within the verifier's budget, since the verifier must know
  them. -/
def IsSoundIP (prot : Protocol) (L : Set (List Bool)) (n T S σ : ℕ) (ℓB aB PB VB : ℝ) : Prop :=
  let pp := ppCode n T S σ
  let ℓ := prot.rounds n T S σ
  let a := prot.msgLen n T S σ
  (∃ t : ℕ, ComputesIn prot.paramM prot.paramOut pp (encBin ℓ ++ encBin a) t ∧ (t : ℝ) ≤ VB) ∧
  (ℓ : ℝ) ≤ ℓB ∧ (a : ℝ) ≤ aB ∧
  ∀ x : List Bool, x.length = n →
    -- verifier time, on every coin sequence and every answer sequence
    (∀ qs as : Fin ℓ → List.Vector Bool a,
      ∃ (t : ℕ) (final : SqrtLogSpace.LocatedCfg prot.verifierM),
        HaltsAt prot.verifierM (verifierInput pp x (msgs qs) (msgs as)) t final ∧ (t : ℝ) ≤ VB) ∧
    -- honest prover: the prover machine answers every round, in total time at most `PB`
    (∀ qs : Fin ℓ → List.Vector Bool a, ∃ (as : Fin ℓ → List.Vector Bool a) (t : Fin ℓ → ℕ),
      (∑ j, (t j : ℝ)) ≤ PB ∧
      ∀ j : Fin ℓ, ComputesIn prot.proverM prot.proverOut
        (proverInput pp x j.val ((msgs qs).take (j.val + 1))) (as j).toList (t j)) ∧
    -- perfect completeness, by the prover machine's answers
    (x ∈ L → ∀ qs as : Fin ℓ → List.Vector Bool a,
      (∀ j : Fin ℓ, ∃ t : ℕ, ComputesIn prot.proverM prot.proverOut
        (proverInput pp x j.val ((msgs qs).take (j.val + 1))) (as j).toList t) →
      Accepts prot.verifierM (verifierInput pp x (msgs qs) (msgs as))) ∧
    -- soundness error `2^{-σ}` against every prover strategy
    (x ∉ L → ∀ Pstar : List (List Bool) → List.Vector Bool a,
      Nat.card {qs : Fin ℓ → List.Vector Bool a //
          Accepts prot.verifierM
            (verifierInput pp x (msgs qs) (msgs fun j : Fin ℓ => Pstar ((msgs qs).take (j.val + 1))))} *
        2 ^ σ ≤ 2 ^ (ℓ * a))

end DoublyEffIP


