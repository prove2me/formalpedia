-- Prove2me | Definitions.Def_MethodFulfillment_IsAlg2Rule
-- name    : MethodFulfillment_IsAlg2Rule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:24.120824+00:00
-- url     : https://prove2.me/theorems/62183907-252f-4790-95bc-41dd52082e75
-- title:
--   Algorithm 2: the magicians' availability rule and the induced strategy
-- statement:
--   An **Algorithm 2 rule** with magician inputs $\nu$ gives, for each period $t$ and history, a probability distribution over the set $A$ of pairs whose magicians make their inventory available, such that
--
--   1. it depends on the run only through the periods before $t$;
--   2. each pair $(i,k)$ belongs to $A$ with exactly the magician's probability $a^{tW^t_{ik}}_{ik}$ (definition `alg2Prob`).
--
--   The induced method-acceptance strategy `alg2Policy` makes the pairs of $A$ available whatever order arrives and whatever method $m$ is drawn: $m$ is accepted when all its magicians are available, and otherwise the pairs of $m$ whose magicians are available are used and the remaining items go to the dummy facility, as in Algorithm 2.
--
--   **Formalization Note** The paper fixes each magician's probability given its own usage, but not the joint law of different magicians' coins, and its argument does not use one. Every joint law with these marginals is admitted. Independent coins, $\Pr(A)=\prod_{x\in A}a_x\prod_{x\notin A}(1-a_x)$, give one such rule. The rule ignores the drawn method ("each magician (i,k) makes the decision independently of m", p.17).
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 2, p.15; Appendix D, p.58; p.17

import Mathlib
import Definitions.Def_MethodFulfillment_alg2Prob

namespace MethodFulfillment

/-- `ρ` implements Algorithm 2 (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…,
Algorithm 2, p.15; Appendix D, p.58), with magician inputs `ν` (`ν = mu' P y`, the
probabilities (12), in Algorithm 2): `ρ t r A` is the probability that, at Lean time `t` on the
run `r`, the set of pairs whose magicians make their inventory available is exactly `A`. It is a
probability distribution over `A`, it depends on the run only through the periods before `t`, and
each pair `(i, k)` is available with exactly the magician's probability `alg2Prob`.

**Formalization Note.** The paper fixes each magician's availability probability given its own
usage, but not the joint law of the different magicians' coins; every joint law with these
marginals is admitted. The independent product
`ρ t r A = ∏_{x ∈ A} alg2Prob x · ∏_{x ∉ A} (1 − alg2Prob x)` is one of them. The rule does not
look at the method drawn at `t` ("each magician (i,k) makes the decision independently of m",
p.17). -/
structure IsAlg2Rule {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {T : ℕ} (P : Instance I K Q T) (ν : I → K → ℕ → ℝ)
    (ρ : Fin T → Run I K Q T → Finset (I × K) → ℝ) : Prop where
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ t r A, 0 ≤ ρ t r A
  /-- Probabilities sum to one. -/
  sum_one : ∀ t r, ∑ A, ρ t r A = 1
  /-- The availability decision at `t` depends on the run only through the periods before `t`. -/
  nonanticipating : ∀ t (r r' : Run I K Q T), (∀ s, s < t → r s = r' s) → ρ t r = ρ t r'
  /-- Each pair is available with the magician's probability. -/
  marginal : ∀ t r i k,
    ∑ A ∈ Finset.univ.filter (fun A : Finset (I × K) => (i, k) ∈ A), ρ t r A =
      alg2Prob P ν t r i k

/-- The method-acceptance strategy of Algorithm 2 built from an availability rule `ρ`: it makes
available the pairs whose magicians are available and ignores the arriving order and the drawn
method. The drawn method `m` is accepted iff `m ⊆ A`; otherwise the submethod `m ∩ A` (the pairs
of `m` whose magicians are available) is used and the remaining items go to the dummy facility. -/
def alg2Policy {I K Q : Type} {T : ℕ} (ρ : Fin T → Run I K Q T → Finset (I × K) → ℝ) :
    Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ :=
  fun t r _ _ A => ρ t r A

end MethodFulfillment


