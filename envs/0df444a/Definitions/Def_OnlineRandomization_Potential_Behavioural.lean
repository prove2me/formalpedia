-- Prove2me | Definitions.Def_OnlineRandomization_Potential_Behavioural
-- name    : OnlineRandomization_Potential_Behavioural
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:44:06.722784+00:00
-- url     : https://prove2.me/theorems/97ac1330-9249-4f15-a3d0-64d02e47593a
-- title:
--   Behavioural randomized online algorithms, their play against an adaptive on-line adversary, and α-competitiveness against such adversaries
-- statement:
--   Section 3 of the paper describes a randomized online algorithm $G$ by its **behaviour**: for every $n$, every request history $r \in R^n$, every new request $r_{n+1} \in R$ and every history of its own answers $a \in A^n$, a probability distribution $g_{n+1}(r r_{n+1}, a)$ on $A$, the law of its next answer $a_{n+1}$.
--
--   Let $S = (Q, P)$ be an adaptive on-line adversary (requests $q_n$, answers $p_n$, depth bound $d_Q$). The **play** of $G$ against $S$ starts from the empty configuration and repeats, from a configuration $(r, a, b) \in R^n \times A^n \times A^n$ (requests, algorithm's answers, adversary's answers):
--
--   1. if $q_n(a) = \mathrm{stop}$, the play ends;
--   2. otherwise the request is $r_{n+1} = q_n(a)$, the adversary answers $b_{n+1} = p_n(a)$, and the algorithm answers $a_{n+1} \sim g_{n+1}(r r_{n+1}, a)$.
--
--   It ends after at most $d_Q$ requests, in a random final configuration $(r, a, b)$ of some length $n$. The cost of the algorithm is $c_G(S) = f_n(r, a)$ and the cost of the adversary is $c_S(G) = f_n(r, b)$. The algorithm is **$\alpha$-competitive against any adaptive on-line adversary** if for every such $S$
--   $$
--   \mathbb E\big[c_G(S)\big] \le \mathbb E\big[\alpha(c_S(G))\big].
--   $$
--
--   This is the notion of competitiveness in Lemma 3.1 of the paper, and the play is the process along which the augmented potential function of Definition 3.1 is evaluated.
--
--   **Formalization Note** The algorithm is a map from (request list, answer list) to a probability mass function on $A$; `g (r ++ [x]) a` is $g_{n+1}(r x, a)$. Section 2 of the paper defines a randomized algorithm as a distribution over deterministic algorithms (the mixed form); the behavioural form is obtained from it by conditioning on the history, and it is the form Definition 3.1 is written in. The law of the final configuration is built recursively with `PMF.bind`, with the adversary's depth as fuel. Expectations under it are $\mathbb E_p[f] = \sum_z p(z) f(z)$ (`pexp`); the law has finite support ($A$ finite, depth bounded), so the sum is a finite sum. As on p. 9 of the paper, $\alpha$ stays inside the expectation.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 7-9, §2 (adversaries and competitiveness) and p. 14, Definition 3.1 (the distributions g_{n+1})

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_Model

namespace OnlineRandomization.Potential

/-- Manuscript p. 14 (Definition 3.1): a randomized online algorithm in behavioural form.
`g (r ++ [x]) a` is the paper's `g_{n+1}(r r_{n+1}, a)`, the law on `A` of the algorithm's next
answer `a_{n+1}` given the requests `r` so far, the new request `r_{n+1} = x`, and the
algorithm's own answers `a` so far. A distribution over deterministic algorithms `G_x` (the
mixed form of p. 7, `RandAlg`) yields it by conditioning on the history; `RandAlg` is kept for
the algorithm `H` of Theorem 3.1, whose coins are shared across request sequences. -/
abbrev BehAlg (R A : Type*) := List R → List A → PMF A

/-- The expectation of a real function under a probability mass function,
`E_p[f] = ∑_z p(z) f(z)`. Every law used here has finite support, so the sum is finite. -/
noncomputable def pexp {X : Type*} (p : PMF X) (f : X → ℝ) : ℝ :=
  ∑' z, (p z).toReal * f z

/-- Manuscript p. 8: the play of a behavioural algorithm `g` against an adaptive on-line
adversary `S`, run for at most `k` more rounds from the configuration `(r, a, b)` (requests,
algorithm's answers, adversary's answers). In each round the adversary's request is
`x = q_n(a)` (stop on `none`), the adversary answers `b_{n+1} = p_n(a)` and the algorithm
answers `a_{n+1} ∼ g(r x, a)`. The result is the law of the final configuration. -/
noncomputable def behPlayAux {R A : Type*} (g : BehAlg R A) (S : OnlineAdv R A) :
    ℕ → List R → List A → List A → PMF (List R × List A × List A)
  | 0, r, a, b => PMF.pure (r, a, b)
  | k + 1, r, a, b =>
    match S.next a with
    | none => PMF.pure (r, a, b)
    | some x => (g (r ++ [x]) a).bind fun a' =>
        behPlayAux g S k (r ++ [x]) (a ++ [a']) (b ++ [S.ans a])

/-- Manuscript p. 8: the law of the final configuration `(r(G,S), a(G,S), b(G,S))` of the
play of `g` against `S` from the empty configuration; `S` stops after at most `d_Q` requests. -/
noncomputable def behPlay {R A : Type*} (g : BehAlg R A) (S : OnlineAdv R A) :
    PMF (List R × List A × List A) :=
  behPlayAux g S S.depth [] [] []

/-- Manuscript p. 9: the behavioural algorithm `g` is `α`-competitive against any adaptive
on-line adversary if `E[c_G(S)] ≤ E[α(c_S(G))]` for every `S`, where `c_G(S) = f_n(r, a)` and
`c_S(G) = f_n(r, b)` at the final configuration; `α` stays inside the expectation, as on p. 9. -/
def IsCompetitiveOnlineBeh {R A : Type*} (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) :
    Prop :=
  ∀ S : OnlineAdv R A,
    pexp (behPlay g S) (fun z => F.cost z.1 z.2.1) ≤
      pexp (behPlay g S) (fun z => α (F.cost z.1 z.2.2))

end OnlineRandomization.Potential


