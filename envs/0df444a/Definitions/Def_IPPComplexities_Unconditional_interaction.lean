-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_interaction
-- name    : IPPComplexities_Unconditional_interaction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:05.931289+00:00
-- url     : https://prove2.me/theorems/e62bbe40-3a9c-407d-a6d6-a1da2525b405
-- title:
--   Private randomized oracle interaction with observed communication and actual costs
-- statement:
--   A deterministic verifier plan is a finite tree of four operations: return a Boolean verdict, query one input coordinate and branch on its answer, send a bit, or receive a prover bit and branch on it. A public next-speaker rule depends only on the bits exchanged. Compatibility requires every communication node to respect that rule; private queries never change the public transcript. A verifier consists of this rule and an arbitrary probability distribution on compatible complete plans. No rationality, computability, advice-size, running-time, or uniform round bound is imposed.
--
--   A prover is an arbitrary behavioral strategy assigning a probability law on its next bit to every communication transcript. Strategies are selected separately for each complete input, which may be hard-wired. They never observe queries, their answers, or the privately chosen plan. The verifier's initial law preserves private correlations throughout execution; it is not resampled after each message. Prover private randomness is represented by the conditional law of its next bit given its full observed transcript, including its own actions (perfect recall).
--
--   The recursive execution returns a probability law on the verdict and the two actual resource counts. Writing $\Pr_V^P[b\mid x]$ for the probability of verdict $b$, the worst-case bound is
--
--   $$\operatorname{Bounded}(V,q,c)\iff
--   \forall x,P,o\in\operatorname{supp}(\operatorname{execution}(V,x,P)),\quad
--   Q(o)\le q\ \land\ C(o)\le c.$$
--
--   Each query is charged, including repeats; each bit in either direction is charged. Unread input coordinates are accessible only through query nodes. Internal time and query history are invisible, so they cannot serve as free communication. The trees are a reusable operational interface for finite external interaction, rather than a restriction to recursive or public-coin verifiers.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), pp. 5–7, Definition 2.1, complexity measures, and §3 nonuniform verifier preamble (PDF pp. 7–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_inputs

namespace IPPComplexities.Unconditional

/-- A deterministic private verifier plan. Only query nodes can inspect the input.
The two children of a query/receive correspond to the false and true answers. -/
inductive Plan (n : ℕ) where
  | halt : Bool → Plan n
  | query : Fin n → Plan n → Plan n → Plan n
  | send : Bool → Plan n → Plan n
  | receive : Plan n → Plan n → Plan n
  deriving DecidableEq

/-- Publicly specified next speaker, as a function only of the bits exchanged.
True means verifier; false means prover. Queries and private time are invisible. -/
abbrev Turn := List Bool → Bool

/-- No information can be transmitted by a hidden choice of the next speaker. -/
def compatible {n : ℕ} (turn : Turn) : Plan n → List Bool → Bool
  | .halt _, _ => true
  | .query _ l r, t => compatible turn l t && compatible turn r t
  | .send b s, t => turn t && compatible turn s (t ++ [b])
  | .receive l r, t => !turn t &&
      compatible turn l (t ++ [false]) && compatible turn r (t ++ [true])

/-- A private arbitrary-real law on complete plans retains all correlations
between private choices. It is not required to be recursive or finitely coded. -/
structure Verifier (n : ℕ) where
  turn : Turn
  law : PMF {s : Plan n // compatible turn s [] = true}

/-- Behavioral prover: its input is hard-wired when a strategy is chosen.
It sees communication, including its own prior bits, but no oracle history. -/
abbrev Prover := List Bool → PMF Bool

structure Outcome where
  verdict : Bool
  queries : ℕ
  communication : ℕ
  deriving DecidableEq

def addQuery (o : Outcome) : Outcome := {o with queries := o.queries + 1}
def addBit (o : Outcome) : Outcome := {o with communication := o.communication + 1}

/-- Exact execution, counting repeated oracle calls and every transmitted bit. -/
noncomputable def play {n : ℕ} (x : Input n) (P : Prover) :
    Plan n → List Bool → PMF Outcome
  | .halt b, _ => PMF.pure ⟨b, 0, 0⟩
  | .query i l r, t =>
      if x i then (play x P r t).map addQuery else (play x P l t).map addQuery
  | .send b s, t => (play x P s (t ++ [b])).map addBit
  | .receive l r, t => (P t).bind fun b =>
      if b then (play x P r (t ++ [true])).map addBit
      else (play x P l (t ++ [false])).map addBit

noncomputable def execution {n : ℕ} (V : Verifier n) (x : Input n)
    (P : Prover) : PMF Outcome := V.law.bind fun s => play x P s.val []

/-- Probability of a verdict, with costs marginalized out. -/
noncomputable def verdictProbability {n : ℕ} (V : Verifier n) (x : Input n)
    (P : Prover) (b : Bool) : ℝ :=
  (((execution V x P).map Outcome.verdict) b).toReal

/-- Worst-case actual costs, over all inputs, provers and supported outcomes. -/
def Bounded {n : ℕ} (V : Verifier n) (q c : ℕ) : Prop :=
  ∀ (x : Input n) (P : Prover) (o : Outcome),
    o ∈ (execution V x P).support → o.queries ≤ q ∧ o.communication ≤ c

end IPPComplexities.Unconditional


