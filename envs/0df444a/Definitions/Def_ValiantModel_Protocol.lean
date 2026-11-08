-- Prove2me | Definitions.Def_ValiantModel_Protocol
-- name    : ValiantModel_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:07.966682+00:00
-- url     : https://prove2.me/theorems/ec74247d-2c59-43e1-8c6c-16945f115224
-- title:
--   Deterministic protocols over the example and membership oracles, with worst-case counts per oracle
-- statement:
--   A **deterministic protocol** on $\{0,1\}^d$ is a finite-depth interaction with the two oracles of Definitions 5 and 6. At each step it stops and outputs a hypothesis, or calls the example oracle and continues on the point it sees, or queries a point of the domain and continues on the Boolean answer.
--
--   Examples and queries interleave freely, and each step may depend on everything seen before, which is the adaptivity of Valiant's model. Any point may be queried, including points never sampled, and any Boolean function may be output, since the model here is improper. The protocol takes neither the target nor the distribution as an argument, so it sees neither.
--
--   Two counts are attached: the largest number of example calls on any path, and the largest number of membership queries on any path.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), pp.1, 14–15 (PDF pp.3, 16–17), Definitions 5–6 and §3.1

import Mathlib
import Definitions.Def_ValiantModel_ConceptSequence

namespace ValiantModel

/-- A deterministic interaction of a learner with the two oracles of Definitions 5 and 6,
arXiv:2605.13840 (version held), p.14 (PDF p.16): stop and output a hypothesis, call the example
oracle and continue on the point seen, or query a point of the domain and continue on the answer.

**Formalization Note.** Examples and queries interleave freely, each step may depend on everything
seen before (adaptivity, p.1, PDF p.3), any point may be queried, and the output is any Boolean
function (improper, §3.1, p.15, PDF p.17). The tree takes neither the target nor the distribution
as an argument, so the learner sees neither. -/
inductive Protocol (d : ℕ) : Type
  | output (g : Hypothesis d) : Protocol d
  | example (k : Point d → Protocol d) : Protocol d
  | query (x : Point d) (k : Bool → Protocol d) : Protocol d

namespace Protocol

/-- The largest number of example-oracle calls on any path of the protocol. -/
def exampleDepth {d : ℕ} : Protocol d → ℕ
  | output _ => 0
  | «example» k => 1 + Finset.univ.sup fun x => exampleDepth (k x)
  | query _ k => max (exampleDepth (k false)) (exampleDepth (k true))

/-- The largest number of membership queries on any path of the protocol. -/
def queryDepth {d : ℕ} : Protocol d → ℕ
  | output _ => 0
  | «example» k => Finset.univ.sup fun x => queryDepth (k x)
  | query _ k => 1 + max (queryDepth (k false)) (queryDepth (k true))

end Protocol

end ValiantModel


