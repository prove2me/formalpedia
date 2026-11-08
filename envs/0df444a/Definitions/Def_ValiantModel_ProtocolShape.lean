-- Prove2me | Definitions.Def_ValiantModel_ProtocolShape
-- name    : ValiantModel_ProtocolShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:34.908197+00:00
-- url     : https://prove2.me/theorems/96ebd245-cb85-41cd-bc45-619a2b41f2ff
-- title:
--   Protocol shapes: query-only, examples-first, exactly $n$ example calls
-- statement:
--   Three shapes of protocol appear in the statements of the paper. A protocol is **query-only** if it never calls the example oracle: it is then a deterministic adaptive query strategy with an output at each leaf. It is **examples-first with $n$ examples** if it first makes exactly $n$ example calls, on every path, and from then on only queries. It **makes exactly $n$ example calls** if every path contains exactly $n$ of them, with queries possibly in between.
--
--   The second shape is the normal form of Remark 3.1, and the third is the count in Theorem 4.9.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.15 (PDF p.17), Remark 3.1; p.26 (PDF p.28), Theorem 4.9

import Mathlib
import Definitions.Def_ValiantModel_Protocol

namespace ValiantModel

namespace Protocol

/-- The protocol never calls the example oracle: it is a deterministic adaptive query strategy
with an output at each leaf. -/
def IsQueryOnly {d : ℕ} : Protocol d → Prop
  | output _ => True
  | «example» _ => False
  | query _ k => IsQueryOnly (k false) ∧ IsQueryOnly (k true)

/-- The shape in Remark 3.1, arXiv:2605.13840 (version held), p.15 (PDF p.17): the protocol first
makes exactly `n` example-oracle calls and from then on only queries. -/
def ExamplesFirst {d : ℕ} : ℕ → Protocol d → Prop
  | 0, p => p.IsQueryOnly
  | _ + 1, output _ => False
  | n + 1, «example» k => ∀ x, ExamplesFirst n (k x)
  | _ + 1, query _ _ => False

/-- Every path of the protocol makes exactly `n` example-oracle calls, as in Theorem 4.9,
arXiv:2605.13840 (version held), p.26 (PDF p.28). -/
def ExactExamples {d : ℕ} : Protocol d → ℕ → Prop
  | output _, n => n = 0
  | «example» k, n => ∃ n', n = n' + 1 ∧ ∀ x, ExactExamples (k x) n'
  | query _ k, n => ExactExamples (k false) n ∧ ExactExamples (k true) n

end Protocol

end ValiantModel


