-- Prove2me | Definitions.Def_gilbreath_finite_extension
-- name    : gilbreath_finite_extension
-- status  : Definition
-- author  : @EvanLLL
-- created : 2026-09-26T00:09:13.039988+00:00
-- url     : https://prove2.me/theorems/30a2f6a3-54f2-4ce0-8433-1d10161479b6
-- title:
--   Finite extension boundaries and ordered absolute-value folding
-- statement:
--   For a natural-valued sequence $a$, let $\Delta a$ be its sequence of adjacent absolute differences. The ordered right boundary of its first $n$ entries is defined recursively by
--   $$
--   E_a(0)=(),\qquad E_a(n+1)=(a_n)\mathbin{+\!\!+}E_{\Delta a}(n).
--   $$
--   It is read from the top row downwards.
--
--   For an ordered tuple $E$, define the folding map by
--   $$
--   F_{()}(x)=x,\qquad F_{(e,E')}(x)=F_{E'}(|x-e|).
--   $$
--   All inputs and outputs are nonnegative integers; subtraction inside each absolute value is formed in the integers.
--
--   Finally, call an ordered tuple complete if the empty tuple is complete and
--   $$
--   \operatorname{Complete}(e,E')
--   \quad\Longleftrightarrow\quad
--   e\le 1+\sum E'\ \text{ and }\ \operatorname{Complete}(E').
--   $$
--
--   These definitions describe finite extensions with terminal target $\{0,1\}$. They provide the normalized folding language for the halved prime-gap triangle. Completeness is a predicate, not an assumption that prime boundaries satisfy it.
-- source:
--   L. Muney, Holes in Valid-Extension Sets of Finite Gilbreath Sequences, arXiv:2606.23721v1, https://arxiv.org/html/2606.23721v1, Section 2 (right anti-diagonal and folding recurrence), Section 8 (reverse preimages), and the normalized reverse-step argument in Section 9, Theorem 20. The boundary convention here is zero-based and includes the top row; the folding target is the normalized set {0,1}.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath

/-- Process the right boundary in its geometric order. -/
def extensionFold : List ℕ → ℕ → ℕ
  | [], x => x
  | e :: es, x => extensionFold es (Int.natAbs ((x : ℤ) - (e : ℤ)))

/-- The right boundary of the first n input entries, from top to bottom. -/
def extensionBoundary (a : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => a n :: extensionBoundary (absDiff a) n

/-- The ordered inequalities for interval completeness with terminal set {0,1}. -/
def ExtensionComplete : List ℕ → Prop
  | [] => True
  | e :: es => e ≤ es.sum + 1 ∧ ExtensionComplete es

end Gilbreath


