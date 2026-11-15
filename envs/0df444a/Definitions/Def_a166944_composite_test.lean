-- Prove2me | Definitions.Def_a166944_composite_test
-- name    : a166944_composite_test
-- status  : Definition
-- author  : @tara_sooo
-- created : 2026-11-14T23:24:58.470064+00:00
-- url     : https://prove2.me/theorems/a2caf870-f71a-459a-991e-2d057981d6f8
-- title:
--   OEIS A166944 — a kernel-decidable compositeness test for first differences
-- statement:
--   This bundle fixes a single computable predicate on natural numbers: whether $n$ has a proper divisor.
--
--   For $n\in\mathbb{N}$ define
--
--   $$
--   \operatorname{isComposite}(n) \;=\; \Bigl(\exists\, m,\; 2\le m < n \;\wedge\; m \mid n\Bigr),
--   $$
--
--   evaluated as a decidable Boolean by trial division over $m < n$. Thus
--   $\operatorname{isComposite}(n)=\texttt{true}$ certifies that $n$ is not prime and
--   not $1$, and $\operatorname{isComposite}(n)=\texttt{false}$ certifies that $n$ has no
--   proper divisor at all.
--
--   The predicate exists so that statements about the *first differences* of the
--   A166944 recurrence can be settled by kernel evaluation rather than by appeal to a
--   prime predicate. Core Lean does not provide `Nat.Prime` — that is a Mathlib
--   declaration — and the recurrence-side development deliberately keeps Mathlib out
--   of its import closure so that iteration on the recurrence stays lightweight.
--   `isComposite` is therefore the Mathlib-free stand-in, and it is strong enough for
--   the classification results that follow: a difference that is not composite is
--   either $1$ or prime, and the statements below pin down exactly which indices
--   produce composite differences.
--
--   **Formalization Note** `List.range (n+1)` is used so the search space is bounded
--   and `decide` terminates; the condition `m < n` excludes $m=n$, so `= false` really
--   does mean "no proper divisor" rather than "no divisor below $n+1$".
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Definition introduced for the Lean development at https://github.com/tara-sooo/A166944-Lean (A166944/CompSweep1000.lean).

import Mathlib.Data.Nat.Prime.Defs
import Definitions.Def_a166944_record_core

namespace A166944Research

/-- Trial-division compositeness test, decidable in the kernel.

`isComposite n = true` iff there is `m` with `2 <= m < n` and `m | n`. Written
with `List.range` so that `decide` can evaluate it: core Lean has no `Prime`
(that lives in Mathlib), and the recurrence-side development deliberately avoids
importing Mathlib. -/
def isComposite (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun m => 2 ≤ m && m < n && n % m == 0)

end A166944Research


