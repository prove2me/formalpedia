-- Prove2me | Definitions.Def_QuasiPolyTrace_Distinguishes
-- name    : QuasiPolyTrace_Distinguishes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:17.255309+00:00
-- url     : https://prove2.me/theorems/53cea612-4b10-410a-a1dd-4c57dd20c23e
-- title:
--   Distinguishing two strings from $T$ traces
-- statement:
--   Fix $n$, a deletion probability $q\in[0,1]$ (retention probability $1-q$), a number of traces $T$ and two strings $x,y\in\{0,1\}^n$. We say $x$ and $y$ **can be distinguished from $T$ traces** when there is a test $D$ that receives $T$ independent traces and answers "x" with probability $D\in[0,1]$, such that
--
--   $$
--   \Pr_{U_1,\dots,U_T\sim\mathrm{Del}(x)}[\text{answer }x]\ \ge\ \tfrac23
--   \qquad\text{and}\qquad
--   \Pr_{U_1,\dots,U_T\sim\mathrm{Del}(y)}[\text{answer }y]\ \ge\ \tfrac23 .
--   $$
--
--   This is the pairwise problem the paper reduces trace reconstruction to: "if one can distinguish pairs of traces in a certain sample complexity, then $O(n)$ factor more traces suffice to reconstruct an arbitrary $x$".
--
--   **Formalization Note** The test may be randomized (its value is its probability of answering "x") and may depend on $n,q,T,x,y$; it sees only the complete traces, whose law is that of the reused block `OAI.TraceReconstruction` (`maskWeight q`, `traceOfMask`), so it is comparable with `SufficientBudget`.
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.43–44 (sample complexity of distinguishing x from y; the O(n) reduction)

import Mathlib
import Definitions.Def_TraceReconstruction

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Distinguishing two strings from `T` traces.** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, pp.43–44: "Thus the
sample complexity of distinguishing x from y from traces of retention probability p is
`≤ 4 · τ_base^{−2·C^b}`", and p.44: "if one can distinguish pairs of traces in a certain sample
complexity, then O(n) factor more traces suffice to reconstruct an arbitrary x".

`Distinguishes n q T x y` holds when some test, given `T` independent traces, answers "x" with
probability at least `2/3` when the traces come from `x` and answers "y" with probability at least `2/3`
when they come from `y`. The deletion probability is `q` (retention probability `1 − q`).

**Formalization Note.**
* The test `D` maps the `T` complete traces to its probability of answering "x", a number in `[0, 1]`,
  so randomized tests are allowed (the paper's test is randomized: it thins and pads the traces). It may
  depend on `n`, `q`, `T`, `x` and `y`, and sees nothing but the traces.
* The trace law is that of the reused block `OAI.TraceReconstruction` (`maskWeight q`, `traceOfMask`),
  with `q` the *deletion* probability, so that this notion matches `SufficientBudget`.
* The success threshold `2/3` is the one of Definition 2 (p.6) and of the paper's test (p.44). -/
def Distinguishes (n : ℕ) (q : ℝ) (T : ℕ) (x y : Word n) : Prop :=
  ∃ D : (Fin T → Trace) → ℝ, (∀ z, 0 ≤ D z ∧ D z ≤ 1) ∧
    (2 / 3 : ℝ) ≤ ∑ a : Fin T → Mask n, (∏ j, maskWeight q (a j)) * D (fun j => traceOfMask x (a j)) ∧
    (2 / 3 : ℝ) ≤ ∑ a : Fin T → Mask n,
      (∏ j, maskWeight q (a j)) * (1 - D (fun j => traceOfMask y (a j)))

end QuasiPolyTrace


