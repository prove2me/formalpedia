-- Prove2me | Definitions.Def_AlgoPFR_Supplement_ExpectedWithin
-- name    : AlgoPFR_Supplement_ExpectedWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:34:17.603692+00:00
-- url     : https://prove2.me/theorems/8b40cf14-7795-44bf-aaad-a311b4ad287c
-- title:
--   Expected resource use of one run of an oracle-RAM program
-- statement:
--   Fix a program $P$ of the randomized log-cost oracle RAM (`AlgoPFR.Machine`), an oracle rate $r$, an input, a law $\mu$ on random tapes, a set of admissible tapes, a resource $f$ (the number of samples, of membership queries, or the log-cost time) and a number $B$. We say that **the expected $f$-cost of one run is at most $B$** if
--
--   $$\mathbb E_{\omega\sim\mu}\bigl[f(\text{run of }P\text{ on }\omega\text{ at its halting step})\bigr]\le B,$$
--
--   where a run that never halts counts as $+\infty$.
--
--   This is the cost notion of Theorem 4.2 and Claims 4.14–4.15 for "one call to the algorithmic access procedures": the per-call cost of a rejection sampler is bounded only in expectation over the call's own randomness.
--
--   **Formalization Note** The bound is stated in upper-integral form: some measurable function $g$ with $\int g\,d\mu\le B$ dominates the halting cost on every admissible tape, and $g=\infty$ wherever the run does not halt. This needs no measurability proof for the run and is never weaker than the plain expectation; a finite $B$ also forces the program to halt almost surely.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 4.2, p.18; Claims 4.14–4.15, pp.37–39

import Mathlib
import Definitions.Def_AlgoPFR_Machine

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace AlgoPFR

namespace Supplement

noncomputable section

/-- **Expected resource use of one run of a program**, the notion behind "the cost of one call to
the algorithmic access procedures … has sample and query complexity poly(K) and time complexity
O(n · poly(K))" in Theorem 4.2, p.18 of Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in
polynomial time*, arXiv:2609.20771 (sha256 60e45066…), made precise as an expectation over the
call's own randomness in Claims 4.14–4.15, pp.37–39 ("each later call … has expected sample
complexity poly(K)").

`ExpectedWithin P r input μ Good f B` says: the expectation under the tape law `μ` of the resource
`f` (for instance `MState.samples`, `MState.queries` or `MState.cost`) read at the halting step of
the run of `P` on `input`, with a run that never halts counted as `∞`, is at most `B`.

**Formalization Note.** The statement is in upper-integral form: there is a measurable majorant
`g` of the halting resource with `∫⁻ g ∂μ ≤ B`. This needs no measurability proof for the run and
is never weaker than the plain expectation. On tapes outside `Good` the majorant is unconstrained;
statements use `Good = IsRunTape A` together with a tape law `tapeMeasure (uniformLaw A hA)` under
which `Good` has full measure. A run that does not halt forces `g ω = ⊤`, so a finite bound `B`
also says that the program halts almost surely. -/
def ExpectedWithin {n : ℕ} (P : Program) (r : Vec n → ℝ) (input : List ℕ)
    (μ : Measure (Tape n)) (Good : Tape n → Prop) (f : MState → ℕ) (B : ℝ) : Prop :=
  ∃ g : Tape n → ℝ≥0∞, Measurable g ∧
    (∀ ω, Good ω → g ω = ⊤ ∨
      ∃ t, (run n P r input ω t).out.isSome ∧ ((f (run n P r input ω t) : ℕ) : ℝ≥0∞) ≤ g ω) ∧
    ∫⁻ ω, g ω ∂μ ≤ ENNReal.ofReal B

end

end Supplement

end AlgoPFR


