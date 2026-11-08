-- Prove2me | Definitions.Def_ValiantModel_runLaw
-- name    : ValiantModel_runLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:35:49.260423+00:00
-- url     : https://prove2.me/theorems/173790f3-0dda-4102-9d87-2c495ce3617e
-- title:
--   The law of a run: ordered samples, query transcript and output
-- statement:
--   Running a deterministic protocol against the example oracle for $D$ and the membership oracle for $h$ produces an **outcome**: the ordered list of samples, the membership transcript as (point, answer) pairs in order, and the output hypothesis. Each example call is a fresh independent draw from $D$, and a query of $x$ is answered by $h(x)$.
--
--   For a randomized learner, given as a distribution over deterministic protocols, the law of the outcome first draws the protocol and then runs it.
--
--   The realized sample and transcript are kept, not only the output, because Definition 12 refers to them.
--
--   **Formalization Note** A randomized learner with a budget is represented by a distribution over deterministic protocols: fixing the internal randomness gives a deterministic protocol (p.15), and with a bounded budget on a finite domain only finitely many protocols are distinct.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.14 (PDF p.16), Definitions 5–6; p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ValiantModel_Protocol

namespace ValiantModel

/-- What a run of a learner produces: the ordered list of example-oracle samples, the membership
query transcript as (point, answer) pairs in order, and the output hypothesis. -/
structure Outcome (d : ℕ) : Type where
  examples : List (Point d)
  transcript : List (Point d × Bool)
  output : Hypothesis d

namespace Protocol

/-- The law of the run of a deterministic protocol against the example oracle for `D` and the
membership oracle for `h` (Definitions 5 and 6, arXiv:2605.13840 (version held), p.14, PDF p.16):
each example call is a fresh independent draw from `D`, and a query of `x` is answered by `h x`. -/
noncomputable def run {d : ℕ} (h : Hypothesis d) (D : PMF (Point d)) :
    Protocol d → PMF (Outcome d)
  | output g => PMF.pure ⟨[], [], g⟩
  | «example» k => D.bind fun x =>
      (run h D (k x)).map fun o => ⟨x :: o.examples, o.transcript, o.output⟩
  | query x k => (run h D (k (h x))).map fun o => ⟨o.examples, (x, h x) :: o.transcript, o.output⟩

end Protocol

/-- The law of the run of a randomized learner, given as a distribution `P` over deterministic
protocols, against the oracles for `h` and `D`: the internal randomness is drawn first and is
independent of the samples.

**Formalization Note.** A randomized learner with a budget is, for each input, a distribution over
deterministic protocols: fixing the internal randomness gives a deterministic protocol (p.15, PDF
p.17), and with a bounded budget on the finite domain only finitely many protocols are distinct.
-/
noncomputable def runLaw {d : ℕ} (P : PMF (Protocol d)) (h : Hypothesis d) (D : PMF (Point d)) :
    PMF (Outcome d) :=
  P.bind fun p => p.run h D

end ValiantModel


