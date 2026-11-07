-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_npAccepts
-- name    : QAdvFew_PoQOracle_npAccepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:31.284097+00:00
-- url     : https://prove2.me/theorems/2972ba95-23e4-45e0-a3f1-7386cc947f3c
-- title:
--   Acceptance as a member of $S_t^{\mathsf{NP}}$
-- statement:
--   $S_t^{\mathsf{NP}}$ is the set of pairs $(M,x)$ taking fewer than $t$ bits to specify, with $M$ a nondeterministic Turing machine syntactically restricted to run in at most $t$ steps. This predicate says that some witness $w$ with $|w|\le t$ makes the verifier $V^O$ accept $(x,w)$ within $t$ steps.
--
--   **Formalization Note** A nondeterministic machine running $t$ steps is encoded as a deterministic verifier reading its choices $w$, and the time restriction is read as a clock.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The nondeterministic machine `(V, x)` accepts as a member of `S^NP_t` (Goldin, Lombardi, Morimae,
*Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, p. 22 (PDF p. 24):
"`M` is a nondeterministic Turing machine … syntactically restricted to run in at most `t` steps"):
some witness `w` with `|w| ≤ t` makes the deterministic verifier `V^O` accept `(x, w)` within `t`
steps.

**Formalization Note** A nondeterministic machine running `t` steps is a deterministic verifier
reading its nondeterministic choices `w`, `|w| ≤ t`; the time restriction is read as a clock. -/
def npAccepts (V : OTM) (O : Oracle) (x : Str) (t : ℕ) : Prop :=
  ∃ w : Str, w.length ≤ t ∧ V.result O (tup [x, w]) t = some true

end QAdvFew.PoQOracle


