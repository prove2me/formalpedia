-- Prove2me | Definitions.Def_UniqueOptScores_NP
-- name    : UniqueOptScores_NP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:05.882721+00:00
-- url     : https://prove2.me/theorems/cde9bd80-913a-43a4-ab16-87c4ae601e1f
-- title:
--   The class $\mathrm{NP}^A$
-- statement:
--   For an oracle $A$, a language $L \subseteq \{0,1\}^*$ belongs to $\mathrm{NP}^A$ if there are a deterministic oracle machine $V$ with a polynomial clock and a polynomial $p$ such that for every input $x$
--   $$
--   x \in L \iff \exists\, y \in \{0,1\}^{p(|x|)}:\ V^A(\langle x, y\rangle) \text{ accepts}.
--   $$
--
--   **Formalization Note** Verifier form of nondeterministic polynomial time: a witness of length $p(|x|)$ is a zero-padded sequence of nondeterministic choices (p.13). Acceptance means output $1$. The clock holds for every oracle.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, pp.13–15 (NP, relativized by giving the defining machine access to A)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_pair

namespace UniqueOptScores

/-- **The class NP^A.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.13–15 (NP, relativized by giving the machine access to `A`).

A language `L` is in `NP A` if there are a clocked deterministic oracle machine `V` (the verifier)
and a polynomial `p` such that `x ∈ L` exactly when some witness `y` of length `p(|x|)` makes `V`
accept `⟨x, y⟩` with oracle `A`.

**Formalization Note.** Verifier form: a witness of length `p(|x|)` is a zero-padded sequence of
nondeterministic choices (p.13). Acceptance is output `[true]`. The clock holds for every oracle
(`IsClocked`), as on p.15. -/
def NP (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (V : HMBinPacking.OracleMachine) (t p : Polynomial ℕ), IsClocked V t ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ y : List Bool, y.length = p.eval x.length ∧ output V A (pair x y) = [true]}

end UniqueOptScores


