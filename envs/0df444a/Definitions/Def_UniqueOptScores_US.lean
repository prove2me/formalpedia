-- Prove2me | Definitions.Def_UniqueOptScores_US
-- name    : UniqueOptScores_US
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:13.638282+00:00
-- url     : https://prove2.me/theorems/5e06a03b-28ef-417b-aca7-936aa34ceba1
-- title:
--   The class $\mathrm{US}^A$ (exact-one acceptance)
-- statement:
--   A language $L$ belongs to $\mathrm{US}^A$ if there is a nondeterministic polynomial-time oracle machine whose number of accepting computations on $x$ is **exactly one** precisely when $x \in L$. In verifier form: there are a clocked deterministic oracle machine $V$ and a polynomial $p$ with
--   $$
--   x \in L \iff \#\{\, y \in \{0,1\}^{p(|x|)} : V^A(\langle x, y\rangle) \text{ accepts} \,\} = 1 .
--   $$
--   On inputs outside $L$ the count may be $0$ or at least $2$; this is what distinguishes $\mathrm{US}$ from $\mathrm{UP}$.
--
--   **Formalization Note** The paper distinguishes computation paths by their choice sequences and encodes them by zero-padded strings of a common length (p.13); accepting computations are then in bijection with accepted witnesses, so the verifier form defines the same class.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.13 (definition of US) and p.15 (US^A)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_output
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_pair

namespace UniqueOptScores

/-- **The class US^A (exact-one acceptance).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.13: "A language L belongs to US [1] if there is a nondeterministic polynomial- time
machine M such that, for every input x, x ∈ L ⇐⇒ M has exactly one accepting computation on x";
p.15: "US^A uses the same exact-one acceptance condition as US, with the witnessing machine given
access to A."

`L ∈ US A` if there are a clocked verifier `V` and a polynomial `p` such that `x ∈ L` exactly when
there is **exactly one** `y` of length `p(|x|)` with `V` accepting `⟨x, y⟩` under oracle `A`.

**Formalization Note.** Verifier form of path counting: under the paper's convention that paths are
encoded by zero-padded choice strings of a common length (p.13), accepting computations correspond
one-to-one to accepted witnesses. NO inputs may have zero or at least two accepted witnesses. -/
def US (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (V : HMBinPacking.OracleMachine) (t p : Polynomial ℕ), IsClocked V t ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃! y : List Bool, y.length = p.eval x.length ∧ output V A (pair x y) = [true]}

end UniqueOptScores


