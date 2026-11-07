-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_NP
-- name    : QAdvFew_PoQOracle_NP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:47.587761+00:00
-- url     : https://prove2.me/theorems/297f9662-af16-47cb-829c-899219a7e5ce
-- title:
--   $\mathsf{NP}^O$
-- statement:
--   A language $L$ is in $\mathsf{NP}^O$ if there are a deterministic polynomial-time oracle verifier $\mathrm{Ver}^O$ and a polynomial $p$ such that, for every $x\in\{0,1\}^*$,
--   $$
--   x\in L \iff \exists w\in\{0,1\}^{p(|x|)},\ \mathrm{Ver}^O(x,w)=1.
--   $$
--
--   **Formalization Note** The verifier reads the pair $(x,w)$ in the tuple encoding, and halts within a polynomial of its input length on every input string.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The class `NP^O` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.2, p. 12 (PDF p. 14)): `L ∈ NP^O` if there are a
deterministic polynomial-time oracle verifier `Ver^O` and a polynomial `p` such that, for every `x`,
`x ∈ L ⟺ ∃ w ∈ {0,1}^{p(|x|)}, Ver^O(x, w) = 1`.

**Formalization Note** The verifier is an oracle Turing machine `V` reading the pair `(x, w)` as
`tup [x, w]`; "polynomial time" is a polynomial `q` such that `V^O` halts within `q(|s|)` steps on
every input string `s`. -/
def NP (O : Oracle) : Set (Set Str) :=
  {L | ∃ (V : OTM) (q p : Polynomial ℕ),
    (∀ s : Str, V.result O s (q.eval s.length) ≠ none) ∧
    ∀ x : Str, x ∈ L ↔ ∃ w : Str, w.length = p.eval x.length ∧
      V.result O (tup [x, w]) (q.eval (tup [x, w]).length) = some true}

end QAdvFew.PoQOracle


