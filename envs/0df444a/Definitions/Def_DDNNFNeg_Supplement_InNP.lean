-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_InNP
-- name    : DDNNFNeg_Supplement_InNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:46:42.605193+00:00
-- url     : https://prove2.me/theorems/4506efb0-47d9-48e6-b2e6-bd395b0ded15
-- title:
--   The class NP
-- statement:
--   A language $L \subseteq \{0,1\}^*$ is in **NP** if there are a polynomial $p$ and a deterministic polynomial-time verifier $V$ such that for every $x$,
--
--   $$x \in L \iff \exists w \in \{0,1\}^{p(|x|)} : V \text{ accepts } (x, w).$$
--
--   **Formalization Note** $V$ is a polynomial-time function on binary strings and accepts when it outputs the string $1$. Certificates of length exactly $p(|x|)$ give the same class as length at most $p(|x|)$.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §4, pp.9–11

import Mathlib
import Definitions.Def_DDNNFNeg_Supplement_PolyTimeFun
import Definitions.Def_DDNNFNeg_Supplement_pairEnc

namespace DDNNFNeg.Supplement

/-- The language `L ⊆ {0,1}*` is in **NP** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §4, p.9–11): there are a polynomial `p` and
a deterministic polynomial-time verifier `V` such that `x ∈ L` iff some certificate `w` of
length `p(|x|)` makes `V` accept `(x, w)`.

**Formalization Note** `V` accepts when its output is the one-bit string `[true]`. Certificates
of length exactly `p(|x|)` give the same class as length at most `p(|x|)`. -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool → List Bool), PolyTimeFun V ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ w : List Bool, w.length = p.eval x.length ∧ V (pairEnc x w) = [true]

end DDNNFNeg.Supplement


