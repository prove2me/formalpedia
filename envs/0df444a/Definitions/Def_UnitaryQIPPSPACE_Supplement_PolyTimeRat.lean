-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Supplement_PolyTimeRat
-- name    : UnitaryQIPPSPACE_Supplement_PolyTimeRat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:45:24.429033+00:00
-- url     : https://prove2.me/theorems/2dbebbb8-9ea1-4439-977e-b8ff6308f2a6
-- title:
--   Polynomial-time computable function $\varepsilon:\mathbb N\to\mathbb Q$
-- statement:
--   A function $\varepsilon:\mathbb N\to\mathbb R$ is **polynomial-time computable** if it takes rational values and there is a polynomial-time computable map $f$ on bit strings such that, for every $n$, $f(1^n)$ is the encoded pair $(a,b)$ of natural numbers with $b\ge1$ and
--   $$\varepsilon(n)=\frac ab.$$
--
--   This is the hypothesis on the precision function $\varepsilon$ in Theorem 1.4 (and in Lemma 5.6): the verifier computes its parameters from $\varepsilon(n)$ in time polynomial in $n$.
--
--   **Formalization Note** Polynomial-time computability is the published `PolyTimeComputable` (Turing machines with a polynomial step bound); the pair is written with the published tuple encoding and binary codes of $a$ and $b$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 1.4, p.4 (PDF p.6), restated p.38 (PDF p.40); Lemma 5.6, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Bits

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

namespace Supplement

/-- **Polynomial-time computable function `ε : ℕ → ℝ`** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, Theorem 1.4, p. 4 (PDF p. 6),
restated p. 38 (PDF p. 40): "Let `ε : ℕ → (0, 1/4]` be polynomial-time computable"; also
Lemma 5.6, p. 43).

`ε` takes rational values, and its exact value is computed in polynomial time from `1^n`: there
is `f : Str → Str` computable in polynomial time (the published `PolyTimeComputable`) such that
for every `n`, `f(1^n)` is the pair `(a, b)` of binary codes with `b ≥ 1` and `ε(n) = a / b`.

**Formalization Note** The pair is encoded with the published tuple encoding `tup` and the binary
code `natCode` of the base mission. -/
def PolyTimeRat (ε : ℕ → ℝ) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n : ℕ, ∃ a b : ℕ, 1 ≤ b ∧
    f (unary n) = tup [natCode a, natCode b] ∧ ε n = (a : ℝ) / (b : ℝ)

end Supplement

end UnitaryQIPPSPACE


