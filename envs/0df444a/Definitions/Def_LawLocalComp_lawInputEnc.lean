-- Prove2me | Definitions.Def_LawLocalComp_lawInputEnc
-- name    : LawLocalComp_lawInputEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:36.721268+00:00
-- url     : https://prove2.me/theorems/66870b3b-9504-4933-86a3-ce6ef1407bb4
-- title:
--   Machine input: parameters, unary pad and law
-- statement:
--   The input of a parametrized law map on parameters $p$ and a law list $\ell$ is: the rational parameters of $p$ in binary, a separator, a block of `pad p` copies of the symbol $1$, a separator, and the encoding of $\ell$.
--
--   **Formalization Note** The pad is the only unary part. With pad $\lceil1/\varepsilon\rceil$, "polynomial in the input length" is "polynomial in the input bits, $1/\varepsilon$ and the bit lengths of the resources".
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; Lemma 4.1, p.6

import Mathlib
import Definitions.Def_LawLocalComp_encPairs

namespace LawLocalComp

/-- **Machine input: parameters, unary pad, law.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2 ("polynomial in input bits, 1/ε and logarithmic supplied resources");
Lemma 4.1, p.6 ("polynomial bit cost in input, k, log N").

For parameters `p`, `lawInputEnc params pad (p, ℓ)` writes the rational parameter list `params p` in
binary, the separator `3`, `pad p` copies of the symbol `1`, the separator `3`, and the law list `ℓ`.

**Formalization Note.** The pad is the only unary component. With `pad = ⌈1/ε⌉₊` a polynomial in the
input length is a polynomial in the input bits, `1/ε` and the bit lengths of the resources, which is
"polynomial in 1/ε and log N" read literally. -/
def lawInputEnc {P : Type} (params : P → List ℚ) (pad : P → ℕ) :
    P × List (ℚ × ℚ) → List OnlineCRS.Combine.Sym :=
  fun x => RobustToDynamics.encListRat (params x.1) ++ [3] ++ List.replicate (pad x.1) 1 ++ [3] ++
    encPairs x.2

end LawLocalComp


