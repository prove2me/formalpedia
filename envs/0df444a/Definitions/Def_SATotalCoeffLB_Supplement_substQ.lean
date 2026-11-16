-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_substQ
-- name    : SATotalCoeffLB_Supplement_substQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:30:08.416201+00:00
-- url     : https://prove2.me/theorems/f8bf1c1c-7f01-4963-bc7a-3bd42fa1688b
-- title:
--   The restriction $C(W,q)$ at a fixed $q\in\{\pm1\}^Q$
-- statement:
--   For $C$ in $\mathbb R[W, Q]/\langle y^2 - 1 : y \in W \cup Q\rangle$ and a fixed $q \in \{\pm1\}^Q$, $C(W, q)$ is the polynomial in the $W$-variables obtained by substituting $q$ for the random variables:
--
--   $$
--   C(W, q)(w) = C(w, q), \qquad w \in \{\pm1\}^W .
--   $$
--
--   **Formalization Note** $q$ is a bit vector, the $\pm1$ value of $q_j$ being $(-1)^{q_j}$, as for the published `CubeFn`.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.6 (Averaging total coefficient size); Theorem 9, p.74

import Mathlib
import Definitions.Def_SATotalCoeffLB_CubeFn

namespace SATotalCoeffLB.Supplement

open SATotalCoeffLB

/-- **The restriction `C(W, q)`**: for `C` in `ℝ[W, Q]/⟨y² − 1⟩` and a fixed assignment
`q ∈ {±1}^Q`, the polynomial in the `W`-variables obtained by substituting `q` (p.6,
"Averaging total coefficient size", and Theorem 9, p.74, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)).

**Formalization Note** `q` is a bit vector `Q → ZMod 2` (`±1` value `(-1)^{q j}`), as for
`CubeFn`. -/
def substQ {W Q : Type*} (C : CubeFn (W ⊕ Q)) (q : Q → ZMod 2) : CubeFn W :=
  fun x => C (Sum.elim x q)

end SATotalCoeffLB.Supplement


