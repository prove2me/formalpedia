-- Prove2me | Definitions.Def_QuantumHMMR_Dt
-- name    : QuantumHMMR_Dt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:29.660197+00:00
-- url     : https://prove2.me/theorems/de732a76-9e79-4c72-bfeb-90b3b20829d1
-- title:
--   The constant $D_t = \prod_{j=0}^{t-2}(2^j + 1)$
-- statement:
--   For an integer $t$,
--   $$
--   D_t = \prod_{j=0}^{t-2} (2^j + 1). \tag{12}
--   $$
--   By Lemma 4.2 it is the rank of the order-$t$ Clifford moment operator for all large $n$. For example $D_4 = 2 \cdot 3 \cdot 5 = 30$.
--
--   **Formalization Note** The product runs over `Finset.range (t - 1)`; it is used for $t \ge 4$ only.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.2, Eq. (12), p.13

import Mathlib

namespace QuantumHMMR

/-- The constant `D_t = ∏_{j=0}^{t-2} (2^j + 1)` of Eq. (12) (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Lemma 4.2, p.13), the rank of
the `t`-th Clifford moment operator for large `n`. For example `D_4 = 2 · 3 · 5 = 30`.

**Formalization Note** The product over `j = 0, …, t - 2` is `Finset.range (t - 1)`; it is used for
`t ≥ 4` only. -/
def Dt (t : ℕ) : ℕ :=
  ∏ j ∈ Finset.range (t - 1), (2 ^ j + 1)

end QuantumHMMR


