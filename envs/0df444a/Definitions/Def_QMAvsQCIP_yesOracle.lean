-- Prove2me | Definitions.Def_QMAvsQCIP_yesOracle
-- name    : QMAvsQCIP_yesOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:22.580209+00:00
-- url     : https://prove2.me/theorems/6300e203-ecf6-4a43-bae5-76b6c39a8545
-- title:
--   Codeword-hash structure oracle $O_H$
-- statement:
--   For a predicate family $H$, the oracle $O_H:Z_\lambda\to\{0,1\}$ marks the pairs whose codeword hashes to the padded string:
--   $$
--   O_H(y,v)=\begin{cases}1,&H(v)=y\|0^{q-\lambda},\\0,&\text{otherwise.}\end{cases}
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, p.24

import Definitions.Def_QMAvsQCIP_Zdom
import Definitions.Def_QMAvsQCIP_hashOf
import Definitions.Def_QMAvsQCIP_padTarget

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **codeword-hash structure oracle** `O_H : Z_λ → {0,1}` of a predicate family `H`:
`O_H(y, v) = 1` iff `H(v) = y∥0^{q−λ}`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "let H(v) = (H_i(v_i))_{i∈[q]} be the
symbol-wise hash. Define O(y, v) = 1 if H(v) = y∥0^{q−λ}, 0 otherwise." -/
def yesOracle {lam : ℕ} {q : ℕ+} (H : ZMod q × Sym lam q → Bool) : Zdom lam q → Bool :=
  fun p => decide (hashOf H p.2.1 = padTarget lam q p.1)

end QMAvsQCIP


