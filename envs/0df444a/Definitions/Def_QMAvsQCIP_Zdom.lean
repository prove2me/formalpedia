-- Prove2me | Definitions.Def_QMAvsQCIP_Zdom
-- name    : QMAvsQCIP_Zdom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:26.160191+00:00
-- url     : https://prove2.me/theorems/55976961-9d63-4878-ab06-2ddbb86454d2
-- title:
--   Query domain $Z_\lambda=\{0,1\}^\lambda\times C$
-- statement:
--   The query domain of the CHS oracles:
--   $$
--   Z_\lambda=\{0,1\}^\lambda\times C, \tag{12}
--   $$
--   pairs $(y,v)$ of a $\lambda$-bit string and a codeword of the multiplicity code. The oracles of the query complexity separation are functions $O:Z_\lambda\to\{0,1\}$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 8, Eq. (12), p.24

import Definitions.Def_QMAvsQCIP_code

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **query domain** `Z_λ = {0,1}^λ × C` of the CHS oracles (Eq. (12)): pairs `(y, v)` of a
`λ`-bit string and a codeword of the multiplicity code `C = code λ q`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 8, p.24 (PDF p.27): "Boolean oracles with query pairs
(y, v) ∈ {0,1}^λ × C: O : Z_λ → {0,1}, Z_λ = {0,1}^λ × C. (12)" -/
abbrev Zdom (lam : ℕ) (q : ℕ+) : Type := (Fin lam → Bool) × {v // v ∈ code lam q}

end QMAvsQCIP


