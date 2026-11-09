-- Prove2me | Definitions.Def_QMAvsQCIP_CHPairs
-- name    : QMAvsQCIP_CHPairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:24.292915+00:00
-- url     : https://prove2.me/theorems/c02c1db0-d2ec-4a39-832e-002b749a47cc
-- title:
--   Codeword-hash pairs $A_H$
-- statement:
--   For a predicate family $H$, the set of **codeword-hash pairs** is
--   $$
--   A_H=\{(z,v)\in\{0,1\}^q\times C : H(v)=z\}. \tag{2}
--   $$
--
--   Theorem 3 and Corollary 2 show that no short message lets an oracle-free decoder recover many elements of $A_H$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 6, Eq. (2), p.18

import Definitions.Def_QMAvsQCIP_code
import Definitions.Def_QMAvsQCIP_hashOf

set_option autoImplicit false

namespace QMAvsQCIP

/-- The set of **codeword-hash pairs** `A_H = {(z, v) ∈ {0,1}^q × C : H(v) = z}` (Eq. (2)).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 6, p.18 (PDF p.21): "We call (z, v) a codeword-hash pair if it belongs to
A_H = {(z, v) ∈ {0,1}^q × C : H(v) = z}. (2)" -/
noncomputable def CHPairs {lam : ℕ} {q : ℕ+} (H : ZMod q × Sym lam q → Bool) :
    Finset ((ZMod q → Bool) × {v // v ∈ code lam q}) :=
  Finset.univ.filter (fun p => hashOf H p.2.1 = p.1)

end QMAvsQCIP


