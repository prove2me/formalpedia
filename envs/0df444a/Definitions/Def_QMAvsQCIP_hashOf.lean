-- Prove2me | Definitions.Def_QMAvsQCIP_hashOf
-- name    : QMAvsQCIP_hashOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:19.207075+00:00
-- url     : https://prove2.me/theorems/ddce24cb-ca2a-4835-ba11-2fd70f3ff865
-- title:
--   Symbol-wise hash $H(v)$
-- statement:
--   For predicates $H_i:\Sigma\to\{0,1\}$, $i\in[q]$, written as one function $H(i,a)=H_i(a)$, the **symbol-wise hash** of a word $v\in\Sigma^q$ is
--   $$
--   H(v)=H_1(v_1)\,\|\,\cdots\,\|\,H_q(v_q)\in\{0,1\}^q .
--   $$
--
--   **Formalization Note** Coordinates are the elements of `ZMod q`.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 6, p.18

import Definitions.Def_QMAvsQCIP_Sym

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **symbol-wise hash** `H(v) = H_1(v_1) ∥ ⋯ ∥ H_q(v_q) ∈ {0,1}^q` of a word `v ∈ Σ^q` under
the predicate family `H_i : Σ → {0,1}`, written as one function `H : [q] × Σ → {0,1}`,
`H(i, a) = H_i(a)`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 6, p.18 (PDF p.21): "For a code C ⊆ Σ^q and predicates H_i : Σ → {0,1} for
i ∈ [q], we define the symbol-wise hash H(v) = H_1(v_1)∥ · · · ∥H_q(v_q)."

**Formalization Note.** Coordinates `i ∈ [q]` are the elements of `ZMod q`. -/
def hashOf {lam q : ℕ} (H : ZMod q × Sym lam q → Bool) (v : ZMod q → Sym lam q) :
    ZMod q → Bool :=
  fun α => H (α, v α)

end QMAvsQCIP


