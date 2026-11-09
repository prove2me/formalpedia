-- Prove2me | Definitions.Def_QMAvsQCIP_Sym
-- name    : QMAvsQCIP_Sym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:25.755257+00:00
-- url     : https://prove2.me/theorems/b788515b-6458-4d54-b522-6da9002731f2
-- title:
--   Symbol alphabet $\Sigma=\mathbb F_q^\lambda$
-- statement:
--   The alphabet of the multiplicity code is
--   $$
--   \Sigma=\mathbb F_q^\lambda ,
--   $$
--   the $\lambda$-tuples of field elements; a codeword has one symbol of $\Sigma$ for each coordinate $i\in[q]$.
--
--   **Formalization Note** The field is `ZMod q`, a field when $q$ is prime; $\lambda$ is written `lam` in Lean.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The symbol alphabet `Σ = F_q^λ` of the multiplicity code: a symbol is a `λ`-tuple of
elements of `ZMod q` (the field `F_q` when `q` is prime).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21): "a univariate multiplicity code C ⊆ Σ^q over Σ = F_q^λ".

**Formalization Note.** `λ` is written `lam` (`λ` is a Lean keyword). -/
abbrev Sym (lam q : ℕ) : Type := Fin lam → ZMod q

end QMAvsQCIP


