-- Prove2me | Definitions.Def_DynHaussler_Xd
-- name    : DynHaussler_Xd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:53.92773+00:00
-- url     : https://prove2.me/theorems/cdd4691b-1d4c-4900-9ac2-72a3e6954fb3
-- title:
--   Lower-bound domain $X_d=\bigsqcup_{m\ge1}(\{m\}\times\mathbb F_{2^m}^d)$ (Eq. (108))
-- statement:
--   For an integer $d\ge1$, the **domain of the fixed lower-bound class** is the disjoint union
--   $$
--   X_d=\bigsqcup_{m\ge1}\bigl(\{m\}\times\mathbb F_{2^m}^d\bigr),
--   $$
--   where $\mathbb F_{2^m}$ is a field with $2^m$ elements. It is countable and depends only on $d$.
--
--   **Formalization Note** The field with $2^m$ elements is Mathlib's `GaloisField 2 m`, $m\ge1$ is a positive natural number (`ℕ+`), and the disjoint union is a dependent pair type.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (108), p.46 (PDF p.48)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **domain** `X_d = ⨆_{m ≥ 1} ({m} × F_{2^m}^d)` of the fixed lower-bound class: the disjoint
union over `m ≥ 1` of the blocks `F_{2^m}^d`, for a field `F_{2^m}` with `2^m` elements (Eq. (108)).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (108), p.46 (PDF p.48).

**Formalization Note** The field with `2^m` elements is Mathlib's `GaloisField 2 m` (of
cardinality `2^m` for `m ≠ 0`); `m ≥ 1` is `m : ℕ+`; the disjoint union is a `Sigma` type. -/
abbrev Xd (d : ℕ) : Type := Σ m : ℕ+, (Fin d → GaloisField 2 (m : ℕ))

end DynHaussler


