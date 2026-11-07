-- Prove2me | Definitions.Def_DynHaussler_hypClass
-- name    : DynHaussler_hypClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:54.474102+00:00
-- url     : https://prove2.me/theorems/e1406c54-88b2-4543-bb79-77dad658e683
-- title:
--   Finite-field hyperplane class $H_q=\{h_{a,b}\}$ on $\mathbb F_q^d$ (Eq. (106))
-- statement:
--   Let $\mathbb F_q$ be a field with $q$ elements and $d\ge1$. On the domain $X_q=\mathbb F_q^d$ define, for $a\in\mathbb F_q^d\setminus\{0\}$ and $b\in\mathbb F_q$,
--   $$
--   H_{a,b}=\{x\in\mathbb F_q^d:\ a\cdot x=b\},\qquad h_{a,b}(x)=\mathbf 1\{x\in H_{a,b}\},
--   $$
--   where $a\cdot x=\sum_{j=1}^d a_jx_j$ is computed in $\mathbb F_q$, and let $H_q=\{h_{a,b}: a\neq0,\ b\in\mathbb F_q\}$ be the set of these hyperplane indicators.
--
--   This class supplies, on one block of the lower-bound domain, at least $q^d$ functions whose traces are pairwise far apart in normalized $\ell_p$ distance.
--
--   **Formalization Note** The field is an arbitrary field type `F` (for a finite field, $q$ is its cardinality). Indicators are real-valued ($0$ or $1$); the set collects the distinct indicator functions, so parameter pairs giving the same hyperplane give one member.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (106), p.46 (PDF p.48)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **finite-field hyperplane class** `H_q = {h_{a,b} : a ∈ F_q^d ∖ {0}, b ∈ F_q}` on
`X_q = F_q^d`, where `h_{a,b}(x) = 1{a · x = b}` and `a · x = ∑_{j=1}^d a_j x_j` is computed in
`F_q` (Eq. (106)).
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (106), p.46 (PDF p.48).

**Formalization Note** `F` is any field; the paper's `F_q` with `q` a prime power is the case of
a finite field with `q = card F` elements. Indicators are real-valued (`1` or `0`), so `H_q` is a
set of functions `(Fin d → F) → ℝ`; the set collects the distinct indicators (two parameter pairs
giving the same hyperplane give one member). -/
noncomputable def hypClass (F : Type*) [Field F] (d : ℕ) : Set ((Fin d → F) → ℝ) :=
  open Classical in
  {h | ∃ a : Fin d → F, a ≠ 0 ∧ ∃ b : F, h = fun x => if ∑ j, a j * x j = b then 1 else 0}

end DynHaussler


