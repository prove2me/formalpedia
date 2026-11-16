-- Prove2me | Definitions.Def_CubicProductLB_Supplement_signCubeP
-- name    : CubicProductLB_Supplement_signCubeP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:08.028891+00:00
-- url     : https://prove2.me/theorems/2eadb897-0ac1-431d-8280-3829a6838df8
-- title:
--   The sign cube $\{-1,1\}^n \subseteq \mathbb F_p^n$
-- statement:
--   For a modulus $p$, the **sign cube** over $\mathbb F_p$ is
--   $$\{-1,1\}^n = \{x \in \mathbb F_p^n : x_i \in \{1,-1\} \text{ for every } i\}.$$
--   Section 15 identifies the signs $\pm1$ with the corresponding elements of $\mathbb F_p$; all identities of that section are functional identities on this set.
--
--   **Formalization Note** Coordinates are indexed by `Fin n`. The base mission's sign cube is hard-wired to $\mathbb F_3$, so the general field needs its own copy; the theorems add $p$ prime, $p>3$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.1, Eqs. (397)–(398), p.51

import Mathlib

namespace CubicProductLB.Supplement

/-- The sign cube `{-1, 1}^n ⊆ F_p^n` over a general prime field (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 15, Eqs. (397)–(398), p.51:
"We identify the signs ±1 with the corresponding elements of F_p").

**Formalization Note** Coordinates are 0-based (`Fin n`). The modulus `p` carries no hypothesis here;
the theorems add `p` prime, `3 < p`. -/
def signCubeP (p n : ℕ) : Set (Fin n → ZMod p) :=
  {x | ∀ i, x i = 1 ∨ x i = -1}

end CubicProductLB.Supplement


