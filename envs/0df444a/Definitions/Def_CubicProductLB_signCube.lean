-- Prove2me | Definitions.Def_CubicProductLB_signCube
-- name    : CubicProductLB_signCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:16.672209+00:00
-- url     : https://prove2.me/theorems/19b12cb0-1364-4d3d-8788-91944434fe79
-- title:
--   The sign cube $X_n = \{-1,1\}^n \subseteq \mathbb F_3^n$
-- statement:
--   The **sign cube** is the set
--   $$X_n = \{-1, 1\}^n \subseteq \mathbb F_3^n$$
--   of vectors over the three-element field all of whose coordinates are $1$ or $-1$. All functional identities of the mission are required on $X_n$ only, not as identities of formal polynomials.
--
--   **Formalization Note** Coordinates are indexed by `Fin n`, that is, from $0$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (1), p.3

import Mathlib

namespace CubicProductLB

/-- The sign cube `X_n = {-1, 1}^n ⊆ F_3^n` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (1), p.3).

**Formalization Note** Coordinates are 0-based (`Fin n`). -/
def signCube (n : ℕ) : Set (Fin n → ZMod 3) :=
  {x | ∀ i, x i = 1 ∨ x i = -1}

end CubicProductLB


