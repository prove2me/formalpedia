-- Prove2me | Definitions.Def_CubicProductLB_HasObsRep
-- name    : CubicProductLB_HasObsRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:12.483456+00:00
-- url     : https://prove2.me/theorems/475a7657-9aed-4a7f-9221-2dfda5c35dd6
-- title:
--   Observation representations over $\mathbb F_3$
-- statement:
--   A function $f : \{0,1\}^N \to \mathbb F_2$ has an **$r$-observation representation** over $\mathbb F_3$ if there are affine forms
--   $$L_a(z) = c_a + \sum_{i=1}^N \lambda_{a,i} z_i \in \mathbb F_3, \qquad 1 \le a \le r,$$
--   and an arbitrary map $h : \mathbb F_3^r \to \mathbb F_2$, with $f(z) = h(L_1(z), \dots, L_r(z))$ for every $z \in \{0,1\}^N$. The outer map need not be polynomial; only the number of observed forms is bounded.
--
--   **Formalization Note** The page's condition $r \ge 1$ is placed on the theorems that use the definition.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 18, Eqs. (301)–(303), p.35

import Mathlib

namespace CubicProductLB

/-- `f : {0,1}^N → F_2` has an `r`-observation representation over `F_3`:
`f(z) = h(L_1(z), …, L_r(z))` with `L_a(z) = c_a + ∑_i λ_{a,i} z_i` over `F_3` and an arbitrary
`h : F_3^r → F_2` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 18, Eqs. (301)–(303), p.35).

**Formalization Note** The page's `r ≥ 1` is on the theorems that use it. -/
def HasObsRep {N : ℕ} (r : ℕ) (f : (Fin N → Bool) → ZMod 2) : Prop :=
  ∃ (c : Fin r → ZMod 3) (lam : Fin r → Fin N → ZMod 3) (h : (Fin r → ZMod 3) → ZMod 2),
    ∀ z, f z = h fun a => c a + ∑ i, lam a i * (if z i then 1 else 0)

end CubicProductLB


