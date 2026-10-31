-- Prove2me | Definitions.Def_CompositeSAA_IsModulus
-- name    : CompositeSAA_IsModulus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:46.19195+00:00
-- url     : https://prove2.me/theorems/1edccd4e-3ae5-4941-a1d9-d33815a9e4bd
-- title:
--   Modulus of continuity $w:\mathbb R_+\to\mathbb R_+$, $\lim_{t\downarrow0}w(t)=w(0)=0$
-- statement:
--   A **modulus of continuity** is a function $w:\mathbb R_+\to\mathbb R_+$ with
--
--   $$
--   \lim_{t\downarrow0}w(t)=w(0)=0 .
--   $$
--
--   A function $g$ admits the modulus $w$ on a set $C$ if $|g(x)-g(x')|\le w(\|x-x'\|)$ for all $x,x'\in C$. The class $\tilde{\mathfrak F}$ of the paper consists of functions admitting given moduli.
--
--   **Formalization Note** $w$ is a function on $\mathbb R$ that is required to be nonnegative on $[0,\infty)$; its values at negative arguments are irrelevant.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.5 (definition of $\tilde{\mathfrak F}$)

import Mathlib

open Filter Topology

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, p.5: a *modulus of continuity*, a function
`w : ℝ₊ → ℝ₊` with `lim_{t↓0} w(t) = w(0) = 0`.

**Formalization Note** `w` is a function on `ℝ`; only its values on `[0, ∞)` matter, where it is
required to be nonnegative. "`lim_{t↓0} w(t) = 0`" is the limit from the right at `0`. -/
def IsModulus (w : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ w t) ∧ Tendsto w (𝓝[>] 0) (𝓝 0)

end CompositeSAA


