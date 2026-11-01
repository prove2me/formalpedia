-- Prove2me | Definitions.Def_MVBlossoms_IsKIndex
-- name    : MVBlossoms_IsKIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:44:15.077992+00:00
-- url     : https://prove2.me/theorems/222c2721-ad64-48e0-9422-cf15f818cb3c
-- title:
--   The index $k(s,u)$
-- statement:
--   For a vertex $u$ and a number $s$,
--
--   $$
--   k(s,u)=\min\{l : \mathrm{tenacity}(\mathrm{base}^l(u))\ge s\},
--   $$
--
--   the index of the first iterated base of $u$ of tenacity at least $s$. The predicate says that $x_0=u,x_1,\dots,x_l$ are the iterated bases of $u$ and $l=k(s,u)$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 26, p.2034

import Mathlib
import Definitions.Def_MVBlossoms_tenacity
import Definitions.Def_MVBlossoms_IsBaseChain

namespace MVBlossoms

/-- **The index `k(s, u)`.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 26, p.2034: "Define k(t, v) such that
base^{k(t,v)}(v) is the first iterated base of v having tenacity at least t: that is,
k(t,v) = min{l | tenacity(base^l(v)) ≥ t}."

`IsKIndex M s u x l`: `x` is the chain of iterated bases of `u` up to index `l`, and `l` is the
least index whose iterated base has tenacity at least `s`, i.e. `k(s, u) = l`. -/
def IsKIndex {V : Type} [DecidableEq V] {G : SimpleGraph V} (M : G.Subgraph) (s : ℕ) (u : V) (x : ℕ → V) (l : ℕ) : Prop :=
  IsBaseChain M u x l ∧ (s : ℕ∞) ≤ tenacity M (x l) ∧ ∀ i < l, tenacity M (x i) < (s : ℕ∞)

end MVBlossoms


