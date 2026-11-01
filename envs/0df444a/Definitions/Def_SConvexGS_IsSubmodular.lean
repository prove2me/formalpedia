-- Prove2me | Definitions.Def_SConvexGS_IsSubmodular
-- name    : SConvexGS_IsSubmodular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:20.679267+00:00
-- url     : https://prove2.me/theorems/490fa3e2-e6d5-402c-be21-ce300085d462
-- title:
--   Submodular function
-- statement:
--   A function $h:\mathbb R^n\to(-\infty,\infty]$ is **submodular** if its negative is supermodular, that is,
--
--   $$h(x\wedge y)+h(x\vee y)\le h(x)+h(y)\qquad\text{for all }x,y\in\mathbb R^n.$$
--
--   Here $\wedge$ and $\vee$ are the componentwise minimum and maximum. Theorem 3 assumes this of $f^*$.
--
--   **Formalization Note** The inequality is written out. For the functions it is applied to, no sum $-\infty+\infty$ occurs, so it is the supermodular inequality for $-h$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9

import Mathlib

namespace SConvexGS

/-- Submodularity on the `(−∞, ∞]` side (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN
3549632 (PDF of 2021-10-29), §1.4, p.9): "A function is submodular if its negative is
supermodular", i.e. `h(x ∧ y) + h(x ∨ y) ≤ h(x) + h(y)` for all `x, y ∈ ℝⁿ`.

Formalization Note: the inequality is written out, for `h` with no value `⊥`, or with `h ≡ ⊥`. For
such `h` no sum `⊥ + ⊤` occurs and this is the supermodular inequality for `−h`. It is used only
for `h = f*` with `f > −∞`. `∧` and `∨` are `⊓` and `⊔` of the Pi lattice. -/
def IsSubmodular {n : ℕ} (h : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x y, h (x ⊓ y) + h (x ⊔ y) ≤ h x + h y

end SConvexGS


