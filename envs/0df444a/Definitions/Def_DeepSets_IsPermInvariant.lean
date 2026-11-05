-- Prove2me | Definitions.Def_DeepSets_IsPermInvariant
-- name    : DeepSets_IsPermInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:32.3898+00:00
-- url     : https://prove2.me/theorems/50d24ab4-1435-4121-9c15-82c5e564c915
-- title:
--   Property 1 — permutation invariance of a function of a finite set
-- statement:
--   Let $\mathfrak X$ be a universe of elements. A finite set $X=\{x_1,\dots,x_M\}$ with $x_m\in\mathfrak X$ can be listed in many orders. A real-valued function $f$ that is given a listing of a set of any size $M\ge 0$ is **permutation invariant** (Property 1) when its value does not depend on the order of the listing:
--   $$
--   f(\{x_1,\dots,x_M\}) = f(\{x_{\pi(1)},\dots,x_{\pi(M)}\})\qquad\text{for every permutation } \pi \text{ of } \{1,\dots,M\}.
--   $$
--   Such functions are the "valid set functions" of Deep Sets: functions of the set itself, not of the order in which its elements are presented. Theorem 2 characterizes them on a countable universe.
--
--   **Formalization Note** The universe is a type `U`. A listing of a set $\{x_1,\dots,x_M\}$ is an injective tuple $x:\mathrm{Fin}\,M\to U$ (the elements of a set are distinct), and the reordered listing $(x_{\pi(1)},\dots,x_{\pi(M)})$ is $x\circ\pi$ for $\pi\in\mathrm{Perm}(\mathrm{Fin}\,M)$. The function is $f : (M:\mathbb N)\to(\mathrm{Fin}\,M\to U)\to\mathbb R$; its values on tuples with repeated entries play no role. The empty set is the case $M=0$.
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A, Property 1, eq. (7), p.12 (PDF p.12); also §2.1, Property 1, p.2

import Mathlib

namespace DeepSets

/-- **Property 1** (Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, *Deep Sets*,
arXiv:1703.06114v3, §A, p.12, eq. (7); also §2.1, p.2): a function `f` acting on sets is
permutation invariant to the order of the objects in the set,
`f({x₁, …, x_M}) = f({x_{π(1)}, …, x_{π(M)}})` for every permutation `π`.

**Formalization Note** The universe `𝔛` of the paper is a type `U` (a script letter is not a
reliable Lean identifier). A finite set `X = {x₁, …, x_M}` with `x_m ∈ 𝔛`, presented in the
listing `x₁, …, x_M`, is an injective tuple `x : Fin M → U` (the elements of a set are
distinct); the listing `x_{π(1)}, …, x_{π(M)}` is `x ∘ π` for `π : Equiv.Perm (Fin M)`.
So `f` assigns a real number `f M x` to each listing of each size `M ≥ 0` (the empty set is the
case `M = 0`), and Property 1 says that this number does not depend on the order of the listing.
Values of `f` on non-injective tuples are never constrained. -/
def IsPermInvariant {U : Type*} (f : (M : ℕ) → (Fin M → U) → ℝ) : Prop :=
  ∀ (M : ℕ) (x : Fin M → U), Function.Injective x →
    ∀ π : Equiv.Perm (Fin M), f M (x ∘ π) = f M x

end DeepSets


