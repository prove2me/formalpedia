-- Prove2me | Definitions.Def_DeepSets_Supplement_IsPermInvariantOn
-- name    : DeepSets_Supplement_IsPermInvariantOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:25:42.865854+00:00
-- url     : https://prove2.me/theorems/5016842b-5390-461b-bd35-b848f2fc21db
-- title:
--   Property 1 at a fixed set size: permutation invariance on $D^M$
-- statement:
--   Fix a set size $M\ge 0$, a set $D$ of elements, and a real-valued function $f$ of $M$ arguments. The function is **permutation invariant on $D^M$** (Property 1 at the fixed size $M$) when
--   $$
--   f(x_1,\dots,x_M)=f(x_{\pi(1)},\dots,x_{\pi(M)})
--   $$
--   for every $(x_1,\dots,x_M)\in D^M$ and every permutation $\pi$ of $\{1,\dots,M\}$. Tuples with repeated entries are included. This is the notion of invariance of the uncountable case (§A.2), used with $D=[0,1]$ in Theorem 7 and with a compact $D\subseteq\mathbb R^d$ in Theorem 9.
--
--   **Formalization Note** A tuple is $x:\mathrm{Fin}\,M\to U$ and the permuted tuple is $x\circ\pi$. Values of $f$ outside $D^M$ are not constrained. The published predicate `DeepSets.IsPermInvariant` of Theorem 2 is a different condition: it concerns a family of functions, one for each size, and constrains tuples of distinct elements only.
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A, Property 1, eq. (7), p.12 (PDF p.12), with the fixed set size and the domain [0,1]^M of §A.2, p.12

import Mathlib

namespace DeepSets.Supplement

/-- **Property 1 at a fixed set size** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A,
Property 1, eq. (7), p.12, as used in §A.2, pp.12–15): for a fixed `M`, a function `f` of
`M` elements of `D` is permutation invariant when
`f(x₁, …, x_M) = f(x_{π(1)}, …, x_{π(M)})` for every permutation `π`.

**Formalization Note** In §A.2 the inputs are all the tuples of `D^M`, repeated entries included
(`D = [0,1]`, or a compact `D ⊆ ℝ^d`). The predicate `DeepSets.IsPermInvariant` of Theorem 2
differs: it takes a family over all sizes and constrains tuples of distinct elements only.
Values of `f` outside `D^M` are not constrained. -/
def IsPermInvariantOn {U : Type*} {M : ℕ} (D : Set U) (f : (Fin M → U) → ℝ) : Prop :=
  ∀ x : Fin M → U, (∀ m, x m ∈ D) → ∀ π : Equiv.Perm (Fin M), f (x ∘ π) = f x

end DeepSets.Supplement


