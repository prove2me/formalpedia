-- Prove2me | Definitions.Def_FinitePermutationCoupling_BlockModel
-- name    : FinitePermutationCoupling_BlockModel
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-11-17T18:25:04.500367+00:00
-- url     : https://prove2.me/theorems/b990c9c6-a645-441c-87c9-15d397e456d6
-- title:
--   Finite permutation classes and conditional completion counts
-- statement:
--   Let $A$ be finite, let $b:A\to K$ label disjoint classes, and designate some classes as active. The product support $P_b$ consists of all permutations preserving $b$; the class of $x$ is $C(x)=b^{-1}(b(x))$. For a source support $S$, exposed inputs $D$, and reference permutation $h$, define
--   $$F(S,D,h)=\{\pi\in S:\pi(d)=h(d)\text{ for every }d\in D\}.$$
--   The uniform density is $\rho_S(h)=\mathbf1[h\in S]/|S|$. Active saturation means membership in $S$ depends only on active input images among permutations in $P_b$. The conditional partner cap is the finite-count condition
--   $$\bigl(|C(x)\setminus D|-1\bigr)\,|\{\pi\in F(S,D,h):\pi(x)=y\}|\le |F(S,D,h)|$$
--   for every active unexposed input $x$ and every target $y$. Natural subtraction is truncated. These definitions record finite counting data only; they assert no existence of a coupling.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4, Section 4.4, proof of Lemma 4.13, equations (76)--(77) and the three-step random-order correction process between them. Abstract notation for the source supports, records B, residual classes, and conditional partner bound. No theorem is included.

import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Perm

namespace FinitePermutationCoupling

open Classical
open scoped BigOperators

variable {α κ : Type*} [Fintype α]

/-- The product of the symmetric groups on the fibers of a class map. -/
noncomputable def blockSupport (block : α → κ) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun π => ∀ x, block (π x) = block x

/-- The class containing a given input. -/
noncomputable def blockFiber (block : α → κ) (x : α) : Finset α :=
  Finset.univ.filter fun y => block y = block x

/-- Source permutations agreeing with an exposed reference assignment. -/
noncomputable def exposedFiber (S : Finset (Equiv.Perm α)) (D : Finset α)
    (h : Equiv.Perm α) : Finset (Equiv.Perm α) :=
  S.filter fun π => ∀ x ∈ D, π x = h x

/-- Uniform finite density, with value zero off the support. -/
noncomputable def density (S : Finset (Equiv.Perm α)) (h : Equiv.Perm α) : ℝ :=
  if h ∈ S then 1 / (S.card : ℝ) else 0

/-- The source condition only constrains the designated active classes. -/
def ActiveSaturated (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) : Prop :=
  ∀ f ∈ blockSupport block, ∀ g ∈ blockSupport block,
    (∀ x, active (block x) → f x = g x) → (f ∈ S ↔ g ∈ S)

/-- Unnormalized form of the conditional partner bound. With `r` unexposed
inputs in a class, every partner has conditional probability at most `1/(r-1)`
when `r ≥ 2`. Empty conditioning fibers and singleton residual classes are allowed. -/
def PartnerCap (block : α → κ) (active : κ → Prop)
    (S : Finset (Equiv.Perm α)) : Prop :=
  ∀ (D : Finset α) (h : Equiv.Perm α) (x y : α),
    active (block x) → x ∉ D →
    ((blockFiber block x \ D).card - 1) *
        ((exposedFiber S D h).filter fun π => π x = y).card ≤
      (exposedFiber S D h).card

end FinitePermutationCoupling


