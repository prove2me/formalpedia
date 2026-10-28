-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup
-- name    : StrictTwoGroups_TwoEquiv_StrictTwoGroup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:13.604008+00:00
-- url     : https://prove2.me/theorems/13b458c5-4f0f-417a-a9b7-255c3fffde47
-- title:
--   §1, p. 3 and §2, p. 6 — strict 2-groups (internal categories in groups)
-- statement:
--   A **strict 2-group** is an internal category in the category of groups (Porst, §2, p. 6). It consists of a group $G_0$ of objects, a group $G_1$ of morphisms, group morphisms
--   $$s,t:G_1\to G_0,\qquad i:G_0\to G_1$$
--   (source, target, identity) and a composition $\circ:G_1\,{}_s\!\times_t G_1\to G_1$, $(a,b)\mapsto a\circ b$ ("$a$ after $b$", defined when $s a=t b$), such that the four diagrams (1) of p. 2 commute:
--
--   1. $s\,i=\mathrm{id}_{G_0}=t\,i$;
--   2. $s(a\circ b)=s b$ and $t(a\circ b)=t a$;
--   3. $a\circ i(s a)=a=i(t a)\circ a$;
--   4. $(a\circ b)\circ c=a\circ(b\circ c)$ whenever $s a=t b$ and $s b=t c$;
--
--   and the composition is a group morphism on the pullback, which is the interchange law (8):
--   $$(a\cdot a')\circ(b\cdot b')=(a\circ b)\cdot(a'\circ b')\qquad\text{for } s a=t b,\ s a'=t b'.$$
--
--   Strict 2-groups are the objects of the 2-category $2\text{-}\mathit{Grp}$.
--
--   **Formalization Note** The structure `StrictTwoGroup` carries $G_0,G_1$, the group morphisms $s,t,i$, a composition `comp` defined as a total function $G_1\to G_1\to G_1$ (`comp a b` $=a\circ b$), and the two equations $s\,i=\mathrm{id}=t\,i$ as fields (they are needed to define the 2-functor $T$). The predicate `IsStrictTwoGroup` carries the remaining clauses 2–4 and the interchange law, each on composable pairs only, so the values of `comp` off $G_1\,{}_s\!\times_t G_1$ are unconstrained and irrelevant. The fields together with the predicate are the paper's definition.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 2 diagrams (1), p. 3 Definition (internal category), p. 6 Definition (strict 2-group) and interchange law (8)

import Mathlib

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- The data of a strict 2-group (§1, p. 3; §2, p. 6): groups `G₀` (objects) and `G₁`
(morphisms), group morphisms `s, t : G₁ → G₀` (source, target) and `i : G₀ → G₁` (identity)
with `s ∘ i = id = t ∘ i`, and a composition `comp a b = a ∘ b` ("`a` after `b`"), meaningful
when `s a = t b`. The remaining axioms are the predicate `IsStrictTwoGroup`. -/
structure StrictTwoGroup where
  G0 : Type u
  G1 : Type u
  [grp0 : Group G0]
  [grp1 : Group G1]
  s : G1 →* G0
  t : G1 →* G0
  i : G0 →* G1
  /-- `comp a b` = `a ∘ b` (`a` after `b`); meaningful when `s a = t b`. -/
  comp : G1 → G1 → G1
  s_i : ∀ g, s (i g) = g
  t_i : ∀ g, t (i g) = g

attribute [instance] StrictTwoGroup.grp0 StrictTwoGroup.grp1

/-- The remaining diagrams (1) of an internal category (source and target of a composite,
units, associativity), each on composable pairs, and the interchange law (8), which says that
the composition `G₁ ₛ×ₜ G₁ → G₁` is a group morphism. Together with the fields of
`StrictTwoGroup` this is the paper's definition of a strict 2-group. -/
def IsStrictTwoGroup (G : StrictTwoGroup.{u}) : Prop :=
  (∀ a b, G.s a = G.t b → G.s (G.comp a b) = G.s b ∧ G.t (G.comp a b) = G.t a) ∧
  (∀ a, G.comp a (G.i (G.s a)) = a ∧ G.comp (G.i (G.t a)) a = a) ∧
  (∀ a b c, G.s a = G.t b → G.s b = G.t c →
    G.comp (G.comp a b) c = G.comp a (G.comp b c)) ∧
  (∀ a b a' b', G.s a = G.t b → G.s a' = G.t b' →
    G.comp (a * a') (b * b') = G.comp a b * G.comp a' b')

end StrictTwoGroups.TwoEquiv


