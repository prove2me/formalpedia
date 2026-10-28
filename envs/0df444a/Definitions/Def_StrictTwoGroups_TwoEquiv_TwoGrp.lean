-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_TwoGrp
-- name    : StrictTwoGroups_TwoEquiv_TwoGrp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:51.574056+00:00
-- url     : https://prove2.me/theorems/80811c40-2640-4d15-b454-1222b7f4e158
-- title:
--   §2, p. 7 — the 2-category 2-Grp of strict 2-groups, internal functors and internal natural transformations
-- statement:
--   The 2-category $2\text{-}\mathit{Grp}$ (Porst, §2, p. 7) has strict 2-groups as objects. A **morphism of strict 2-groups** $F=(F_0,F_1):\mathcal G\to\mathcal G'$ is a functor in the category of groups: group morphisms $F_0:G_0\to G_0'$, $F_1:G_1\to G_1'$ making the diagrams (2) of p. 3 commute,
--   $$s'F_1=F_0 s,\quad t'F_1=F_0 t,\quad F_1 i=i'F_0,\quad F_1(a\circ b)=F_1a\circ' F_1b .$$
--   A **2-morphism** $\vartheta:F\Rightarrow E$ is a natural transformation in the category of groups: a group morphism $\vartheta:G_0\to G_1'$ with (4), p. 3,
--   $$s'\vartheta=F_0,\qquad t'\vartheta=E_0,\qquad \vartheta(t a)\circ' F_1 a=E_1 a\circ'\vartheta(s a)\quad(a\in G_1).$$
--   1-cells compose componentwise and the identity 1-cell is $(\mathrm{id},\mathrm{id})$. The identity 2-cell of $F$ is $g\mapsto i'(F_0 g)$; the vertical composite of $\vartheta:F\Rightarrow E$ and $\bar\vartheta:E\Rightarrow K$ is $g\mapsto\bar\vartheta g\circ'\vartheta g$; the horizontal composite of $\vartheta:F\Rightarrow E$ ($\mathcal G\to\mathcal G'$) and $\vartheta':F'\Rightarrow E'$ ($\mathcal G'\to\mathcal G''$) is, by (5) on p. 4,
--   $$(\vartheta'\circ\vartheta)(g)=\vartheta'(E_0 g)\circ'' F'_1(\vartheta g).$$
--
--   **Formalization Note** `twoGrp` is a `Raw2Cat`: lawful objects are those satisfying `IsStrictTwoGroup`; 1-cells are pairs of plain functions and 2-cells plain functions $G_0\to G_1'$, with "is a group morphism" ($f(xy)=f(x)f(y)$) a clause of the lawfulness predicates `IsTwoGrpHom` and `IsTwoGrpTwoHom`. Compositions are written diagrammatically (see `Raw2Cat`); the composition inside each strict 2-group keeps the paper's order.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, p. 7, §2 Definition (morphisms and 2-morphisms of strict 2-groups, 2-Grp); p. 3 diagrams (2), (4); pp. 4–5 formulas (5), (6)

import Mathlib
import Definitions.Def_StrictTwoGroups_TwoEquiv_Raw2Cat
import Definitions.Def_StrictTwoGroups_TwoEquiv_StrictTwoGroup

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- A morphism of strict 2-groups (§2, p. 7): a pair `(F₀, F₁)` of group morphisms that is an
internal functor, i.e. makes the diagrams (2) of p. 3 commute:
`s' F₁ = F₀ s`, `t' F₁ = F₀ t`, `F₁ i = i' F₀`, and `F₁(a ∘ b) = F₁ a ∘' F₁ b` on composable
pairs. -/
def IsTwoGrpHom {G G' : StrictTwoGroup.{u}} (F : (G.G0 → G'.G0) × (G.G1 → G'.G1)) : Prop :=
  (∀ x y : G.G0, F.1 (x * y) = F.1 x * F.1 y) ∧
  (∀ a b : G.G1, F.2 (a * b) = F.2 a * F.2 b) ∧
  (∀ a : G.G1, G'.s (F.2 a) = F.1 (G.s a) ∧ G'.t (F.2 a) = F.1 (G.t a)) ∧
  (∀ g : G.G0, F.2 (G.i g) = G'.i (F.1 g)) ∧
  (∀ a b : G.G1, G.s a = G.t b → F.2 (G.comp a b) = G'.comp (F.2 a) (F.2 b))

/-- A 2-morphism `ϑ : F ⇒ E` of strict 2-groups (§2, p. 7): a group morphism `ϑ : G₀ → G₁'`
that is an internal natural transformation, i.e. makes the diagrams (4) of p. 3 commute:
`s' ϑ = F₀`, `t' ϑ = E₀`, and `ϑ(t a) ∘' F₁ a = E₁ a ∘' ϑ(s a)` for all `a ∈ G₁`. -/
def IsTwoGrpTwoHom {G G' : StrictTwoGroup.{u}} (F E : (G.G0 → G'.G0) × (G.G1 → G'.G1))
    (ϑ : G.G0 → G'.G1) : Prop :=
  (∀ x y : G.G0, ϑ (x * y) = ϑ x * ϑ y) ∧
  (∀ g : G.G0, G'.s (ϑ g) = F.1 g ∧ G'.t (ϑ g) = E.1 g) ∧
  (∀ a : G.G1, G'.comp (ϑ (G.t a)) (F.2 a) = G'.comp (E.2 a) (ϑ (G.s a)))

/-- The 2-category `2-Grp` of strict 2-groups (§2, p. 7, with §1, pp. 4–5): strict 2-groups,
internal functors and internal natural transformations in the category of groups.
1-cells compose componentwise; the identity 2-cell of `F` is `g ↦ i'(F₀ g)`; vertical
composition of `ϑ : F ⇒ E` and `ϑ' : E ⇒ K` is `g ↦ ϑ' g ∘' ϑ g`; horizontal composition of
`ϑ : F ⇒ E` (on `G → G'`) and `ϑ' : F' ⇒ E'` (on `G' → G''`) is
`g ↦ ϑ'(E₀ g) ∘'' F'₁(ϑ g)` (formula (5)). -/
def twoGrp : Raw2Cat.{u} where
  Ob := StrictTwoGroup.{u}
  Hom1 G G' := (G.G0 → G'.G0) × (G.G1 → G'.G1)
  Hom2 G G' := G.G0 → G'.G1
  IsOb := IsStrictTwoGroup
  Is1 F := IsTwoGrpHom F
  Is2 F E ϑ := IsTwoGrpTwoHom F E ϑ
  id1 _ := (fun x => x, fun a => a)
  comp1 F F' := (fun x => F'.1 (F.1 x), fun a => F'.2 (F.2 a))
  id2 {_ G'} F := fun g => G'.i (F.1 g)
  vcomp {_ G'} _ _ _ ϑ ϑ' := fun g => G'.comp (ϑ' g) (ϑ g)
  hcomp {_ _ G''} _ E F' _ ϑ ϑ' := fun g => G''.comp (ϑ' (E.1 g)) (F'.2 (ϑ g))

end StrictTwoGroups.TwoEquiv


