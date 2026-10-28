-- Prove2me | Definitions.Def_StrictTwoGroups_TwoEquiv_Raw2Cat
-- name    : StrictTwoGroups_TwoEquiv_Raw2Cat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:11.00048+00:00
-- url     : https://prove2.me/theorems/7867d77d-004b-4798-a545-e86fbec1c743
-- title:
--   §1, pp. 4–5 — strict 2-categories, 2-functors, 2-natural isomorphisms and 2-equivalence (raw data with lawfulness predicates)
-- statement:
--   A **strict 2-category** $\mathcal G$ has objects, for each pair of objects $(A,B)$ a set of 1-cells $\mathcal G_1(A,B)$ and a set of 2-cells $\mathcal G_2(A,B)$, identity 1-cells $i_A$, identity 2-cells $i_f$, a vertical composition $\bullet$ of 2-cells and a horizontal composition $\circ$ of 1-cells and of 2-cells. The axioms (Porst, §1, p. 4) say that each $\mathcal G(A,B)$ is a category under vertical composition, that horizontal composition
--   $$\circ:\mathcal G(B,C)\times\mathcal G(A,B)\longrightarrow\mathcal G(A,C)$$
--   is a functor (it preserves identity 2-cells and satisfies the interchange law $(\varphi'\bullet\theta')\circ(\varphi\bullet\theta)=(\varphi'\circ\varphi)\bullet(\theta'\circ\theta)$), that it is associative on 1-cells and on 2-cells, and that identities are units: $i_B\circ F=F=F\circ i_A$ and $i_{i_B}\circ\vartheta=\vartheta=\vartheta\circ i_{i_A}$.
--
--   A **2-functor** $F:\mathcal G\to\mathcal G'$ maps objects, 1-cells and 2-cells, each $F_{A,B}$ is a functor, and $F$ preserves horizontal composition and identities on both levels. A **2-natural transformation** $\vartheta:F\Rightarrow E$ assigns to each object $A$ a 1-cell $\vartheta_A:FA\to EA$ such that diagram (7) commutes: $\vartheta_B\circ Ff=Ef\circ\vartheta_A$ for 1-cells $f:A\to B$, and for a 2-cell $\alpha:f\Rightarrow g$ the whiskered composites agree, $i_{\vartheta_B}\circ F\alpha=E\alpha\circ i_{\vartheta_A}$. It is a **2-natural isomorphism** when every $\vartheta_A$ is an isomorphism. Two 2-categories are **2-equivalent** when there are 2-functors $F:\mathcal G\to\mathcal G'$, $E:\mathcal G'\to\mathcal G$ and 2-natural isomorphisms $E\circ F\cong\mathrm{id}_{\mathcal G}$ and $F\circ E\cong\mathrm{id}_{\mathcal G'}$.
--
--   These notions are the common language of the mission: the 2-categories $2\text{-}\mathit{Grp}$ and $X\text{-}\mathit{Mod}$, the 2-functors $T$ and $S$, and the round-trip isomorphisms $\xi$ and $\zeta$ are stated in them.
--
--   **Formalization Note** A `Raw2Cat` is raw data: object, 1-cell and 2-cell types, predicates `IsOb`, `Is1`, `Is2` selecting the lawful ones (`Is2 f g θ` says that `θ` is a lawful 2-cell $f\Rightarrow g$), and the identities and compositions. The axioms are the predicate `IsStrict2Category`, every clause quantified over lawful objects, 1-cells and 2-cells only. All compositions are written in diagrammatic order: `comp1 f g` is "$f$, then $g$" (the paper's $g\circ f$); `vcomp f g h θ φ` is $\varphi\bullet\theta$; `hcomp f g f' g' θ θ'` is $\theta'\circ\theta$ with $\theta$ on the first hop. 2-cells are typed by their objects only, so the boundary 1-cells are explicit arguments. `IsTwoNatIso` asks for a lawful two-sided inverse 1-cell of each component. `TwoEquivalent` includes that both sides are 2-categories.
-- source:
--   Porst, Strict 2-Groups are Crossed Modules, arXiv:0812.1464v1, pp. 4–5, §1 Definitions of 2-category, 2-functor, 2-natural transformation (diagram (7)), 2-equivalent

import Mathlib

set_option autoImplicit false

namespace StrictTwoGroups.TwoEquiv

universe u

/-- Raw strict 2-category data (§1, p. 4): objects, 1-cells, 2-cells, identities and the
three compositions, together with predicates selecting the lawful objects, 1-cells and 2-cells.
The laws are the predicate `IsStrict2Category`. All compositions are diagrammatic:
`comp1 f g` is "f, then g". 2-cells are indexed by their objects only; `Is2 f g θ` says that
`θ` is a lawful 2-cell `f ⇒ g`, and the boundary 1-cells are explicit arguments of `vcomp`,
`hcomp` and `id2`. -/
structure Raw2Cat where
  Ob : Type (u+1)
  Hom1 : Ob → Ob → Type u
  Hom2 : Ob → Ob → Type u
  IsOb : Ob → Prop
  Is1 : ∀ {a b : Ob}, Hom1 a b → Prop
  /-- `Is2 f g θ`: `θ` is a lawful 2-cell `f ⇒ g`. -/
  Is2 : ∀ {a b : Ob}, Hom1 a b → Hom1 a b → Hom2 a b → Prop
  id1 : ∀ a : Ob, Hom1 a a
  /-- `comp1 f g`: `f`, then `g`. -/
  comp1 : ∀ {a b c : Ob}, Hom1 a b → Hom1 b c → Hom1 a c
  /-- `id2 f`: the identity 2-cell `f ⇒ f`. -/
  id2 : ∀ {a b : Ob}, Hom1 a b → Hom2 a b
  /-- `vcomp f g h θ θ'`: `θ : f ⇒ g`, then `θ' : g ⇒ h`. -/
  vcomp : ∀ {a b : Ob}, Hom1 a b → Hom1 a b → Hom1 a b → Hom2 a b → Hom2 a b → Hom2 a b
  /-- `hcomp f g f' g' θ θ'`: `θ : f ⇒ g` on `a → b`, then `θ' : f' ⇒ g'` on `b → c`. -/
  hcomp : ∀ {a b c : Ob}, Hom1 a b → Hom1 a b → Hom1 b c → Hom1 b c →
    Hom2 a b → Hom2 b c → Hom2 a c

namespace Raw2Cat

/-- The axioms of a 2-category (§1, p. 4), on lawful objects, 1-cells and 2-cells only:
closure of the lawful cells under identities and compositions; each `G(A, B)` is a category
under vertical composition; horizontal composition is a functor
`G(A, B) × G(B, C) → G(A, C)` (preserves identity 2-cells and satisfies the interchange law);
horizontal composition is associative on 1-cells and 2-cells; identities are units. -/
def IsStrict2Category (C : Raw2Cat.{u}) : Prop :=
  -- closure
  (∀ a, C.IsOb a → C.Is1 (C.id1 a)) ∧
  (∀ {a b c} (f : C.Hom1 a b) (g : C.Hom1 b c), C.IsOb a → C.IsOb b → C.IsOb c →
    C.Is1 f → C.Is1 g → C.Is1 (C.comp1 f g)) ∧
  (∀ {a b} (f : C.Hom1 a b), C.IsOb a → C.IsOb b → C.Is1 f → C.Is2 f f (C.id2 f)) ∧
  (∀ {a b} (f g h : C.Hom1 a b) (θ θ' : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is1 h → C.Is2 f g θ → C.Is2 g h θ' →
    C.Is2 f h (C.vcomp f g h θ θ')) ∧
  (∀ {a b c} (f g : C.Hom1 a b) (f' g' : C.Hom1 b c) (θ : C.Hom2 a b) (θ' : C.Hom2 b c),
    C.IsOb a → C.IsOb b → C.IsOb c → C.Is1 f → C.Is1 g → C.Is1 f' → C.Is1 g' →
    C.Is2 f g θ → C.Is2 f' g' θ' →
    C.Is2 (C.comp1 f f') (C.comp1 g g') (C.hcomp f g f' g' θ θ')) ∧
  -- each G(A, B) is a category under vertical composition
  (∀ {a b} (f g : C.Hom1 a b) (θ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is2 f g θ →
    C.vcomp f f g (C.id2 f) θ = θ ∧ C.vcomp f g g θ (C.id2 g) = θ) ∧
  (∀ {a b} (f g h k : C.Hom1 a b) (θ φ ψ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is1 h → C.Is1 k → C.Is2 f g θ → C.Is2 g h φ → C.Is2 h k ψ →
    C.vcomp f h k (C.vcomp f g h θ φ) ψ = C.vcomp f g k θ (C.vcomp g h k φ ψ)) ∧
  -- horizontal composition is a functor: identities and the interchange law
  (∀ {a b c} (f : C.Hom1 a b) (f' : C.Hom1 b c), C.IsOb a → C.IsOb b → C.IsOb c →
    C.Is1 f → C.Is1 f' →
    C.hcomp f f f' f' (C.id2 f) (C.id2 f') = C.id2 (C.comp1 f f')) ∧
  (∀ {a b c} (f g h : C.Hom1 a b) (f' g' h' : C.Hom1 b c) (θ φ : C.Hom2 a b)
    (θ' φ' : C.Hom2 b c), C.IsOb a → C.IsOb b → C.IsOb c →
    C.Is1 f → C.Is1 g → C.Is1 h → C.Is1 f' → C.Is1 g' → C.Is1 h' →
    C.Is2 f g θ → C.Is2 g h φ → C.Is2 f' g' θ' → C.Is2 g' h' φ' →
    C.hcomp f h f' h' (C.vcomp f g h θ φ) (C.vcomp f' g' h' θ' φ') =
      C.vcomp (C.comp1 f f') (C.comp1 g g') (C.comp1 h h')
        (C.hcomp f g f' g' θ θ') (C.hcomp g h g' h' φ φ')) ∧
  -- horizontal composition is associative
  (∀ {a b c d} (f : C.Hom1 a b) (f' : C.Hom1 b c) (f'' : C.Hom1 c d),
    C.IsOb a → C.IsOb b → C.IsOb c → C.IsOb d → C.Is1 f → C.Is1 f' → C.Is1 f'' →
    C.comp1 (C.comp1 f f') f'' = C.comp1 f (C.comp1 f' f'')) ∧
  (∀ {a b c d} (f g : C.Hom1 a b) (f' g' : C.Hom1 b c) (f'' g'' : C.Hom1 c d)
    (θ : C.Hom2 a b) (θ' : C.Hom2 b c) (θ'' : C.Hom2 c d),
    C.IsOb a → C.IsOb b → C.IsOb c → C.IsOb d →
    C.Is1 f → C.Is1 g → C.Is1 f' → C.Is1 g' → C.Is1 f'' → C.Is1 g'' →
    C.Is2 f g θ → C.Is2 f' g' θ' → C.Is2 f'' g'' θ'' →
    C.hcomp (C.comp1 f f') (C.comp1 g g') f'' g'' (C.hcomp f g f' g' θ θ') θ'' =
      C.hcomp f g (C.comp1 f' f'') (C.comp1 g' g'') θ (C.hcomp f' g' f'' g'' θ' θ'')) ∧
  -- identities are units: iB ∘ F = F = F ∘ iA and iB ∘ ϑ = ϑ = ϑ ∘ iA
  (∀ {a b} (f : C.Hom1 a b), C.IsOb a → C.IsOb b → C.Is1 f →
    C.comp1 (C.id1 a) f = f ∧ C.comp1 f (C.id1 b) = f) ∧
  (∀ {a b} (f g : C.Hom1 a b) (θ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is2 f g θ →
    C.hcomp (C.id1 a) (C.id1 a) f g (C.id2 (C.id1 a)) θ = θ ∧
    C.hcomp f g (C.id1 b) (C.id1 b) θ (C.id2 (C.id1 b)) = θ)

end Raw2Cat

/-- Raw 2-functor data (§1, p. 5): a map of objects, of 1-cells and of 2-cells. The 2-cell
map takes the boundary 1-cells as explicit arguments. -/
structure Raw2Functor (C D : Raw2Cat.{u}) where
  obj : C.Ob → D.Ob
  map1 : ∀ {a b : C.Ob}, C.Hom1 a b → D.Hom1 (obj a) (obj b)
  map2 : ∀ {a b : C.Ob}, C.Hom1 a b → C.Hom1 a b → C.Hom2 a b → D.Hom2 (obj a) (obj b)

namespace Raw2Functor

/-- The composite `E ∘ F` of raw 2-functors: `F`, then `E`. -/
def comp {C D E : Raw2Cat.{u}} (F : Raw2Functor C D) (G : Raw2Functor D E) :
    Raw2Functor C E where
  obj a := G.obj (F.obj a)
  map1 f := G.map1 (F.map1 f)
  map2 f g θ := G.map2 (F.map1 f) (F.map1 g) (F.map2 f g θ)

/-- The identity raw 2-functor. -/
def id (C : Raw2Cat.{u}) : Raw2Functor C C where
  obj a := a
  map1 f := f
  map2 _ _ θ := θ

end Raw2Functor

/-- A 2-functor (§1, p. 5): it sends lawful objects, 1-cells and 2-cells to lawful ones, and
on lawful data each `F_{A,B}` is a functor (preserves identity 2-cells and vertical
composition) and `F` preserves composition and identities on both levels:
`F_{B,C}(−) ∘ F_{A,B}(−) = F_{A,C}(− ∘ −)` and `i_{FD}(−) = F_{D,D} i(−)`. -/
def IsTwoFunctor {C D : Raw2Cat.{u}} (F : Raw2Functor C D) : Prop :=
  (∀ a, C.IsOb a → D.IsOb (F.obj a)) ∧
  (∀ {a b} (f : C.Hom1 a b), C.IsOb a → C.IsOb b → C.Is1 f → D.Is1 (F.map1 f)) ∧
  (∀ {a b} (f g : C.Hom1 a b) (θ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is2 f g θ → D.Is2 (F.map1 f) (F.map1 g) (F.map2 f g θ)) ∧
  -- F_{A,B} is a functor
  (∀ {a b} (f : C.Hom1 a b), C.IsOb a → C.IsOb b → C.Is1 f →
    F.map2 f f (C.id2 f) = D.id2 (F.map1 f)) ∧
  (∀ {a b} (f g h : C.Hom1 a b) (θ φ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is1 h → C.Is2 f g θ → C.Is2 g h φ →
    F.map2 f h (C.vcomp f g h θ φ) =
      D.vcomp (F.map1 f) (F.map1 g) (F.map1 h) (F.map2 f g θ) (F.map2 g h φ)) ∧
  -- preservation of horizontal composition, on 1-cells and on 2-cells
  (∀ {a b c} (f : C.Hom1 a b) (g : C.Hom1 b c), C.IsOb a → C.IsOb b → C.IsOb c →
    C.Is1 f → C.Is1 g → F.map1 (C.comp1 f g) = D.comp1 (F.map1 f) (F.map1 g)) ∧
  (∀ {a b c} (f g : C.Hom1 a b) (f' g' : C.Hom1 b c) (θ : C.Hom2 a b) (θ' : C.Hom2 b c),
    C.IsOb a → C.IsOb b → C.IsOb c → C.Is1 f → C.Is1 g → C.Is1 f' → C.Is1 g' →
    C.Is2 f g θ → C.Is2 f' g' θ' →
    F.map2 (C.comp1 f f') (C.comp1 g g') (C.hcomp f g f' g' θ θ') =
      D.hcomp (F.map1 f) (F.map1 g) (F.map1 f') (F.map1 g')
        (F.map2 f g θ) (F.map2 f' g' θ')) ∧
  -- preservation of identities, on 1-cells and on 2-cells
  (∀ a, C.IsOb a → F.map1 (C.id1 a) = D.id1 (F.obj a)) ∧
  (∀ a, C.IsOb a → F.map2 (C.id1 a) (C.id1 a) (C.id2 (C.id1 a)) = D.id2 (D.id1 (F.obj a)))

/-- A 2-natural isomorphism `ϑ : F ⇒ E` (§1, p. 5): for every lawful object `A` a lawful
1-cell `ϑ_A : F A → E A` that is an isomorphism (it has a lawful two-sided inverse 1-cell),
such that diagram (7) commutes: on lawful 1-cells `f : A → B`,
`ϑ_B ∘ F f = E f ∘ ϑ_A` (diagrammatically `F f ; ϑ_B = ϑ_A ; E f`), and on lawful 2-cells
`α : f ⇒ g`, the whiskering identity `F α` then `i ϑ_B` equals `i ϑ_A` then `E α`. -/
def IsTwoNatIso {C D : Raw2Cat.{u}} (F E : Raw2Functor C D)
    (ϑ : ∀ a : C.Ob, D.Hom1 (F.obj a) (E.obj a)) : Prop :=
  (∀ a, C.IsOb a → D.Is1 (ϑ a) ∧
    ∃ ψ : D.Hom1 (E.obj a) (F.obj a), D.Is1 ψ ∧
      D.comp1 (ϑ a) ψ = D.id1 (F.obj a) ∧ D.comp1 ψ (ϑ a) = D.id1 (E.obj a)) ∧
  (∀ {a b} (f : C.Hom1 a b), C.IsOb a → C.IsOb b → C.Is1 f →
    D.comp1 (F.map1 f) (ϑ b) = D.comp1 (ϑ a) (E.map1 f)) ∧
  (∀ {a b} (f g : C.Hom1 a b) (θ : C.Hom2 a b), C.IsOb a → C.IsOb b →
    C.Is1 f → C.Is1 g → C.Is2 f g θ →
    D.hcomp (F.map1 f) (F.map1 g) (ϑ b) (ϑ b) (F.map2 f g θ) (D.id2 (ϑ b)) =
      D.hcomp (ϑ a) (ϑ a) (E.map1 f) (E.map1 g) (D.id2 (ϑ a)) (E.map2 f g θ))

/-- Two 2-categories are 2-equivalent (§1, p. 5): both are 2-categories, and there are
2-functors `F : C → D`, `E : D → C` and 2-natural isomorphisms `ϑ : E ∘ F ⇒ id_C`,
`σ : F ∘ E ⇒ id_D`. -/
def TwoEquivalent (C D : Raw2Cat.{u}) : Prop :=
  Raw2Cat.IsStrict2Category C ∧ Raw2Cat.IsStrict2Category D ∧
  ∃ (F : Raw2Functor C D) (E : Raw2Functor D C)
    (ϑ : ∀ a : C.Ob, C.Hom1 ((F.comp E).obj a) a)
    (σ : ∀ b : D.Ob, D.Hom1 ((E.comp F).obj b) b),
    IsTwoFunctor F ∧ IsTwoFunctor E ∧
    IsTwoNatIso (F.comp E) (Raw2Functor.id C) ϑ ∧
    IsTwoNatIso (E.comp F) (Raw2Functor.id D) σ

end StrictTwoGroups.TwoEquiv


