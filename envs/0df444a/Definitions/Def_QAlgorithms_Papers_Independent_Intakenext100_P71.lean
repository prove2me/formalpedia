-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P71
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:41:02.936247+00:00
-- url     : https://prove2.me/theorems/38fca872-e2ab-4f6d-821c-319152660931
-- title:
--   Definitions for Butterflies I: morphisms of 2-group stacks
-- statement:
--   The objects the formalized statements of *Butterflies I: morphisms of 2-group stacks* (arXiv:0808.3627) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GroupSheaf`: Group objects of the topos in §§1.4 and 2.1, PDF pp.10–11. The sheaf condition is Mathlib's categorical sheaf condition for group-valued presheaves.
--   - `GroupSheaf.sections`: Local sections, with their actual group structure; §1.4, PDF p.11.
--   - `GroupSheaf.res`: Restriction is a homomorphism; §2.1, PDF p.11.
--   - `GroupSheaf.Hom`: Homomorphisms of group sheaves, including restriction naturality; §1.4, p.10.
--   - `onSections`: Evaluation of a homomorphism on local sections.
--   - `IsLocalEpi`: Local epimorphism, §2.1, PDF p.11: every section lifts on a covering sieve. This asserts local lifting on every object, rather than surjectivity on global sections.
--   - `RightCrossedModule`: Right crossed modules of group sheaves, Definition 3.2.1, PDF p.18. The action is by group automorphisms; its restriction naturality, equivariance, and Peiffer identity are all included. Terms have cohomological degrees −1,0.
--   - `RightCrossedModule.d`: Boundary evaluation, Definition 3.2.1, PDF p.18.
--   - `identityCrossedModule`: The identity crossed module of an arbitrary group sheaf, with right conjugation action; Definition 3.2.1, PDF p.18. This supplies a nonabelian sanity model without imposing any commutativity on its terms.
--   - `StrictMorphism`: Strict morphisms with both boundary and action compatibility, Definition 3.2.3, PDF p.18.
--   - `Butterfly`: Butterflies, Definition 4.1.3, PDF p.26. The NW–SE diagonal is a complex (the printed “NW–SW” is a typo). The NE–SW extension has a monic first map, its actual kernel image, and a locally epimorphic projection. Both conjugation axioms are retained.
--   - `Butterfly.IsReversible`: Reversibility, Definition 4.1.5, PDF p.26: the other diagonal is also an extension.
--   - `ButterflyIso`: Butterfly isomorphisms, Definition 4.1.7, PDF pp.26–27. A natural homomorphism bijective on each section group is an isomorphism of sheaves.
--   - `Splitting`: A chosen homomorphic splitting, §4.5.2, PDF p.35. The equation pi ∘ s = id is part of the meaning of “splitting”.
--   - `splitCoordinates`: The actual semidirect-product coordinates associated to a splitting, §§4.5.1–4.5.2, PDF p.35.
--   - `Braiding`: Braiding brackets in the right-action convention, §§7.1.2,7.1.7, pp.63,65. Under target(x,g)=x*d(g), c(x,y) labels the arrow x*y → y*x: x*y*(y⁻¹*x⁻¹*y*x)=y*x. The source explanation is consistent; the plan note reversing this orientation is incorrect and is not followed.
--   - `Braiding.IsSymmetric`: Symmetry, §7.2, PDF p.66, as an equation on the specified bracket.
--   - `Braiding.IsPicard`: Picardness, §§7.1.1,7.3.4, PDF pp.62–63,69; symmetry is also required.
--   - `Butterfly.IsBraided`: Braided butterflies, Definition 7.4.1, PDF p.69.
-- source:
--   Butterflies I: morphisms of 2-group stacks, arXiv:0808.3627v2, https://arxiv.org/abs/0808.3627v2

import Mathlib

/-!
Paper: Aldrovandi–Noohi, Butterflies I, arXiv:0808.3627v2.
All new definitions here are paper-local. Groups are sheaves on the given site;
right actions use d(g^x) = x⁻¹ d(g) x. No fiber products in the site are assumed.
The accompanying HARD.md accounts for the nodes whose full interfaces are deferred.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P71

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]

/-- Group objects of the topos in §§1.4 and 2.1, PDF pp.10–11.
The sheaf condition is Mathlib's categorical sheaf condition for group-valued presheaves. -/
structure GroupSheaf (J : GrothendieckTopology C) where
  presheaf : Cᵒᵖ ⥤ GrpCat.{w}
  isSheaf : Presheaf.IsSheaf J presheaf

variable {J : GrothendieckTopology C}

/-- Local sections, with their actual group structure; §1.4, PDF p.11. -/
abbrev GroupSheaf.sections (A : GroupSheaf.{u, v, w} J) (U : C) :=
  A.presheaf.obj (op U)

/-- Restriction is a homomorphism; §2.1, PDF p.11. -/
abbrev GroupSheaf.res (A : GroupSheaf.{u, v, w} J) {U V : C} (i : V ⟶ U) :=
  (A.presheaf.map i.op).hom

/-- Homomorphisms of group sheaves, including restriction naturality; §1.4, p.10. -/
abbrev GroupSheaf.Hom (A B : GroupSheaf.{u, v, w} J) :=
  A.presheaf ⟶ B.presheaf

/-- Evaluation of a homomorphism on local sections. -/
abbrev onSections {A B : GroupSheaf.{u, v, w} J} (f : A.Hom B) (U : C) :=
  (f.app (op U)).hom

/-- Local epimorphism, §2.1, PDF p.11: every section lifts on a covering sieve.
This asserts local lifting on every object, rather than surjectivity on global sections. -/
def IsLocalEpi {A B : GroupSheaf.{u, v, w} J} (f : A.Hom B) : Prop :=
  ∀ (U : C) (b : B.sections U), ∃ R : Sieve U, R ∈ J U ∧
    ∀ (V : C) (i : V ⟶ U), R i →
      ∃ a : A.sections V, onSections f V a = B.res i b

/-- Right crossed modules of group sheaves, Definition 3.2.1, PDF p.18.
The action is by group automorphisms; its restriction naturality, equivariance,
and Peiffer identity are all included. Terms have cohomological degrees −1,0. -/
structure RightCrossedModule (J : GrothendieckTopology C) where
  one : GroupSheaf.{u, v, w} J
  zero : GroupSheaf.{u, v, w} J
  boundary : one.Hom zero
  act : ∀ U : C, one.sections U → zero.sections U → one.sections U
  act_id : ∀ U g, act U g 1 = g
  act_comp : ∀ U g x y, act U g (x * y) = act U (act U g x) y
  act_one : ∀ U x, act U 1 x = 1
  act_mul : ∀ U g h x, act U (g * h) x = act U g x * act U h x
  act_res : ∀ (U V : C) (i : V ⟶ U) g x,
    one.res i (act U g x) = act V (one.res i g) (zero.res i x)
  equivariance : ∀ U g x,
    onSections boundary U (act U g x) = x⁻¹ * onSections boundary U g * x
  peiffer : ∀ U g h, act U g (onSections boundary U h) = h⁻¹ * g * h

/-- Boundary evaluation, Definition 3.2.1, PDF p.18. -/
abbrev RightCrossedModule.d (G : RightCrossedModule.{u, v, w} J) (U : C) :=
  onSections G.boundary U

/-- The identity crossed module of an arbitrary group sheaf, with right
conjugation action; Definition 3.2.1, PDF p.18. This supplies a nonabelian
sanity model without imposing any commutativity on its terms. -/
def identityCrossedModule (A : GroupSheaf.{u, v, w} J) : RightCrossedModule J where
  one := A
  zero := A
  boundary := 𝟙 A.presheaf
  act := fun _ g x => x⁻¹ * g * x
  act_id := by intro U g; simp
  act_comp := by intro U g x y; simp [mul_assoc]
  act_one := by intro U x; simp
  act_mul := by intro U g h x; simp [mul_assoc]
  act_res := by intro U V i g x; simp
  equivariance := by intro U g x; rfl
  peiffer := by intro U g h; rfl

/-- Sanity: the identity crossed module has exactly the right Peiffer conjugation. -/
example (A : GroupSheaf.{u, v, w} J) (U : C) (g h : A.sections U) :
    (identityCrossedModule A).act U g ((identityCrossedModule A).d U h) =
      h⁻¹ * g * h := by
  rfl

/-- Strict morphisms with both boundary and action compatibility,
Definition 3.2.3, PDF p.18. -/
structure StrictMorphism (H G : RightCrossedModule.{u, v, w} J) where
  f1 : H.one.Hom G.one
  f0 : H.zero.Hom G.zero
  boundary_commutes : ∀ U h,
    onSections f0 U (H.d U h) = G.d U (onSections f1 U h)
  action_commutes : ∀ U h x,
    onSections f1 U (H.act U h x) =
      G.act U (onSections f1 U h) (onSections f0 U x)

/-- Butterflies, Definition 4.1.3, PDF p.26.
The NW–SE diagonal is a complex (the printed “NW–SW” is a typo).
The NE–SW extension has a monic first map, its actual kernel image, and a
locally epimorphic projection. Both conjugation axioms are retained. -/
structure Butterfly (H G : RightCrossedModule.{u, v, w} J) where
  center : GroupSheaf.{u, v, w} J
  kappa : H.one.Hom center
  iota : G.one.Hom center
  pi : center.Hom H.zero
  j : center.Hom G.zero
  pi_kappa : ∀ U h, onSections pi U (onSections kappa U h) = H.d U h
  j_iota : ∀ U g, onSections j U (onSections iota U g) = G.d U g
  j_kappa : ∀ U h, onSections j U (onSections kappa U h) = 1
  pi_iota : ∀ U g, onSections pi U (onSections iota U g) = 1
  iota_injective : ∀ U, Function.Injective (onSections iota U)
  kernel_pi : ∀ U e, onSections pi U e = 1 ↔
    ∃ g, onSections iota U g = e
  pi_localEpi : IsLocalEpi pi
  iota_equivariant : ∀ U g e,
    onSections iota U (G.act U g (onSections j U e)) =
      e⁻¹ * onSections iota U g * e
  kappa_equivariant : ∀ U h e,
    onSections kappa U (H.act U h (onSections pi U e)) =
      e⁻¹ * onSections kappa U h * e

/-- Reversibility, Definition 4.1.5, PDF p.26: the other diagonal is also an extension. -/
def Butterfly.IsReversible {H G : RightCrossedModule.{u, v, w} J}
    (E : Butterfly H G) : Prop :=
  (∀ U, Function.Injective (onSections E.kappa U)) ∧
  (∀ U e, onSections E.j U e = 1 ↔ ∃ h, onSections E.kappa U h = e) ∧
  IsLocalEpi E.j

/-- Butterfly isomorphisms, Definition 4.1.7, PDF pp.26–27.
A natural homomorphism bijective on each section group is an isomorphism of sheaves. -/
structure ButterflyIso {H G : RightCrossedModule.{u, v, w} J}
    (E Eprime : Butterfly H G) where
  map : E.center.Hom Eprime.center
  bijective : ∀ U, Function.Bijective (onSections map U)
  kappa_commutes : ∀ U h,
    onSections map U (onSections E.kappa U h) = onSections Eprime.kappa U h
  iota_commutes : ∀ U g,
    onSections map U (onSections E.iota U g) = onSections Eprime.iota U g
  pi_commutes : ∀ U e,
    onSections Eprime.pi U (onSections map U e) = onSections E.pi U e
  j_commutes : ∀ U e,
    onSections Eprime.j U (onSections map U e) = onSections E.j U e

/-- A chosen homomorphic splitting, §4.5.2, PDF p.35.
The equation pi ∘ s = id is part of the meaning of “splitting”. -/
structure Splitting {H G : RightCrossedModule.{u, v, w} J} (E : Butterfly H G) where
  sectionHom : H.zero.Hom E.center
  section_law : ∀ U y, onSections E.pi U (onSections sectionHom U y) = y

/-- The actual semidirect-product coordinates associated to a splitting,
§§4.5.1–4.5.2, PDF p.35. -/
def splitCoordinates {H G : RightCrossedModule.{u, v, w} J}
    {E : Butterfly H G} (s : Splitting E) (U : C)
    (a : H.zero.sections U × G.one.sections U) : E.center.sections U :=
  onSections s.sectionHom U a.1 * onSections E.iota U a.2

/-- Braiding brackets in the right-action convention, §§7.1.2,7.1.7, pp.63,65.
Under target(x,g)=x*d(g), c(x,y) labels the arrow x*y → y*x:
x*y*(y⁻¹*x⁻¹*y*x)=y*x. The source explanation is consistent; the plan
note reversing this orientation is incorrect and is not followed. -/
structure Braiding (G : RightCrossedModule.{u, v, w} J) where
  bracket : ∀ U : C, G.zero.sections U → G.zero.sections U → G.one.sections U
  naturality : ∀ (U V : C) (i : V ⟶ U) x y,
    G.one.res i (bracket U x y) = bracket V (G.zero.res i x) (G.zero.res i y)
  boundary : ∀ U x y, G.d U (bracket U x y) = y⁻¹ * x⁻¹ * y * x
  right_cocycle : ∀ U x y z,
    bracket U x (y * z) = G.act U (bracket U x y) z * bracket U x z
  left_cocycle : ∀ U x y z,
    bracket U (x * y) z = bracket U y z * G.act U (bracket U x z) y
  naturality_right : ∀ U x h, bracket U x (G.d U h) = h⁻¹ * G.act U h x
  naturality_left : ∀ U g y, bracket U (G.d U g) y = (G.act U g y)⁻¹ * g

/-- Symmetry, §7.2, PDF p.66, as an equation on the specified bracket. -/
def Braiding.IsSymmetric {G : RightCrossedModule.{u, v, w} J} (c : Braiding G) : Prop :=
  ∀ U x y, c.bracket U x y = (c.bracket U y x)⁻¹

/-- Picardness, §§7.1.1,7.3.4, PDF pp.62–63,69; symmetry is also required. -/
def Braiding.IsPicard {G : RightCrossedModule.{u, v, w} J} (c : Braiding G) : Prop :=
  c.IsSymmetric ∧ ∀ U x, c.bracket U x x = 1

/-- Braided butterflies, Definition 7.4.1, PDF p.69. -/
def Butterfly.IsBraided {H G : RightCrossedModule.{u, v, w} J}
    (E : Butterfly H G) (cH : Braiding H) (cG : Braiding G) : Prop :=
  ∀ U x y,
    onSections E.kappa U (cH.bracket U (onSections E.pi U x) (onSections E.pi U y)) *
      onSections E.iota U (cG.bracket U (onSections E.j U x) (onSections E.j U y)) =
      y⁻¹ * x⁻¹ * y * x

/-- Sanity: the splitting coordinates send the semidirect-product unit to the center unit. -/
example {H G : RightCrossedModule.{u, v, w} J} {E : Butterfly H G}
    (s : Splitting E) (U : C) : splitCoordinates s U (1, 1) = 1 := by
  simp [splitCoordinates]

/-- Sanity for the nonabelian right-action convention: conjugating successively
by x and y is conjugation by x*y, with no commutativity assumption. -/
example {A : Type w} [Group A] (g x y : A) :
    (x * y)⁻¹ * g * (x * y) = y⁻¹ * (x⁻¹ * g * x) * y := by
  simp [mul_assoc]

end QAlgorithms.Papers.Independent.Intakenext100.P71


