-- Prove2me | Definitions.Def_RSF_cat
-- name    : RSF_cat
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-23T02:18:32.991162+00:00
-- url     : https://prove2.me/theorems/60e853f4-0b47-42c4-b9b7-c4ee21068df1
-- title:
--   The six-functor world: spaces, maps, the six operations, and the map classes
-- statement:
--   The interface of the six-functor formalism: an abstract world of spaces and maps with composition; the objects of the sheaf categories of each space; the structure sheaf; the six operations - the tensor product, the internal hom, the pullback and pushforward along maps, and the lower and upper shriek functors along maps; the shift and Tate twist operations; the distinguished classes of maps - bdcs, etale, proper, adically smooth, p-cohomologically smooth, and the pure-dimension predicate; the diamondification of maps; the cartesian squares for proper base change; the invertibility of objects for the tensor product; and the Riemann-Hilbert world of the p-torsion correspondence between overconvergent etale F_p-sheaves and phi-modules. The geometry of the thesis - small v-stacks, diamonds, and the solid almost module categories - is carried as interface data; constructing it for the actual geometry is part of the proposed work of the mission.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), introduction, Section 1.2 (Definition 1.2.2 and the formalism of Theorem 1.2.4; Theorems 1.2.5, 1.2.6, 1.2.7, and 1.2.8).

import Mathlib

/-!
# The categorical layer: the six-functor world interface

The categorical layer of the RSF mission, carrying the propositional content
of the introduction of Lucas Mann, "A p-Adic 6-Functor Formalism in
Rigid-Analytic Geometry" (arXiv:2206.02022): the six-functor world - the
abstract world of spaces with the six operations of the thesis, the tensor
product and internal hom, the pullback and pushforward, the lower and upper
shriek functors, the shift and Tate twist operations, the distinguished
classes of maps (bdcs, etale, proper, adically smooth, p-cohomologically
smooth, pure dimension), and the diamondification of maps; the cartesian
squares for proper base change; the invertibility of objects for the tensor
product; and the Riemann-Hilbert world of the p-torsion correspondence
between etale F_p-sheaves and phi-modules.

The geometry of the thesis - small v-stacks, diamonds, and the solid almost
module categories - exceeds the objects available in Mathlib; as in this
repository's established interface pattern, the world carries the operations
as bundled data and the theorem drafts quantify over it. Constructing the
interface data for the actual geometry of the thesis is part of the proposed
work of the mission.
-/

namespace RSF

/-- The six-functor world: spaces, maps, composition, the objects of the
sheaf categories with the six operations, and the distinguished classes of
maps. A map of `Map X Y` is a map from the space `X` to the space `Y`; the
six operations follow the conventions of the thesis: pullback along
`f : X → Y` goes from `C Y` to `C X`, pushforward and lower shriek along
`f` go from `C X` to `C Y`, and upper shriek along `f` goes from `C Y` to
`C X`. -/
structure SixFunctorWorld where
  Space : Type
  Map : Space → Space → Type
  idMap : ∀ X : Space, Map X X
  compMap : ∀ X Y Z : Space, Map X Y → Map Y Z → Map X Z
  C : Space → Type
  unit : ∀ X : Space, C X
  tensor : ∀ X : Space, C X → C X → C X
  internalHom : ∀ X : Space, C X → C X → C X
  pull : ∀ X Y : Space, Map X Y → C Y → C X
  push : ∀ X Y : Space, Map X Y → C X → C Y
  lshriek : ∀ X Y : Space, Map X Y → C X → C Y
  ushriek : ∀ X Y : Space, Map X Y → C Y → C X
  shift : ∀ X : Space, ℕ → C X → C X
  tateTwist : ∀ X : Space, ℕ → C X → C X
  IsBdcs : ∀ X Y : Space, Map X Y → Prop
  IsEtale : ∀ X Y : Space, Map X Y → Prop
  IsProper : ∀ X Y : Space, Map X Y → Prop
  IsAdicSmooth : ∀ X Y : Space, Map X Y → Prop
  IsPCohSmooth : ∀ X Y : Space, Map X Y → Prop
  IsPureDim : ∀ X Y : Space, Map X Y → ℕ → Prop
  diamond : ∀ X Y : Space, Map X Y → Map X Y

/-- A cartesian square in the six-functor world: the diagram with vertical
maps `f'` and `f` and horizontal maps `g'` and `g`, labeled cartesian. The
proper base change property of Theorem 1.2.4 relates the lower shriek of
`f` to its base change along `g`. -/
structure CartSquare (w : SixFunctorWorld) where
  Y' : w.Space
  Y : w.Space
  X' : w.Space
  X : w.Space
  f : w.Map Y X
  g : w.Map X' X
  f' : w.Map Y' X'
  g' : w.Map Y' Y
  isCartesian : Prop

/-- An object `L` of `C X` is invertible for the tensor product: it has a
two-sided tensor inverse. The purity theorem 1.2.5 asserts that the upper
shriek of the structure sheaf along a p-cohomologically smooth bdcs map is
invertible in this sense. -/
def IsInvertible (w : SixFunctorWorld) (X : w.Space) (L : w.C X) : Prop :=
  ∃ E : w.C X, w.tensor X L E = w.unit X ∧ w.tensor X E L = w.unit X

/-- The Riemann-Hilbert world of the p-torsion correspondence of Theorem
1.2.7: the objects of overconvergent etale F_p-sheaves, the objects of
phi-modules, their hom-types, the tensor-with-structure-sheaf functor and
its action on homs, and the perfectness predicate. -/
structure RHWorld where
  Sheaf : Type
  PhiMod : Type
  Hom1 : Sheaf → Sheaf → Type
  Hom2 : PhiMod → PhiMod → Type
  T : Sheaf → PhiMod
  Tmor : ∀ A B : Sheaf, Hom1 A B → Hom2 (T A) (T B)
  IsPerfect : PhiMod → Prop

end RSF


