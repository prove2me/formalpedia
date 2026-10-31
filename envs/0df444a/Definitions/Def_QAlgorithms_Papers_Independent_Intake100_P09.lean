-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P09
-- name    : QAlgorithms_Papers_Independent_Intake100_P09
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:48:54.960997+00:00
-- url     : https://prove2.me/theorems/05bb30b3-f597-4e15-b57c-0c35670d9272
-- title:
--   Definitions for Equivariance In Higher Geometry
-- statement:
--   The objects the formalized statements of *Equivariance In Higher Geometry* (arXiv:1004.4558) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SmoothManifold`: Finite-dimensional smooth manifolds without boundary, allowing an empty carrier. The model, charts and smooth compatibility are actual Mathlib data. We use the usual Hausdorff, second countable convention for Man (source: Section 2.1, PDF pp. 4--5).
--   - `SmoothMap`: Smooth maps in Man (Section 2.1, PDF pp. 4--5).
--   - `smoothIdentity`: The identity smooth map.
--   - `smoothProduct`: The Cartesian product with its product atlas, not a formal product symbol (source: Lemma 5.6, PDF p. 24).
--   - `smoothProductMap`: The actual product of two smooth maps, with value (f(x),g(y)) (source: Lemma 5.6, PDF p. 24).
--   - `SmoothPullback`: A pullback square in Man: the unique mediating map is required to be smooth, not just a set map (Section 2.2, PDF p. 9).
--   - `CoverPretopology`: The paper's singleton-cover pretopology on Man: identities, composition, existence of pullbacks of covers, and closure under smooth base change. Only pullbacks along covers are required; arbitrary smooth maps need not have pullbacks in Man (Section 2.2, PDF p. 9).
-- source:
--   Equivariance In Higher Geometry, arXiv:1004.4558v4, https://arxiv.org/abs/1004.4558v4

import Mathlib

/-!
Statements from Nikolaus--Schweigert, *Equivariance in Higher Geometry*,
arXiv:1004.4558v4. Only Lemma 5.6 is drafted here; the remaining targets and
missing constructions are recorded individually in the unit's GAPS.json.
No bicategory, gerbe, or stack is represented by an uninterpreted predicate.
-/

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intake100.P09

open scoped Manifold ContDiff

/-- Finite-dimensional smooth manifolds without boundary, allowing an empty
carrier. The model, charts and smooth compatibility are actual Mathlib data.
We use the usual Hausdorff, second countable convention for Man
(source: Section 2.1, PDF pp. 4--5). -/
structure SmoothManifold where
  Model : Type u
  [modelNorm : NormedAddCommGroup Model]
  [modelReal : NormedSpace ℝ Model]
  [modelFinite : FiniteDimensional ℝ Model]
  Chart : Type u
  [chartTopology : TopologicalSpace Chart]
  model : ModelWithCorners ℝ Model Chart
  [modelBoundaryless : model.Boundaryless]
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [charts : ChartedSpace Chart carrier]
  [smooth : IsManifold model ∞ carrier]

attribute [instance] SmoothManifold.modelNorm SmoothManifold.modelReal
  SmoothManifold.modelFinite SmoothManifold.chartTopology
  SmoothManifold.modelBoundaryless SmoothManifold.topology
  SmoothManifold.hausdorff SmoothManifold.secondCountable
  SmoothManifold.charts SmoothManifold.smooth

/-- Smooth maps in Man (Section 2.1, PDF pp. 4--5). -/
abbrev SmoothMap (M N : SmoothManifold.{u}) :=
  ContMDiffMap M.model N.model M.carrier N.carrier ∞

/-- The identity smooth map. -/
def smoothIdentity (M : SmoothManifold.{u}) : SmoothMap M M :=
  ContMDiffMap.id

/-- The Cartesian product with its product atlas, not a formal product symbol
(source: Lemma 5.6, PDF p. 24). -/
def smoothProduct (M N : SmoothManifold.{u}) : SmoothManifold.{u} where
  Model := M.Model × N.Model
  modelNorm := inferInstance
  modelReal := inferInstance
  modelFinite := inferInstance
  Chart := ModelProd M.Chart N.Chart
  chartTopology := inferInstance
  model := M.model.prod N.model
  modelBoundaryless := inferInstance
  carrier := M.carrier × N.carrier
  topology := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  charts := inferInstance
  smooth := inferInstance

/-- The actual product of two smooth maps, with value (f(x),g(y))
(source: Lemma 5.6, PDF p. 24). -/
def smoothProductMap {Y M Yother Mother : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap Yother Mother) :
    SmoothMap (smoothProduct Y Yother) (smoothProduct M Mother) :=
  ⟨Prod.map f g, f.contMDiff.prodMap g.contMDiff⟩

/-- A pullback square in Man: the unique mediating map is required to be
smooth, not just a set map (Section 2.2, PDF p. 9). -/
structure SmoothPullback {Y M N : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap N M) where
  object : SmoothManifold.{u}
  first : SmoothMap object Y
  second : SmoothMap object N
  commutes : f.comp first = g.comp second
  universal : ∀ (T : SmoothManifold.{u}) (a : SmoothMap T Y) (b : SmoothMap T N),
    f.comp a = g.comp b →
      ∃! l : SmoothMap T object, first.comp l = a ∧ second.comp l = b

/-- The paper's singleton-cover pretopology on Man: identities, composition,
existence of pullbacks of covers, and closure under smooth base change.
Only pullbacks along covers are required; arbitrary smooth maps need not
have pullbacks in Man (Section 2.2, PDF p. 9). -/
structure CoverPretopology where
  covers : {Y M : SmoothManifold.{u}} → SmoothMap Y M → Prop
  identity_mem : ∀ M : SmoothManifold.{u}, covers (smoothIdentity M)
  composition_mem : ∀ {Y M N : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap M N),
    covers f → covers g → covers (g.comp f)
  pullback_exists : ∀ {Y M N : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap N M),
    covers f → Nonempty (SmoothPullback f g)
  pullback_mem : ∀ {Y M N : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap N M) (P : SmoothPullback f g),
    covers f → covers P.second

/-- Sanity check: the ordinary real line supplies a concrete, nonempty
instance of the manifold bundle. -/
example : Nonempty SmoothManifold.{0} :=
  ⟨{ Model := ℝ
     modelNorm := inferInstance
     modelReal := inferInstance
     modelFinite := inferInstance
     Chart := ℝ
     chartTopology := inferInstance
     model := 𝓘(ℝ, ℝ)
     modelBoundaryless := inferInstance
     carrier := ℝ
     topology := inferInstance
     hausdorff := inferInstance
     secondCountable := inferInstance
     charts := inferInstance
     smooth := inferInstance }⟩

/-- Sanity check: the identity square is a smooth categorical pullback,
including uniqueness of the smooth lift. -/
example (M : SmoothManifold.{u}) :
    Nonempty (SmoothPullback (smoothIdentity M) (smoothIdentity M)) := by
  refine ⟨{
    object := M
    first := smoothIdentity M
    second := smoothIdentity M
    commutes := rfl
    universal := ?_ }⟩
  intro T a b hab
  change a = b at hab
  subst b
  refine ⟨a, ⟨rfl, rfl⟩, ?_⟩
  intro l hl
  exact hl.1

/-- Sanity check: the identity acts on the underlying manifold as identity. -/
example (M : SmoothManifold.{u}) (x : M.carrier) : smoothIdentity M x = x := rfl

/-- Sanity check: the product map uses each input exactly once and in order. -/
example {Y M Yother Mother : SmoothManifold.{u}}
    (f : SmoothMap Y M) (g : SmoothMap Yother Mother)
    (x : Y.carrier) (y : Yother.carrier) :
    smoothProductMap f g (x, y) = (f x, g y) := rfl

/-- Sanity check: the cover class contains the identity on every manifold,
including the empty manifold. -/
example (tau : CoverPretopology.{u}) (M : SmoothManifold.{u}) :
    tau.covers (smoothIdentity M) := tau.identity_mem M

end QAlgorithms.Papers.Independent.Intake100.P09


