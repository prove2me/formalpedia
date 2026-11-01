-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P59
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P59
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:47:50.84999+00:00
-- url     : https://prove2.me/theorems/9c5b0ec4-1c86-4ed0-aa01-3767a263f335
-- title:
--   Definitions for Crossed Module Bundle Gerbes; Classification, String Group and Differential Geometry
-- statement:
--   The objects the formalized statements of *Crossed Module Bundle Gerbes; Classification, String Group and Differential Geometry* (arXiv:math/0510078) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GroupLevel`: The degree-n group of a simplicial group (source: PDF p. 3).
--   - `BaseLevel`: The degree-n set of the simplicial base (source: PDF p. 3).
--   - `Twisting`: All four twisting identities of section 1.1, PDF p. 3. There is no value on X_0: `value n` is the twisting from X_(n+1) to G_n.
--   - `trivialTwisting`: The trivial twisting, used to test the exceptional zeroth-face convention.
--   - `TwistedPoint`: Degreewise total space G_n times X_n of P(tau), section 1.2, PDF p. 4.
--   - `twistedFace`: The source's twisted face maps, including right multiplication by tau in face zero. Together with `twistedDegeneracy` these specify the full simplicial object, rather than a product with the untwisted zeroth face (PDF p. 4).
--   - `twistedDegeneracy`: Degeneracies of the twisted product are componentwise (PDF p. 4).
--   - `twistedLeft`: The principal left action on P(tau), section 1.2, PDF p. 4.
--   - `canonicalSection`: Canonical pseudo-cross section; its value need not commute with face zero (section 1.2, PDF p. 4). The projection is the second coordinate.
--   - `TwistingGauge`: The degreewise gauge functions satisfying exactly the three displayed laws of section 1.3, PDF p. 4. Correction: the printed word "simplicial" is replaced by those laws; ordinary zeroth-face naturality is not also imposed.
--   - `TwistedBundleIso`: Actual equivariant bundle isomorphisms over X in the twisted-product presentation: degreewise bijections preserve the projection and action and commute with every face and degeneracy (sections 1.2-1.3, PDF p. 4).
--   - `identityGauge`: Identity gauge, testing that no ordinary face-zero law is added to a gauge.
--   - `identityBundleIso`: Identity bundle isomorphism for the explicit twisted maps.
--   - `positiveFaceKernel`: The source's Gbar_n, section 3, PDF p. 7: kernel of the composite partial_1 ... partial_n, equivalently restriction to the first vertex. This is not the intersection of the face kernels. Gbar_0 is the trivial subgroup.
--   - `boundaryImage`: The actual image of Gbar_(n+1) under face zero (section 3, PDF p. 7).
-- source:
--   Crossed Module Bundle Gerbes; Classification, String Group and Differential Geometry, arXiv:math/0510078v2, https://arxiv.org/abs/math/0510078v2

import Mathlib

/-!
Statements from Jurco, arXiv:math/0510078v2. The geometric results whose full
interfaces are not implemented are individually recorded in the unit's HARD.md.
Only the two theorem declarations below are proof targets; examples are sanity tests.
-/

open CategoryTheory
open scoped Simplicial

universe u

namespace QAlgorithms.Papers.Independent.Intakenext100.P59

/-- The degree-n group of a simplicial group (source: PDF p. 3). -/
abbrev GroupLevel (G : SimplicialObject GrpCat.{u}) (n : ℕ) : Type u :=
  G.obj (Opposite.op (SimplexCategory.mk n))

/-- The degree-n set of the simplicial base (source: PDF p. 3). -/
abbrev BaseLevel (X : SSet.{u}) (n : ℕ) : Type u :=
  X.obj (Opposite.op (SimplexCategory.mk n))

/-- All four twisting identities of section 1.1, PDF p. 3. There is no value
on X_0: `value n` is the twisting from X_(n+1) to G_n. -/
structure Twisting (G : SimplicialObject GrpCat.{u}) (X : SSet.{u}) where
  value : ∀ n : ℕ, BaseLevel X (n + 1) → GroupLevel G n
  faceZero : ∀ (n : ℕ) (x : BaseLevel X (n + 2)),
    (G.δ (n := n) 0).hom (value (n + 1) x) =
      value n (X.δ (n := n + 1) 1 x) *
        (value n (X.δ (n := n + 1) 0 x))⁻¹
  facePositive : ∀ (n : ℕ) (i : Fin (n + 2)), 0 < i.val →
    ∀ x : BaseLevel X (n + 2),
      (G.δ (n := n) i).hom (value (n + 1) x) =
        value n (X.δ (n := n + 1) i.succ x)
  degeneracy : ∀ (n : ℕ) (i : Fin (n + 1)) (x : BaseLevel X (n + 1)),
    (G.σ (n := n) i).hom (value n x) =
      value (n + 1) (X.σ (n := n + 1) i.succ x)
  degeneracyZero : ∀ (n : ℕ) (x : BaseLevel X n),
    value n (X.σ (n := n) 0 x) = 1

/-- The trivial twisting, used to test the exceptional zeroth-face convention. -/
def trivialTwisting (G : SimplicialObject GrpCat.{u}) (X : SSet.{u}) :
    Twisting G X where
  value := fun _ _ => 1
  faceZero := by intros; simp
  facePositive := by intros; simp
  degeneracy := by intros; simp
  degeneracyZero := by intros; rfl

example (G : SimplicialObject GrpCat.{u}) (X : SSet.{u})
    (n : ℕ) (x : BaseLevel X (n + 1)) :
    (trivialTwisting G X).value n x = 1 := rfl

/-- Degreewise total space G_n times X_n of P(tau), section 1.2, PDF p. 4. -/
abbrev TwistedPoint (G : SimplicialObject GrpCat.{u}) (X : SSet.{u}) (n : ℕ) :=
  GroupLevel G n × BaseLevel X n

/-- The source's twisted face maps, including right multiplication by tau in
face zero. Together with `twistedDegeneracy` these specify the full simplicial
object, rather than a product with the untwisted zeroth face (PDF p. 4). -/
def twistedFace {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau : Twisting G X) (n : ℕ) (i : Fin (n + 2))
    (p : TwistedPoint G X (n + 1)) : TwistedPoint G X n :=
  if i.val = 0 then
    ((G.δ (n := n) i).hom p.1 * tau.value n p.2,
      X.δ (n := n) i p.2)
  else
    ((G.δ (n := n) i).hom p.1, X.δ (n := n) i p.2)

/-- Degeneracies of the twisted product are componentwise (PDF p. 4). -/
def twistedDegeneracy {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (p : TwistedPoint G X n) :
    TwistedPoint G X (n + 1) :=
  ((G.σ (n := n) i).hom p.1, X.σ (n := n) i p.2)

/-- The principal left action on P(tau), section 1.2, PDF p. 4. -/
def twistedLeft {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (n : ℕ) (g : GroupLevel G n) (p : TwistedPoint G X n) :
    TwistedPoint G X n :=
  (g * p.1, p.2)

/-- Canonical pseudo-cross section; its value need not commute with face zero
(section 1.2, PDF p. 4). The projection is the second coordinate. -/
def canonicalSection (G : SimplicialObject GrpCat.{u}) (X : SSet.{u})
    (n : ℕ) (x : BaseLevel X n) : TwistedPoint G X n :=
  (1, x)

example {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau : Twisting G X) (n : ℕ) (p : TwistedPoint G X (n + 1)) :
    twistedFace tau n 0 p =
      ((G.δ (n := n) 0).hom p.1 * tau.value n p.2,
        X.δ (n := n) 0 p.2) := rfl

example {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (n : ℕ) (p : TwistedPoint G X n) : twistedLeft n 1 p = p := by
  simp [twistedLeft]

example (G : SimplicialObject GrpCat.{u}) (X : SSet.{u})
    (n : ℕ) (x : BaseLevel X n) : (canonicalSection G X n x).2 = x := rfl

example {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (n : ℕ) (i : Fin (n + 1)) (x : BaseLevel X n) :
    twistedDegeneracy n i (canonicalSection G X n x) =
      canonicalSection G X (n + 1) (X.σ (n := n) i x) := by
  simp [twistedDegeneracy, canonicalSection]

/-- The degreewise gauge functions satisfying exactly the three displayed
laws of section 1.3, PDF p. 4. Correction: the printed word "simplicial" is
replaced by those laws; ordinary zeroth-face naturality is not also imposed. -/
structure TwistingGauge {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau tauPrime : Twisting G X) where
  value : ∀ n : ℕ, BaseLevel X n → GroupLevel G n
  faceZero : ∀ (n : ℕ) (x : BaseLevel X (n + 1)),
    (G.δ (n := n) 0).hom (value (n + 1) x) * tauPrime.value n x =
      tau.value n x * value n (X.δ (n := n) 0 x)
  facePositive : ∀ (n : ℕ) (i : Fin (n + 2)), 0 < i.val →
    ∀ x : BaseLevel X (n + 1),
      (G.δ (n := n) i).hom (value (n + 1) x) =
        value n (X.δ (n := n) i x)
  degeneracy : ∀ (n : ℕ) (i : Fin (n + 1)) (x : BaseLevel X n),
    (G.σ (n := n) i).hom (value n x) =
      value (n + 1) (X.σ (n := n) i x)

/-- Actual equivariant bundle isomorphisms over X in the twisted-product
presentation: degreewise bijections preserve the projection and action and
commute with every face and degeneracy (sections 1.2-1.3, PDF p. 4). -/
structure TwistedBundleIso {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau tauPrime : Twisting G X) where
  map : ∀ n : ℕ, TwistedPoint G X n ≃ TwistedPoint G X n
  overBase : ∀ (n : ℕ) (p : TwistedPoint G X n), (map n p).2 = p.2
  equivariant : ∀ (n : ℕ) (g : GroupLevel G n) (p : TwistedPoint G X n),
    map n (twistedLeft n g p) = twistedLeft n g (map n p)
  face : ∀ (n : ℕ) (i : Fin (n + 2)) (p : TwistedPoint G X (n + 1)),
    map n (twistedFace tau n i p) = twistedFace tauPrime n i (map (n + 1) p)
  degeneracy : ∀ (n : ℕ) (i : Fin (n + 1)) (p : TwistedPoint G X n),
    map (n + 1) (twistedDegeneracy n i p) = twistedDegeneracy n i (map n p)

/-- Identity gauge, testing that no ordinary face-zero law is added to a gauge. -/
def identityGauge {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau : Twisting G X) : TwistingGauge tau tau where
  value := fun _ _ => 1
  faceZero := by intros; simp
  facePositive := by intros; simp
  degeneracy := by intros; simp

/-- Identity bundle isomorphism for the explicit twisted maps. -/
def identityBundleIso {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau : Twisting G X) : TwistedBundleIso tau tau where
  map := fun _ => Equiv.refl _
  overBase := by intros; rfl
  equivariant := by intros; rfl
  face := by intros; rfl
  degeneracy := by intros; rfl

example {G : SimplicialObject GrpCat.{u}} {X : SSet.{u}}
    (tau : Twisting G X) (n : ℕ) (p : TwistedPoint G X n) :
    (identityBundleIso tau).map n p =
      (p.1 * (identityGauge tau).value n p.2, p.2) := by
  simp [identityBundleIso, identityGauge]

/-- The source's Gbar_n, section 3, PDF p. 7: kernel of the composite
partial_1 ... partial_n, equivalently restriction to the first vertex. This is
not the intersection of the face kernels. Gbar_0 is the trivial subgroup. -/
def positiveFaceKernel (G : SimplicialObject GrpCat.{u}) :
    (n : ℕ) → Subgroup (GroupLevel G n) := fun n =>
  match n with
  | 0 => ⊥
  | n + 1 =>
    MonoidHom.ker
      (G.map (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk (n + 1)) 0).op).hom

/-- The actual image of Gbar_(n+1) under face zero (section 3, PDF p. 7). -/
def boundaryImage (G : SimplicialObject GrpCat.{u}) (n : ℕ) :
    Subgroup (GroupLevel G n) :=
  (positiveFaceKernel G (n + 1)).map (G.δ (n := n) 0).hom

example (G : SimplicialObject GrpCat.{u}) : positiveFaceKernel G 0 = ⊥ := rfl

example (G : SimplicialObject GrpCat.{u}) (n : ℕ) :
    (1 : GroupLevel G (n + 1)) ∈ positiveFaceKernel G (n + 1) := by
  exact (positiveFaceKernel G (n + 1)).one_mem

example (G : SimplicialObject GrpCat.{u}) (n : ℕ) :
    (1 : GroupLevel G n) ∈ boundaryImage G n := by
  exact (boundaryImage G n).one_mem

end QAlgorithms.Papers.Independent.Intakenext100.P59


