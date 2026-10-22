-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P02
-- name    : QAlgorithms_Papers_Independent_Gap48_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:48:18.925895+00:00
-- url     : https://prove2.me/theorems/a10fbd2f-5764-470d-a85d-b30dae67620e
-- title:
--   Definitions for Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group
-- statement:
--   The objects the formalized statements of *Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group* (arXiv:0911.2483) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `inversePairing`: Definition 50, PDF p. 20: x maps to x tensor i(x), and f maps to f tensor i(f), for the given monoidal structure.
--   - `FunctorialInverseChoice`: Definition 50, PDF p. 20: a chosen covariant inverse functor with a natural isomorphism to the constant tensor-unit functor.
-- source:
--   Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group, arXiv:0911.2483v3, https://arxiv.org/abs/0911.2483v3

import Mathlib

/-!
Statements from Schommer-Pries, arXiv:0911.2483v3, PDF p. 20.
Other planned nodes are explicitly deferred in HARD.md and GAPS.json.
-/

namespace QAlgorithms.Papers.Independent.Gap48.P02

open CategoryTheory MonoidalCategory

universe v u

/-- Definition 50, PDF p. 20: x maps to x tensor i(x),
and f maps to f tensor i(f), for the given monoidal structure. -/
def inversePairing (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (i : M ⥤ M) : M ⥤ M :=
  (Functor.prod' (𝟭 M) i) ⋙ MonoidalCategory.tensor M

/-- Definition 50, PDF p. 20: a chosen covariant inverse functor
with a natural isomorphism to the constant tensor-unit functor. -/
structure FunctorialInverseChoice (M : Type u) [Category.{v} M]
    [MonoidalCategory M] where
  inverse : M ⥤ M
  evaluation : inversePairing M inverse ≅ (Functor.const M).obj (𝟙_ M)

/-- Sanity for Definition 50: the actual tensor product on objects. -/
example (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (i : M ⥤ M) (x : M) :
    (inversePairing M i).obj x = x ⊗ i.obj x := rfl

/-- Sanity for Definition 50: both arrow factors vary covariantly. -/
example (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (i : M ⥤ M) {x y : M} (f : x ⟶ y) :
    (inversePairing M i).map f = f ⊗ₘ i.map f := rfl

/-- Sanity for Definition 50: a singleton monoidal category
has a functorial inverse choice, so the hypothesis is satisfiable. -/
example : Nonempty (FunctorialInverseChoice (Discrete PUnit)) := by
  refine ⟨⟨𝟭 _, ?_⟩⟩
  exact NatIso.ofComponents
    (fun _ => Discrete.eqToIso (Subsingleton.elim _ _))
    (by intros; apply Subsingleton.elim)

end QAlgorithms.Papers.Independent.Gap48.P02


