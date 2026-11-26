-- Prove2me | Definitions.Def_TDLC_Refutation
-- name    : TDLC_Refutation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:24:03.66029+00:00
-- url     : https://prove2.me/theorems/db7c734d-b827-5e68-8966-ab7e4578f093
-- title:
--   Refutation
-- statement:
--   Definitions and structural lemmas for Refutation, from Arthur Freitas Ramos, Daniel O. Martinez-Rivillas, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/two-dimensional-lambda-calculus-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Certified naturality and obstruction to unrestricted naturality in a typed two-dimensional lambda calculus development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Refutation.lean

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
namespace TDLC.Refutation
universe u v
structure GroupData (G : Type v) where
  one : G
  mul : G → G → G
  inv : G → G
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  inv_mul : ∀ x, mul (inv x) x = one
  mul_inv : ∀ x, mul x (inv x) = one
  inv_one : inv one = one
  inv_inv : ∀ x, inv (inv x) = x
def Constant {A B : Type u} (f : A → B) : Prop := ∀ x y, f x = f y
abbrev Marker := (A B : Type u) → A → B → B
variable {G : Type v} (g : GroupData G) (mark : Marker.{u})
noncomputable def grade (g : GroupData G) (mark : Marker.{u})
    {A : Type u} {x y : A} : Step x y → (A → G) → G
  | @Step.beta A B f a, val =>
      if Classical.propDecidable (Constant f) |>.decide then
        g.mul (g.inv (val (f a))) (val (mark A B a (f a)))
      else g.one
  | .eta _, _ => g.one
  | .apCong f s, val => grade g mark s (fun x => val (f x))
  | .lamCong _, _ => g.one
  | .refl _, _ => g.one
  | .sym s, val => g.inv (grade g mark s val)
  | .trans s t, val => g.mul (grade g mark s val) (grade g mark t val)
noncomputable def pathGrade (g : GroupData G) (mark : Marker.{u})
    {A : Type u} {x y : A} : Path x y → (A → G) → G
  | .nil _, _ => g.one
  | .seq s p, val => g.mul (grade g mark s val) (pathGrade g mark p val)
def dMul (x y : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (((x.val % 3 + (if x.val < 3 then y.val % 3 else 3 - y.val % 3)) % 3) +
    (if (x.val < 3) = (y.val < 3) then 0 else 3))
def dInv (x : Fin 6) : Fin 6 :=
  if x.val < 3 then Fin.ofNat 6 ((3 - x.val) % 3) else x
def dihedral : GroupData (Fin 6) where
  one := 0
  mul := dMul
  inv := dInv
  one_mul := by decide
  mul_one := by decide
  assoc := by decide
  inv_mul := by decide
  mul_inv := by decide
  inv_one := by decide
  inv_inv := by decide
noncomputable def diagonalMarker : Marker.{0} := by
  classical
  exact fun A B a b => if h : A = B then cast h a else b
def valuation (x : Fin 3) : Fin 6 := if x = 0 then 0 else if x = 1 then 3 else 4
def badFamily (x : Fin 3) : Step x x :=
  .beta (fun _ : Fin 3 => x) 1
def testStep : Step (0 : Fin 3) 0 := .beta (fun _ : Fin 3 => 0) 2
def testPath : Path (0 : Fin 3) 0 := Path.lEmbed testStep
def badLeft : Path (0 : Fin 3) 0 :=
  Path.ap (fun x : Fin 3 => x) testPath ++ₚ Path.lEmbed (badFamily 0)
def badRight : Path (0 : Fin 3) 0 :=
  Path.lEmbed (badFamily 0) ++ₚ Path.ap (fun x : Fin 3 => x) testPath
def StepNat : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Step (f x) (g x)) → {x y : A} → (s : Step x y) →
    Step2 (Path.ap f (Path.lEmbed s) ++ₚ Path.lEmbed (h y))
      (Path.lEmbed (h x) ++ₚ Path.ap g (Path.lEmbed s))
def NatPath : Type 1 :=
  {A B : Type} → {f g : A → B} →
    (h : (x : A) → Path (f x) (g x)) → {x y : A} → (p : Path x y) →
    Path2 (Path.ap f p ++ₚ h y) (h x ++ₚ Path.ap g p)
end TDLC.Refutation


