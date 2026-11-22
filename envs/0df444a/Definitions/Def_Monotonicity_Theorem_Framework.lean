-- Prove2me | Definitions.Def_Monotonicity_Theorem_Framework
-- name    : Monotonicity_Theorem_Framework
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-09T17:44:54.656581+00:00
-- url     : https://prove2.me/theorems/48707ad8-9f0f-4efb-b375-2979acb6d356
-- title:
--   Monotonicity theorem framework
-- statement:
--   Foundational function, order, infinitude, monotonicity, graph, and continuity predicates used by the monotonicity theorem drafts.
-- source:
--   monotonicity.tex, function and continuity framework

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic
universe u
namespace Monotonicity_Theorem
abbrev Power (R : Type u) (n : Nat) := Fin n -> R
namespace Power
variable {R : Type u}
def left {n m : Nat} (z : Power R (n + m)) : Power R n := fun i => z (Fin.castAdd m i)
def right {n m : Nat} (z : Power R (n + m)) : Power R m := fun j => z (Fin.natAdd n j)
def deleteCoord {n : Nat} (k : Fin (n + 1)) (z : Power R (n + 1)) : Power R n := fun i => z (Fin.succAbove k i)
def append {n m : Nat} (x : Power R n) (y : Power R m) : Power R (n + m) := Fin.append x y
end Power
class DenseLinearOrderNoEndpoints (R : Type u) where
  lt : R -> R -> Prop
  irrefl : forall x : R, Not (lt x x)
  trans : forall {x y z : R}, lt x y -> lt y z -> lt x z
  trichotomy : forall x y : R, (lt x y /\ Not (lt y x) /\ Not (x = y)) \/ (x = y /\ Not (lt x y) /\ Not (lt y x)) \/ (lt y x /\ Not (lt x y) /\ Not (x = y))
  dense : forall {x y : R}, lt x y -> exists z : R, lt x z /\ lt z y
  no_left_endpoint : forall x : R, exists y : R, lt y x
  no_right_endpoint : forall x : R, exists y : R, lt x y
inductive Endpoint (R : Type u) where
  | negInf : Endpoint R
  | finite (value : R) : Endpoint R
  | posInf : Endpoint R
namespace Endpoint
variable {R : Type u}
def lt (D : DenseLinearOrderNoEndpoints R) : Endpoint R -> Endpoint R -> Prop
  | .negInf, .negInf => False
  | .negInf, .finite _ => True
  | .negInf, .posInf => True
  | .finite _, .negInf => False
  | .finite a, .finite b => D.lt a b
  | .finite _, .posInf => True
  | .posInf, _ => False
end Endpoint
def setEmpty {A : Type u} : Set A := fun _ => False
def setUnion {A : Type u} (X Y : Set A) : Set A := fun a => X a \/ Y a
def setInter {A : Type u} (X Y : Set A) : Set A := fun a => X a /\ Y a
def setCompl {A : Type u} (X : Set A) : Set A := fun a => Not (X a)
def pointSet {R : Type u} (a : R) : Set (Power R 1) := fun x => x 0 = a
def openInterval {R : Type u} (D : DenseLinearOrderNoEndpoints R) (a b : Endpoint R) : Set (Power R 1) := fun x => Endpoint.lt D a (.finite (x 0)) /\ Endpoint.lt D (.finite (x 0)) b
inductive FiniteUnionOfPointsAndIntervals {R : Type u} (D : DenseLinearOrderNoEndpoints R) : Set (Power R 1) -> Prop where
  | empty : FiniteUnionOfPointsAndIntervals D (fun _ => False)
  | point (a : R) : FiniteUnionOfPointsAndIntervals D (pointSet a)
  | interval (a b : Endpoint R) : FiniteUnionOfPointsAndIntervals D (openInterval D a b)
  | union {A B : Set (Power R 1)} : FiniteUnionOfPointsAndIntervals D A -> FiniteUnionOfPointsAndIntervals D B -> FiniteUnionOfPointsAndIntervals D (fun x => A x \/ B x)
structure OMinimalStructure {R : Type u} (D : DenseLinearOrderNoEndpoints R) where
  S : (n : Nat) -> Set (Set (Power R n))
  empty_mem : forall n : Nat, S n (setEmpty : Set (Power R n))
  union_mem : forall {n : Nat} {A B : Set (Power R n)}, S n A -> S n B -> S n (setUnion A B)
  inter_mem : forall {n : Nat} {A B : Set (Power R n)}, S n A -> S n B -> S n (setInter A B)
  compl_mem : forall {n : Nat} {A : Set (Power R n)}, S n A -> S n (setCompl A)
  diagonal_mem : forall {n : Nat} (i j : Fin n), i < j -> S n (fun x : Power R n => x i = x j)
  product_mem : forall {n m : Nat} {A : Set (Power R n)} {B : Set (Power R m)}, S n A -> S m B -> S (n + m) (fun z : Power R (n + m) => A (Power.left z) /\ B (Power.right z))
  project_mem : forall {n : Nat} (k : Fin (n + 1)) {A : Set (Power R (n + 1))}, S (n + 1) A -> S n (fun y : Power R n => exists x : Power R (n + 1), A x /\ Power.deleteCoord k x = y)
  reindex_mem : forall {n m : Nat} (sigma : Fin n -> Fin m) {A : Set (Power R n)}, S n A -> S m (fun x : Power R m => A (fun i : Fin n => x (sigma i)))
  existsLast_mem : forall {n m : Nat} {A : Set (Power R (n + m))}, S (n + m) A -> S n (fun x : Power R n => exists y : Power R m, A (Power.append x y))
  lt_mem : S 2 (fun p : Power R 2 => D.lt (p 0) (p 1))
  ominimal : forall A : Set (Power R 1), S 1 A <-> FiniteUnionOfPointsAndIntervals D A
end Monotonicity_Theorem
namespace Monotonicity_Theorem
namespace Power
variable {R : Type u}
def coord1 (x : Power R 1) : R := x 0
end Power
def FunctionGraph {m n : Nat} {R : Type u} {A : Set (Power R m)} {B : Set (Power R n)} (f : {x : Power R m // A x} -> {y : Power R n // B y}) : Set (Power R (m + n)) := fun z => exists hx : A (Power.left z), Power.right z = (f (Subtype.mk (Power.left z) hx)).1
structure DefinableFunction {R : Type u} {D : DenseLinearOrderNoEndpoints R} (M : OMinimalStructure D) {m n : Nat} (A : Set (Power R m)) (B : Set (Power R n)) where
  domain_mem : M.S m A
  codomain_mem : M.S n B
  toFun : {x : Power R m // A x} -> {y : Power R n // B y}
  graph_mem : M.S (m + n) (FunctionGraph toFun)
@[reducible] def Lt1 {R : Type u} (D : DenseLinearOrderNoEndpoints R) (x y : Power R 1) : Prop := D.lt (Power.coord1 x) (Power.coord1 y)
def IsFinite1 {R : Type u} (A : Set (Power R 1)) : Prop := exists L : List R, forall x : Power R 1, A x <-> Power.coord1 x ∈ L
def IsInfinite1 {R : Type u} (A : Set (Power R 1)) : Prop := Not (IsFinite1 A)
def StrictlyIncreasingOn {R : Type u} (D : DenseLinearOrderNoEndpoints R) (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop := forall x y (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f (Subtype.mk x hx)).1 (f (Subtype.mk y hy)).1
def StrictlyDecreasingOn {R : Type u} (D : DenseLinearOrderNoEndpoints R) (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop := forall x y (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f (Subtype.mk y hy)).1 (f (Subtype.mk x hx)).1
def StrictlyMonotoneOn {R : Type u} (D : DenseLinearOrderNoEndpoints R) (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop := StrictlyIncreasingOn D I B f \/ StrictlyDecreasingOn D I B f
def ContinuousPoints {R : Type u} (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) := I
end Monotonicity_Theorem


