-- Prove2me | Definitions.Def_Monotonicity_Theorem_Framework2
-- name    : Monotonicity_Theorem_Framework2
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-14T21:33:33.972739+00:00
-- url     : https://prove2.me/theorems/21d1e8e3-c907-435f-9c23-ae17196eed27
-- title:
--   O-minimal structure framework
-- statement:
--   The o-minimal structure interface over a dense linear order without endpoints.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Finite.Basic
universe u
namespace Monotonicity_Theorem
abbrev Power (R : Type u) (n : Nat) := Fin n → R
namespace Power
variable {R : Type u}
def left {n m : Nat} (z : Power R (n + m)) : Power R n := fun i => z (Fin.castAdd m i)
def right {n m : Nat} (z : Power R (n + m)) : Power R m := fun j => z (Fin.natAdd n j)
def deleteCoord {n : Nat} (k : Fin (n + 1)) (z : Power R (n + 1)) : Power R n := fun i => z (Fin.succAbove k i)
def append {n m : Nat} (x : Power R n) (y : Power R m) : Power R (n + m) := Fin.append x y
end Power
-- Dense linear orders without endpoints are Mathlib's
-- `[LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]`.
-- All order reasoning uses Mathlib's API directly: `lt_trans`, `lt_irrefl`,
-- `lt_trichotomy` for case splits, `exists_between` for density, and
-- `exists_lt` / `exists_gt` for no-endpoint witnesses.
inductive Endpoint (R : Type u) where
  | negInf : Endpoint R
  | finite (value : R) : Endpoint R
  | posInf : Endpoint R
namespace Endpoint
variable {R : Type u} [LinearOrder R]
def lt : Endpoint R → Endpoint R → Prop
  | .negInf, .negInf => False
  | .negInf, .finite _ => True
  | .negInf, .posInf => True
  | .finite _, .negInf => False
  | .finite a, .finite b => a < b
  | .finite _, .posInf => True
  | .posInf, _ => False
end Endpoint
def setEmpty {A : Type u} : Set A := fun _ => False
def setUnion {A : Type u} (X Y : Set A) : Set A := fun a => X a ∨ Y a
def setInter {A : Type u} (X Y : Set A) : Set A := fun a => X a ∧ Y a
def setCompl {A : Type u} (X : Set A) : Set A := fun a => ¬ (X a)
def pointSet {R : Type u} (a : R) : Set (Power R 1) := fun x => x 0 = a
def openInterval {R : Type u} [LinearOrder R] (a b : Endpoint R) : Set (Power R 1) := fun x => Endpoint.lt a (.finite (x 0)) ∧ Endpoint.lt (.finite (x 0)) b
inductive FiniteUnionOfPointsAndIntervals {R : Type u} [LinearOrder R] : Set (Power R 1) → Prop where
  | empty : FiniteUnionOfPointsAndIntervals (fun _ => False)
  | point (a : R) : FiniteUnionOfPointsAndIntervals (pointSet a)
  | interval (a b : Endpoint R) : FiniteUnionOfPointsAndIntervals (openInterval a b)
  | union {A B : Set (Power R 1)} : FiniteUnionOfPointsAndIntervals A → FiniteUnionOfPointsAndIntervals B → FiniteUnionOfPointsAndIntervals (fun x => A x ∨ B x)
structure OMinimalStructure (R : Type u) [LinearOrder R] where
  S : (n : Nat) → Set (Set (Power R n))
  empty_mem : ∀ n : Nat, S n (setEmpty : Set (Power R n))
  union_mem : ∀ {n : Nat} {A B : Set (Power R n)}, S n A → S n B → S n ((A ∪ B))
  inter_mem : ∀ {n : Nat} {A B : Set (Power R n)}, S n A → S n B → S n ((A ∩ B))
  compl_mem : ∀ {n : Nat} {A : Set (Power R n)}, S n A → S n (Aᶜ)
  diagonal_mem : ∀ {n : Nat} (i j : Fin n), i < j → S n (fun x : Power R n => x i = x j)
  product_mem : ∀ {n m : Nat} {A : Set (Power R n)} {B : Set (Power R m)}, S n A → S m B → S (n + m) (fun z : Power R (n + m) => A (Power.left z) ∧ B (Power.right z))
  project_mem : ∀ {n : Nat} (k : Fin (n + 1)) {A : Set (Power R (n + 1))}, S (n + 1) A → S n (fun y : Power R n => ∃ x : Power R (n + 1), A x ∧ Power.deleteCoord k x = y)
  reindex_mem : ∀ {n m : Nat} (sigma : Fin n → Fin m) {A : Set (Power R n)}, S n A → S m (fun x : Power R m => A (fun i : Fin n => x (sigma i)))
  existsLast_mem : ∀ {n m : Nat} {A : Set (Power R (n + m))}, S (n + m) A → S n (fun x : Power R n => ∃ y : Power R m, A (Power.append x y))
  lt_mem : S 2 (fun p : Power R 2 => p 0 < p 1)
  ominimal : ∀ A : Set (Power R 1), S 1 A ↔ FiniteUnionOfPointsAndIntervals A
end Monotonicity_Theorem
namespace Monotonicity_Theorem
namespace Power
variable {R : Type u}
def coord1 (x : Power R 1) : R := x 0
end Power
def FunctionGraph {m n : Nat} {R : Type u} {A : Set (Power R m)} {B : Set (Power R n)} (f : {x : Power R m // A x} → {y : Power R n // B y}) : Set (Power R (m + n)) := fun z => ∃ hx : A (Power.left z), Power.right z = (f (Subtype.mk (Power.left z) hx)).1
structure DefinableFunction {R : Type u} [LinearOrder R] (M : OMinimalStructure R) {m n : Nat} (A : Set (Power R m)) (B : Set (Power R n)) where
  domain_mem : M.S m A
  codomain_mem : M.S n B
  toFun : {x : Power R m // A x} → {y : Power R n // B y}
  graph_mem : M.S (m + n) (FunctionGraph toFun)
@[reducible] def Lt1 {R : Type u} [LinearOrder R] (x y : Power R 1) : Prop := Power.coord1 x < Power.coord1 y
def StrictlyIncreasingOn {R : Type u} [LinearOrder R] (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} → {y : Power R 1 // B y}) : Prop := ∀ x y (hx : I x) (hy : I y), Lt1 x y → Lt1 (f (Subtype.mk x hx)).1 (f (Subtype.mk y hy)).1
def StrictlyDecreasingOn {R : Type u} [LinearOrder R] (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} → {y : Power R 1 // B y}) : Prop := ∀ x y (hx : I x) (hy : I y), Lt1 x y → Lt1 (f (Subtype.mk y hy)).1 (f (Subtype.mk x hx)).1
def StrictlyMonotoneOn {R : Type u} [LinearOrder R] (I B : Set (Power R 1)) (f : {x : Power R 1 // I x} → {y : Power R 1 // B y}) : Prop := StrictlyIncreasingOn I B f ∨ StrictlyDecreasingOn I B f
def ContinuousPoints {R : Type u} [LinearOrder R] (I : Set (Power R 1)) (G : Set (Power R 2)) : Set (Power R 1) :=
  fun x => I x ∧ ∀ w₀ : R, G (Power.append (n := 1) (m := 1) (fun _ => Power.coord1 x) (fun _ => w₀)) →
    ∀ ε₁ ε₂ : R, ε₁ < w₀ → w₀ < ε₂ →
      ∃ δ₁ δ₂ : R, δ₁ < (Power.coord1 x) ∧ (Power.coord1 x) < δ₂ ∧
        ∀ y v : R, I (fun _ => y) → G (Power.append (n := 1) (m := 1) (fun _ => y) (fun _ => v)) →
          δ₁ < y → y < δ₂ → ε₁ < v ∧ v < ε₂
end Monotonicity_Theorem


