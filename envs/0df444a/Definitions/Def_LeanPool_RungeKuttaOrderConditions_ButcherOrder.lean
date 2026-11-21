-- Prove2me | Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
-- name    : LeanPool_RungeKuttaOrderConditions_ButcherOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:57:22.043826+00:00
-- url     : https://prove2.me/theorems/580b516b-9fe7-4c03-b83d-e2259304455d
-- title:
--   Butcher Order
-- statement:
--   Definitions and structural lemmas for Butcher Order, from Carles Marín; LeanPool contributors's pinned Certified Runge-Kutta order conditions development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RungeKuttaOrderConditions/ButcherOrder.lean

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace RungeKuttaOrderConditions
structure Q15 where
  /-- Rational component. -/
  re : ℚ
  /-- Coefficient of √15. -/
  im : ℚ
deriving DecidableEq
namespace Q15
@[ext] theorem ext' {x y : Q15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Q15 := ⟨0, 0⟩
instance : One Q15  := ⟨1, 0⟩
instance : Add Q15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Q15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Q15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Q15 := ⟨fun x y =>
  ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Q15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Q15).im = 0 := rfl
@[simp] theorem one_re : (1 : Q15).re = 1 := rfl
@[simp] theorem one_im : (1 : Q15).im = 0 := rfl
@[simp] theorem add_re (x y : Q15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Q15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Q15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Q15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Q15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Q15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Q15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Q15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Q15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
@[simp] theorem natCast_eq (n : ℕ) : ((n : ℕ) : Q15) = ⟨(n : ℚ), 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.cast_succ, ih]; ext <;> simp [Nat.cast_succ]
end Q15
structure Z15 where
  /-- Integer component. -/
  re : Int
  /-- Integer coefficient of √15. -/
  im : Int
deriving DecidableEq
namespace Z15
@[ext] theorem ext' {x y : Z15} (hr : x.re = y.re) (hi : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
instance : Zero Z15 := ⟨0, 0⟩
instance : One Z15  := ⟨1, 0⟩
instance : Add Z15  := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Z15  := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Z15  := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
instance : Mul Z15 := ⟨fun x y =>
  ⟨x.re * y.re + 15 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
@[simp] theorem zero_re : (0 : Z15).re = 0 := rfl
@[simp] theorem zero_im : (0 : Z15).im = 0 := rfl
@[simp] theorem one_re : (1 : Z15).re = 1 := rfl
@[simp] theorem one_im : (1 : Z15).im = 0 := rfl
@[simp] theorem add_re (x y : Z15) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Z15) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : Z15) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Z15) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Z15) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Z15) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : Z15) : (x * y).re = x.re * y.re + 15 * x.im * y.im := rfl
@[simp] theorem mul_im (x y : Z15) : (x * y).im = x.re * y.im + x.im * y.re := rfl
instance : CommRing Z15 where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
end Z15
namespace Butcher
inductive RTree where
  /-- A rooted tree node with an ordered forest of children. -/
  | node : List RTree → RTree
deriving Repr, Inhabited
abbrev Forest := List RTree
def leaf : RTree := .node []
def graft (F : Forest) : RTree := .node F
mutual
  /-- Number of vertices in a rooted tree. -/
  def order : RTree → Nat | .node F => 1 + orderF F
  /-- Total number of vertices in a forest. -/
  def orderF : Forest → Nat | [] => 0 | t :: ts => order t + orderF ts
end
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
mutual
  /-- density γ(t) = |t| · ∏_children γ.  γ(•)=1, γ(•–•)=2,
      γ(cherry)=3, γ(ladder₃)=6. -/
  def gamma : RTree → Nat | .node F => order (.node F) * gammaF F
  /-- Product of the densities of the trees in a forest. -/
  def gammaF : Forest → Nat | [] => 1 | t :: ts => gamma t * gammaF ts
end
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
def dot (u v : List K) : K := (List.zipWith (· * ·) u v).sum
def pmul (u v : List K) : List K := List.zipWith (· * ·) u v
def mulMatVec (A : List (List K)) (v : List K) : List K := A.map (fun row => dot row v)
mutual
  /-- Internal elementary weight vector for a rooted tree. -/
  def phiVec (A : List (List K)) : RTree → List K
    | .node F => phiForest A F
  /-- ∏ over children of (A · phiVec child), pointwise; empty forest ↦ all-ones (length s). -/
  def phiForest (A : List (List K)) : Forest → List K
    | []      => A.map (fun _ => 1)
    | t :: ts => pmul (mulMatVec A (phiVec A t)) (phiForest A ts)
end
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
def Phi (A : List (List K)) (b : List K) (t : RTree) : K := dot b (phiVec A t)
abbrev orderCond (A : List (List K)) (b : List K) (t : RTree) : Prop :=
  (gamma t : K) * Phi A b t = 1
def t1 : RTree := leaf
def t2 : RTree := .node [leaf]
def t31 : RTree := .node [leaf, leaf]
def t32 : RTree := .node [.node [leaf]]
def t41 : RTree := .node [leaf, leaf, leaf]
def t42 : RTree := .node [leaf, .node [leaf]]
def t43 : RTree := .node [.node [leaf, leaf]]
def t44 : RTree := .node [.node [.node [leaf]]]
def t5bushy : RTree := .node [leaf, leaf, leaf, leaf]
def eulerA : List (List ℚ) := [[0]]
def eulerB : List ℚ := [1]
def heunA : List (List ℚ) := [[0,0],[1,0]]
def heunB : List ℚ := [1/2, 1/2]
def rk4A : List (List ℚ) := [[0,0,0,0],[1/2,0,0,0],[0,1/2,0,0],[0,0,1,0]]
def rk4B : List ℚ := [1/6, 1/3, 1/3, 1/6]
def dpA : List (List ℚ) :=
  [[0,0,0,0,0,0,0],
   [1/5,0,0,0,0,0,0],
   [3/40,9/40,0,0,0,0,0],
   [44/45,-56/15,32/9,0,0,0,0],
   [19372/6561,-25360/2187,64448/6561,-212/729,0,0,0],
   [9017/3168,-355/33,46732/5247,49/176,-5103/18656,0,0],
   [35/384,0,500/1113,125/192,-2187/6784,11/84,0]]
def dpB : List ℚ := [35/384, 0, 500/1113, 125/192, -2187/6784, 11/84, 0]
def gaussA : List (List Q15) :=
  [[⟨5/36, 0⟩,     ⟨2/9, -1/15⟩, ⟨5/36, -1/30⟩],
   [⟨5/36, 1/24⟩,  ⟨2/9, 0⟩,     ⟨5/36, -1/24⟩],
   [⟨5/36, 1/30⟩,  ⟨2/9, 1/15⟩,  ⟨5/36, 0⟩]]
def gaussB : List Q15 := [⟨5/18, 0⟩, ⟨4/9, 0⟩, ⟨5/18, 0⟩]
theorem one_le_order (t : RTree) : 1 ≤ order t := by
  cases t with | node F => simp only [order]; omega
def build : Nat → List RTree × List Forest
  | 0     => ([], [[]])
  | n + 1 =>
      let fs := (build n).2
      let trees := fs.map RTree.node
      let forests := [] :: trees.flatMap (fun t =>
          (fs.filter (fun ts => decide (order t + orderF ts ≤ n + 1))).map (fun ts => t :: ts))
      (trees, forests)
def treesB (n : Nat) : List RTree := (build n).1
mutual
theorem mem_build_trees : ∀ (n : Nat) (t : RTree), order t ≤ n → t ∈ (build n).1
  | n, RTree.node F, h => by
      cases n with
      | zero => simp only [order] at h; omega
      | succ m =>
          have hF : orderF F ≤ m := by simp only [order] at h; omega
          have hmemF : F ∈ (build m).2 := mem_build_forests m F hF
          change RTree.node F ∈ (build (m+1)).1
          simp only [build, List.mem_map]; exact ⟨F, hmemF, rfl⟩
  termination_by n t => (n, sizeOf t)
  decreasing_by simp_wf; omega

theorem mem_build_forests : ∀ (n : Nat) (F : Forest), orderF F ≤ n → F ∈ (build n).2
  | n, [], _ => by cases n <;> simp [build]
  | n, t :: ts, h => by
      have ht1 : 1 ≤ order t := one_le_order t
      cases n with
      | zero => simp only [orderF] at h; omega
      | succ m =>
          have hsum : order t + orderF ts ≤ m + 1 := by simpa only [orderF] using h
          have htm : order t ≤ m + 1 := by omega
          have htsm : orderF ts ≤ m := by omega
          have hmem_t : t ∈ (build (m+1)).1 := mem_build_trees (m+1) t htm
          have hmem_ts : ts ∈ (build m).2 := mem_build_forests m ts htsm
          have hfilt :
              ts ∈ ((build m).2).filter
                (fun ts => decide (order t + orderF ts ≤ m + 1)) :=
            List.mem_filter.2 ⟨hmem_ts, by simpa using hsum⟩
          change (t :: ts) ∈ (build (m+1)).2
          simp only [build, List.mem_cons, List.mem_flatMap, List.mem_map]
          refine Or.inr ⟨t, ?_, ts, hfilt, rfl⟩
          simpa only [build, List.mem_map] using hmem_t
  termination_by n F => (n, sizeOf F)
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega
end
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
def catalog (p : Nat) : List RTree := (treesB p).filter (fun t => decide (order t ≤ p))
def treesUpToFour : List RTree :=
  [t1, t2, t31, t41, t42, t32, .node [.node [leaf], leaf], t43, t44]
def treesUpToFive : List RTree :=
  [t1, t2, t31, t41, t5bushy, .node [leaf, leaf, .node [leaf]], t42,
   .node [leaf, .node [leaf], leaf], .node [leaf, .node [leaf, leaf]],
   .node [leaf, .node [.node [leaf]]], t32, .node [.node [leaf], leaf],
   .node [.node [leaf], leaf, leaf], .node [.node [leaf], .node [leaf]], t43,
   .node [.node [leaf, leaf], leaf], .node [.node [leaf, leaf, leaf]],
   .node [.node [leaf, .node [leaf]]], t44, .node [.node [.node [leaf]], leaf],
   .node [.node [.node [leaf], leaf]], .node [.node [.node [leaf, leaf]]],
   .node [.node [.node [.node [leaf]]]]]
def satisfiesOrderConditions (A : List (List K)) (b : List K) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCond A b t
def gaussOnes : List Q15 := [1, 1, 1]
def gaussC : List Q15 := [⟨1 / 2, -1 / 10⟩, ⟨1 / 2, 0⟩, ⟨1 / 2, 1 / 10⟩]
def gaussAc : List Q15 := [⟨1 / 5, -1 / 20⟩, ⟨1 / 8, 0⟩, ⟨1 / 5, 1 / 20⟩]
def gaussAAc : List Q15 :=
  [⟨7 / 120, -3 / 200⟩, ⟨1 / 48, 0⟩, ⟨7 / 120, 3 / 200⟩]
def gaussIA : List (List Z15) :=
  [[⟨50, 0⟩,   ⟨80, -24⟩, ⟨50, -12⟩],
   [⟨50, 15⟩,  ⟨80, 0⟩,   ⟨50, -15⟩],
   [⟨50, 12⟩,  ⟨80, 24⟩,  ⟨50, 0⟩]]
def gaussIB : List Z15 := [⟨100, 0⟩, ⟨160, 0⟩, ⟨100, 0⟩]
def Dscale : Int := 360
abbrev orderCondInt (A : List (List Z15)) (b : List Z15) (D : Int) (t : RTree) : Prop :=
  (⟨(gamma t : Int), 0⟩ : Z15) * Phi A b t = ⟨D ^ (order t), 0⟩
def satisfiesOrderConditionsInt (A : List (List Z15)) (b : List Z15) (D : Int) (p : Nat) : Prop :=
  ∀ t, order t ≤ p → orderCondInt A b D t
def toQ15 (x : Z15) : Q15 := ⟨(x.re : ℚ), (x.im : ℚ)⟩
def smulVec (c : K) (v : List K) : List K := v.map (c * ·)
def smulMat (c : K) (A : List (List K)) : List (List K) := A.map (smulVec c)
end Butcher
end RungeKuttaOrderConditions


