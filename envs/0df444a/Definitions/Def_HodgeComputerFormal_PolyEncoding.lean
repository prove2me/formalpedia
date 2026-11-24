-- Prove2me | Definitions.Def_HodgeComputerFormal_PolyEncoding
-- name    : HodgeComputerFormal_PolyEncoding
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:25:55.01677+00:00
-- url     : https://prove2.me/theorems/b0c4533d-6274-4c55-bb1d-a7fd13838da7
-- title:
--   Signed polynomial ASTs, sparse bivariate expressions, and Kronecker checker definitions
-- statement:
--   Reusable polynomial-encoding and certified evaluation machinery:
--
--   1. `SignedExpressions`: arithmetic evaluation `ringEval` of `Lean.Grind.CommRing.Expr` over arbitrary commutative rings.
--   2. `BivariateExpressions` & `BivariateDifferentiation`: sparse bivariate polynomial ASTs `Biv` in $(x, y)$ with `Expr` coefficients, together with `denote`, `scale`, `merge`, `multiply`, `dx`, `dy`, and soundness lemmas.
--   3. `KroneckerCheck` definitions: fast integer evaluators `fastEvalZ`, `fastSplitNat`, `fastMass3`, `checkKronecker3`, `checkBivEq3`; polymorphic ring-operation record `PolyOps α`, degree/$L^1$-bound tracker `PB`, relational transfer `PolyOpsRel`, and bound predicates `RespectsBound` and `RespectsBound2D`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/PolynomialEncoding/KroneckerCheck.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GrindInstances
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

section
/-! Positive and negative semiring parts of a ring expression.
This permits positional-encoding certificates to use nonnegative polynomial
coefficients while retaining the exact signed expression. All semantic
identities are proved, and no executable extension is introduced.
Prepared with OpenAI Codex assistance. -/
namespace PolynomialEncoding.SignedExpressions
open Lean.Grind.CommRing

def pairMul {R : Type*} [CommSemiring R] (p q : R × R) : R × R :=
  (p.1*q.1+p.2*q.2,p.1*q.2+p.2*q.1)
def pairPow {R : Type*} [CommSemiring R] (p : R × R) : ℕ → R × R
  | 0 => (1,0)
  | n+1 => pairMul p (pairPow p n)
def numberPair {R : Type*} [CommSemiring R] : Int → R × R
  | .ofNat n => (n,0)
  | .negSucc n => (0,n+1)
def splitEval {R : Type*} [CommSemiring R] (v : Nat → R) : Expr → R × R
  | .num n => numberPair n
  | .natCast n => (n,0)
  | .intCast n => numberPair n
  | .var i => (v i,0)
  | .neg a => let p:=splitEval v a; (p.2,p.1)
  | .add a b => let p:=splitEval v a; let q:=splitEval v b; (p.1+q.1,p.2+q.2)
  | .sub a b => let p:=splitEval v a; let q:=splitEval v b; (p.1+q.2,p.2+q.1)
  | .mul a b => pairMul (splitEval v a) (splitEval v b)
  | .pow a n => pairPow (splitEval v a) n

def ringEval {R : Type*} [CommRing R] (v : Nat → R) : Expr → R
  | .num n => n
  | .natCast n => n
  | .intCast n => n
  | .var i => v i
  | .neg a => -ringEval v a
  | .add a b => ringEval v a+ringEval v b
  | .sub a b => ringEval v a-ringEval v b
  | .mul a b => ringEval v a*ringEval v b
  | .pow a n => ringEval v a^n

section Semiring
variable {R S : Type*} [CommSemiring R] [CommSemiring S]
lemma pairMul_map (φ : R →+* S) (p q : R×R) :
    (φ (pairMul p q).1,φ (pairMul p q).2)=
      pairMul (φ p.1,φ p.2) (φ q.1,φ q.2) := by simp [pairMul]
lemma pairPow_map (φ : R →+* S) (p : R×R) (n : ℕ) :
    (φ (pairPow p n).1,φ (pairPow p n).2)=pairPow (φ p.1,φ p.2) n := by
  induction n with
  | zero => simp [pairPow]
  | succ n ih =>
    change (φ (pairMul p (pairPow p n)).1,φ (pairMul p (pairPow p n)).2)=_
    rw [pairMul_map,ih]
    rfl
lemma splitEval_map (φ : R →+* S) (v : Nat → R) (e : Expr) :
    (φ (splitEval v e).1,φ (splitEval v e).2)=splitEval (fun i=>φ (v i)) e := by
  induction e with
  | num n => cases n <;> simp [splitEval,numberPair]
  | intCast n => cases n <;> simp [splitEval,numberPair]
  | natCast n => simp [splitEval]
  | var i => simp [splitEval]
  | neg a ih =>
    have h1:=congrArg Prod.fst ih
    have h2:=congrArg Prod.snd ih
    simp only [splitEval]
    exact Prod.ext h2 h1
  | add a b ha hb =>
    have ha1:=congrArg Prod.fst ha; have ha2:=congrArg Prod.snd ha
    have hb1:=congrArg Prod.fst hb; have hb2:=congrArg Prod.snd hb
    dsimp only at ha1 ha2 hb1 hb2
    simp only [splitEval,map_add,ha1,ha2,hb1,hb2]
  | sub a b ha hb =>
    have ha1:=congrArg Prod.fst ha; have ha2:=congrArg Prod.snd ha
    have hb1:=congrArg Prod.fst hb; have hb2:=congrArg Prod.snd hb
    dsimp only at ha1 ha2 hb1 hb2
    simp only [splitEval,map_add,ha1,ha2,hb1,hb2]
  | mul a b ha hb =>
    change (φ (pairMul (splitEval v a) (splitEval v b)).1,
      φ (pairMul (splitEval v a) (splitEval v b)).2)=_
    rw [pairMul_map,ha,hb]
    rfl
  | pow a n ha =>
    change (φ (pairPow (splitEval v a) n).1,φ (pairPow (splitEval v a) n).2)=_
    rw [pairPow_map,ha]
    rfl
end Semiring

section Ring
variable {R : Type*} [CommRing R]
lemma pairPow_difference (p : R×R) (n : ℕ) :
    (pairPow p n).1-(pairPow p n).2=(p.1-p.2)^n := by
  induction n with
  | zero => simp [pairPow]
  | succ n ih =>
    simp only [pairPow,pairMul,pow_succ']
    linear_combination (p.1-p.2)*ih
lemma splitEval_difference (v : Nat → R) (e : Expr) :
    (splitEval v e).1-(splitEval v e).2=ringEval v e := by
  induction e with
  | num n => cases n <;> simp [splitEval,numberPair,ringEval,Int.cast_negSucc]
  | intCast n => cases n <;> simp [splitEval,numberPair,ringEval,Int.cast_negSucc]
  | natCast n => simp [splitEval,ringEval]
  | var i => simp [splitEval,ringEval]
  | neg a ha => simp only [splitEval,ringEval]; linear_combination -ha
  | add a b ha hb => simp only [splitEval,ringEval]; linear_combination ha+hb
  | sub a b ha hb => simp only [splitEval,ringEval]; linear_combination ha-hb
  | mul a b ha hb =>
    simp only [splitEval,pairMul,ringEval]
    rw [← ha,← hb]
    ring
  | pow a n ha => rw [splitEval,pairPow_difference,ha]; rfl

lemma ringEval_denote (ctx : Context R) (e : Expr) :
    ringEval (fun i=>ctx.get i) e=e.denote ctx := by
  induction e <;> simp only [ringEval,Expr.denote,Var.denote,denoteInt_eq, *]
end Ring
end PolynomialEncoding.SignedExpressions

end

section
/-! Sparse bivariate polynomials whose coefficients are ring expressions.
The operations preserve evaluation, with no assumptions about ordering or
uniqueness of the input terms. This connects coefficient certificates to the
whole covariant identity. Prepared with OpenAI Codex assistance. -/
namespace PolynomialEncoding.BivariateExpressions
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions

inductive Biv where
  | nil
  | cons (coefficient : Expr) (xDegree yDegree : ℕ) (rest : Biv)

def append : Biv → Biv → Biv
  | .nil,q => q
  | .cons a i j p,q => .cons a i j (append p q)

def merge : ℕ → Biv → Biv → Biv
  | 0,p,q => append p q
  | _+1,.nil,q => q
  | _+1,p,.nil => p
  | n+1,.cons a i j p,.cons b k l q =>
    if i=k ∧ j=l then .cons (.add a b) i j (merge n p q)
    else if 32*i+j>32*k+l then .cons a i j (merge n p (.cons b k l q))
    else .cons b k l (merge n (.cons a i j p) q)

def scale (a : Expr) (i j : ℕ) : Biv → Biv
  | .nil => .nil
  | .cons b k l q => .cons (.mul a b) (i+k) (j+l) (scale a i j q)

def multiply : Biv → Biv → Biv
  | .nil,_ => .nil
  | .cons a i j p,q => merge 512 (scale a i j q) (multiply p q)

variable {K : Type*} [CommRing K]
def denote (v : ℕ → K) (x y : K) : Biv → K
  | .nil => 0
  | .cons a i j p => ringEval v a*x^i*y^j+denote v x y p

lemma append_denote (v : ℕ → K) (x y : K) (p q : Biv) :
    denote v x y (append p q)=denote v x y p+denote v x y q := by
  induction p with
  | nil => simp [append,denote]
  | cons a i j p ih => simp [append,denote,ih,add_assoc]

lemma merge_denote (v : ℕ → K) (x y : K) (n : ℕ) (p q : Biv) :
    denote v x y (merge n p q)=denote v x y p+denote v x y q := by
  induction n generalizing p q with
  | zero => exact append_denote v x y p q
  | succ n ih =>
    cases p with
    | nil => simp [merge,denote]
    | cons a i j p =>
      cases q with
      | nil => simp [merge,denote]
      | cons b k l q =>
        simp only [merge]
        split_ifs with h h'
        · obtain ⟨rfl,rfl⟩ := h
          simp only [denote,ringEval,ih]
          ring
        · simp only [denote,ih]; ring
        · simp only [denote,ih]; ring

lemma scale_denote (v : ℕ → K) (x y : K) (a : Expr) (i j : ℕ) (p : Biv) :
    denote v x y (scale a i j p)=ringEval v a*x^i*y^j*denote v x y p := by
  induction p with
  | nil => simp [scale,denote]
  | cons b k l p ih =>
    simp only [scale,denote,ringEval,ih,pow_add]
    ring

theorem multiply_denote (v : ℕ → K) (x y : K) (p q : Biv) :
    denote v x y (multiply p q)=denote v x y p*denote v x y q := by
  induction p with
  | nil => simp [multiply,denote]
  | cons a i j p ih =>
    rw [multiply,merge_denote,scale_denote,ih]
    simp only [denote]
    ring

lemma cons_denote_eq (v : ℕ → K) (x y : K) (a b : Expr) (i j : ℕ) (p q : Biv)
    (hab : ringEval v a=ringEval v b) (hpq : denote v x y p=denote v x y q) :
    denote v x y (.cons a i j p)=denote v x y (.cons b i j q) := by
  simp only [denote,hab,hpq]

end PolynomialEncoding.BivariateExpressions

end

section
/-! Differentiation of the sparse bivariate expressions used in the exact
coefficient certificates. Prepared for fqlx with OpenAI Codex assistance. -/
namespace PolynomialEncoding.BivariateExpressions
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions MvPolynomial

def dx : Biv → Biv
  | .nil => .nil
  | .cons _ 0 _ p => dx p
  | .cons a (i+1) j p => .cons (.mul (.natCast (i+1)) a) i j (dx p)

def dy : Biv → Biv
  | .nil => .nil
  | .cons _ _ 0 p => dy p
  | .cons a i (j+1) p => .cons (.mul (.natCast (j+1)) a) i j (dy p)

variable {K : Type*} [CommRing K]

lemma ringEval_C (v : ℕ → K) (e : Expr) :
    ringEval (fun i => C (σ := Fin 2) (v i)) e=C (ringEval v e) := by
  induction e <;> simp_all [ringEval]

lemma pderiv_denote_dx (v : ℕ → K) (p : Biv) :
    pderiv 0 (denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) p)=
      denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) (dx p) := by
  induction p with
  | nil => simp [denote,dx]
  | cons a i j p ih =>
    rw [denote,map_add,ih]
    rw [ringEval_C]
    cases i with
    | zero => simp [dx]
    | succ i =>
      simp [dx,denote,ringEval,ringEval_C]
      ring

lemma pderiv_denote_dy (v : ℕ → K) (p : Biv) :
    pderiv 1 (denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) p)=
      denote (fun i => C (v i)) (X (0 : Fin 2)) (X 1) (dy p) := by
  induction p with
  | nil => simp [denote,dy]
  | cons a i j p ih =>
    rw [denote,map_add,ih]
    rw [ringEval_C]
    cases j with
    | zero => simp [dy]
    | succ j =>
      simp [dy,denote,ringEval,ringEval_C]
      ring

end PolynomialEncoding.BivariateExpressions

end

section
noncomputable section
namespace PolynomialEncoding.KroneckerCheck
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open scoped BigOperators Polynomial

def varsInRange (n : ℕ) : Expr → Bool
  | .num _ | .natCast _ | .intCast _ => true
  | .var i => decide (i < n)
  | .neg a => varsInRange n a
  | .add a b | .sub a b | .mul a b => varsInRange n a && varsInRange n b
  | .pow a _ => varsInRange n a

/-- Per-variable degree upper bound of a ring expression. -/
def exprDeg (i : ℕ) : Expr → ℕ
  | .num _ | .natCast _ | .intCast _ => 0
  | .var j => if j = i then 1 else 0
  | .neg a => exprDeg i a
  | .add a b | .sub a b => max (exprDeg i a) (exprDeg i b)
  | .mul a b => exprDeg i a + exprDeg i b
  | .pow a k => k * exprDeg i a

/-- Mixed-radix stride for variable `i` given base bounds `bound : Fin n → ℕ`. -/

def fastEvalZ (v : ℕ → ℤ) : Expr → ℤ
  | .num n => n
  | .natCast n => Int.ofNat n
  | .intCast n => n
  | .var i => v i
  | .neg a => Int.neg (fastEvalZ v a)
  | .add a b => Int.add (fastEvalZ v a) (fastEvalZ v b)
  | .sub a b => Int.sub (fastEvalZ v a) (fastEvalZ v b)
  | .mul a b => Int.mul (fastEvalZ v a) (fastEvalZ v b)
  | .pow a n => Int.pow (fastEvalZ v a) n

lemma fastEvalZ_eq (v : ℕ → ℤ) : ∀ e : Expr, fastEvalZ v e = ringEval v e
  | .num _ => rfl
  | .natCast _ => rfl
  | .intCast _ => rfl
  | .var _ => rfl
  | .neg a => congrArg (-·) (fastEvalZ_eq v a)
  | .add a b => congrArg₂ (· + ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .sub a b => congrArg₂ (· - ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .mul a b => congrArg₂ (· * ·) (fastEvalZ_eq v a) (fastEvalZ_eq v b)
  | .pow a n => congrArg (· ^ n) (fastEvalZ_eq v a)

def fastPairMul (p q : ℕ × ℕ) : ℕ × ℕ :=
  (Nat.add (Nat.mul p.1 q.1) (Nat.mul p.2 q.2), Nat.add (Nat.mul p.1 q.2) (Nat.mul p.2 q.1))

def fastPairPow (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => fastPairMul p (fastPairPow p n)

def fastSplitNat (v : ℕ → ℕ) : Expr → ℕ × ℕ
  | .num (.ofNat n) => (n, 0)
  | .num (.negSucc n) => (0, Nat.add n 1)
  | .natCast n => (n, 0)
  | .intCast (.ofNat n) => (n, 0)
  | .intCast (.negSucc n) => (0, Nat.add n 1)
  | .var i => (v i, 0)
  | .neg a => let p := fastSplitNat v a; (p.2, p.1)
  | .add a b => let p := fastSplitNat v a; let q := fastSplitNat v b; (Nat.add p.1 q.1, Nat.add p.2 q.2)
  | .sub a b => let p := fastSplitNat v a; let q := fastSplitNat v b; (Nat.add p.1 q.2, Nat.add p.2 q.1)
  | .mul a b => fastPairMul (fastSplitNat v a) (fastSplitNat v b)
  | .pow a n => fastPairPow (fastSplitNat v a) n

lemma fastPairPow_eq (p : ℕ × ℕ) : ∀ n : ℕ, fastPairPow p n = pairPow p n
  | 0 => rfl
  | n + 1 => by simp [fastPairPow, pairPow, fastPairMul, pairMul, fastPairPow_eq p n]

lemma fastSplitNat_eq (v : ℕ → ℕ) : ∀ e : Expr, fastSplitNat v e = splitEval v e
  | .num (.ofNat _) => rfl
  | .num (.negSucc _) => rfl
  | .natCast _ => rfl
  | .intCast (.ofNat _) => rfl
  | .intCast (.negSucc _) => rfl
  | .var _ => rfl
  | .neg a => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a]
  | .add a b => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .sub a b => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .mul a b => by simp [fastSplitNat, splitEval, fastPairMul, pairMul, fastSplitNat_eq v a, fastSplitNat_eq v b]
  | .pow a n => by simp [fastSplitNat, splitEval, fastSplitNat_eq v a, fastPairPow_eq]

def fastMass3 (e f : Expr) : ℕ × ℕ :=
  let pe := fastSplitNat (fun | 0 | 1 | 2 => 1 | _ => 0) e
  let pf := fastSplitNat (fun | 0 | 1 | 2 => 1 | _ => 0) f
  (Nat.add pe.1 pf.2, Nat.add pf.1 pe.2)

def checkKronecker3With (d0 d1 d2 b : ℕ) (b0 b1 b2 : ℤ) (e f : Expr) : Bool :=
  let m := fastMass3 e f
  decide (0 < b) && varsInRange 3 e && varsInRange 3 f &&
  decide (exprDeg 0 e < d0) && decide (exprDeg 1 e < d1) && decide (exprDeg 2 e < d2) &&
  decide (exprDeg 0 f < d0) && decide (exprDeg 1 f < d1) && decide (exprDeg 2 f < d2) &&
  decide (m.1 < b) && decide (m.2 < b) &&
  decide (fastEvalZ (fun | 0 => b0 | 1 => b1 | 2 => b2 | _ => 0) e =
          fastEvalZ (fun | 0 => b0 | 1 => b1 | 2 => b2 | _ => 0) f)

def checkKronecker3 (d0 d1 d2 b : ℕ) (e f : Expr) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  let b2 : ℤ := Int.ofNat (Nat.pow b (Nat.mul d0 d1))
  checkKronecker3With d0 d1 d2 b b0 b1 b2 e f


def negBiv : Biv → Biv
  | .nil => .nil
  | .cons a i j p => .cons (.neg a) i j (negBiv p)

lemma negBiv_denote {K : Type*} [CommRing K] (v : ℕ → K) (x y : K) (p : Biv) :
    denote v x y (negBiv p) = -denote v x y p := by
  induction p with
  | nil => simp [negBiv, denote]
  | cons a i j p ih => simp only [negBiv, denote, ringEval, ih]; ring

def checkBivZero3Aux (d0 d1 d2 b : ℕ) (b0 b1 b2 : ℤ) : Biv → Bool
  | .nil => true
  | .cons a _ _ p =>
    checkKronecker3With d0 d1 d2 b b0 b1 b2 a (.num 0) &&
    checkBivZero3Aux d0 d1 d2 b b0 b1 b2 p

def checkBivEq3 (d0 d1 d2 b : ℕ) (p q : Biv) : Bool :=
  let b0 : ℤ := Int.ofNat b
  let b1 : ℤ := Int.ofNat (Nat.pow b d0)
  let b2 : ℤ := Int.ofNat (Nat.pow b (Nat.mul d0 d1))
  checkBivZero3Aux d0 d1 d2 b b0 b1 b2 (merge 512 p (negBiv q))

/-! ### Part 2: `PolyOps`, `PB`, `PolyOpsRel`, and Factored 3-Variable Hybrid Checkers -/

/-- Polymorphic ring-operation backend allowing one polynomial algorithm to execute over
`ℤ`, bound-tracking records `PB`, `Unit` (for shape/length checks), `MvPolynomial (Fin 3) ℤ`,
or any commutative ring `R`. -/
structure PolyOps (α : Type*) where
  zero : α
  ofInt : ℤ → α
  add : α → α → α
  sub : α → α → α
  neg : α → α
  mul : α → α → α
  pow : α → ℕ → α

/-- Degree bounds `(d0, d1, d2)` and coefficient `ℓ¹`-norm bound `M` for a 3-variable polynomial. -/
structure PB where
  dS : ℕ
  dQ : ℕ
  dT : ℕ
  M : ℕ
  deriving DecidableEq

def intOps : PolyOps ℤ where
  zero := 0
  ofInt n := n
  add a b := Int.add a b
  sub a b := Int.sub a b
  neg a := Int.neg a
  mul a b := Int.mul a b
  pow a k := Int.pow a k

def pbOps : PolyOps PB where
  zero := ⟨0, 0, 0, 0⟩
  ofInt n := ⟨0, 0, 0, Int.natAbs n⟩
  add a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  sub a b := ⟨Nat.max a.dS b.dS, Nat.max a.dQ b.dQ, Nat.max a.dT b.dT, Nat.add a.M b.M⟩
  neg a := a
  mul a b := ⟨Nat.add a.dS b.dS, Nat.add a.dQ b.dQ, Nat.add a.dT b.dT, Nat.mul a.M b.M⟩
  pow a k := ⟨Nat.mul a.dS k, Nat.mul a.dQ k, Nat.mul a.dT k, Nat.pow a.M k⟩

def unitOps : PolyOps Unit where
  zero := ()
  ofInt _ := ()
  add _ _ := ()
  sub _ _ := ()
  neg _ := ()
  mul _ _ := ()
  pow _ _ := ()

abbrev P3Z := MvPolynomial (Fin 3) ℤ

def ringOps (R : Type*) [CommRing R] : PolyOps R where
  zero := 0
  ofInt n := (n : R)
  add a b := a + b
  sub a b := a - b
  neg a := -a
  mul a b := a * b
  pow a k := a ^ k

abbrev poly3Ops : PolyOps P3Z := ringOps P3Z

/-- Logical relation between two `PolyOps` backends preserving all ring operations. -/
structure PolyOpsRel {α β : Type*} (o1 : PolyOps α) (o2 : PolyOps β) (R : α → β → Prop) : Prop where
  rel_zero : R o1.zero o2.zero
  rel_ofInt : ∀ n, R (o1.ofInt n) (o2.ofInt n)
  rel_add : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.add a1 a2) (o2.add b1 b2)
  rel_sub : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.sub a1 a2) (o2.sub b1 b2)
  rel_neg : ∀ {a b}, R a b → R (o1.neg a) (o2.neg b)
  rel_mul : ∀ {a1 a2 b1 b2}, R a1 b1 → R a2 b2 → R (o1.mul a1 a2) (o2.mul b1 b2)
  rel_pow : ∀ {a b} k, R a b → R (o1.pow a k) (o2.pow b k)

/-- Explicit sharing combinator preserving common subexpressions across relational transfer
without triggering exponential let-unfolding in the kernel. -/
def letB {α β : Type*} (x : α) (f : α → β) : β := f x

lemma letB_rel {α₁ α₂ β₁ β₂ : Type*} {Ra : α₁ → α₂ → Prop} {Rb : β₁ → β₂ → Prop}
    {x₁ : α₁} {x₂ : α₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂}
    (hx : Ra x₁ x₂) (hf : ∀ {a₁ a₂}, Ra a₁ a₂ → Rb (f₁ a₁) (f₂ a₂)) :
    Rb (letB x₁ f₁) (letB x₂ f₂) := hf hx

lemma letB_step {α β : Type*} {x y : α} {f : α → β} {z : β} (hxy : x = y) (hf : f y = z) :
    letB x f = z := by rw [letB, hxy, hf]

lemma letB_intro {α β : Type*} {P : β → Prop} {x : α} {f : α → β}
    (h : ∀ a, a = x → P (f a)) : P (letB x f) := h x rfl

def v3Int (s q t : ℤ) : Fin 3 → ℤ
  | 0 => s
  | 1 => q
  | 2 => t

lemma poly3ToIntRel (s q t : ℤ) :
    PolyOpsRel poly3Ops intOps (fun p z => MvPolynomial.eval (v3Int s q t) p = z) where
  rel_zero := by simp [poly3Ops, ringOps, intOps]
  rel_ofInt n := by simp [poly3Ops, ringOps, intOps]
  rel_add h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]
  rel_sub h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]; rfl
  rel_neg h := by simp [poly3Ops, ringOps, intOps, h]; rfl
  rel_mul h1 h2 := by simp [poly3Ops, ringOps, intOps, h1, h2]
  rel_pow k h := by simp [poly3Ops, ringOps, intOps, h]

lemma poly3ToRingRel {R : Type*} [CommRing R] (v : Fin 3 → R) :
    PolyOpsRel poly3Ops (ringOps R)
      (fun p x => MvPolynomial.eval₂Hom (Int.castRingHom R) v p = x) where
  rel_zero := by simp [poly3Ops, ringOps]
  rel_ofInt n := by simp [poly3Ops, ringOps]
  rel_add h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_add, h1, h2]
  rel_sub h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_sub, h1, h2]
  rel_neg h := by dsimp only [poly3Ops, ringOps]; rw [map_neg, h]
  rel_mul h1 h2 := by dsimp only [poly3Ops, ringOps]; rw [map_mul, h1, h2]
  rel_pow k h := by dsimp only [poly3Ops, ringOps]; rw [map_pow, h]

def evalQT (q t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.C q
    | 2 => Polynomial.C t)

lemma eval_evalQT (p : P3Z) (s q t : ℤ) :
    (evalQT q t p).eval s = MvPolynomial.eval (v3Int s q t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalQT, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int]

/-- Coefficient `ℓ¹`-norm of an integer polynomial. -/
def polyL1 (f : Polynomial ℤ) : ℕ :=
  ∑ i ∈ f.support, (f.coeff i).natAbs

lemma polyL1_eq_sum_range (f : Polynomial ℤ) (N : ℕ) (hN : ∀ i ∈ f.support, i < N) :
    polyL1 f = ∑ i ∈ Finset.range N, (f.coeff i).natAbs := by
  unfold polyL1
  apply Finset.sum_subset
  · intro i hi; exact Finset.mem_range.mpr (hN i hi)
  · intro i _ hi
    have h0 : f.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [h0]

lemma polyL1_zero : polyL1 0 = 0 := by simp [polyL1]

lemma polyL1_C (c : ℤ) : polyL1 (Polynomial.C c) = c.natAbs := by
  by_cases hc : c = 0
  · subst hc; simp [polyL1]
  · simp only [polyL1, Polynomial.support_C hc, Finset.sum_singleton, Polynomial.coeff_C_zero]

lemma polyL1_X : polyL1 Polynomial.X = 1 := by
  rw [polyL1_eq_sum_range Polynomial.X 2 (fun i hi => by
    have : i = 1 := by simpa [Polynomial.support_X] using hi
    omega)]
  simp [Finset.sum_range_succ]

lemma polyL1_neg (f : Polynomial ℤ) : polyL1 (-f) = polyL1 f := by
  simp [polyL1, Polynomial.support_neg]

lemma polyL1_add (f g : Polynomial ℤ) : polyL1 (f + g) ≤ polyL1 f + polyL1 g := by
  set N := max f.natDegree g.natDegree + 1
  have hf : ∀ i ∈ f.support, i < N := fun i hi => Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_mem_supp i hi).trans (le_max_left _ _))
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le ((Polynomial.le_natDegree_of_mem_supp i hi).trans (le_max_right _ _))
  have hfg : ∀ i ∈ (f + g).support, i < N := fun i hi => by
    rcases Finset.mem_union.mp (Polynomial.support_add hi) with h | h
    · exact hf i h
    · exact hg i h
  rw [polyL1_eq_sum_range (f + g) N hfg, polyL1_eq_sum_range f N hf, polyL1_eq_sum_range g N hg,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact Int.natAbs_add_le _ _

lemma polyL1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) :
    polyL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyL1_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (polyL1_add _ _).trans (Nat.add_le_add_left ih _)

lemma polyL1_C_mul (c : ℤ) (g : Polynomial ℤ) :
    polyL1 (Polynomial.C c * g) = c.natAbs * polyL1 g := by
  set N := g.natDegree + 1
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)
  have hcg : ∀ i ∈ (Polynomial.C c * g).support, i < N := fun i hi => by
    have h0 : (Polynomial.C c * g).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    rw [Polynomial.coeff_C_mul] at h0
    exact hg i (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul h0))
  rw [polyL1_eq_sum_range (Polynomial.C c * g) N hcg, polyL1_eq_sum_range g N hg, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Polynomial.coeff_C_mul, Int.natAbs_mul]

lemma polyL1_X_pow_mul (n : ℕ) (g : Polynomial ℤ) :
    polyL1 (Polynomial.X ^ n * g) = polyL1 g := by
  set N := g.natDegree + 1
  have hg : ∀ i ∈ g.support, i < N := fun i hi => Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi)
  have hxg : ∀ i ∈ (Polynomial.X ^ n * g).support, i < n + N := fun i hi => by
    have hle := Polynomial.le_natDegree_of_mem_supp i hi
    have hdeg := (Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℤ) ^ n) (q := g)).trans
      (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le n) _)
    omega
  rw [polyL1_eq_sum_range (Polynomial.X ^ n * g) (n + N) hxg, polyL1_eq_sum_range g N hg,
    Finset.sum_range_add]
  have hlo : ∑ x ∈ Finset.range n, ((Polynomial.X ^ n * g).coeff x).natAbs = 0 := by
    apply Finset.sum_eq_zero; intro x hx
    rw [Finset.mem_range] at hx
    rw [Polynomial.coeff_X_pow_mul', if_neg (by omega)]; rfl
  rw [hlo, zero_add]
  apply Finset.sum_congr rfl; intro x _
  rw [add_comm, Polynomial.coeff_X_pow_mul]

lemma polyL1_mul (f g : Polynomial ℤ) : polyL1 (f * g) ≤ polyL1 f * polyL1 g := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul]
  refine (polyL1_sum_le _ _).trans ?_
  rw [polyL1, Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  rw [mul_assoc, polyL1_C_mul, polyL1_X_pow_mul]

lemma polyL1_pow (f : Polynomial ℤ) (k : ℕ) : polyL1 (f ^ k) ≤ (polyL1 f) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ← Polynomial.C_1, polyL1_C]; rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (polyL1_mul _ _).trans (Nat.mul_le_mul ih le_rfl)

def RespectsBound (Qmax Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ q t : ℤ, q.natAbs ≤ Qmax → t.natAbs ≤ Tmax → polyL1 (evalQT q t p) ≤ b.M)

lemma respectsBoundRel (Qmax Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound Qmax Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops, ringOps] at hm,
    fun _ _ _ _ => by simp [poly3Ops, ringOps, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
        exact (MvPolynomial.mem_support_iff.mp hm)
          (by dsimp only [poly3Ops, ringOps]; rw [hC, MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun q t _ _ => by
      have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
      dsimp only [poly3Ops, ringOps, pbOps]
      rw [hC, evalQT, MvPolynomial.eval₂Hom_C, polyL1_C]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops, ringOps] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops, ringOps] using hm),
    fun q t hq ht => by simp only [poly3Ops, ringOps, pbOps, map_neg, polyL1_neg]; exact h.2 q t hq ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun q t hq ht => by
      simp only [poly3Ops, ringOps, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 q t hq ht) (h2.2 q t hq ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, ringOps, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun q t _ _ => by simp only [poly3Ops, ringOps, pbOps, pow_zero, map_one]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun q t hq ht => by
          simp only [poly3Ops, ringOps, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 q t hq ht) _)⟩

lemma respectsBound_X0 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ _ => by simp [evalQT, polyL1_X]⟩

lemma respectsBound_X1 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 1) ⟨0, 1, 0, Qmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t hq _ => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, hq]⟩

lemma respectsBound_X2 (Qmax Tmax : ℕ) :
    RespectsBound Qmax Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun q t _ ht => by simp only [evalQT, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

lemma natDegree_divX_le_pred {R : Type*} [Semiring R] (g : R[X]) :
    g.divX.natDegree ≤ g.natDegree - 1 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [Polynomial.coeff_divX]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)


def evalT2D (D : ℕ) (t : ℤ) : P3Z →+* Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => match i with
    | 0 => Polynomial.X
    | 1 => Polynomial.X ^ D
    | 2 => Polynomial.C t)

lemma eval_evalT2D (D : ℕ) (p : P3Z) (B : ℕ) (t : ℤ) :
    (evalT2D D t p).eval (B : ℤ) = MvPolynomial.eval (v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p := by
  induction p using MvPolynomial.induction_on' with
  | add p1 p2 h1 h2 => simp only [map_add, Polynomial.eval_add, h1, h2]
  | monomial m c =>
    simp only [evalT2D, MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval_monomial,
      Polynomial.eval_mul, Polynomial.eval_C, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Fin.prod_univ_three, Polynomial.eval_pow, Polynomial.eval_X, v3Int, Nat.cast_pow]

def RespectsBound2D (D Tmax : ℕ) (p : P3Z) (b : PB) : Prop :=
  (∀ m ∈ p.support, m 0 ≤ b.dS ∧ m 1 ≤ b.dQ ∧ m 2 ≤ b.dT) ∧
  (∀ t : ℤ, t.natAbs ≤ Tmax → polyL1 (evalT2D D t p) ≤ b.M)

lemma respectsBound2DRel (D Tmax : ℕ) :
    PolyOpsRel poly3Ops pbOps (RespectsBound2D D Tmax) where
  rel_zero := ⟨fun m hm => by simp [poly3Ops, ringOps] at hm,
    fun _ _ => by simp [poly3Ops, ringOps, pbOps, polyL1_zero]⟩
  rel_ofInt n := ⟨fun m hm => by
      have hm0 : m = 0 := by
        by_contra hne
        have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
        exact (MvPolynomial.mem_support_iff.mp hm)
          (by dsimp only [poly3Ops, ringOps]; rw [hC, MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
      subst hm0; simp [pbOps],
    fun t _ => by
      have hC : (n : P3Z) = MvPolynomial.C n := (map_intCast (MvPolynomial.C : ℤ →+* P3Z) n).symm
      dsimp only [poly3Ops, ringOps, pbOps]
      rw [hC, evalT2D, MvPolynomial.eval₂Hom_C, polyL1_C]⟩
  rel_add h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_add]
      exact (polyL1_add _ _).trans (Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_sub h1 h2 := ⟨fun m hm => by
      dsimp only [poly3Ops, ringOps] at hm
      rw [sub_eq_add_neg] at hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · obtain ⟨a, b, c⟩ := h1.1 m h
        exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _), c.trans (le_max_left _ _)⟩
      · rw [MvPolynomial.support_neg] at h
        obtain ⟨a, b, c⟩ := h2.1 m h
        exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _), c.trans (le_max_right _ _)⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_sub]
      rw [sub_eq_add_neg]
      exact (polyL1_add _ _).trans (by rw [polyL1_neg]; exact Nat.add_le_add (h1.2 t ht) (h2.2 t ht))⟩
  rel_neg h := ⟨fun m hm => h.1 m (by simpa [poly3Ops, ringOps] using hm),
    fun t ht => by simp only [poly3Ops, ringOps, pbOps, map_neg, polyL1_neg]; exact h.2 t ht⟩
  rel_mul h1 h2 := ⟨fun m hm => by
      rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
      obtain ⟨a1, b1, c1⟩ := h1.1 m1 hm1
      obtain ⟨a2, b2, c2⟩ := h2.1 m2 hm2
      exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
    fun t ht => by
      simp only [poly3Ops, ringOps, pbOps, map_mul]
      exact (polyL1_mul _ _).trans (Nat.mul_le_mul (h1.2 t ht) (h2.2 t ht))⟩
  rel_pow k h := by
    induction k with
    | zero =>
      refine ⟨fun m hm => by
        have : m = 0 := by simpa [poly3Ops, ringOps, MvPolynomial.support_one] using hm
        subst this; simp [pbOps],
        fun t _ => by simp only [poly3Ops, ringOps, pbOps, pow_zero, map_one]; rw [← Polynomial.C_1, polyL1_C]; rfl⟩
    | succ k ih =>
      refine ⟨fun m hm => by
        rw [show poly3Ops.pow _ (k + 1) = _ ^ k * _ from pow_succ _ k] at hm
        rcases Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm) with ⟨m1, hm1, m2, hm2, rfl⟩
        obtain ⟨a1, b1, c1⟩ := ih.1 m1 hm1
        obtain ⟨a2, b2, c2⟩ := h.1 m2 hm2
        simp only [pbOps]
        exact ⟨Nat.add_le_add a1 a2, Nat.add_le_add b1 b2, Nat.add_le_add c1 c2⟩,
        fun t ht => by
          simp only [poly3Ops, ringOps, pbOps, map_pow]
          exact (polyL1_pow _ _).trans (Nat.pow_le_pow_left (h.2 t ht) _)⟩

lemma respectsBound2D_X0 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 0) ⟨1, 0, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 0 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by simp [evalT2D, polyL1_X]⟩

lemma respectsBound2D_X1 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 1) ⟨0, 1, 0, 1⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 1 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t _ => by
      simp only [evalT2D, MvPolynomial.eval₂Hom_X']
      rw [← mul_one ((Polynomial.X : Polynomial ℤ) ^ D), polyL1_X_pow_mul, ← Polynomial.C_1, polyL1_C]; rfl⟩

lemma respectsBound2D_X2 (D Tmax : ℕ) :
    RespectsBound2D D Tmax (MvPolynomial.X 2) ⟨0, 0, 1, Tmax⟩ := by
  refine ⟨fun m hm => by
    have : m = Finsupp.single 2 1 := by simpa [MvPolynomial.support_X] using hm
    subst this; simp,
    fun t ht => by simp only [evalT2D, MvPolynomial.eval₂Hom_X', polyL1_C, ht]⟩

/-- Soundness of factored 2D Kronecker (variables `0, 1` at `(B, B^D)`) × 1D grid (variable `2`)
vanishing check. -/

def allRange (lo : ℤ) : ℕ → (ℤ → Bool) → Bool
  | 0, _ => true
  | k + 1, f => f lo && allRange (Int.add lo 1) k f

lemma allRange_append (lo : ℤ) (m n : ℕ) (f : ℤ → Bool) :
    allRange lo (m + n) f = (allRange lo m f && allRange (lo + (m : ℤ)) n f) := by
  induction m generalizing lo with
  | zero => simp [allRange]
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [allRange, Bool.and_assoc]
    congr 1
    change allRange (lo + 1) (k + n) f = (allRange (lo + 1) k f && allRange (lo + ((k + 1 : ℕ) : ℤ)) n f)
    rw [ih (lo + 1)]
    congr 2; push_cast; ring

def rangeInt (lo : ℤ) (n : ℕ) : Finset ℤ :=
  (Finset.range n).image (fun k : ℕ => lo + (k : ℤ))

lemma rangeInt_card (lo : ℤ) (n : ℕ) : (rangeInt lo n).card = n := by
  rw [rangeInt, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

lemma allRange_spec (lo : ℤ) (n : ℕ) (f : ℤ → Bool)
    (h : allRange lo n f = true) : ∀ x ∈ rangeInt lo n, f x = true := by
  induction n generalizing lo with
  | zero => intro x hx; simp [rangeInt] at hx
  | succ k ih =>
    simp only [allRange, Bool.and_eq_true] at h
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    cases j with
    | zero => simpa using h.1
    | succ j' =>
      have hmem : (lo + 1) + (j' : ℤ) ∈ rangeInt (lo + 1) k :=
        Finset.mem_image.mpr ⟨j', Finset.mem_range.mpr (by omega), rfl⟩
      have hres := ih (lo + 1) h.2 _ hmem
      rwa [show (lo + 1) + (j' : ℤ) = lo + ((j' + 1 : ℕ) : ℤ) by push_cast; ring] at hres

lemma rangeInt_natAbs_le (lo : ℤ) (n M : ℕ)
    (hlo : lo.natAbs ≤ M) (hhi : (lo + (n : ℤ) - 1).natAbs ≤ M) :
    ∀ x ∈ rangeInt lo n, x.natAbs ≤ M := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  rw [Finset.mem_range] at hk
  omega

/-- Precomputed power table `[c, c*x, ..., c*x^(n-1)]` over any `PolyOps α`. -/
def powList {α : Type*} (o : PolyOps α) (x : α) : ℕ → α → List α
  | 0, _ => []
  | n + 1, cur => cur :: powList o x n (o.mul cur x)

def getPow {α : Type*} (o : PolyOps α) (x : α) (tbl : List α) (k : ℕ) : α :=
  tbl.getD k (o.pow x k)

lemma powList_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2) :
    ∀ n {c1 c2}, R c1 c2 → List.Forall₂ R (powList o1 x1 n c1) (powList o2 x2 n c2)
  | 0, _, _, _ => List.Forall₂.nil
  | n + 1, _, _, hc => List.Forall₂.cons hc (powList_rel hR hx n (hR.rel_mul hc hx))

lemma list_forall₂_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (i : ℕ) (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ ht, i + 1, h1, h2 =>
      list_forall₂_getElem ht i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

lemma list_getD_rel_gen {α β : Type*} {R : α → β → Prop} {d1 : α} {d2 : β} (hd : R d1 d2) :
    ∀ {t1 : List α} {t2 : List β}, List.Forall₂ R t1 t2 → ∀ k : ℕ, R (t1.getD k d1) (t2.getD k d2)
  | [], [], .nil, k => by simp only [List.getD_nil]; exact hd
  | _ :: _, _ :: _, .cons h _, 0 => by simp only [List.getD_cons_zero]; exact h
  | _ :: _, _ :: _, .cons _ ht, k + 1 => by simp only [List.getD_cons_succ]; exact list_getD_rel_gen hd ht k

lemma getPow_rel {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}
    (hR : PolyOpsRel o1 o2 R) {x1 : α} {x2 : β} (hx : R x1 x2)
    {t1 : List α} {t2 : List β} (ht : List.Forall₂ R t1 t2) (k : ℕ) :
    R (getPow o1 x1 t1 k) (getPow o2 x2 t2 k) :=
  list_getD_rel_gen (hR.rel_pow k hx) ht k

lemma powList_ring_getD_gen {R : Type*} [CommRing R] (x d : R) :
    ∀ n m k, (powList (ringOps R) x n (x ^ m)).getD k d = if k < n then x ^ (m + k) else d
  | 0, _, _ => by simp [powList]
  | n + 1, m, 0 => by simp [powList]
  | n + 1, m, k + 1 => by
    change (powList (ringOps R) x n (x ^ m * x)).getD k d = _
    rw [← pow_succ, powList_ring_getD_gen x d n (m + 1) k]
    by_cases hk : k < n
    · have h1 : k + 1 < n + 1 := by omega
      simp [hk, h1, show m + 1 + k = m + (k + 1) by omega]
    · have h1 : ¬(k + 1 < n + 1) := by omega
      simp [hk, h1]

lemma getPow_ring_eq {R : Type*} [CommRing R] (x : R) (n k : ℕ) :
    getPow (ringOps R) x (powList (ringOps R) x n ((ringOps R).ofInt 1)) k = x ^ k := by
  have h1 : (ringOps R).ofInt 1 = x ^ 0 := by simp [ringOps]
  rw [getPow, h1, powList_ring_getD_gen]
  simp [ringOps]

lemma getPow_poly3_eq (x : P3Z) (n k : ℕ) :
    getPow poly3Ops x (powList poly3Ops x n (poly3Ops.ofInt 1)) k = x ^ k :=
  getPow_ring_eq x n k

end PolynomialEncoding.KroneckerCheck
end


