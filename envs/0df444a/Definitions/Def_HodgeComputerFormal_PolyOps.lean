-- Prove2me | Definitions.Def_HodgeComputerFormal_PolyOps
-- name    : HodgeComputerFormal_PolyOps
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:26:42.585286+00:00
-- url     : https://prove2.me/theorems/ec66613c-3d9f-4033-a942-ca70ea30ceea
-- title:
--   Polymorphic univariate and bivariate list-polynomial operations (`UPoly`, `BivL`, `UBivL`)
-- statement:
--   Generic dense list-polynomial algebra parameterized by a `PolyOps α` record:
--
--   - `UPoly α` (univariate polynomials in $U$), `BivL α` (bivariate polynomials in $(x, y)$), and `UBivL α` (univariate $U$-polynomials over `BivL α`), with addition, negation, subtraction, scaling, shift, multiplication, synthetic division by $U - 1$, and quadratic reduction modulo $21 S x^2 + 21 T y^2 + H_0$.
--   - Complete relational transfer theorems (`PolyOpsRel`) lifting every operation simultaneously across `ℤ` (kernel evaluation), `PB` (degree and $L^1$ bounds), `MvPolynomial (Fin 3) ℤ` (symbolic ring), and `K5` (field evaluation).
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/PolynomialEncoding/PolyOps.lean

import Definitions.Def_HodgeComputerFormal_PolyEncoding

set_option autoImplicit false

/-! Dense list-based univariate, bivariate, and trivariate polynomial algebra over any
abstract `PolyOps α` backend, with relational lifts (`PolyOpsRel`), length bounds,
synthetic division by `X - 1`, bilinear contraction (`dotW` + `combineBivDot`), and
ring-evaluation homomorphisms into any commutative ring `R`.

Extracted from the `symmetric-sextic-residual` construction (`benediamond`). -/

noncomputable section
namespace PolynomialEncoding.PolyOps
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.KroneckerCheck
open scoped BigOperators Polynomial

/-- Dense univariate polynomial as a little-endian coefficient list `[c₀, c₁, ...]`. -/
abbrev UPoly (α : Type*) := List α

/-- Dense bivariate polynomial in `(x, y)` as a list of `y`-polynomials in increasing `x`-degree. -/
abbrev BivL (α : Type*) := List (List α)

/-- Dense univariate polynomial in `U` whose coefficients are bivariate polynomials in `(x, y)`. -/
abbrev UBivL (α : Type*) := List (BivL α)

def uAdd {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => o.add a b :: uAdd o as bs

def uNeg {α : Type*} (o : PolyOps α) (a : UPoly α) : UPoly α :=
  a.map o.neg

def uSub {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], b => uNeg o b
  | a, [] => a
  | a :: as, b :: bs => o.sub a b :: uSub o as bs

def uSc {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) : UPoly α :=
  a.map (o.mul c)

def uShift {α : Type*} (o : PolyOps α) (a : UPoly α) : UPoly α :=
  o.zero :: a

def uTail {α : Type*} : UPoly α → UPoly α
  | [] => []
  | _ :: tl => tl

def uMul {α : Type*} (o : PolyOps α) : UPoly α → UPoly α → UPoly α
  | [], _ => []
  | a :: as, b => uAdd o (uSc o a b) (uShift o (uMul o as b))

def uMonomial {α : Type*} (o : PolyOps α) : ℕ → α → UPoly α
  | 0, c => [c]
  | k + 1, c => o.zero :: uMonomial o k c

def uEval {α : Type*} (o : PolyOps α) : UPoly α → α → α
  | [], _ => o.zero
  | a :: as, t => o.add a (o.mul t (uEval o as t))

def uPow {α : Type*} (o : PolyOps α) (p : UPoly α) : ℕ → UPoly α
  | 0 => [o.ofInt 1]
  | n + 1 => uMul o (uPow o p n) p

def bivAdd {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], b => b
  | a, [] => a
  | r1 :: rs1, r2 :: rs2 => uAdd o r1 r2 :: bivAdd o rs1 rs2

def bivNeg {α : Type*} (o : PolyOps α) (b : BivL α) : BivL α :=
  b.map (uNeg o)

def bivSub {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], b => bivNeg o b
  | a, [] => a
  | r1 :: rs1, r2 :: rs2 => uSub o r1 r2 :: bivSub o rs1 rs2

def bivSc {α : Type*} (o : PolyOps α) (c : α) (b : BivL α) : BivL α :=
  b.map (uSc o c)

def bivConst {α : Type*} (c : α) : BivL α := [[c]]

def bivMul {α : Type*} (o : PolyOps α) : BivL α → BivL α → BivL α
  | [], _ => []
  | r :: rs, b => bivAdd o (b.map (uMul o r)) ([] :: bivMul o rs b)

/-- Single division-free reduction step modulo a quadratic relation `s * x^2 = t * y^2 + n`:
multiplies the polynomial by `s` and replaces every `x^{k+2}` with `(t * y^2 + n) * x^k`. -/
def bivRedOnce {α : Type*} (o : PolyOps α) (s t n : α) : BivL α → BivL α
  | [] => []
  | [r0] => [uSc o s r0]
  | [r0, r1] => [uSc o s r0, uSc o s r1]
  | r0 :: r1 :: rest =>
      bivAdd o [uSc o s r0, uSc o s r1]
        (rest.map fun ri => uAdd o (uSc o n ri) (uShift o (uShift o (uSc o t ri))))

def ubAdd {α : Type*} (o : PolyOps α) : UBivL α → UBivL α → UBivL α
  | [], b => b
  | a, [] => a
  | b1 :: bs1, b2 :: bs2 => bivAdd o b1 b2 :: ubAdd o bs1 bs2

def ubNeg {α : Type*} (o : PolyOps α) (a : UBivL α) : UBivL α :=
  a.map (bivNeg o)

def ubSub {α : Type*} (o : PolyOps α) : UBivL α → UBivL α → UBivL α
  | [], b => ubNeg o b
  | a, [] => a
  | b1 :: bs1, b2 :: bs2 => bivSub o b1 b2 :: ubSub o bs1 bs2

def ubSc {α : Type*} (o : PolyOps α) (c : α) (a : UBivL α) : UBivL α :=
  a.map (bivSc o c)

def ubBmul {α : Type*} (o : PolyOps α) (b0 : BivL α) (a : UBivL α) : UBivL α :=
  a.map (bivMul o b0)

def ubShift {α : Type*} (a : UBivL α) : UBivL α := [] :: a

def ubMulU {α : Type*} (o : PolyOps α) : UPoly α → UBivL α → UBivL α
  | [], _ => []
  | c :: cs, ub => ubAdd o (ubSc o c ub) (ubShift (ubMulU o cs ub))

/-- Synthetic division of `P(U)` by `(U - 1)`, returning `(P(1), Q(U))` with
`P(U) = P(1) + (U - 1) * Q(U)`. -/
def ubSynDiv1Rem {α : Type*} (o : PolyOps α) : UBivL α → BivL α × UBivL α
  | [] => ([], [])
  | [b] => (b, [])
  | b :: b' :: rest =>
      let (r, q) := ubSynDiv1Rem o (b' :: rest)
      (bivAdd o b r, r :: q)

/-- Coefficient-wise inner product of `A` against a weight table `W` (indexed `1 .. M`)
at degree offset `j + shift`. -/
def dotWAux {α : Type*} (o : PolyOps α) (W : List α) (M shift j : ℕ) : ℕ → UPoly α → α
  | _, [] => o.zero
  | i, a :: as =>
      let idx := i + j + shift
      let term := if 1 ≤ idx ∧ idx ≤ M then o.mul a (W.getD (idx - 1) o.zero) else o.zero
      o.add term (dotWAux o W M shift j (i + 1) as)

def dotWGo {α : Type*} (o : PolyOps α) (M : ℕ) (A W : UPoly α) (shift j : ℕ) : ℕ → UPoly α
  | 0 => []
  | k + 1 => dotWAux o W M shift j 0 A :: dotWGo o M A W shift (j + 1) k

/-- Bilinear weight contraction vector `[dotWAux ... 0, ..., dotWAux ... (nB - 1)]`. -/
def dotW {α : Type*} (o : PolyOps α) (M nB : ℕ) (A W : UPoly α) (shift : ℕ) : UPoly α :=
  dotWGo o M A W shift 0 nB

def combineBivDot {α : Type*} (o : PolyOps α) : UBivL α → UPoly α → BivL α
  | [], _ => []
  | _, [] => []
  | b :: bs, c :: cs => bivAdd o (bivSc o c b) (combineBivDot o bs cs)

/-- Scalar-or-univariate-polynomial wrapper avoiding list allocations on constant subexpressions. -/
inductive SPoly (α : Type*)
  | sc : α → SPoly α
  | poly : UPoly α → SPoly α

def sToU {α : Type*} : SPoly α → UPoly α
  | .sc a => [a]
  | .poly p => p

def sNeg {α : Type*} (o : PolyOps α) : SPoly α → SPoly α
  | .sc a => .sc (o.neg a)
  | .poly p => .poly (uNeg o p)

def sAdd {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.add a b)
  | .sc a, .poly [] => .sc a
  | .sc a, .poly (b :: bs) => .poly (o.add a b :: bs)
  | .poly p, .poly q => .poly (uAdd o p q)
  | .poly [], .sc b => .sc b
  | .poly (a :: as), .sc b => .poly (o.add a b :: as)

def sSub {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.sub a b)
  | a, b => .poly (uSub o (sToU a) (sToU b))

def sMul {α : Type*} (o : PolyOps α) : SPoly α → SPoly α → SPoly α
  | .sc a, .sc b => .sc (o.mul a b)
  | .sc a, .poly p => .poly (uSc o a p)
  | .poly p, .sc b => .poly (uSc o b p)
  | .poly p, .poly q => .poly (uMul o p q)

def sShiftK {α : Type*} (o : PolyOps α) : ℕ → SPoly α → SPoly α
  | 0, x => x
  | k, .sc a => .poly (uMonomial o k a)
  | k + 1, .poly p => sShiftK o k (.poly (uShift o p))

/-- Evaluate a 2-variable `Expr` (variables `0, 1`) using precomputed power tables `p0, p1`. -/
def evalExpr2 {α : Type*} (o : PolyOps α) (x0 x1 : α) (p0 p1 : List α) : Expr → α
  | .num c => o.ofInt c
  | .natCast n => o.ofInt (n : ℤ)
  | .intCast z => o.ofInt z
  | .var 0 => x0
  | .var 1 => x1
  | .var _ => o.zero
  | .neg a => o.neg (evalExpr2 o x0 x1 p0 p1 a)
  | .add a b => o.add (evalExpr2 o x0 x1 p0 p1 a) (evalExpr2 o x0 x1 p0 p1 b)
  | .sub a b => o.sub (evalExpr2 o x0 x1 p0 p1 a) (evalExpr2 o x0 x1 p0 p1 b)
  | .mul a b => o.mul (evalExpr2 o x0 x1 p0 p1 a) (evalExpr2 o x0 x1 p0 p1 b)
  | .pow (.var 0) k => getPow o x0 p0 k
  | .pow (.var 1) k => getPow o x1 p1 k
  | .pow a k => o.pow (evalExpr2 o x0 x1 p0 p1 a) k

/-- Evaluate a 3-variable `Expr` as a univariate polynomial in variable `2` over `(x0, x1)`. -/
def evalExpr3SPoly {α : Type*} (o : PolyOps α) (x0 x1 : α) (p0 p1 : List α) : Expr → SPoly α
  | .num c => .sc (o.ofInt c)
  | .natCast n => .sc (o.ofInt (n : ℤ))
  | .intCast z => .sc (o.ofInt z)
  | .var 0 => .sc x0
  | .var 1 => .sc x1
  | .var 2 => .poly [o.zero, o.ofInt 1]
  | .var _ => .sc o.zero
  | .neg a => sNeg o (evalExpr3SPoly o x0 x1 p0 p1 a)
  | .add a b => sAdd o (evalExpr3SPoly o x0 x1 p0 p1 a) (evalExpr3SPoly o x0 x1 p0 p1 b)
  | .sub a b => sSub o (evalExpr3SPoly o x0 x1 p0 p1 a) (evalExpr3SPoly o x0 x1 p0 p1 b)
  | .mul a b =>
      match b with
      | .var 2 => sShiftK o 1 (evalExpr3SPoly o x0 x1 p0 p1 a)
      | .pow (.var 2) k => sShiftK o k (evalExpr3SPoly o x0 x1 p0 p1 a)
      | _ => sMul o (evalExpr3SPoly o x0 x1 p0 p1 a) (evalExpr3SPoly o x0 x1 p0 p1 b)
  | .pow a k =>
      match a with
      | .var 0 => .sc (getPow o x0 p0 k)
      | .var 1 => .sc (getPow o x1 p1 k)
      | .var 2 => .poly (uMonomial o k (o.ofInt 1))
      | _ => .poly (uPow o (sToU (evalExpr3SPoly o x0 x1 p0 p1 a)) k)

def evalExpr3PolyT {α : Type*} (o : PolyOps α) (x0 x1 : α) (p0 p1 : List α) (e : Expr) : UPoly α :=
  sToU (evalExpr3SPoly o x0 x1 p0 p1 e)

/-! ### Length Lemmas -/

lemma uAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (uAdd o a b).length = max a.length b.length
  | [], b => by simp [uAdd]
  | a :: as, [] => by simp [uAdd]
  | _ :: as, _ :: bs => by simp [uAdd, uAdd_len o as bs, Nat.succ_max_succ]

lemma uSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (uSub o a b).length = max a.length b.length
  | [], b => by simp [uSub, uNeg]
  | a :: as, [] => by simp [uSub]
  | _ :: as, _ :: bs => by simp [uSub, uSub_len o as bs, Nat.succ_max_succ]

lemma uSc_len {α : Type*} (o : PolyOps α) (c : α) (a : UPoly α) :
    (uSc o c a).length = a.length :=
  List.length_map _

lemma uMul_len_le {α : Type*} (o : PolyOps α) :
    ∀ a b, b ≠ [] → (uMul o a b).length ≤ a.length + b.length - 1
  | [], _, _ => by simp [uMul]
  | [_], b, hb => by
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | _ :: y :: xs, b, hb => by
      have ih := uMul_len_le o (y :: xs) b hb
      simp only [uMul, uAdd_len, uSc, uShift, List.length_map, List.length_cons] at ih ⊢
      omega

lemma ubAdd_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubAdd o a b).length = max a.length b.length
  | [], b => by simp [ubAdd]
  | a :: as, [] => by simp [ubAdd]
  | _ :: as, _ :: bs => by simp [ubAdd, ubAdd_len o as bs, Nat.succ_max_succ]

lemma ubSub_len {α : Type*} (o : PolyOps α) : ∀ a b, (ubSub o a b).length = max a.length b.length
  | [], b => by simp [ubSub, ubNeg]
  | a :: as, [] => by simp [ubSub]
  | _ :: as, _ :: bs => by simp [ubSub, ubSub_len o as bs, Nat.succ_max_succ]

lemma ubMulU_len_le {α : Type*} (o : PolyOps α) :
    ∀ u b, b ≠ [] → (ubMulU o u b).length ≤ u.length + b.length - 1
  | [], _, _ => by simp [ubMulU]
  | [_], b, hb => by
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons, List.length_nil]
      have : 1 ≤ b.length := List.length_pos_of_ne_nil hb
      omega
  | _ :: c' :: cs, b, hb => by
      have ih := ubMulU_len_le o (c' :: cs) b hb
      simp only [ubMulU, ubAdd_len, ubSc, ubShift, List.length_map, List.length_cons] at ih ⊢
      omega

lemma ubSynDiv1Rem_len {α : Type*} (o : PolyOps α) :
    ∀ a, (ubSynDiv1Rem o a).2.length = a.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: b' :: rest => by
      have ih := ubSynDiv1Rem_len o (b' :: rest)
      simp only [ubSynDiv1Rem, List.length_cons] at ih ⊢
      omega

lemma dotWGo_len {α : Type*} (o : PolyOps α) (M : ℕ) (A W : UPoly α) (shift : ℕ) :
    ∀ j k, (dotWGo o M A W shift j k).length = k
  | _, 0 => rfl
  | j, k + 1 => by simp [dotWGo, dotWGo_len o M A W shift (j + 1) k]

lemma dotW_len {α : Type*} (o : PolyOps α) (M nB : ℕ) (A W : UPoly α) (shift : ℕ) :
    (dotW o M nB A W shift).length = nB :=
  dotWGo_len o M A W shift 0 nB

lemma dotWGo_getD {α : Type*} (o : PolyOps α) (M : ℕ) (A W : UPoly α) (shift : ℕ) (d : α) :
    ∀ j k idx, idx < k → (dotWGo o M A W shift j k).getD idx d = dotWAux o W M shift (j + idx) 0 A
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | j, _ + 1, 0, _ => by simp [dotWGo]
  | j, k + 1, idx + 1, h => by
      simp only [dotWGo, List.getD_cons_succ]
      rw [dotWGo_getD o M A W shift d (j + 1) k idx (Nat.lt_of_succ_lt_succ h)]
      congr 1; omega

lemma dotW_getD {α : Type*} (o : PolyOps α) (M nB : ℕ) (A W : UPoly α) (shift : ℕ) (d : α)
    {j : ℕ} (hj : j < nB) :
    (dotW o M nB A W shift).getD j d = dotWAux o W M shift j 0 A := by
  simpa [dotW] using dotWGo_getD o M A W shift d 0 nB j hj

/-! ### Relational Lifts Across `PolyOpsRel` -/

section PolyOpsRelLifts
variable {α β : Type*} {o1 : PolyOps α} {o2 : PolyOps β} {R : α → β → Prop}

abbrev URel (R : α → β → Prop) := List.Forall₂ R
abbrev BRel (R : α → β → Prop) := List.Forall₂ (List.Forall₂ R)
abbrev UBRel (R : α → β → Prop) := List.Forall₂ (List.Forall₂ (List.Forall₂ R))

lemma uAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uAdd o1 a1 a2) (uAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (hR.rel_add ha hb) (uAdd_rel hR has hbs)

lemma uNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : URel R a b) :
    URel R (uNeg o1 a) (uNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR.rel_neg hab) ih

lemma uSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uSub o1 a1 a2) (uSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => uNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (hR.rel_sub ha hb) (uSub_rel hR has hbs)

lemma uSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : URel R a b) :
    URel R (uSc o1 c1 a) (uSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR.rel_mul hc hab) ih

lemma uShift_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : URel R a b) :
    URel R (uShift o1 a) (uShift o2 b) :=
  .cons hR.rel_zero h

lemma uTail_rel : ∀ {a b}, URel R a b → URel R (uTail a) (uTail b)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons _ h => h

lemma uMul_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, URel R a1 b1 → URel R a2 b2 → URel R (uMul o1 a1 a2) (uMul o2 b1 b2)
  | [], _, [], _, .nil, _ => .nil
  | _ :: _, _, _ :: _, _, .cons ha has, h2 =>
      uAdd_rel hR (uSc_rel hR ha h2) (uShift_rel hR (uMul_rel hR has h2))

lemma uMonomial_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ k {c1 c2}, R c1 c2 → URel R (uMonomial o1 k c1) (uMonomial o2 k c2)
  | 0, _, _, hc => .cons hc .nil
  | k + 1, _, _, hc => .cons hR.rel_zero (uMonomial_rel hR k hc)

lemma uEval_rel (hR : PolyOpsRel o1 o2 R) {t1 t2} (ht : R t1 t2) :
    ∀ {a b}, URel R a b → R (uEval o1 a t1) (uEval o2 b t2)
  | [], [], .nil => hR.rel_zero
  | _ :: _, _ :: _, .cons ha has => hR.rel_add ha (hR.rel_mul ht (uEval_rel hR ht has))

lemma uPow_rel (hR : PolyOpsRel o1 o2 R) {p1 p2} (hp : URel R p1 p2) :
    ∀ k, URel R (uPow o1 p1 k) (uPow o2 p2 k)
  | 0 => .cons (hR.rel_ofInt 1) .nil
  | k + 1 => uMul_rel hR (uPow_rel hR hp k) hp

lemma bivAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivAdd o1 a1 a2) (bivAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (uAdd_rel hR ha hb) (bivAdd_rel hR has hbs)

lemma bivNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : BRel R a b) :
    BRel R (bivNeg o1 a) (bivNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (uNeg_rel hR hab) ih

lemma bivSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivSub o1 a1 a2) (bivSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => bivNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (uSub_rel hR ha hb) (bivSub_rel hR has hbs)

lemma bivSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : BRel R a b) :
    BRel R (bivSc o1 c1 a) (bivSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (uSc_rel hR hc hab) ih

lemma bivConst_rel {c1 c2} (hc : R c1 c2) : BRel R (bivConst c1) (bivConst c2) :=
  .cons (.cons hc .nil) .nil

lemma bivMul_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, BRel R a1 b1 → BRel R a2 b2 → BRel R (bivMul o1 a1 a2) (bivMul o2 b1 b2)
  | [], _, [], _, .nil, _ => .nil
  | _ :: _, _, _ :: _, _, .cons ha has, h2 => by
      refine bivAdd_rel hR ?_ (.cons .nil (bivMul_rel hR has h2))
      clear has
      induction h2 with
      | nil => exact .nil
      | cons hb _ ih => exact .cons (uMul_rel hR ha hb) ih

lemma bivRedOnce_rel (hR : PolyOpsRel o1 o2 R)
    {s1 s2 t1 t2 n1 n2} (hs : R s1 s2) (ht : R t1 t2) (hn : R n1 n2) :
    ∀ {a b}, BRel R a b → BRel R (bivRedOnce o1 s1 t1 n1 a) (bivRedOnce o2 s2 t2 n2 b)
  | [], [], .nil => .nil
  | [_], [_], .cons h0 .nil => .cons (uSc_rel hR hs h0) .nil
  | [_, _], [_, _], .cons h0 (.cons h1 .nil) => .cons (uSc_rel hR hs h0) (.cons (uSc_rel hR hs h1) .nil)
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons h0 (.cons h1 (.cons h2 hrest)) => by
      refine bivAdd_rel hR (.cons (uSc_rel hR hs h0) (.cons (uSc_rel hR hs h1) .nil)) ?_
      have hmap : ∀ {x y}, BRel R x y →
          BRel R (x.map fun ri => uAdd o1 (uSc o1 n1 ri) (uShift o1 (uShift o1 (uSc o1 t1 ri))))
                 (y.map fun ri => uAdd o2 (uSc o2 n2 ri) (uShift o2 (uShift o2 (uSc o2 t2 ri)))) := by
        intro x y hxy; induction hxy with
        | nil => exact .nil
        | cons hxy' _ ih =>
            exact .cons (uAdd_rel hR (uSc_rel hR hn hxy') (uShift_rel hR (uShift_rel hR (uSc_rel hR ht hxy')))) ih
      exact hmap (.cons h2 hrest)

lemma ubAdd_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, UBRel R a1 b1 → UBRel R a2 b2 → UBRel R (ubAdd o1 a1 a2) (ubAdd o2 b1 b2)
  | [], _, [], _, .nil, h2 => h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (bivAdd_rel hR ha hb) (ubAdd_rel hR has hbs)

lemma ubNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : UBRel R a b) :
    UBRel R (ubNeg o1 a) (ubNeg o2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivNeg_rel hR hab) ih

lemma ubSub_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a1 a2 b1 b2}, UBRel R a1 b1 → UBRel R a2 b2 → UBRel R (ubSub o1 a1 a2) (ubSub o2 b1 b2)
  | [], _, [], _, .nil, h2 => ubNeg_rel hR h2
  | _ :: _, [], _ :: _, [], h1, .nil => h1
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons ha has, .cons hb hbs =>
      .cons (bivSub_rel hR ha hb) (ubSub_rel hR has hbs)

lemma ubSc_rel (hR : PolyOpsRel o1 o2 R) {c1 c2} (hc : R c1 c2) {a b} (h : UBRel R a b) :
    UBRel R (ubSc o1 c1 a) (ubSc o2 c2 b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivSc_rel hR hc hab) ih

lemma ubBmul_rel (hR : PolyOpsRel o1 o2 R) {b1 b2} (hb : BRel R b1 b2) {a1 a2} (ha : UBRel R a1 a2) :
    UBRel R (ubBmul o1 b1 a1) (ubBmul o2 b2 a2) := by
  induction ha with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (bivMul_rel hR hb hab) ih

lemma ubShift_rel {a b} (h : UBRel R a b) : UBRel R (ubShift a) (ubShift b) :=
  .cons .nil h

lemma ubMulU_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {u1 u2 b1 b2}, URel R u1 u2 → UBRel R b1 b2 → UBRel R (ubMulU o1 u1 b1) (ubMulU o2 u2 b2)
  | [], [], _, _, .nil, _ => .nil
  | _ :: _, _ :: _, _, _, .cons hc hcs, hb =>
      ubAdd_rel hR (ubSc_rel hR hc hb) (ubShift_rel (ubMulU_rel hR hcs hb))

lemma ubSynDiv1Rem_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {a b}, UBRel R a b →
      BRel R (ubSynDiv1Rem o1 a).1 (ubSynDiv1Rem o2 b).1 ∧
      UBRel R (ubSynDiv1Rem o1 a).2 (ubSynDiv1Rem o2 b).2
  | [], [], .nil => ⟨.nil, .nil⟩
  | [_], [_], .cons h .nil => ⟨h, .nil⟩
  | _ :: _ :: _, _ :: _ :: _, .cons h1 (.cons h2 hrest) =>
      let ih := ubSynDiv1Rem_rel hR (.cons h2 hrest)
      ⟨bivAdd_rel hR h1 ih.1, .cons ih.1 ih.2⟩

lemma list_getD_rel (hR : PolyOpsRel o1 o2 R) {l1 l2} (hl : URel R l1 l2) (k : ℕ) :
    R (l1.getD k o1.zero) (l2.getD k o2.zero) := by
  induction hl generalizing k with
  | nil => exact hR.rel_zero
  | cons hab _ ih =>
      cases k with
      | zero => exact hab
      | succ k' => exact ih k'

lemma dotWAux_rel (hR : PolyOpsRel o1 o2 R) {W1 W2} (hW : URel R W1 W2) (M shift j : ℕ) :
    ∀ i {A1 A2}, URel R A1 A2 → R (dotWAux o1 W1 M shift j i A1) (dotWAux o2 W2 M shift j i A2)
  | _, [], [], .nil => hR.rel_zero
  | i, _ :: _, _ :: _, .cons ha has => by
      dsimp only [dotWAux]
      apply hR.rel_add
      · split_ifs
        · exact hR.rel_mul ha (list_getD_rel hR hW _)
        · exact hR.rel_zero
      · exact dotWAux_rel hR hW M shift j (i + 1) has

lemma dotWGo_rel (hR : PolyOpsRel o1 o2 R) {A1 A2 W1 W2} (hA : URel R A1 A2) (hW : URel R W1 W2)
    (M shift : ℕ) :
    ∀ j k, URel R (dotWGo o1 M A1 W1 shift j k) (dotWGo o2 M A2 W2 shift j k)
  | _, 0 => .nil
  | j, k + 1 => .cons (dotWAux_rel hR hW M shift j 0 hA) (dotWGo_rel hR hA hW M shift (j + 1) k)

lemma dotW_rel (hR : PolyOpsRel o1 o2 R) {A1 A2 W1 W2} (hA : URel R A1 A2) (hW : URel R W1 W2)
    (M nB shift : ℕ) :
    URel R (dotW o1 M nB A1 W1 shift) (dotW o2 M nB A2 W2 shift) :=
  dotWGo_rel hR hA hW M shift 0 nB

lemma combineBivDot_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ {B1 B2 t1 t2}, UBRel R B1 B2 → URel R t1 t2 → BRel R (combineBivDot o1 B1 t1) (combineBivDot o2 B2 t2)
  | [], [], _, _, .nil, _ => .nil
  | _ :: _, _ :: _, [], [], _, .nil => .nil
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons hb hbs, .cons hc hcs =>
      bivAdd_rel hR (bivSc_rel hR hc hb) (combineBivDot_rel hR hbs hcs)

inductive SRel (R : α → β → Prop) : SPoly α → SPoly β → Prop
  | sc {a b} : R a b → SRel R (.sc a) (.sc b)
  | poly {a b} : URel R a b → SRel R (.poly a) (.poly b)

lemma sToU_rel {a b} (h : SRel R a b) : URel R (sToU a) (sToU b) := by
  cases h with
  | sc hab => exact .cons hab .nil
  | poly hab => exact hab

lemma sNeg_rel (hR : PolyOpsRel o1 o2 R) {a b} (h : SRel R a b) :
    SRel R (sNeg o1 a) (sNeg o2 b) := by
  cases h with
  | sc hab => exact .sc (hR.rel_neg hab)
  | poly hab => exact .poly (uNeg_rel hR hab)

lemma sAdd_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sAdd o1 a1 a2) (sAdd o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_add ha hb)
      | poly hb =>
          cases hb with
          | nil => exact .sc ha
          | cons hb0 hbs => exact .poly (.cons (hR.rel_add ha hb0) hbs)
  | poly ha =>
      cases h2 with
      | sc hb =>
          cases ha with
          | nil => exact .sc hb
          | cons ha0 has => exact .poly (.cons (hR.rel_add ha0 hb) has)
      | poly hb => exact .poly (uAdd_rel hR ha hb)

lemma sSub_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sSub o1 a1 a2) (sSub o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_sub ha hb)
      | poly hb => exact .poly (uSub_rel hR (.cons ha .nil) hb)
  | poly ha =>
      cases h2 with
      | sc hb => exact .poly (uSub_rel hR ha (.cons hb .nil))
      | poly hb => exact .poly (uSub_rel hR ha hb)

lemma sMul_rel (hR : PolyOpsRel o1 o2 R) {a1 a2 b1 b2} (h1 : SRel R a1 b1) (h2 : SRel R a2 b2) :
    SRel R (sMul o1 a1 a2) (sMul o2 b1 b2) := by
  cases h1 with
  | sc ha =>
      cases h2 with
      | sc hb => exact .sc (hR.rel_mul ha hb)
      | poly hb => exact .poly (uSc_rel hR ha hb)
  | poly ha =>
      cases h2 with
      | sc hb => exact .poly (uSc_rel hR hb ha)
      | poly hb => exact .poly (uMul_rel hR ha hb)

lemma sShiftK_rel (hR : PolyOpsRel o1 o2 R) :
    ∀ k {a b}, SRel R a b → SRel R (sShiftK o1 k a) (sShiftK o2 k b)
  | 0, _, _, h => h
  | k + 1, _, _, .sc hab => .poly (uMonomial_rel hR (k + 1) hab)
  | k + 1, _, _, .poly hab => sShiftK_rel hR k (.poly (uShift_rel hR hab))

lemma evalExpr2_rel (hR : PolyOpsRel o1 o2 R) {x0₁ x1₁ : α} {x0₂ x1₂ : β}
    (hx0 : R x0₁ x0₂) (hx1 : R x1₁ x1₂) {p0₁ p1₁ : List α} {p0₂ p1₂ : List β}
    (hp0 : URel R p0₁ p0₂) (hp1 : URel R p1₁ p1₂) :
    ∀ e : Expr, R (evalExpr2 o1 x0₁ x1₁ p0₁ p1₁ e) (evalExpr2 o2 x0₂ x1₂ p0₂ p1₂ e)
  | .num c => hR.rel_ofInt c
  | .natCast n => hR.rel_ofInt n
  | .intCast z => hR.rel_ofInt z
  | .var 0 => hx0
  | .var 1 => hx1
  | .var (_ + 2) => hR.rel_zero
  | .neg a => hR.rel_neg (evalExpr2_rel hR hx0 hx1 hp0 hp1 a)
  | .add a b => hR.rel_add (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b)
  | .sub a b => hR.rel_sub (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b)
  | .mul a b => hR.rel_mul (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b)
  | .pow (.var 0) k => getPow_rel hR hx0 hp0 k
  | .pow (.var 1) k => getPow_rel hR hx1 hp1 k
  | .pow (.var (_ + 2)) k => hR.rel_pow k hR.rel_zero
  | .pow (.num c) k => hR.rel_pow k (hR.rel_ofInt c)
  | .pow (.natCast n) k => hR.rel_pow k (hR.rel_ofInt n)
  | .pow (.intCast z) k => hR.rel_pow k (hR.rel_ofInt z)
  | .pow (.neg a) k => hR.rel_pow k (hR.rel_neg (evalExpr2_rel hR hx0 hx1 hp0 hp1 a))
  | .pow (.add a b) k => hR.rel_pow k (hR.rel_add (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b))
  | .pow (.sub a b) k => hR.rel_pow k (hR.rel_sub (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b))
  | .pow (.mul a b) k => hR.rel_pow k (hR.rel_mul (evalExpr2_rel hR hx0 hx1 hp0 hp1 a) (evalExpr2_rel hR hx0 hx1 hp0 hp1 b))
  | .pow (.pow a j) k => hR.rel_pow k (evalExpr2_rel hR hx0 hx1 hp0 hp1 (.pow a j))

lemma evalExpr3SPoly_rel (hR : PolyOpsRel o1 o2 R) {x0₁ x1₁ : α} {x0₂ x1₂ : β}
    (hx0 : R x0₁ x0₂) (hx1 : R x1₁ x1₂) {p0₁ p1₁ : List α} {p0₂ p1₂ : List β}
    (hp0 : URel R p0₁ p0₂) (hp1 : URel R p1₁ p1₂) :
    ∀ e : Expr, SRel R (evalExpr3SPoly o1 x0₁ x1₁ p0₁ p1₁ e) (evalExpr3SPoly o2 x0₂ x1₂ p0₂ p1₂ e)
  | .num c => .sc (hR.rel_ofInt c)
  | .natCast n => .sc (hR.rel_ofInt n)
  | .intCast z => .sc (hR.rel_ofInt z)
  | .var 0 => .sc hx0
  | .var 1 => .sc hx1
  | .var 2 => .poly (.cons hR.rel_zero (.cons (hR.rel_ofInt 1) .nil))
  | .var (_ + 3) => .sc hR.rel_zero
  | .neg a => sNeg_rel hR (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 a)
  | .add a b => sAdd_rel hR (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 a) (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 b)
  | .sub a b => sSub_rel hR (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 a) (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 b)
  | .mul a b => by
      have ha := evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 a
      have hb := evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 b
      dsimp only [evalExpr3SPoly]
      split
      · exact sShiftK_rel hR 1 ha
      · exact sShiftK_rel hR _ ha
      · exact sMul_rel hR ha hb
  | .pow a k => by
      have ha := evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 a
      dsimp only [evalExpr3SPoly]
      split
      · exact .sc (getPow_rel hR hx0 hp0 k)
      · exact .sc (getPow_rel hR hx1 hp1 k)
      · exact .poly (uMonomial_rel hR k (hR.rel_ofInt 1))
      · exact .poly (uPow_rel hR (sToU_rel ha) k)

lemma evalExpr3PolyT_rel (hR : PolyOpsRel o1 o2 R) {x0₁ x1₁ : α} {x0₂ x1₂ : β}
    (hx0 : R x0₁ x0₂) (hx1 : R x1₁ x1₂) {p0₁ p1₁ : List α} {p0₂ p1₂ : List β}
    (hp0 : URel R p0₁ p0₂) (hp1 : URel R p1₁ p1₂) (e : Expr) :
    URel R (evalExpr3PolyT o1 x0₁ x1₁ p0₁ p1₁ e) (evalExpr3PolyT o2 x0₂ x1₂ p0₂ p1₂ e) :=
  sToU_rel (evalExpr3SPoly_rel hR hx0 hx1 hp0 hp1 e)

end PolyOpsRelLifts

/-! ### Ring Evaluation Semantics Over Any `[CommRing R]` -/

section RingEval
variable {R : Type*} [CommRing R]

def evalUPoly : UPoly R → R[X]
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * evalUPoly as

def evalYList (y : R) : UPoly R → R
  | [] => 0
  | a :: as => a + y * evalYList y as

def evalBivL (x y : R) : BivL R → R
  | [] => 0
  | r :: rs => evalYList y r + x * evalBivL x y rs

def evalUBivL (x y : R) : UBivL R → R[X]
  | [] => 0
  | b :: bs => Polynomial.C (evalBivL x y b) + Polynomial.X * evalUBivL x y bs

lemma list_getD_of_le {α : Type*} (a : List α) (d : α) {k : ℕ} (hk : a.length ≤ k) :
    a.getD k d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl

lemma evalUPoly_uAdd : ∀ a b : UPoly R,
    evalUPoly (uAdd (ringOps R) a b) = evalUPoly a + evalUPoly b
  | [], b => by simp [uAdd, evalUPoly]
  | a :: as, [] => by simp [uAdd, evalUPoly]
  | a :: as, b :: bs => by
      simp only [uAdd, evalUPoly, evalUPoly_uAdd as bs]; dsimp only [ringOps]; simp only [map_add]; ring

lemma evalUPoly_uNeg (a : UPoly R) : evalUPoly (uNeg (ringOps R) a) = -evalUPoly a := by
  induction a with
  | nil => simp [uNeg, evalUPoly]
  | cons a as ih =>
      simp only [uNeg, List.map_cons, evalUPoly] at ih ⊢; rw [ih]; dsimp only [ringOps]; simp only [map_neg]; ring

lemma evalUPoly_uSub : ∀ a b : UPoly R,
    evalUPoly (uSub (ringOps R) a b) = evalUPoly a - evalUPoly b
  | [], b => by simp [uSub, evalUPoly, evalUPoly_uNeg]
  | a :: as, [] => by simp [uSub, evalUPoly]
  | a :: as, b :: bs => by
      simp only [uSub, evalUPoly, evalUPoly_uSub as bs]; dsimp only [ringOps]; simp only [map_sub]; ring

lemma evalUPoly_uSc (c : R) (a : UPoly R) :
    evalUPoly (uSc (ringOps R) c a) = Polynomial.C c * evalUPoly a := by
  induction a with
  | nil => simp [uSc, evalUPoly]
  | cons a as ih =>
      simp only [uSc, List.map_cons, evalUPoly] at ih ⊢; rw [ih]; dsimp only [ringOps]; simp only [map_mul]; ring

lemma evalUPoly_uShift (a : UPoly R) :
    evalUPoly (uShift (ringOps R) a) = Polynomial.X * evalUPoly a := by
  simp [uShift, evalUPoly, ringOps]

lemma evalUPoly_uMul : ∀ a b : UPoly R,
    evalUPoly (uMul (ringOps R) a b) = evalUPoly a * evalUPoly b
  | [], b => by simp [uMul, evalUPoly]
  | a :: as, b => by
      simp only [uMul, evalUPoly, evalUPoly_uAdd, evalUPoly_uSc, evalUPoly_uShift,
        evalUPoly_uMul as b]; ring

lemma evalUPoly_uTail : ∀ a : UPoly R,
    evalUPoly a = Polynomial.C (a.headD 0) + Polynomial.X * evalUPoly (uTail a)
  | [] => by simp [evalUPoly, uTail]
  | _ :: _ => by simp [evalUPoly, uTail]

lemma evalUPoly_coeff (a : UPoly R) : ∀ k, (evalUPoly a).coeff k = a.getD k 0 := by
  induction a with
  | nil => intro k; simp [evalUPoly]
  | cons x xs ih =>
      intro k; cases k with
      | zero => simp [evalUPoly]
      | succ k' => simp [evalUPoly, Polynomial.coeff_X_mul, ih k']

lemma evalUPoly_coeff_eq_zero_of_le (a : UPoly R) {k : ℕ} (hk : a.length ≤ k) :
    (evalUPoly a).coeff k = 0 := by
  rw [evalUPoly_coeff, list_getD_of_le a 0 hk]

lemma evalYList_uAdd (y : R) : ∀ a b : UPoly R,
    evalYList y (uAdd (ringOps R) a b) = evalYList y a + evalYList y b
  | [], b => by simp [uAdd, evalYList]
  | a :: as, [] => by simp [uAdd, evalYList]
  | a :: as, b :: bs => by simp only [uAdd, evalYList, evalYList_uAdd y as bs]; dsimp only [ringOps]; ring

lemma evalYList_uNeg (y : R) (a : UPoly R) :
    evalYList y (uNeg (ringOps R) a) = -evalYList y a := by
  induction a with
  | nil => simp [uNeg, evalYList]
  | cons a as ih => simp only [uNeg, List.map_cons, evalYList] at ih ⊢; rw [ih]; dsimp only [ringOps]; ring

lemma evalYList_uSub (y : R) : ∀ a b : UPoly R,
    evalYList y (uSub (ringOps R) a b) = evalYList y a - evalYList y b
  | [], b => by simp [uSub, evalYList, evalYList_uNeg]
  | a :: as, [] => by simp [uSub, evalYList]
  | a :: as, b :: bs => by simp only [uSub, evalYList, evalYList_uSub y as bs]; dsimp only [ringOps]; ring

lemma evalYList_uSc (y c : R) (a : UPoly R) :
    evalYList y (uSc (ringOps R) c a) = c * evalYList y a := by
  induction a with
  | nil => simp [uSc, evalYList]
  | cons a as ih => simp only [uSc, List.map_cons, evalYList] at ih ⊢; rw [ih]; dsimp only [ringOps]; ring

lemma evalYList_uShift (y : R) (a : UPoly R) :
    evalYList y (uShift (ringOps R) a) = y * evalYList y a := by
  simp [uShift, evalYList, ringOps]

lemma evalYList_uMul (y : R) : ∀ a b : UPoly R,
    evalYList y (uMul (ringOps R) a b) = evalYList y a * evalYList y b
  | [], b => by simp [uMul, evalYList]
  | a :: as, b => by
      simp only [uMul, evalYList, evalYList_uAdd, evalYList_uSc, evalYList_uShift,
        evalYList_uMul y as b]; ring

lemma evalBivL_bivAdd (x y : R) : ∀ a b : BivL R,
    evalBivL x y (bivAdd (ringOps R) a b) = evalBivL x y a + evalBivL x y b
  | [], b => by simp [bivAdd, evalBivL]
  | a :: as, [] => by simp [bivAdd, evalBivL]
  | a :: as, b :: bs => by
      simp only [bivAdd, evalBivL, evalYList_uAdd, evalBivL_bivAdd x y as bs]; ring

lemma evalBivL_bivNeg (x y : R) (a : BivL R) :
    evalBivL x y (bivNeg (ringOps R) a) = -evalBivL x y a := by
  induction a with
  | nil => simp [bivNeg, evalBivL]
  | cons a as ih => simp only [bivNeg, List.map_cons, evalBivL, evalYList_uNeg] at ih ⊢; rw [ih]; ring

lemma evalBivL_bivSub (x y : R) : ∀ a b : BivL R,
    evalBivL x y (bivSub (ringOps R) a b) = evalBivL x y a - evalBivL x y b
  | [], b => by simp [bivSub, evalBivL, evalBivL_bivNeg]
  | a :: as, [] => by simp [bivSub, evalBivL]
  | a :: as, b :: bs => by
      simp only [bivSub, evalBivL, evalYList_uSub, evalBivL_bivSub x y as bs]; ring

lemma evalBivL_bivSc (x y c : R) (a : BivL R) :
    evalBivL x y (bivSc (ringOps R) c a) = c * evalBivL x y a := by
  induction a with
  | nil => simp [bivSc, evalBivL]
  | cons a as ih => simp only [bivSc, List.map_cons, evalBivL, evalYList_uSc] at ih ⊢; rw [ih]; ring

lemma evalBivL_bivMul (x y : R) : ∀ a b : BivL R,
    evalBivL x y (bivMul (ringOps R) a b) = evalBivL x y a * evalBivL x y b
  | [], b => by simp [bivMul, evalBivL]
  | r :: rs, b => by
      have hmap : ∀ (l : BivL R), evalBivL x y (l.map (uMul (ringOps R) r)) = evalYList y r * evalBivL x y l := by
        intro l; induction l with
        | nil => simp [evalBivL]
        | cons z zs ih => simp only [List.map_cons, evalBivL, evalYList_uMul, ih]; ring
      simp only [bivMul, evalBivL, evalBivL_bivAdd, hmap, evalBivL_bivMul x y rs b, evalYList]; ring

lemma evalBivL_bivRedOnce {x y s t n : R} (hx2 : s * x ^ 2 = t * y ^ 2 + n) (b : BivL R) :
    evalBivL x y (bivRedOnce (ringOps R) s t n b) = s * evalBivL x y b := by
  have hrest : ∀ l : BivL R,
      evalBivL x y (l.map fun ri => uAdd (ringOps R) (uSc (ringOps R) n ri)
        (uShift (ringOps R) (uShift (ringOps R) (uSc (ringOps R) t ri)))) =
      s * (x ^ 2 * evalBivL x y l) := by
    intro l; induction l with
    | nil => simp [evalBivL]
    | cons r rs ih =>
        simp only [List.map_cons, evalBivL, evalYList_uAdd, evalYList_uSc, evalYList_uShift, ih]
        linear_combination -evalYList y r * hx2
  match b with
  | [] => simp [bivRedOnce, evalBivL]
  | [r0] => simp [bivRedOnce, evalBivL, evalYList_uSc]
  | [r0, r1] => simp only [bivRedOnce, evalBivL, evalYList_uSc]; ring
  | r0 :: r1 :: r2 :: rest =>
      simp only [bivRedOnce, evalBivL_bivAdd, evalBivL, evalYList_uSc, hrest (r2 :: rest)]
      ring

lemma evalUBivL_ubAdd (x y : R) : ∀ a b : UBivL R,
    evalUBivL x y (ubAdd (ringOps R) a b) = evalUBivL x y a + evalUBivL x y b
  | [], b => by simp [ubAdd, evalUBivL]
  | a :: as, [] => by simp [ubAdd, evalUBivL]
  | a :: as, b :: bs => by
      simp only [ubAdd, evalUBivL, evalBivL_bivAdd, map_add, evalUBivL_ubAdd x y as bs]; ring

lemma evalUBivL_ubNeg (x y : R) (a : UBivL R) :
    evalUBivL x y (ubNeg (ringOps R) a) = -evalUBivL x y a := by
  induction a with
  | nil => simp [ubNeg, evalUBivL]
  | cons a as ih =>
      simp only [ubNeg, List.map_cons, evalUBivL, evalBivL_bivNeg, map_neg] at ih ⊢; rw [ih]; ring

lemma evalUBivL_ubSub (x y : R) : ∀ a b : UBivL R,
    evalUBivL x y (ubSub (ringOps R) a b) = evalUBivL x y a - evalUBivL x y b
  | [], b => by simp [ubSub, evalUBivL, evalUBivL_ubNeg]
  | a :: as, [] => by simp [ubSub, evalUBivL]
  | a :: as, b :: bs => by
      simp only [ubSub, evalUBivL, evalBivL_bivSub, map_sub, evalUBivL_ubSub x y as bs]; ring

lemma evalUBivL_ubSc (x y c : R) (a : UBivL R) :
    evalUBivL x y (ubSc (ringOps R) c a) = Polynomial.C c * evalUBivL x y a := by
  induction a with
  | nil => simp [ubSc, evalUBivL]
  | cons a as ih =>
      simp only [ubSc, List.map_cons, evalUBivL, evalBivL_bivSc, map_mul] at ih ⊢; rw [ih]; ring

lemma evalUBivL_ubBmul (x y : R) (b0 : BivL R) (a : UBivL R) :
    evalUBivL x y (ubBmul (ringOps R) b0 a) = Polynomial.C (evalBivL x y b0) * evalUBivL x y a := by
  induction a with
  | nil => simp [ubBmul, evalUBivL]
  | cons a as ih =>
      simp only [ubBmul, List.map_cons, evalUBivL, evalBivL_bivMul, map_mul] at ih ⊢; rw [ih]; ring

lemma evalUBivL_ubShift (x y : R) (a : UBivL R) :
    evalUBivL x y (ubShift a) = Polynomial.X * evalUBivL x y a := by
  simp [ubShift, evalUBivL, evalBivL]

lemma evalUBivL_ubMulU (x y : R) : ∀ (u : UPoly R) (b : UBivL R),
    evalUBivL x y (ubMulU (ringOps R) u b) = evalUPoly u * evalUBivL x y b
  | [], b => by simp [ubMulU, evalUPoly, evalUBivL]
  | c :: cs, b => by
      simp only [ubMulU, evalUPoly, evalUBivL_ubAdd, evalUBivL_ubSc, evalUBivL_ubShift,
        evalUBivL_ubMulU x y cs b]; ring

lemma evalUBivL_ubSynDiv1Rem (x y : R) :
    ∀ a : UBivL R, evalUBivL x y a = Polynomial.C (evalBivL x y (ubSynDiv1Rem (ringOps R) a).1) +
      (Polynomial.X - 1) * evalUBivL x y (ubSynDiv1Rem (ringOps R) a).2
  | [] => by simp [ubSynDiv1Rem, evalUBivL, evalBivL]
  | [_] => by simp [ubSynDiv1Rem, evalUBivL]
  | _ :: b' :: rest => by
      have ih := evalUBivL_ubSynDiv1Rem x y (b' :: rest)
      simp only [ubSynDiv1Rem, evalUBivL, evalBivL_bivAdd, map_add] at ih ⊢
      linear_combination Polynomial.X * ih

lemma evalUBivL_coeff (x y : R) (a : UBivL R) :
    ∀ k, (evalUBivL x y a).coeff k = evalBivL x y (a.getD k []) := by
  induction a with
  | nil => intro k; simp [evalUBivL, evalBivL]
  | cons b bs ih =>
      intro k; cases k with
      | zero => simp [evalUBivL]
      | succ k' => simp [evalUBivL, Polynomial.coeff_X_mul, ih k']

lemma evalBivL_combineBivDot_uAdd (x y : R) (B : UBivL R) :
    ∀ (t1 t2 : UPoly R),
      evalBivL x y (combineBivDot (ringOps R) B (uAdd (ringOps R) t1 t2)) =
      evalBivL x y (combineBivDot (ringOps R) B t1) + evalBivL x y (combineBivDot (ringOps R) B t2) := by
  induction B with
  | nil => intro _ _; simp [combineBivDot, evalBivL]
  | cons b bs ih =>
      intro t1 t2
      cases t1 with
      | nil => simp [uAdd, combineBivDot, evalBivL]
      | cons a as => cases t2 with
        | nil => simp [uAdd, combineBivDot, evalBivL]
        | cons c cs =>
            simp only [uAdd, combineBivDot, evalBivL_bivAdd, evalBivL_bivSc, ih as cs]
            dsimp only [ringOps]; ring

lemma evalBivL_combineBivDot_uSc (x y c : R) (B : UBivL R) :
    ∀ t : UPoly R, evalBivL x y (combineBivDot (ringOps R) B (uSc (ringOps R) c t)) =
      c * evalBivL x y (combineBivDot (ringOps R) B t) := by
  induction B with
  | nil => intro _; simp [combineBivDot, evalBivL]
  | cons b bs ih =>
      intro t; cases t with
      | nil => simp [uSc, combineBivDot, evalBivL]
      | cons a as =>
          rw [show uSc (ringOps R) c (a :: as) = (ringOps R).mul c a :: uSc (ringOps R) c as from rfl]
          simp only [combineBivDot, evalBivL_bivAdd, evalBivL_bivSc, ih as]
          dsimp only [ringOps]; ring

/-- Bilinear weight-contraction identity: contracting `B(U)` against `dotW (ringOps R) M nB A W shift`
computes `∑ k : Fin M, coeff_{k+1}(X^shift * A(X) * B(X)) * W[k]`. -/
theorem evalBivL_combineBivDot_dotW (x y : R) (M nB : ℕ) (A : UPoly R) (B : UBivL R)
    (W : UPoly R) (shift : ℕ) (hBlen : B.length ≤ nB) (hdeg : A.length + B.length + shift ≤ M + 2) :
    evalBivL x y (combineBivDot (ringOps R) B (dotW (ringOps R) M nB A W shift)) =
      ∑ k : Fin M, ((Polynomial.X ^ shift * evalUPoly A * evalUBivL x y B).coeff (k.val + 1)) * W.getD k.val 0 := by
  have hdot : ∀ (j i : ℕ) (L : UPoly R),
      dotWAux (ringOps R) W M shift j i L =
        ∑ m ∈ Finset.range L.length,
          if 1 ≤ i + m + j + shift ∧ i + m + j + shift ≤ M then
            L.getD m 0 * W.getD (i + m + j + shift - 1) 0
          else 0 := by
    intro j i L; induction L generalizing i with
    | nil => simp [dotWAux, ringOps]
    | cons a as ih =>
        simp only [dotWAux, List.length_cons, Finset.sum_range_succ', ih (i + 1)]
        dsimp only [ringOps]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl; intro m _
        have heq : i + 1 + m + j + shift = i + (m + 1) + j + shift := by omega
        simp [heq]
  have hcomb : ∀ (L : UBivL R) (ts : UPoly R), L.length ≤ ts.length →
      evalBivL x y (combineBivDot (ringOps R) L ts) =
        ∑ j ∈ Finset.range L.length, ts.getD j 0 * evalBivL x y (L.getD j []) := by
    intro L; induction L with
    | nil => intro _ _; simp [combineBivDot, evalBivL]
    | cons b bs ih =>
        intro ts hle; cases ts with
        | nil => simp at hle
        | cons t ts' =>
            simp only [combineBivDot, evalBivL_bivAdd, evalBivL_bivSc, List.length_cons,
              Finset.sum_range_succ', ih ts' (by simpa using hle)]
            rw [add_comm]; simp
  rw [hcomb B (dotW (ringOps R) M nB A W shift) (by rw [dotW_len]; exact hBlen)]
  have hgetD_dot : ∀ j < B.length,
      (dotW (ringOps R) M nB A W shift).getD j 0 =
        ∑ i ∈ Finset.range A.length,
          if 1 ≤ i + j + shift ∧ i + j + shift ≤ M then
            A.getD i 0 * W.getD (i + j + shift - 1) 0
          else 0 := by
    intro j hj
    rw [dotW_getD (ringOps R) M nB A W shift 0 (lt_of_lt_of_le hj hBlen), hdot]
    simp only [zero_add]
  rw [Finset.sum_congr rfl fun j hj => by rw [hgetD_dot j (Finset.mem_range.mp hj), Finset.sum_mul]]
  rw [← Finset.sum_product']
  have hcoeff (k : Fin M) :
      (Polynomial.X ^ shift * evalUPoly A * evalUBivL x y B).coeff (k.val + 1) =
        ∑ p ∈ Finset.range B.length ×ˢ Finset.range A.length,
          if p.2 + p.1 + shift = k.val + 1 then A.getD p.2 0 * evalBivL x y (B.getD p.1 []) else 0 := by
    rw [mul_assoc, Polynomial.coeff_X_pow_mul']
    split_ifs with hsh
    · rw [Polynomial.coeff_mul]
      have hcongr : ∀ q : ℕ × ℕ, (evalUPoly A).coeff q.1 * (evalUBivL x y B).coeff q.2 =
          if q.1 < A.length ∧ q.2 < B.length then A.getD q.1 0 * evalBivL x y (B.getD q.2 []) else 0 := by
        intro q; rw [evalUPoly_coeff, evalUBivL_coeff]
        split_ifs with h
        · rfl
        · push Not at h
          by_cases h1 : q.1 < A.length
          · rw [list_getD_of_le B [] (h h1), evalBivL, mul_zero]
          · rw [list_getD_of_le A 0 (by omega), zero_mul]
      simp_rw [hcongr]
      rw [← Finset.sum_filter]
      symm; rw [← Finset.sum_filter]
      refine Finset.sum_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_antidiagonal] at hp ⊢
        exact ⟨by omega, hp.1.2, hp.1.1⟩
      · intro p1 _ p2 _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
      · intro q hq
        simp at hq
        refine ⟨(q.2, q.1), ?_, rfl⟩
        simp
        exact ⟨⟨hq.2.2, hq.2.1⟩, by omega⟩
      · intro _ _; rfl
    · symm; apply Finset.sum_eq_zero; intro p _
      have : p.2 + p.1 + shift ≠ k.val + 1 := by omega
      simp [this]
  simp_rw [hcoeff, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p hp
  simp only [Finset.mem_product, Finset.mem_range] at hp
  have hleM : p.2 + p.1 + shift ≤ M := by omega
  by_cases h0 : p.2 + p.1 + shift = 0
  · simp only [h0, show ¬(1 ≤ 0 ∧ 0 ≤ M) by omega, ↓reduceIte, zero_mul]
    symm; apply Finset.sum_eq_zero; intro k _
    simp only [show (0 : ℕ) ≠ k.val + 1 by omega, ↓reduceIte, zero_mul]
  · have hge1 : 1 ≤ p.2 + p.1 + shift := by omega
    have hk_lt : p.2 + p.1 + shift - 1 < M := by omega
    let k0 : Fin M := ⟨p.2 + p.1 + shift - 1, hk_lt⟩
    rw [if_pos ⟨hge1, hleM⟩, Finset.sum_eq_single k0]
    · simp only [k0, show p.2 + p.1 + shift - 1 + 1 = p.2 + p.1 + shift by omega, ↓reduceIte]; ring
    · intro k _ hne
      have hne' : p.2 + p.1 + shift ≠ k.val + 1 := fun h => hne (Fin.ext (by dsimp [k0]; omega))
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ k0) h

lemma uEval_uAdd (t : R) : ∀ a b : UPoly R,
    uEval (ringOps R) (uAdd (ringOps R) a b) t = uEval (ringOps R) a t + uEval (ringOps R) b t
  | [], b => by simp [uAdd, uEval, ringOps]
  | a :: as, [] => by simp [uAdd, uEval, ringOps]
  | a :: as, b :: bs => by simp only [uAdd, uEval, uEval_uAdd t as bs]; dsimp only [ringOps]; ring

lemma uEval_uNeg (t : R) (a : UPoly R) :
    uEval (ringOps R) (uNeg (ringOps R) a) t = -uEval (ringOps R) a t := by
  induction a with
  | nil => simp [uNeg, uEval, ringOps]
  | cons a as ih => simp only [uNeg, List.map_cons, uEval] at ih ⊢; rw [ih]; dsimp only [ringOps]; ring

lemma uEval_uSub (t : R) : ∀ a b : UPoly R,
    uEval (ringOps R) (uSub (ringOps R) a b) t = uEval (ringOps R) a t - uEval (ringOps R) b t
  | [], b => by simp only [uSub, uEval_uNeg, uEval]; dsimp only [ringOps]; ring
  | a :: as, [] => by simp [uSub, uEval, ringOps]
  | a :: as, b :: bs => by simp only [uSub, uEval, uEval_uSub t as bs]; dsimp only [ringOps]; ring

lemma uEval_uSc (t c : R) (a : UPoly R) :
    uEval (ringOps R) (uSc (ringOps R) c a) t = c * uEval (ringOps R) a t := by
  induction a with
  | nil => simp [uSc, uEval, ringOps]
  | cons a as ih => simp only [uSc, List.map_cons, uEval] at ih ⊢; rw [ih]; dsimp only [ringOps]; ring

lemma uEval_uShift (t : R) (a : UPoly R) :
    uEval (ringOps R) (uShift (ringOps R) a) t = t * uEval (ringOps R) a t := by
  simp [uShift, uEval, ringOps]

lemma uEval_uMul (t : R) : ∀ a b : UPoly R,
    uEval (ringOps R) (uMul (ringOps R) a b) t = uEval (ringOps R) a t * uEval (ringOps R) b t
  | [], b => by simp [uMul, uEval, ringOps]
  | a :: as, b => by
      simp only [uMul, uEval, uEval_uAdd, uEval_uSc, uEval_uShift, uEval_uMul t as b]
      dsimp only [ringOps]; ring

lemma uEval_uMonomial (t c : R) : ∀ k,
    uEval (ringOps R) (uMonomial (ringOps R) k c) t = c * t ^ k
  | 0 => by simp [uMonomial, uEval, ringOps]
  | k + 1 => by simp only [uMonomial, uEval, uEval_uMonomial t c k, pow_succ]; dsimp only [ringOps]; ring

lemma uEval_uPow (t : R) (p : UPoly R) :
    ∀ k, uEval (ringOps R) (uPow (ringOps R) p k) t = (uEval (ringOps R) p t) ^ k
  | 0 => by simp [uPow, uEval, ringOps]
  | k + 1 => by simp only [uPow, uEval_uMul, uEval_uPow t p k, pow_succ]

lemma uEval_sNeg (t : R) : ∀ a : SPoly R,
    uEval (ringOps R) (sToU (sNeg (ringOps R) a)) t = -uEval (ringOps R) (sToU a) t
  | .sc a => by simp only [sNeg, sToU, uEval]; dsimp only [ringOps]; ring
  | .poly p => by simp only [sNeg, sToU, uEval_uNeg]

lemma uEval_sAdd (t : R) : ∀ a b : SPoly R,
    uEval (ringOps R) (sToU (sAdd (ringOps R) a b)) t = uEval (ringOps R) (sToU a) t + uEval (ringOps R) (sToU b) t
  | .sc a, .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [ringOps]; ring
  | .sc a, .poly [] => by simp only [sAdd, sToU, uEval]; dsimp only [ringOps]; ring
  | .sc a, .poly (b :: bs) => by simp only [sAdd, sToU, uEval]; dsimp only [ringOps]; ring
  | .poly [], .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [ringOps]; ring
  | .poly (a :: as), .sc b => by simp only [sAdd, sToU, uEval]; dsimp only [ringOps]; ring
  | .poly p, .poly q => by simp only [sAdd, sToU, uEval_uAdd]

lemma uEval_sSub (t : R) : ∀ a b : SPoly R,
    uEval (ringOps R) (sToU (sSub (ringOps R) a b)) t = uEval (ringOps R) (sToU a) t - uEval (ringOps R) (sToU b) t
  | .sc a, .sc b => by simp only [sSub, sToU, uEval]; dsimp only [ringOps]; ring
  | .sc a, .poly p => by simp only [sSub, sToU, uEval_uSub]
  | .poly p, .sc b => by simp only [sSub, sToU, uEval_uSub]
  | .poly p, .poly q => by simp only [sSub, sToU, uEval_uSub]

lemma uEval_sMul (t : R) : ∀ a b : SPoly R,
    uEval (ringOps R) (sToU (sMul (ringOps R) a b)) t = uEval (ringOps R) (sToU a) t * uEval (ringOps R) (sToU b) t
  | .sc a, .sc b => by simp only [sMul, sToU, uEval]; dsimp only [ringOps]; ring
  | .sc a, .poly p => by simp only [sMul, sToU, uEval_uSc, uEval]; dsimp only [ringOps]; ring
  | .poly p, .sc b => by simp only [sMul, sToU, uEval_uSc, uEval]; dsimp only [ringOps]; ring
  | .poly p, .poly q => by simp only [sMul, sToU, uEval_uMul]

lemma uEval_sShiftK (t : R) : ∀ k (a : SPoly R),
    uEval (ringOps R) (sToU (sShiftK (ringOps R) k a)) t = uEval (ringOps R) (sToU a) t * t ^ k
  | 0, a => by simp only [sShiftK, pow_zero, mul_one]
  | k + 1, .sc a => by
      simp only [sShiftK, sToU, uEval_uMonomial, uEval]; dsimp only [ringOps]; rw [pow_succ]; ring
  | k + 1, .poly p => by
      change uEval (ringOps R) (sToU (sShiftK (ringOps R) k (.poly (uShift (ringOps R) p)))) t = _
      rw [uEval_sShiftK t k (.poly (uShift (ringOps R) p)), sToU, sToU, uEval_uShift, pow_succ]
      ring

end RingEval

/-- Canonical 2-variable valuation `0 ↦ X 0, 1 ↦ X 1` into `P3Z = MvPolynomial (Fin 3) ℤ`. -/
def v3P3_01 : ℕ → P3Z
  | 0 => MvPolynomial.X 0
  | 1 => MvPolynomial.X 1
  | _ => 0

/-- Canonical 3-variable valuation `0 ↦ X 0, 1 ↦ X 1, 2 ↦ X 2` into `P3Z`. -/
def v3P3_012 : ℕ → P3Z
  | 0 => MvPolynomial.X 0
  | 1 => MvPolynomial.X 1
  | 2 => MvPolynomial.X 2
  | _ => 0

lemma evalExpr2_poly3_eq (n0 n1 : ℕ) :
    ∀ e : Expr,
      evalExpr2 poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
        (powList poly3Ops (MvPolynomial.X 0) n0 (poly3Ops.ofInt 1))
        (powList poly3Ops (MvPolynomial.X 1) n1 (poly3Ops.ofInt 1)) e =
      ringEval v3P3_01 e
  | .num c => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .natCast n => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .intCast z => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .var 0 => rfl
  | .var 1 => rfl
  | .var (_ + 2) => rfl
  | .neg a => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq n0 n1 a]; rfl
  | .add a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .sub a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .mul a b => by rw [evalExpr2, ringEval, evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .pow (.var 0) k => by simp [evalExpr2, getPow_poly3_eq, ringEval, v3P3_01]
  | .pow (.var 1) k => by simp [evalExpr2, getPow_poly3_eq, ringEval, v3P3_01]
  | .pow (.var (_ + 2)) k => by simp [evalExpr2, poly3Ops, ringOps, ringEval, v3P3_01]
  | .pow (.num c) k => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .pow (.natCast n) k => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .pow (.intCast z) k => by simp [evalExpr2, poly3Ops, ringOps, ringEval]
  | .pow (.neg a) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq n0 n1 a]; rfl
  | .pow (.add a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .pow (.sub a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .pow (.mul a b) k => by simp only [evalExpr2, ringEval]; rw [evalExpr2_poly3_eq n0 n1 a, evalExpr2_poly3_eq n0 n1 b]; rfl
  | .pow (.pow a j) k => by
      have ih := evalExpr2_poly3_eq n0 n1 (.pow a j)
      change poly3Ops.pow (evalExpr2 _ _ _ _ _ (.pow a j)) k = (ringEval v3P3_01 (.pow a j)) ^ k
      rw [ih]; rfl

lemma uEval_evalExpr3SPoly_P3Z (n0 n1 : ℕ) :
    ∀ e : Expr,
      uEval poly3Ops (sToU (evalExpr3SPoly poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
        (powList poly3Ops (MvPolynomial.X 0) n0 (poly3Ops.ofInt 1))
        (powList poly3Ops (MvPolynomial.X 1) n1 (poly3Ops.ofInt 1)) e)) (MvPolynomial.X 2) =
      ringEval v3P3_012 e
  | .num c => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval]
  | .natCast n => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval]
  | .intCast z => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval]
  | .var 0 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval, v3P3_012]
  | .var 1 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval, v3P3_012]
  | .var 2 => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval, v3P3_012]
  | .var (_ + 3) => by simp [evalExpr3SPoly, sToU, uEval, poly3Ops, ringOps, ringEval, v3P3_012]
  | .neg a => by
      simp [evalExpr3SPoly, uEval_sNeg, ringEval, uEval_evalExpr3SPoly_P3Z n0 n1 a]
  | .add a b => by
      simp [evalExpr3SPoly, uEval_sAdd, ringEval,
        uEval_evalExpr3SPoly_P3Z n0 n1 a, uEval_evalExpr3SPoly_P3Z n0 n1 b]
  | .sub a b => by
      simp [evalExpr3SPoly, uEval_sSub, ringEval,
        uEval_evalExpr3SPoly_P3Z n0 n1 a, uEval_evalExpr3SPoly_P3Z n0 n1 b]
  | .mul a b => by
      have ha := uEval_evalExpr3SPoly_P3Z n0 n1 a
      have hb := uEval_evalExpr3SPoly_P3Z n0 n1 b
      dsimp only [evalExpr3SPoly, ringEval]
      split
      · simp [uEval_sShiftK, ha, ringEval, v3P3_012]
      · simp [uEval_sShiftK, ha, ringEval, v3P3_012]
      · simp [uEval_sMul, ha, hb]
  | .pow a k => by
      have ha := uEval_evalExpr3SPoly_P3Z n0 n1 a
      dsimp only [evalExpr3SPoly, ringEval]
      split
      · simp only [sToU, uEval, getPow_poly3_eq, ringEval, v3P3_012]; dsimp only [poly3Ops, ringOps]; ring
      · simp only [sToU, uEval, getPow_poly3_eq, ringEval, v3P3_012]; dsimp only [poly3Ops, ringOps]; ring
      · simp only [sToU, uEval_uMonomial, ringEval, v3P3_012]; dsimp only [poly3Ops, ringOps]; simp
      · rw [sToU, uEval_uPow, ha]

lemma uEval_evalExpr3PolyT_P3Z (n0 n1 : ℕ) (e : Expr) :
    uEval poly3Ops (evalExpr3PolyT poly3Ops (MvPolynomial.X 0) (MvPolynomial.X 1)
      (powList poly3Ops (MvPolynomial.X 0) n0 (poly3Ops.ofInt 1))
      (powList poly3Ops (MvPolynomial.X 1) n1 (poly3Ops.ofInt 1)) e) (MvPolynomial.X 2) =
    ringEval v3P3_012 e :=
  uEval_evalExpr3SPoly_P3Z n0 n1 e

end PolynomialEncoding.PolyOps


