-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27
-- name    : QAlgorithms_Papers_Independent_Dependency50_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:42:33.733699+00:00
-- url     : https://prove2.me/theorems/01c11074-fb52-4b83-9879-a1d44a8ae6f9
-- title:
--   Definitions for Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination
-- statement:
--   The objects the formalized statements of *Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination* (arXiv:1201.3731) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sgr`: Integer-valued sign, including sign zero; source PDF p. 12.
--   - `firstSign`: First nonzero sign in a finite sequence; source PDF p. 20.
--   - `rightSign`: Right sign from successive formal derivatives, starting at order zero; source PDF pp. 12, 20. The degree bound includes the final constant derivative.
--   - `LerXorGtr`: Indexed comparison view; the constructors, rather than the reversed explanatory prose, determine the Boolean indices. Source PDF p. 13.
--   - `IntBound`: A finite endpoint carries a closedness flag; infinity is interpreted according to its left/right position. Source PDF p. 14.
--   - `Interval`: Reified interval; source PDF p. 14.
--   - `intervalMem`: Semantic interval membership; source PDF pp. 14–15.
--   - `lowerFits`: Comparison of lower bounds for the sufficient inclusion test; source p. 15.
--   - `upperFits`: Comparison of upper bounds for the sufficient inclusion test; source p. 15.
--   - `subint`: Endpoint-comparison test, not a complete test for semantic inclusion of empty intervals; source PDF pp. 15–16.
--   - `PolynomialIVT`: The source's discrete real closed field interface: a discrete ordered field with a supplied witness-returning polynomial IVT, and no completeness axiom. Source PDF p. 16, Definition 2.
--   - `crossingRoot`: One root on a strict sign-changing cell, using the supplied IVT. We test both orientations so no positive-to-negative sign change is lost; source pp. 18–19.
--   - `scanCells`: Scan cells separated by derivative roots; also retain critical points that are themselves roots. Source PDF pp. 18–19.
--   - `rootsAux`: Degree-bounded derivative recursion for root isolation, with explicit zero and reversed-interval cases. Source PDF pp. 18–19.
--   - `roots`: Ordered distinct roots in the open interval, with zero-polynomial convention. The extra unit of fuel handles constants. Source PDF pp. 18–19.
--   - `rootsOn`: Exact root-list specification, excluding spurious entries; source PDF p. 18.
--   - `nextRoot`: Source PDF p. 19, including the max default and zero branch.
--   - `prevRoot`: Order-dual counterpart explicitly named on source p. 20. Arguments are the interval's left and right bounds; its left neighborhood ends at b.
--   - `neighpr`: Right neighborhood, source PDF p. 20.
--   - `neighpl`: Left neighborhood, source PDF p. 20.
--   - `monicTransform`: Inverse-free monic equation transform for positive degree; source pp. 22–23. For degree d, this is X^d + sum_(i<d) p_i l^(d-1-i) X^i.
--   - `signTransform`: Sign constraint transform under y = l*x, scaled by the even power l^(2e). Only nonnegative powers occur. Source PDF pp. 22–23.
--   - `feasible`: Root/sign feasibility, source formula (5.1), PDF p. 21.
--   - `cauchyJump`: Jump of Q/P from the truncated difference of natural root multiplicities. If the difference is negative it truncates to zero, whose parity is even; this implements the source's no-pole case. Source PDF p. 24.
--   - `cind`: Open-interval Cauchy index, using distinct denominator roots; source p. 24.
--   - `taq`: Tarski query, counting each occurrence of an arbitrary input list; source p. 25.
--   - `constraints1`: Natural sign count; source PDF pp. 25–26.
--   - `ctmat1`: Source PDF pp. 10, 26; signs [1,-1,0], query powers [1,2,0].
--   - `tvec1`: Query row vector; source PDF p. 26.
--   - `cvec1`: Sign-count row vector; source PDF p. 26.
--   - `signValue`: Sign coordinate order fixed on source PDF p. 26.
--   - `exponentValue`: Exponent coordinate order matching source PDF p. 26.
--   - `tensorMatrix`: Tensor power using product indices, including the empty product at n=0; source PDF pp. 27–28.
--   - `cvec`: Generalized sign-count row vector; source PDF p. 27.
--   - `tvec`: Generalized query row vector; source PDF p. 27.
--   - `Term`: Field terms with natural-number variable names; source PDF p. 29.
--   - `Formula`: Full source formula syntax, including named binders; source PDF pp. 29–30.
--   - `evalTerm`: Total term evaluation with zero default and total field inverse; source p. 30.
--   - `assignVar`: Update one named variable, padding omitted entries with zero; source p. 30.
--   - `holds`: Propositional interpretation, source PDF p. 30.
--   - `qfForm`: Recursive quantifier-free syntax test, source PDF p. 30.
--   - `qfEval`: Boolean interpretation on the quantifier-free fragment. Quantifiers receive an arbitrary false default; correctness is only asserted under qfForm=true. Source PDF p. 30.
--   - `PolyF`: Unnormalized formal coefficient lists are intentional: specialization may lower the degree. Source PDF pp. 29, 31–33.
--   - `evalPoly`: Horner evaluation of formal coefficients, source PDF p. 30.
--   - `polyZeroF`: Formula saying that every coefficient specializes to zero; source PDF p. 33.
--   - `ifCps`: CPS conditional, source PDF p. 33.
--   - `lcoefCps`: Complete recursive leading-coefficient CPS transform, source PDF p. 33. The tail-zero test is semantic coefficient vanishing, not syntactic equality.
--   - `testF`: Concrete direct sign test, source PDF p. 34.
--
--   (The variable-update function is named `assignVar` here; the source formalization called it `setEnv`, an identifier Prove2Me's checker rejects.)
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, https://arxiv.org/abs/1201.3731v2

import Mathlib

/-!
Statements from Cohen and Mahboubi, arXiv:1201.3731v2.
All new objects are local to this paper. The noncomputable annotation below reflects
Mathlib's polynomial representation; no executable real-algebraic encoding or QE
implementation is claimed. Root enumeration has an explicit derivative/IVT body,
not a choice of a list satisfying its desired specification.
-/

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Integer-valued sign, including sign zero; source PDF p. 12. -/
def sgr {R : Type*} [Zero R] [LinearOrder R] (x : R) : ℤ :=
  if x = 0 then 0 else if 0 < x then 1 else -1

/-- First nonzero sign in a finite sequence; source PDF p. 20. -/
def firstSign : List ℤ → ℤ
  | [] => 0
  | s :: ss => if s = 0 then firstSign ss else s

/-- Right sign from successive formal derivatives, starting at order zero;
source PDF pp. 12, 20. The degree bound includes the final constant derivative. -/
def rightSign {R : Type*} [CommRing R] [LinearOrder R]
    (p : Polynomial R) (x : R) : ℤ :=
  firstSign ((List.range (p.natDegree + 1)).map
    (fun k => sgr ((((Polynomial.derivative : Polynomial R → Polynomial R)^[k]) p).eval x)))

example : sgr (0 : ℚ) = 0 := by simp [sgr]

example : firstSign [0, 0, -1, 1] = -1 := by decide

/-- Indexed comparison view; the constructors, rather than the reversed explanatory
prose, determine the Boolean indices. Source PDF p. 13. -/
inductive LerXorGtr {R : Type*} [LE R] [LT R] (x y : R) : Bool → Bool → Prop
  | lerNotGtr (h : x ≤ y) : LerXorGtr x y true false
  | gtrNotLer (h : y < x) : LerXorGtr x y false true

/-- A finite endpoint carries a closedness flag; infinity is interpreted according
to its left/right position. Source PDF p. 14. -/
inductive IntBound (R : Type*)
  | finite (closed : Bool) (value : R)
  | infinity

/-- Reified interval; source PDF p. 14. -/
structure Interval (R : Type*) where
  lower : IntBound R
  upper : IntBound R

/-- Semantic interval membership; source PDF pp. 14–15. -/
def intervalMem {R : Type*} [LinearOrder R] (i : Interval R) (x : R) : Prop :=
  (match i.lower with
    | .infinity => True
    | .finite closed a => if closed then a ≤ x else a < x) ∧
  (match i.upper with
    | .infinity => True
    | .finite closed b => if closed then x ≤ b else x < b)

/-- Comparison of lower bounds for the sufficient inclusion test; source p. 15. -/
def lowerFits {R : Type*} [LinearOrder R] : IntBound R → IntBound R → Bool
  | _, .infinity => true
  | .infinity, .finite _ _ => false
  | .finite ic i, .finite oc o =>
      decide (o < i) || (decide (o = i) && (oc || !ic))

/-- Comparison of upper bounds for the sufficient inclusion test; source p. 15. -/
def upperFits {R : Type*} [LinearOrder R] : IntBound R → IntBound R → Bool
  | _, .infinity => true
  | .infinity, .finite _ _ => false
  | .finite ic i, .finite oc o =>
      decide (i < o) || (decide (i = o) && (oc || !ic))

/-- Endpoint-comparison test, not a complete test for semantic inclusion of empty
intervals; source PDF pp. 15–16. -/
def subint {R : Type*} [LinearOrder R] (i j : Interval R) : Bool :=
  lowerFits i.lower j.lower && upperFits i.upper j.upper

example : subint (R := ℚ) ⟨.finite true 1, .finite false 2⟩
    ⟨.finite false 0, .finite false 2⟩ = true := by decide

/-- The source's discrete real closed field interface: a discrete ordered field
with a supplied witness-returning polynomial IVT, and no completeness axiom.
Source PDF p. 16, Definition 2. -/
class PolynomialIVT (R : Type*) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] where
  root : ∀ (p : Polynomial R) (a b : R), a ≤ b → p.eval a ≤ 0 → 0 ≤ p.eval b →
    { x : R // a ≤ x ∧ x ≤ b ∧ p.eval x = 0 }

/-- One root on a strict sign-changing cell, using the supplied IVT. We test both
orientations so no positive-to-negative sign change is lost; source pp. 18–19. -/
def crossingRoot {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : List R :=
  if h : a ≤ b ∧ p.eval a < 0 ∧ 0 < p.eval b then
    [(PolynomialIVT.root p a b h.1 (le_of_lt h.2.1) (le_of_lt h.2.2)).val]
  else if h : a ≤ b ∧ (-p).eval a < 0 ∧ 0 < (-p).eval b then
    [(PolynomialIVT.root (-p) a b h.1 (le_of_lt h.2.1) (le_of_lt h.2.2)).val]
  else []

/-- Scan cells separated by derivative roots; also retain critical points that
are themselves roots. Source PDF pp. 18–19. -/
def scanCells {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) : R → List R → List R
  | _, [] => []
  | a, c :: cs => crossingRoot p a c ++
      (if p.eval c = 0 then [c] else []) ++ scanCells p c cs

/-- Degree-bounded derivative recursion for root isolation, with explicit zero
and reversed-interval cases. Source PDF pp. 18–19. -/
def rootsAux {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] : ℕ → Polynomial R → R → R → List R
  | 0, _, _, _ => []
  | n + 1, p, a, b =>
      if p = 0 ∨ b ≤ a then [] else
        (scanCells p a (rootsAux n p.derivative a b ++ [b])).filter
          (fun x => decide (a < x ∧ x < b))

/-- Ordered distinct roots in the open interval, with zero-polynomial convention.
The extra unit of fuel handles constants. Source PDF pp. 18–19. -/
def roots {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : List R :=
  rootsAux (p.natDegree + 1) p a b

/-- Exact root-list specification, excluding spurious entries; source PDF p. 18. -/
def rootsOn {R : Type*} [CommRing R] [LinearOrder R]
    (p : Polynomial R) (a b : R) (s : List R) : Prop :=
  ∀ x, x ∈ s ↔ (a < x ∧ x < b ∧ p.eval x = 0)

example {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) :
    rootsAux 0 p a b = [] := rfl

/-- Source PDF p. 19, including the max default and zero branch. -/
def nextRoot {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : R :=
  if p = 0 then a else (roots p a b).headD (max b a)

/-- Order-dual counterpart explicitly named on source p. 20. Arguments are the
interval's left and right bounds; its left neighborhood ends at b. -/
def prevRoot {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : R :=
  if p = 0 then b else (roots p a b).reverse.headD (min a b)

/-- Right neighborhood, source PDF p. 20. -/
def neighpr {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : Set R :=
  Set.Ioo a (nextRoot p a b)

/-- Left neighborhood, source PDF p. 20. -/
def neighpl {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) : Set R :=
  Set.Ioo (prevRoot p a b) b

/-- Inverse-free monic equation transform for positive degree; source pp. 22–23.
For degree d, this is X^d + sum_(i<d) p_i l^(d-1-i) X^i. -/
def monicTransform {R : Type*} [CommRing R] (p : Polynomial R) : Polynomial R :=
  X ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree,
    Polynomial.monomial i (p.coeff i * p.leadingCoeff ^ (p.natDegree - 1 - i))

/-- Sign constraint transform under y = l*x, scaled by the even power l^(2e).
Only nonnegative powers occur. Source PDF pp. 22–23. -/
def signTransform {R : Type*} [CommRing R] (l : R) (q : Polynomial R) : Polynomial R :=
  ∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.monomial i (q.coeff i * l ^ (2 * q.natDegree - i))

/-- Root/sign feasibility, source formula (5.1), PDF p. 21. -/
def feasible {R : Type*} [CommRing R] [LT R]
    (p : Polynomial R) (qs : List (Polynomial R)) : Prop :=
  ∃ x : R, p.eval x = 0 ∧ ∀ q ∈ qs, 0 < q.eval x

/-- Jump of Q/P from the truncated difference of natural root multiplicities.
If the difference is negative it truncates to zero, whose parity is even; this
implements the source's no-pole case. Source PDF p. 24. -/
def cauchyJump {R : Type*} [Field R] [LinearOrder R]
    (q p : Polynomial R) (x : R) : ℤ :=
  if q ≠ 0 ∧ Odd (Polynomial.rootMultiplicity x p - Polynomial.rootMultiplicity x q)
  then if rightSign (q * p) x < 0 then -1 else 1
  else 0

/-- Open-interval Cauchy index, using distinct denominator roots; source p. 24. -/
def cind {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (q p : Polynomial R) : ℤ :=
  ((roots p a b).map (cauchyJump q p)).sum

/-- Tarski query, counting each occurrence of an arbitrary input list; source p. 25. -/
def taq {R : Type*} [CommRing R] [LinearOrder R]
    (z : List R) (q : Polynomial R) : ℤ :=
  (z.map (fun x => sgr (q.eval x))).sum

/-- Natural sign count; source PDF pp. 25–26. -/
def constraints1 {R : Type*} [CommRing R] [LinearOrder R]
    (z : List R) (q : Polynomial R) (s : ℤ) : ℕ :=
  (z.filter (fun x => decide (sgr (q.eval x) = s))).length

example {R : Type*} [CommRing R] [LinearOrder R] (q : Polynomial R) :
    taq [] q = 0 := rfl

example {R : Type*} [CommRing R] [LinearOrder R] (q : Polynomial R) (s : ℤ) :
    constraints1 [] q s = 0 := rfl

/-- Source PDF pp. 10, 26; signs [1,-1,0], query powers [1,2,0]. -/
def ctmat1 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 1; -1, 1, 1; 0, 0, 1]

/-- Query row vector; source PDF p. 26. -/
def tvec1 {R : Type*} [CommRing R] [LinearOrder R]
    (z : List R) (q : Polynomial R) : Fin 3 → ℚ :=
  ![(taq z q : ℚ), (taq z (q ^ 2) : ℚ), (taq z 1 : ℚ)]

/-- Sign-count row vector; source PDF p. 26. -/
def cvec1 {R : Type*} [CommRing R] [LinearOrder R]
    (z : List R) (q : Polynomial R) : Fin 3 → ℚ :=
  ![(constraints1 z q 1 : ℚ), (constraints1 z q (-1) : ℚ),
    (constraints1 z q 0 : ℚ)]

example : ctmat1 1 0 = -1 := rfl

/-- Sign coordinate order fixed on source PDF p. 26. -/
def signValue (i : Fin 3) : ℤ := ![1, -1, 0] i

/-- Exponent coordinate order matching source PDF p. 26. -/
def exponentValue (i : Fin 3) : ℕ := ![1, 2, 0] i

/-- Tensor power using product indices, including the empty product at n=0;
source PDF pp. 27–28. -/
def tensorMatrix (n : ℕ) : Matrix (Fin n → Fin 3) (Fin n → Fin 3) ℚ :=
  fun s e => ∏ k, ctmat1 (s k) (e k)

/-- Generalized sign-count row vector; source PDF p. 27. -/
def cvec {R : Type*} [CommRing R] [LinearOrder R] {n : ℕ}
    (z : List R) (qs : Fin n → Polynomial R) : (Fin n → Fin 3) → ℚ :=
  fun s => ((z.filter (fun x => decide (∀ k, sgr ((qs k).eval x) = signValue (s k)))).length : ℚ)

/-- Generalized query row vector; source PDF p. 27. -/
def tvec {R : Type*} [CommRing R] [LinearOrder R] {n : ℕ}
    (z : List R) (qs : Fin n → Polynomial R) : (Fin n → Fin 3) → ℚ :=
  fun e => (taq z (∏ k, qs k ^ exponentValue (e k)) : ℚ)

example (s e : Fin 0 → Fin 3) : tensorMatrix 0 s e = 1 := by simp [tensorMatrix]

/-- Field terms with natural-number variable names; source PDF p. 29. -/
inductive Term (R : Type*)
  | var (i : ℕ)
  | const (a : R)
  | add (a b : Term R)
  | opp (a : Term R)
  | mul (a b : Term R)
  | inv (a : Term R)

/-- Full source formula syntax, including named binders; source PDF pp. 29–30. -/
inductive Formula (R : Type*)
  | bool (b : Bool)
  | equal (a b : Term R)
  | lt (a b : Term R)
  | le (a b : Term R)
  | and (a b : Formula R)
  | or (a b : Formula R)
  | implies (a b : Formula R)
  | not (a : Formula R)
  | ex (i : ℕ) (a : Formula R)
  | all (i : ℕ) (a : Formula R)

/-- Total term evaluation with zero default and total field inverse; source p. 30. -/
def evalTerm {R : Type*} [Field R] (e : List R) : Term R → R
  | .var i => e[i]?.getD 0
  | .const a => a
  | .add a b => evalTerm e a + evalTerm e b
  | .opp a => -evalTerm e a
  | .mul a b => evalTerm e a * evalTerm e b
  | .inv a => (evalTerm e a)⁻¹

/-- Update one named variable, padding omitted entries with zero; source p. 30. -/
def assignVar {R : Type*} [Zero R] : List R → ℕ → R → List R
  | [], 0, x => [x]
  | [], n + 1, x => 0 :: assignVar [] n x
  | _ :: es, 0, x => x :: es
  | a :: es, n + 1, x => a :: assignVar es n x

/-- Propositional interpretation, source PDF p. 30. -/
def holds {R : Type*} [Field R] [LinearOrder R] (e : List R) : Formula R → Prop
  | .bool b => b = true
  | .equal a b => evalTerm e a = evalTerm e b
  | .lt a b => evalTerm e a < evalTerm e b
  | .le a b => evalTerm e a ≤ evalTerm e b
  | .and a b => holds e a ∧ holds e b
  | .or a b => holds e a ∨ holds e b
  | .implies a b => holds e a → holds e b
  | .not a => ¬holds e a
  | .ex i a => ∃ x : R, holds (assignVar e i x) a
  | .all i a => ∀ x : R, holds (assignVar e i x) a

/-- Recursive quantifier-free syntax test, source PDF p. 30. -/
def qfForm {R : Type*} : Formula R → Bool
  | .bool _ | .equal _ _ | .lt _ _ | .le _ _ => true
  | .and a b | .or a b | .implies a b => qfForm a && qfForm b
  | .not a => qfForm a
  | .ex _ _ | .all _ _ => false

/-- Boolean interpretation on the quantifier-free fragment. Quantifiers receive
an arbitrary false default; correctness is only asserted under qfForm=true.
Source PDF p. 30. -/
def qfEval {R : Type*} [Field R] [LinearOrder R] (e : List R) : Formula R → Bool
  | .bool b => b
  | .equal a b => decide (evalTerm e a = evalTerm e b)
  | .lt a b => decide (evalTerm e a < evalTerm e b)
  | .le a b => decide (evalTerm e a ≤ evalTerm e b)
  | .and a b => qfEval e a && qfEval e b
  | .or a b => qfEval e a || qfEval e b
  | .implies a b => !qfEval e a || qfEval e b
  | .not a => !qfEval e a
  | .ex _ _ | .all _ _ => false

/-- Unnormalized formal coefficient lists are intentional: specialization may
lower the degree. Source PDF pp. 29, 31–33. -/
abbrev PolyF (R : Type*) := List (Term R)

/-- Horner evaluation of formal coefficients, source PDF p. 30. -/
def evalPoly {R : Type*} [Field R] (e : List R) : PolyF R → Polynomial R
  | [] => 0
  | a :: q => C (evalTerm e a) + X * evalPoly e q

/-- Formula saying that every coefficient specializes to zero; source PDF p. 33. -/
def polyZeroF {R : Type*} [Zero R] : PolyF R → Formula R
  | [] => .bool true
  | a :: q => .and (.equal a (.const 0)) (polyZeroF q)

/-- CPS conditional, source PDF p. 33. -/
def ifCps {R : Type*} (cond th el : Formula R) : Formula R :=
  .or (.and cond th) (.and (.not cond) el)

/-- Complete recursive leading-coefficient CPS transform, source PDF p. 33.
The tail-zero test is semantic coefficient vanishing, not syntactic equality. -/
def lcoefCps {R : Type*} [Zero R] : PolyF R → (Term R → Formula R) → Formula R
  | [], k => k (.const 0)
  | a :: q, k => ifCps (polyZeroF q) (k a) (lcoefCps q k)

/-- Concrete direct sign test, source PDF p. 34. -/
def testF {R : Type*} [Zero R] (p : PolyF R) : Formula R :=
  lcoefCps p (fun x => .lt (.const 0) x)

example (k : Term ℚ → Formula ℚ) : lcoefCps [] k = k (.const 0) := rfl

example : qfEval ([] : List ℚ) (.equal (.inv (.const 0)) (.const 0)) = true := by
  simp [qfEval, evalTerm]

example : qfForm (Formula.all 0 (.bool true) : Formula ℚ) = false := rfl

example : assignVar ([1, 2] : List ℚ) 0 3 = [3, 2] := rfl

example (a : ℚ) : (evalPoly [] [Term.const a]).coeff 0 = a := by
  simp [evalPoly, evalTerm]

end

end QAlgorithms.Papers.Independent.Dependency50.P27


