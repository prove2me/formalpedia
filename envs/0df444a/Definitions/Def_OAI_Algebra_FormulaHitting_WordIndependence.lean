-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence
-- name    : OAI_Algebra_FormulaHitting_WordIndependence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:03:37.37387+00:00
-- url     : https://prove2.me/theorems/ef8c766c-3f52-46fd-8349-decb35d8337e
-- title:
--   Polynomial-weighted word combinations and the differential transform on them
-- statement:
--   Let $F$ be a field of characteristic zero and $n\in\mathbb{N}$. Words are lists over $\{0,\dots,n-1\}$, and $\Phi(w)\in F[[X]]$ is the word series: $\Phi(\varepsilon)=1$ and $\Phi(iw)=\int\Phi(w)\,\frac{dX}{X+i+1}$.
--
--   1. **Polynomial word combinations.** These are finitely supported families $c=(c_w)_w$ of polynomials $c_w\in F[X]$.
--   2. **Encoding.** The additive map $c\mapsto\sum_wc_w\,\Phi(w)\in F[[X]]$.
--   3. **Stripping a letter.** $(\mathrm{strip}_ic)_w=c_{iw}$.
--   4. **Differential transform.** For $q,p_0\in F[X]$ and $Q_0,\dots,Q_{n-1}\in F[X]$,
--   $$
--   \bigl(T_{q,p_0,Q}\,c\bigr)_w=q\,\bigl(p_0\,c_w'-p_0'\,c_w\bigr)+\sum_{i=0}^{n-1}p_0\,Q_i\,c_{iw}.
--   $$
--   In particular, a single term on the empty word maps to the single term $q(p_0p'-p_0'p)$ on the empty word. A single term $p$ on $iw$ maps to the term $q(p_0p'-p_0'p)$ on $iw$ plus the term $p_0Q_ip$ on $w$. The building blocks $p\mapsto q(p_0p'-p_0'p)$ and $p\mapsto qp$ are additive maps on $F[X]$.
--   5. **Natural poles.** $-1,-2,\dots,-n$; the $i$-th is $-(i+1)$.
--   6. **Length bound.** $c$ has length bound $D$ if $c_w\neq0$ implies $|w|\le D$.
--   7. **Top support.** The set of words $w$ with $c_w\ne0$ and $|w|=D$.
--
--   Up to the factors involved, differentiating an encoded combination produces the transform. Since the transform lowers word length, induction on the top length shows that the $\Phi(w)$ are linearly independent over $F[X]$.
--
--   **Formalization Note** The type of combinations is `PolyWords F n = List (Fin n) →₀ F[X]`. The maps are `polynomialEncode`, `stripLetter`, `polynomialDifferential`, `polynomialMul` and `polynomialTransform`, all bundled as additive monoid homomorphisms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/WordIndependence.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/WordIndependence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FormulaHitting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence

namespace OAI

noncomputable section
open Polynomial PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

abbrev PolyWords (F : Type*) [Field F] (n : ℕ) := List (Fin n) →₀ F[X]

def polynomialEncode : PolyWords F n →+ PowerSeries F :=
  Finsupp.liftAddHom fun w =>
    { toFun := fun p => (p : PowerSeries F) * wordSeries w
      map_zero' := by simp
      map_add' := by intro p q; simp [add_mul] }

omit [CharZero F] in
@[simp] theorem polynomialEncode_single (w : List (Fin n)) (p : F[X]) :
    polynomialEncode (Finsupp.single w p) = (p : PowerSeries F) * wordSeries w := by
  simp [polynomialEncode]

def stripLetter (i : Fin n) : PolyWords F n →+ PolyWords F n :=
  Finsupp.comapDomain.addMonoidHom (List.cons_injective (a := i))

omit [CharZero F] in
@[simp] theorem stripLetter_apply (i : Fin n) (c : PolyWords F n) (w : List (Fin n)) :
    stripLetter i c w = c (i :: w) := rfl

omit [CharZero F] in
@[simp] theorem stripLetter_single_nil (i : Fin n) (p : F[X]) :
    stripLetter i (Finsupp.single [] p) = 0 := by
  ext w
  simp [stripLetter_apply]

omit [CharZero F] in
@[simp] theorem stripLetter_single_cons (i j : Fin n) (w : List (Fin n)) (p : F[X]) :
    stripLetter i (Finsupp.single (j :: w) p) =
      if i = j then Finsupp.single w p else 0 := by
  classical
  by_cases h : i = j
  · subst j
    ext v
    simp [stripLetter_apply, Finsupp.single_apply]
  · ext v
    simp [stripLetter_apply, h]

def polynomialDifferential (q p0 : F[X]) : F[X] →+ F[X] where
  toFun p := q * (p0 * p.derivative - p0.derivative * p)
  map_zero' := by simp
  map_add' p r := by simp [Polynomial.derivative_add]; ring

def polynomialMul (q : F[X]) : F[X] →+ F[X] where
  toFun p := q * p
  map_zero' := mul_zero q
  map_add' := mul_add q

def polynomialTransform (q p0 : F[X]) (Q : Fin n → F[X]) : PolyWords F n →+ PolyWords F n :=
  Finsupp.mapRange.addMonoidHom (polynomialDifferential q p0) +
    ∑ i, (Finsupp.mapRange.addMonoidHom (polynomialMul (p0 * Q i))).comp (stripLetter i)

omit [CharZero F] in
@[simp] theorem polynomialTransform_apply (q p0 : F[X]) (Q : Fin n → F[X])
    (c : PolyWords F n) (w : List (Fin n)) :
    polynomialTransform q p0 Q c w =
      q * (p0 * (c w).derivative - p0.derivative * c w) +
        ∑ i, (p0 * Q i) * c (i :: w) := by
  classical
  simp [polynomialTransform, polynomialDifferential, polynomialMul]

omit [CharZero F] in
@[simp] theorem polynomialTransform_single_nil (q p0 : F[X]) (Q : Fin n → F[X])
    (p : F[X]) :
    polynomialTransform q p0 Q (Finsupp.single [] p) =
      Finsupp.single [] (q * (p0 * p.derivative - p0.derivative * p)) := by
  classical
  simp [polynomialTransform, polynomialDifferential, polynomialMul]

omit [CharZero F] in
@[simp] theorem polynomialTransform_single_cons (q p0 : F[X]) (Q : Fin n → F[X])
    (i : Fin n) (w : List (Fin n)) (p : F[X]) :
    polynomialTransform q p0 Q (Finsupp.single (i :: w) p) =
      Finsupp.single (i :: w) (q * (p0 * p.derivative - p0.derivative * p)) +
        Finsupp.single w ((p0 * Q i) * p) := by
  classical
  simp [polynomialTransform, polynomialDifferential, polynomialMul, apply_ite]

def naturalPoles (i : Fin n) : F := -((i.val + 1 : ℕ) : F)

def LengthBound (D : ℕ) (c : PolyWords F n) : Prop :=
  ∀ w, c w ≠ 0 → w.length ≤ D

def topSupport (D : ℕ) (c : PolyWords F n) : Finset (List (Fin n)) :=
  c.support.filter fun w => w.length = D

omit [CharZero F] in
@[simp] theorem mem_topSupport (D : ℕ) (c : PolyWords F n) (w : List (Fin n)) :
    w ∈ topSupport D c ↔ c w ≠ 0 ∧ w.length = D := by
  simp [topSupport]

end NCHitting

end

end OAI


