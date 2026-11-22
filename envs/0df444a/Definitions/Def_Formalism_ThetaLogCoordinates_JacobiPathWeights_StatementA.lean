-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:39.026799+00:00
-- url     : https://prove2.me/theorems/3a9737f1-e9bf-4ee4-9c2e-93ef14689cc2
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/StatementA.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_LiftWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
def nthElt {n : ℕ} (J : Finset (Fin n)) (a : ℕ) : ℕ := ((J.sort (· ≤ ·)).map Fin.val).getD a n
def SemiStd {n C : ℕ} (T : Fin C → Finset (Fin n)) : Prop :=
  ∀ c c' : Fin C, c.val + 1 = c'.val → ∀ a < (T c').card, nthElt (T c) a ≤ nthElt (T c') a
def initSeg (n h : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < h
def genX (k : Type*) [CommRing k] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b => X (a, b)
def tabMinors (k : Type*) [CommRing k] {n C : ℕ} (T : Fin C → Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) k :=
  ∏ c, minorF (genX k n) (initSeg n (T c).card) (T c)
def tabDiag {n C : ℕ} (T : Fin C → Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ c, ∑ b ∈ T c, ∑ a : Fin n,
    if a.val = ((T c).filter (· < b)).card then Finsupp.single (a, b) 1 else 0
def LeadingMinors : Prop :=
  ∀ (k : Type) [CommRing k] (n C : ℕ) (T : Fin C → Finset (Fin n)),
    coeff (tabDiag T) (tabMinors k T) = 1 ∧
    (∀ e ∈ (tabMinors k T).support, e ≠ tabDiag T →
      ∃ x : Fin n × Fin n, e x < tabDiag T x ∧
        ∀ y : Fin n × Fin n, (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2)) → e y = tabDiag T y) ∧
    (∀ T' : Fin C → Finset (Fin n), SemiStd T → SemiStd T' → tabDiag T = tabDiag T' → T = T')
def LemmaA : Prop :=
  ∀ (k : Type) [Field k] (n C : ℕ),
    LinearIndependent k (fun T : {T : Fin C → Finset (Fin n) // SemiStd T} => tabMinors k T.1)
def pathWord {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ℕ → Form R n
  | 0 => oneF
  | i + 1 =>
    if colHeight (μ (i + 1)) c = colHeight (μ i) c then pathWord isVec μ c Xr i
    else stepF (isVec i == decide (1 ≤ c)) (pathWord isVec μ c Xr i) (Xr i)
def canIdx {n : ℕ} (μN : Fin n → ℤ) (c : ℤ) : Finset (Fin n) :=
  if 1 ≤ c then univ.filter fun m => m.val < colHeight μN c
  else univ.filter fun m => colHeight μN c ≤ m.val
def psiPath (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (I : ℤ → Finset (Fin n)) : MvPolynomial (ℕ × Fin n) R :=
  ∏ᶠ c : ℤ, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)
def IsIndex {n : ℕ} (μN : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  ∀ c : ℤ, (I c).card = if 1 ≤ c then colHeight μN c else n - colHeight μN c
def PathWordIsColWord : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ) (c : ℤ), IsPath n isVec B μ N →
    ∃ (L : ℕ) (lt : ℕ → ℕ), StrictMono lt ∧ (∀ l < L, lt l < N) ∧
      (∀ i < N, colHeight (μ (i + 1)) c ≠ colHeight (μ i) c ↔ ∃ l < L, lt l = i) ∧
      (∀ l ≤ L, 0 ≤ colDeg (decide (1 ≤ c)) isVec lt l ∧ colDeg (decide (1 ≤ c)) isVec lt l ≤ (n : ℤ)) ∧
      (∀ l < L, colDeg (decide (1 ≤ c)) isVec lt l =
        if 1 ≤ c then (colHeight (μ (lt l)) c : ℤ) else (n : ℤ) - colHeight (μ (lt l)) c) ∧
      (colDeg (decide (1 ≤ c)) isVec lt L =
        if 1 ≤ c then (colHeight (μ N) c : ℤ) else (n : ℤ) - colHeight (μ N) c) ∧
      ∀ (R : Type) [CommRing R] (Xr : ℕ → Fin n → R),
        pathWord isVec μ c Xr N = colWord (decide (1 ≤ c)) isVec lt Xr L
def PsiDegrees : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)).Finite ∧
    ∀ i : ℕ, IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (psiPath R isVec μ N I) (if i < N then B i else 0)
def expE (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (a b : Fin n) :
    MvPolynomial (ℕ × Fin n) R →ₐ[R] Polynomial (MvPolynomial (ℕ × Fin n) R) :=
  aeval fun x =>
    if isVec x.1 then
      (if x.2 = b then Polynomial.C (X x) + Polynomial.X * Polynomial.C (X (x.1, a)) else Polynomial.C (X x))
    else
      (if x.2 = a then Polynomial.C (X x) - Polynomial.X * Polynomial.C (X (x.1, b)) else Polynomial.C (X x))
def LemmaA1hw : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ N →
    (∀ m : Fin n, IsWeightedHomogeneous
      (fun x : ℕ × Fin n => if x.2 = m then (if isVec x.1 then (1 : ℤ) else -1) else 0)
      (psiPath R isVec μ N (canIdx (μ N))) (μ N m)) ∧
    ∀ a b : Fin n, a < b →
      expE R isVec a b (psiPath R isVec μ N (canIdx (μ N))) =
        Polynomial.C (psiPath R isVec μ N (canIdx (μ N)))
def PathProductLinearIndependent : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (ν : Fin n → ℤ),
    LinearIndependent k
      (fun P : {μ : ℕ → Fin n → ℤ // IsPath n isVec B μ N ∧ μ N = ν ∧ ∀ i, N < i → μ i = 0} =>
        psiPath k isVec P.1 N (canIdx ν))
def LemmaA1lead : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ),
    IsPath n isVec B μ (N + 1) →
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ e : ℕ × Fin n →₀ ℕ, (∀ x ∈ e.support, x.1 < N) →
        coeff (e + ∑ m : Fin n, Finsupp.single (N, m) (|μ (N + 1) m - μ N m|).toNat)
            (psiPath R isVec μ (N + 1) (canIdx (μ (N + 1)))) =
          (ε : R) * coeff e (psiPath R isVec μ N (canIdx (μ N)))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


