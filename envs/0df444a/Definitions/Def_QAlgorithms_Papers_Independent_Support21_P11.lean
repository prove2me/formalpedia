-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11
-- name    : QAlgorithms_Papers_Independent_Support21_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:56:21.75709+00:00
-- url     : https://prove2.me/theorems/918ae3d0-88ff-47d3-b7fc-5c6b2d48f244
-- title:
--   Definitions for Admissibility Conditions for Degenerate Cyclotomic BMW Algebras
-- statement:
--   The objects the formalized statements of *Admissibility Conditions for Degenerate Cyclotomic BMW Algebras* (arXiv:0905.4253) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `parameterPolynomial`: The monic polynomial product (z-u_i), PDF p.3, preceding (2.4).
--   - `signedCoeff`: Signed elementary symmetric coefficient a_j, PDF p.3.
--   - `CyclotomicRecurrence`: The monic cyclotomic recurrence (2.4), PDF p.3.
--   - `WeaklyAdmissible`: Weak admissibility, Definition 2.5 and Corollary 2.4, PDF p.3.
--   - `triangularRhs`: Right side of the triangular relations (4.1), PDF p.6.
--   - `TriangularRelations`: All triangular relations (4.1); j<r guards the natural subtraction, PDF p.6.
--   - `BMWAdmissible`: This paper's admissibility, Definition 4.2, PDF p.6 (not [3]'s terminology).
--   - `schurQList`: Coefficients of the product of (1+ut)/(1-ut), PDF p.5. For one factor its positive coefficients are 2u^b; convolution adds factors. The recursion is on the list, so this is a finite coefficient formula.
--   - `schurQ`: Schur q-function evaluated at the ordered parameter list, PDF p.5.
--   - `schurEta`: The polynomial expression eta_a, (3.5)--(3.7), PDF p.5. The inverse of 2 is used only under IsUnit (2:R) or in characteristic !=2 fields.
--   - `UAdmissible`: u-admissibility, Definition 3.4, PDF p.5; used only when 2 is invertible.
--   - `weightGamma`: Rational weights gamma_i, equation (3.1), PDF p.4. Theorems use distinct parameters or independent variables, so no denominator vanishes.
--   - `idealFamily`: The indexed r-vector family in W e_1, PDF pp.4,6,8.
--   - `algebraFamily`: The three indexed monomial types of Lemma 3.1(2), PDF p.4. The index type has cardinality 3r^2, retaining repeated vectors.
--   - `leftIdeal`: The actual left ideal W e_1, using the accepted image span, PDF p.4.
--   - `NonzeroCorner`: The nonzero-corner condition in Theorem 3.2, PDF p.4.
--   - `HasCyclicModule`: The r-dimensional cyclic module in Theorem 3.2(3), PDF p.4. A unital algebra action on F^r is arbitrary; faithfulness is not assumed.
--   - `universalHStep`: One step of the explicit integer-polynomial recursion in Lemma 4.4, PDF p.7. First solve (4.1) in reverse j order; thereafter solve the monic recurrence. The r=0 fallback is unused by all source theorems.
--   - `universalH`: The universal integer polynomials H_a constructed in Lemma 4.4, PDF p.7. Primitive recursion fills entry k at step k+1, using only earlier entries. The family is defined before and independently of any evaluation ring or omega.
--   - `evalH`: Evaluation of the constructed integer polynomial in any ground ring, PDF p.7.
--   - `IsGeneratorReversal`: R-linear generator-fixing anti-automorphism of order two, PDF p.2. Involutivity supplies bijectivity; multiplication order is reversed.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, https://arxiv.org/abs/0905.4253v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

/-!
Goodman, Admissibility Conditions for Degenerate Cyclotomic BMW Algebras,
arXiv:0905.4253v2. Generator indices in the accepted presentation are zero based.
The paper's W_{2,r} always has two strands and cyclotomic degree r.
New definitions below belong only to this paper. No injectivity of tower maps,
cellular structure, or framework axioms of another paper are asserted here.
-/

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- The monic polynomial product (z-u_i), PDF p.3, preceding (2.4). -/
def parameterPolynomial {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) :
    Polynomial R := ∏ i : Fin r, (Polynomial.X - Polynomial.C (u i))

/-- Signed elementary symmetric coefficient a_j, PDF p.3. -/
def signedCoeff {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (j : ℕ) : R :=
  (parameterPolynomial u).coeff j

/-- The monic cyclotomic recurrence (2.4), PDF p.3. -/
def CyclotomicRecurrence {R : Type*} [CommRing R] {r : ℕ}
    (omega : ℕ → R) (u : Fin r → R) : Prop :=
  ∀ a : ℕ, ∑ j ∈ Finset.range (r + 1), signedCoeff u j * omega (j + a) = 0

/-- Weak admissibility, Definition 2.5 and Corollary 2.4, PDF p.3. -/
def WeaklyAdmissible {R : Type*} [CommRing R] {r : ℕ}
    (omega : ℕ → R) (u : Fin r → R) : Prop :=
  (∀ a : ℕ, 1 ≤ a → Odd a →
    2 * omega a = (∑ b ∈ Finset.Icc 1 a,
      (-1 : R) ^ (b - 1) * omega (b - 1) * omega (a - b)) - omega (a - 1)) ∧
  CyclotomicRecurrence omega u

/-- Right side of the triangular relations (4.1), PDF p.6. -/
def triangularRhs {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (j : ℕ) : R :=
  (if Odd (r - j) then (-2 : R) * signedCoeff u j else 0) +
    (if Even j then signedCoeff u (j + 1) else 0)

/-- All triangular relations (4.1); j<r guards the natural subtraction, PDF p.6. -/
def TriangularRelations {R : Type*} [CommRing R] {r : ℕ}
    (omega : ℕ → R) (u : Fin r → R) : Prop :=
  ∀ j : ℕ, j < r →
    ∑ mu ∈ Finset.range (r - j), omega mu * signedCoeff u (mu + j + 1) =
      triangularRhs u j

/-- This paper's admissibility, Definition 4.2, PDF p.6 (not [3]'s terminology). -/
def BMWAdmissible {R : Type*} [CommRing R] {r : ℕ}
    (omega : ℕ → R) (u : Fin r → R) : Prop :=
  TriangularRelations omega u ∧ CyclotomicRecurrence omega u

/-- Coefficients of the product of (1+ut)/(1-ut), PDF p.5.
For one factor its positive coefficients are 2u^b; convolution adds factors.
The recursion is on the list, so this is a finite coefficient formula. -/
def schurQList {R : Type*} [CommRing R] : List R → ℕ → R
  | [], a => if a = 0 then 1 else 0
  | u :: us, a => schurQList us a +
      ∑ b ∈ Finset.Icc 1 a, (2 * u ^ b) * schurQList us (a - b)

/-- Schur q-function evaluated at the ordered parameter list, PDF p.5. -/
def schurQ {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (a : ℕ) : R :=
  schurQList (List.ofFn u) a

/-- The polynomial expression eta_a, (3.5)--(3.7), PDF p.5.
The inverse of 2 is used only under IsUnit (2:R) or in characteristic !=2 fields. -/
def schurEta {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (a : ℕ) : R :=
  schurQ u (a + 1) - Ring.inverse (2 : R) * (-1 : R) ^ r * schurQ u a +
    (if a = 0 then Ring.inverse (2 : R) else 0)

/-- u-admissibility, Definition 3.4, PDF p.5; used only when 2 is invertible. -/
def UAdmissible {R : Type*} [CommRing R] {r : ℕ}
    (omega : ℕ → R) (u : Fin r → R) : Prop := ∀ a : ℕ, omega a = schurEta u a

/-- Rational weights gamma_i, equation (3.1), PDF p.4.
Theorems use distinct parameters or independent variables, so no denominator vanishes. -/
def weightGamma {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (i : Fin r) : F :=
  (2 * u i - (-1 : F) ^ r) *
    ∏ j ∈ Finset.univ.erase i, (u i + u j) / (u i - u j)

/-- The indexed r-vector family in W e_1, PDF pp.4,6,8. -/
def idealFamily (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (a : Fin r) : CyclotomicBMW R omega 2 r u :=
  cyclotomicX R omega 2 r u 0 ^ a.val * cyclotomicE R omega 2 r u 0

/-- The three indexed monomial types of Lemma 3.1(2), PDF p.4.
The index type has cardinality 3r^2, retaining repeated vectors. -/
def algebraFamily (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (t : Fin 3 × Fin r × Fin r) :
    CyclotomicBMW R omega 2 r u :=
  if t.1.val = 0 then
    cyclotomicX R omega 2 r u 0 ^ t.2.1.val * cyclotomicE R omega 2 r u 0 *
      cyclotomicX R omega 2 r u 0 ^ t.2.2.val
  else if t.1.val = 1 then
    cyclotomicX R omega 2 r u 0 ^ t.2.1.val *
      cyclotomicX R omega 2 r u 1 ^ t.2.2.val * cyclotomicS R omega 2 r u 0
  else
    cyclotomicX R omega 2 r u 0 ^ t.2.1.val *
      cyclotomicX R omega 2 r u 1 ^ t.2.2.val

/-- The actual left ideal W e_1, using the accepted image span, PDF p.4. -/
def leftIdeal (R : Type*) [CommRing R] (omega : ℕ → R) (r : ℕ) (u : Fin r → R) :
    Submodule R (CyclotomicBMW R omega 2 r u) :=
  rightProductSpan R Set.univ (cyclotomicE R omega 2 r u 0)

/-- The nonzero-corner condition in Theorem 3.2, PDF p.4. -/
def NonzeroCorner (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) : Prop :=
  cornerSpan R Set.univ (cyclotomicE R omega 2 r u 0) ≠ ⊥

/-- The r-dimensional cyclic module in Theorem 3.2(3), PDF p.4.
A unital algebra action on F^r is arbitrary; faithfulness is not assumed. -/
def HasCyclicModule (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) : Prop :=
  ∃ rho : CyclotomicBMW F omega 2 r u →ₐ[F] Module.End F (Fin r → F),
    ∃ v : Fin r → F, ∃ b : Module.Basis (Fin r) F (Fin r → F),
      (∀ i : Fin r, b i = (rho (cyclotomicX F omega 2 r u 0) ^ i.val) v) ∧
      LinearMap.range (rho (cyclotomicE F omega 2 r u 0)) = Submodule.span F {v}

/-- One step of the explicit integer-polynomial recursion in Lemma 4.4, PDF p.7.
First solve (4.1) in reverse j order; thereafter solve the monic recurrence.
The r=0 fallback is unused by all source theorems. -/
def universalHStep (r : ℕ) (previous : ℕ → MvPolynomial (Fin r) ℤ) (k : ℕ) :
    MvPolynomial (Fin r) ℤ :=
  let u : Fin r → MvPolynomial (Fin r) ℤ := fun i => MvPolynomial.X i
  if k < r then
    let j := r - 1 - k
    triangularRhs u j - ∑ mu ∈ Finset.range k, previous mu * signedCoeff u (mu + j + 1)
  else if 0 < r then
    - ∑ j ∈ Finset.range r, signedCoeff u j * previous (j + (k - r))
  else 0

/-- The universal integer polynomials H_a constructed in Lemma 4.4, PDF p.7.
Primitive recursion fills entry k at step k+1, using only earlier entries.
The family is defined before and independently of any evaluation ring or omega. -/
def universalH (r a : ℕ) : MvPolynomial (Fin r) ℤ :=
  (Nat.rec (motive := fun _ : ℕ => ℕ → MvPolynomial (Fin r) ℤ)
    (fun _ : ℕ => (0 : MvPolynomial (Fin r) ℤ))
    (fun k previous => Function.update previous k (universalHStep r previous k)) (a + 1)) a

/-- Evaluation of the constructed integer polynomial in any ground ring, PDF p.7. -/
def evalH {R : Type*} [CommRing R] {r : ℕ} (u : Fin r → R) (a : ℕ) : R :=
  MvPolynomial.eval₂ (Int.castRingHom R) u (universalH r a)

/-- R-linear generator-fixing anti-automorphism of order two, PDF p.2.
Involutivity supplies bijectivity; multiplication order is reversed. -/
def IsGeneratorReversal {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (n : ℕ) (s e x : ℕ → A) (star : A →ₗ[R] A) : Prop :=
  Function.Involutive star ∧ star 1 = 1 ∧
  (∀ a b : A, star (a * b) = star b * star a) ∧
  (∀ i : ℕ, i + 1 < n → star (s i) = s i ∧ star (e i) = e i) ∧
  (∀ j : ℕ, j < n → star (x j) = x j)

/-- A one-parameter q-series has constant coefficient 1, including u=0. -/
example {R : Type*} [CommRing R] (u : R) : schurQList [u] 0 = 1 := by
  simp [schurQList]

/-- The primitive recursion begins with exactly the first triangular equation. -/
example (r : ℕ) : universalH r 0 = universalHStep r (fun _ => 0) 0 := by
  simp [universalH]

/-- The first indexed ideal vector is e_1, for every positive degree. -/
example (R : Type*) [CommRing R] (omega : ℕ → R) (r : ℕ)
    (u : Fin r → R) (hr : 0 < r) :
    idealFamily R omega r u ⟨0, hr⟩ = cyclotomicE R omega 2 r u 0 := by
  simp [idealFamily]

end QAlgorithms.Papers.Independent.Support21.P11


