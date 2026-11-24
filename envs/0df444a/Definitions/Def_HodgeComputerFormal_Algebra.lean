-- Prove2me | Definitions.Def_HodgeComputerFormal_Algebra
-- name    : HodgeComputerFormal_Algebra
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:17:59.683326+00:00
-- url     : https://prove2.me/theorems/68808406-1089-472d-b36d-3af26e7a0d3b
-- title:
--   HodgeComputer formal algebra, verify bridge, and polynomial calculus
-- statement:
--   Foundational algebraic and differential calculus definitions for hypersurface residue certificates over $\mathbb{C}[X_0,\dots,X_n]$:
--
--   1. Directional derivative $\operatorname{directional}(F, N) = \sum_i (\partial_i F) N_i$, divergence $\operatorname{divergence}(N) = \sum_i \partial_i N_i$, and cleared divergence numerator $\operatorname{divergenceNumerator}(D, N) = D \operatorname{divergence}(N) - \operatorname{directional}(D, N)$, together with the equivalence bridge to `HodgeComputer.Verify` and `HodgeComputer.HasCertificate`.
--   2. Sextic-hypersurface type abbreviations (`HodgeComputer.Sextic.Poly`), chain-rule formulas for `MvPolynomial.eval₂Hom` under derivations, extension of ring derivations to fraction fields (`extendRingDerivation`), legality characterization (`legal_of_residue_ne_zero`), and the coordinate-family field divergence $\operatorname{fieldDivergence}(D, u) = \sum_i D_i(u_i)$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HodgeComputer/VerifyBridge.lean

import Definitions.Def_DiamondCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

section
/-!
# Polynomial identities for rational vector-field certificates

All identities hold over an arbitrary commutative coefficient ring and finite variable type.
They concern polynomial numerators: no fraction field or denominator hypothesis is hidden here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeTestbed

open MvPolynomial
open scoped BigOperators

variable {σ R : Type*} [Fintype σ] [CommRing R]

/-- `dP(N)`, the polynomial directional derivative of `P` along `N`. -/
def directional (P : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, pderiv i P * N i

/-- The divergence of a polynomial vector field. -/
def divergence (N : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (N i)

/-- The numerator of `div(N / D)` when cleared by `D²`. -/
def divergenceNumerator (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := D * divergence N - directional D N

/-- The numerator of `A - dF(N/D) + F div(N/D)` after clearing by `D²`. -/
def clearedDefect (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := A * D ^ 2 - D * directional F N + F * divergenceNumerator D N

/-- The two polynomial equations of a certificate, before degree/parity/legality checks. -/
structure Equations (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R)
    (C : MvPolynomial σ R) : Prop where
  e1 : directional F N = A * D
  e2 : divergenceNumerator D N = F * C

/-- The precise cleared game identity supplied by E1 and E2. -/
theorem Equations.clearedDefect_eq {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) :
    clearedDefect F A D N = F ^ 2 * C := by
  unfold clearedDefect
  rw [h.e1, h.e2]
  ring

/-- Thus the cleared defect has the required factor `F²`. -/
theorem Equations.square_dvd_clearedDefect {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) :
    F ^ 2 ∣ clearedDefect F A D N := ⟨C, h.clearedDefect_eq⟩

theorem directional_mul (P H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    directional P (fun i => H * N i) = H * directional P N := by
  unfold directional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directional_product (P H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    directional (H * P) N = P * directional H N + H * directional P N := by
  unfold directional
  simp only [pderiv_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem divergence_mul (H : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    divergence (fun i => H * N i) = directional H N + H * divergence N := by
  unfold divergence directional
  simp only [pderiv_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- Multiplying both `D` and `N` by `H` multiplies the divergence numerator by `H²`.
The derivatives of `H` cancel exactly. No regularity or nonzero assumption is needed. -/
theorem divergenceNumerator_mul (H D : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    divergenceNumerator (H * D) (fun i => H * N i) =
      H ^ 2 * divergenceNumerator D N := by
  unfold divergenceNumerator
  rw [divergence_mul, directional_mul, directional_product]
  ring

/-- Denominator scaling preserves the equations, with residual multiplier `H² C`.
Legality of the new denominator is a separate condition in `Certificate.scale`. -/
theorem Equations.scale {F A D C : MvPolynomial σ R}
    {N : σ → MvPolynomial σ R} (h : Equations F A D N C) (H : MvPolynomial σ R) :
    Equations F A (H * D) (fun i => H * N i) (H ^ 2 * C) where
  e1 := by rw [directional_mul, h.e1]; ring
  e2 := by rw [divergenceNumerator_mul, h.e2]; ring

/-- A strict certificate is the special case with residual polynomial zero. -/
theorem strict_to_equations {F A D : MvPolynomial σ R} {N : σ → MvPolynomial σ R}
    (h1 : directional F N = A * D) (h2 : divergenceNumerator D N = 0) :
    Equations F A D N 0 := ⟨h1, by simpa using h2⟩

/-- A vector field with one polynomial component. -/
def coordinateField (j : σ) (P : MvPolynomial σ R) : σ → MvPolynomial σ R :=
by
  classical
  exact fun i => if i = j then P else 0

theorem directional_coordinateField (F P : MvPolynomial σ R) (j : σ) :
    directional F (coordinateField j P) = pderiv j F * P := by
  classical
  simp [directional, coordinateField]

theorem divergence_coordinateField (P : MvPolynomial σ R) (j : σ) :
    divergence (coordinateField j P) = pderiv j P := by
  classical
  unfold divergence coordinateField
  simp only [apply_ite, map_zero]
  simp

/-- The elementary Jacobian direction has zero divergence when its component is a
variable different from the direction. This is a control construction, not an arbitrary target. -/
theorem jacobianDirection_equations (F : MvPolynomial σ R) (j k : σ) (hjk : k ≠ j) :
    Equations F (X k * pderiv j F) 1 (coordinateField j (X k)) 0 := by
  apply strict_to_equations
  · rw [directional_coordinateField]
    ring
  · simp [divergenceNumerator, divergence_coordinateField, pderiv_X_of_ne hjk,
      directional]

end HodgeTestbed

end

section
noncomputable section
namespace HodgeComputer
open MvPolynomial

theorem Homogeneous.of_isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℕ}
    (h : P.IsHomogeneous k) : Homogeneous P (k : ℤ) := by
  intro m hm
  exact_mod_cast (show m.degree = k by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm)

theorem Homogeneous.isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : 0 ≤ k) : P.IsHomogeneous k.toNat := by
  intro m hm
  have hd := h hm
  have he : m.degree = k.toNat := by omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he

theorem Homogeneous.eq_zero_of_neg {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : k < 0) : P = 0 := by
  ext m
  change P.coeff m = 0
  by_contra hm
  have hd := h hm
  omega

theorem homogeneous_zero {σ : Type*} (k : ℤ) : Homogeneous (0 : MvPolynomial σ ℂ) k := by
  intro m hm
  exact False.elim (hm rfl)

theorem Homogeneous.add {σ : Type*} {P Q : MvPolynomial σ ℂ} {k : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q k) : Homogeneous (P + Q) k := by
  by_cases hk : 0 ≤ k
  · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).add (hQ.isHomogeneous hk))
    simpa only [Int.toNat_of_nonneg hk] using h
  · rw [hP.eq_zero_of_neg (by omega), hQ.eq_zero_of_neg (by omega), zero_add]
    exact homogeneous_zero k

theorem Homogeneous.mul {σ : Type*} {P Q : MvPolynomial σ ℂ} {k l : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q l) : Homogeneous (P * Q) (k + l) := by
  by_cases hk : 0 ≤ k
  · by_cases hl : 0 ≤ l
    · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).mul (hQ.isHomogeneous hl))
      simpa only [Nat.cast_add, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl] using h
    · rw [hQ.eq_zero_of_neg (by omega), mul_zero]
      exact homogeneous_zero _
  · rw [hP.eq_zero_of_neg (by omega), zero_mul]
    exact homogeneous_zero _

theorem Homogeneous.C_mul {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (c : ℂ) : Homogeneous (C c * P) k := by
  simpa using (Homogeneous.of_isHomogeneous (isHomogeneous_C (σ := σ) c)).mul h

theorem normalized_identity {n : ℕ} {F A D Q : AmbientPoly n} {q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h1 : (q : AmbientPoly n) * HodgeTestbed.directional F N = A * D)
    (h2 : HodgeTestbed.divergenceNumerator D N = F ^ q * Q) :
    defect F A D q N = F ^ (q + 1) * Q := by
  unfold defect
  change A * D ^ 2 - (q : AmbientPoly n) * D * HodgeTestbed.directional F N +
    F * HodgeTestbed.divergenceNumerator D N = F ^ (q + 1) * Q
  rw [show (q : AmbientPoly n) * D * HodgeTestbed.directional F N = D * (A * D) by rw [← h1]; ring, h2]
  ring

end HodgeComputer

end

section
/-! Polynomial notation for the sextic constructions in projective five-space.
The general certificate contract is defined independently in `Verify`. -/

namespace HodgeComputer.Sextic

abbrev Poly := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ

end HodgeComputer.Sextic

end

section
/- Source component: PolynomialPartials -/
section
/-! Ambient polynomial partial derivatives in the integer-linear interface
used by the residue and finite-field extension lemmas. -/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial

variable {R σ : Type*} [CommRing R]

theorem pderiv_commute (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    if_neg hij, if_neg (Ne.symm hij), add_zero]
  rw [show m+Finsupp.single i 1+Finsupp.single j 1 =
    m+Finsupp.single j 1+Finsupp.single i 1 by abel]
  ring

def integerPartial (i : σ) :
    Derivation ℤ (MvPolynomial σ R) (MvPolynomial σ R) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem integerPartial_apply (i : σ) (p : MvPolynomial σ R) :
    integerPartial i p = MvPolynomial.pderiv i p := rfl

@[simp] theorem integerPartial_C (i : σ) (r : R) :
    integerPartial i (MvPolynomial.C r) = 0 := by
  simp [integerPartial]

@[simp] theorem integerPartial_X_self (i : σ) :
    integerPartial i (MvPolynomial.X i : MvPolynomial σ R) = 1 := by
  simp

@[simp] theorem integerPartial_X_of_ne (i j : σ) (h : j ≠ i) :
    integerPartial i (MvPolynomial.X j : MvPolynomial σ R) = 0 := by
  simp [h]

theorem integerPartial_commute (i j : σ) (p : MvPolynomial σ R) :
    integerPartial i (integerPartial j p) = integerPartial j (integerPartial i p) :=
  pderiv_commute i j p

theorem integerPartials_commute (i j : σ) :
    Function.Commute (integerPartial (R := R) i) (integerPartial j) :=
  integerPartial_commute i j

end HoldoutConstruction

end
end

/- Source component: PolynomialChainRule -/
section
/-!
The polynomial chain rule over a coefficient ring killed by an integer-
linear derivation. It applies to coordinates in arbitrary field extensions;
no independence of those coordinates is assumed.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

variable {R L σ : Type*} [CommRing R] [Field L] [Fintype σ] [DecidableEq σ]

theorem derivation_eval₂_chain
    (D : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r) = 0) (p : MvPolynomial σ R) :
    D (MvPolynomial.eval₂Hom φ x p) =
      ∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*D (x i) := by
  let θ := MvPolynomial.eval₂Hom φ x
  change D (θ p) = ∑ i, θ (MvPolynomial.pderiv i p)*D (x i)
  induction p using MvPolynomial.induction_on with
  | C r => simp [θ, hC]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz]
    simp only [θ, MvPolynomial.eval₂Hom_X', smul_eq_mul] at hp ⊢
    rw [hp]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval₂Hom_X',
      add_mul, Finset.sum_add_distrib]
    have hsum : (∑ i, MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i p)*
        x j*D (x i)) = x j*(∑ i, MvPolynomial.eval₂Hom φ x
          (MvPolynomial.pderiv i p)*D (x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hdelta : (∑ i, MvPolynomial.eval₂Hom φ x p *
        MvPolynomial.eval₂Hom φ x (MvPolynomial.pderiv i (MvPolynomial.X j))*D (x i)) =
      MvPolynomial.eval₂Hom φ x p*D (x j) := by
      simp [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, ite_mul]
    rw [hdelta]
    ring

end HoldoutConstruction

end
end

end

section
noncomputable section
namespace HoldoutConstruction
open scoped BigOperators

/-- Passing from a domain to its fraction field preserves the kernel of a polynomial quotient map. -/
theorem residue_fractionMap_kernel {R B K : Type*} [CommRing R] [CommRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (π : R →+* B) (f : R) (kernel : ∀ p, π p = 0 ↔ f ∣ p) (p : R) :
    ((algebraMap B K).comp π) p = 0 ↔ f ∣ p := by
  change algebraMap B K (π p) = 0 ↔ f ∣ p
  rw [← map_zero (algebraMap B K), (IsFractionRing.injective B K).eq_iff, kernel]

/-- Nonzero reduction of a denominator is the exact legality condition when `f` is irreducible. -/
theorem legal_of_residue_ne_zero {R K : Type*} [CommRing R] [Field K]
    (ρ : R →+* K) (f D : R) (irreducible : Irreducible f)
    (kernel : ∀ p, ρ p = 0 ↔ f ∣ p) (nonzero : ρ D ≠ 0) :
    D ≠ 0 ∧ IsRelPrime f D := by
  refine ⟨?_, irreducible.isRelPrime_iff_not_dvd.mpr ?_⟩
  · intro h; exact nonzero (by rw [h, map_zero])
  · exact fun h => nonzero ((kernel D).mpr h)

/-- Divergence of a vector field with respect to a finite family of derivations. -/
def fieldDivergence {K ι : Type*} [Field K] [Fintype ι]
    (D : ι → Derivation ℤ K K) (u : ι → K) : K :=
  ∑ i, D i (u i)

end HoldoutConstruction
end
end


