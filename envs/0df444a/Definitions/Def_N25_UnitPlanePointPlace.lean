-- Prove2me | Definitions.Def_N25_UnitPlanePointPlace
-- name    : N25_UnitPlanePointPlace
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:50.263098+00:00
-- url     : https://prove2.me/theorems/3799f418-fd1e-4f13-9b70-eb9579a9f71c
-- title:
--   Rational unit-plane points as places of two function fields
-- statement:
--   For $u,v∈ℚ$ with $R(u,v)=0$ and $u≠0$, the file packages the branch-factor, derivative, and discrete-valuation certificates needed to define a place $P_{u,v}$ of the unit-plane function field. It then transports $P_{u,v}$ through the proved birational field equivalence to a place of the canonical function field. These constructions turn rational affine points into degree-one places on both models.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_AdjoinRoot_LocalDVRAtRationalPoint
import Definitions.Def_N25_PlaneBranchPolynomial
import Definitions.Def_N25_UnitPlaneDerivative
import Definitions.Def_N25_UnitPlaneRationalPoint
import Definitions.Def_N25_UnitPlaneDomain
import Definitions.Def_N25_CanonicalFunctionField
import Definitions.Def_AlgebraicCurve_DiscreteValuationRingPlace
import Definitions.Def_AlgebraicCurve_PlaceAlgEquiv
/-! Places of the unit-plane function field at rational points with nonzero first coordinate.

The local ring at such a point is a discrete valuation ring: the vertical derivative does not vanish there, by a
Euclidean certificate together with the absence of rational roots of the branch factor. These proofs are carried
here because the place is defined from that discrete valuation ring. -/

/-! ### The branch factor has no rational roots -/
noncomputable section

/-! The branch factor has no rational roots, by parity and a modulo-eight obstruction. -/
namespace N25
open Polynomial

private theorem branch_form_ne_zero (n d : ℤ) (hd : Odd d) : planeBranchForm n d ≠ 0 := by
  intro h
  have hn : Even n := by
    rcases Int.even_or_odd n with he | ho
    · exact he
    · obtain ⟨a, ha⟩ := ho
      obtain ⟨b, hb⟩ := hd
      have hn2 : (n : ZMod 2) = 1 := by rw [ha]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; simp
      have hd2 : (d : ZMod 2) = 1 := by rw [hb]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; simp
      have h2 := congrArg (Int.castRingHom (ZMod 2)) h
      norm_num [planeBranchForm, hn2, hd2] at h2
      exact False.elim ((by decide : (643 : ZMod 2) ≠ 0) h2)
  let j : ℤ := 27*n^8-14*n^7*d+221*n^6*d^2+64*n^5*d^3+275*n^4*d^4+
    4*n^3*d^5+25*n^2*d^6+26*n*d^7+19*d^8
  have heq : planeBranchForm n d = n^3*j-8*n*d^10+4*d^11 := by
    dsimp [planeBranchForm,j]
    ring
  rw [heq] at h
  obtain ⟨a, ha⟩ := hn
  rw [ha] at h
  have h4 : 4*(2*a^3*j-4*a*d^10+d^11) = 0 := by linear_combination h
  have hp := (mul_eq_zero.mp h4).resolve_left (by norm_num : (4 : ℤ) ≠ 0)
  have heven : Even (d^11) := by
    refine ⟨-a^3*j+2*a*d^10, ?_⟩
    linear_combination hp
  exact (Int.not_even_iff_odd.mpr hd.pow) heven

/-- The discriminant's degree-eleven factor has no rational root. -/
theorem planeBranchValue_ne_zero (t : ℚ) : planeBranchValue t ≠ 0 := by
  intro ht
  have he : Polynomial.aeval t planeBranchIntPolynomial = 0 := by
    norm_num [planeBranchIntPolynomial, planeBranchValue, Polynomial.aeval_def]
    exact ht
  have hdeg : planeBranchIntPolynomial.natDegree = 11 := by
    unfold planeBranchIntPolynomial planeBranchValue
    compute_degree <;> norm_num
  have hl : planeBranchIntPolynomial.leadingCoeff = 27 := by
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [planeBranchIntPolynomial, planeBranchValue, Polynomial.coeff_mul, Polynomial.coeff_X]
  let n := IsFractionRing.num ℤ t
  let d : ℤ := IsFractionRing.den ℤ t
  have hdiv : d ∣ 27 := by
    simpa only [hl] using den_dvd_of_is_root he
  have hd : Odd d := by
    rcases Int.even_or_odd d with hEven | hOdd
    · obtain ⟨a, ha⟩ := hdiv
      have hEven27 : Even (27 : ℤ) := by rw [ha]; exact hEven.mul_right a
      norm_num at hEven27
    · exact hOdd
  have hd0 : (d : ℚ) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (IsFractionRing.den ℤ t).property
  have hf : planeBranchValue ((n : ℚ)/(d : ℚ)) = 0 := by
    rw [show (n : ℚ)/(d : ℚ) = t from IsFractionRing.mk'_num_den' ℤ t]
    exact ht
  have hq : planeBranchForm (n : ℚ) (d : ℚ) = 0 := by
    unfold planeBranchValue at hf
    field_simp [hd0] at hf
    unfold planeBranchForm
    linear_combination hf
  have hz : planeBranchForm n d = 0 := by
    dsimp [planeBranchForm] at hq ⊢
    exact_mod_cast hq
  exact branch_form_ne_zero n d hd hz

/-- The cubic branch factor has no rational root. -/
theorem planeCubicBranch_ne_zero (t : ℚ) : t^3+t^2+2*t+1 ≠ 0 := by
  intro ht
  let p : Polynomial ℤ := X^3+X^2+2*X+1
  have hp : p.Monic := by
    dsimp [p]
    monicity
    all_goals norm_num
  have he : Polynomial.aeval t p = 0 := by
    norm_num [p, Polynomial.aeval_def]
    exact ht
  obtain ⟨n, hn, hndvd⟩ := exists_integer_of_is_root_of_monic hp he
  have hu : IsUnit n := isUnit_of_dvd_one (by simpa [p] using hndvd)
  rcases Int.isUnit_iff.mp hu with h | h
  · have ht1 : t = 1 := by simpa [h] using hn
    norm_num [ht1] at ht
  · have htm1 : t = -1 := by simpa [h] using hn
    norm_num [htm1] at ht

end N25

end

/-! ### Nonvanishing of the vertical derivative -/
noncomputable section

/-! A polynomial Euclidean certificate excludes vertical ramification away from the branch factors. -/
namespace N25

/-- The explicit Bezout identity, checked integrally over every commutative ring. -/
theorem planeDerivative_bezout {k : Type*} [CommRing k] (u v : k) :
    planeDerivativeBezoutLeft u v * planeRelation u v +
      planeDerivativeBezoutRight u v * planeDerivativeV u v =
      u^6*(planeCubicBranchValue u)^2*planeBranchValue u := by
  unfold planeDerivativeBezoutLeft planeDerivativeBezoutRight planeRelation
    planeDerivativeV planeCubicBranchValue planeBranchValue
  ring

/-- A point off the three explicit branch factors has nonzero second partial derivative. -/
theorem planeDerivativeV_ne_zero_of_relation {k : Type*} [CommRing k] [IsDomain k]
    (u v : k) (hr : planeRelation u v = 0) (hu : u ≠ 0)
    (hc : planeCubicBranchValue u ≠ 0) (hp : planeBranchValue u ≠ 0) :
    planeDerivativeV u v ≠ 0 := by
  intro hd
  have h := planeDerivative_bezout u v
  rw [hr,hd,mul_zero,mul_zero,zero_add] at h
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 hu) (pow_ne_zero 2 hc)) hp) h.symm

/-- The explicit partial derivative is the actual derivative in the second polynomial variable. -/
theorem planeRelation_derivative_polynomial {k : Type*} [CommRing k] (u : k) :
    (planeRelation (Polynomial.C u) Polynomial.X).derivative =
      planeDerivativeV (Polynomial.C u) Polynomial.X := by
  simp [planeRelation,planeDerivativeV,Polynomial.derivative_mul,Polynomial.derivative_pow]
  simp only [map_ofNat]
  ring

/-- Evaluating the polynomial derivative gives the explicit second partial derivative. -/
theorem planeRelation_derivative_eval {k : Type*} [CommRing k] (u v : k) :
    Polynomial.eval v ((planeRelation (Polynomial.C u) Polynomial.X).derivative) =
      planeDerivativeV u v := by
  rw [planeRelation_derivative_polynomial]
  simp [planeDerivativeV]

/-- Every rational plane point with nonzero first coordinate has nonzero second partial derivative. -/
theorem planeDerivativeV_ne_zero_rat (u v : ℚ) (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    planeDerivativeV u v ≠ 0 :=
  planeDerivativeV_ne_zero_of_relation u v hr hu
    (by simpa only [planeCubicBranchValue] using planeCubicBranch_ne_zero u)
    (planeBranchValue_ne_zero u)

/-- The actual second-variable polynomial derivative is nonzero at these rational points. -/
theorem planeRelation_derivative_eval_ne_zero_rat (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    Polynomial.eval v ((planeRelation (Polynomial.C u) Polynomial.X).derivative) ≠ 0 := by
  rw [planeRelation_derivative_eval]
  exact planeDerivativeV_ne_zero_rat u v hr hu

end N25

end

/-! ### The local ring at a rational plane point -/
noncomputable section

namespace N25

/-- Evaluating the derivative in the actual coordinate ring agrees with the
explicit second partial derivative of the plane equation. -/
theorem unitPlaneEvaluation25_derivative (u v : ℚ) (hr : planeRelation u v = 0) :
    unitPlaneEvaluation25 u v hr
      (AdjoinRoot.mk unitPlanePolynomial unitPlanePolynomial.derivative) =
      planeDerivativeV u v := by
  rw [unitPlaneEvaluation25, AdjoinRoot.liftAlgHom_mk]
  unfold unitPlanePolynomial
  rw [planeRelation_derivative_polynomial]
  simp [planeDerivativeV, Polynomial.eval₂_pow]

/-- Every rational plane point with nonzero first coordinate has an actual DVR
as its evaluation-kernel local ring. -/
theorem unitPlanePointLocalRing25_isDVR (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    ∃ _ : IsDomain (UnitPlanePointLocalRing25 u v hr),
      IsDiscreteValuationRing (UnitPlanePointLocalRing25 u v hr) := by
  apply AdjoinRoot.localDVR_at_rationalPoint unitPlanePolynomial
    unitPlanePolynomial_monic (unitPlaneEvaluation25 u v hr)
    (unitPlanePointIdeal25 u v hr) rfl
  rw [unitPlaneEvaluation25_derivative]
  exact planeDerivativeV_ne_zero_rat u v hr hu

end N25

end

/-! ### The places -/
noncomputable section
namespace N25

/-- The place of the actual plane function field defined by a rational plane
point with nonzero first coordinate. -/
def unitPlanePointPlace25 (u v : ℚ) (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    AlgebraicCurve.Place ℚ UnitPlaneFF25 := by
  let h := unitPlanePointLocalRing25_isDVR u v hr hu
  letI : IsDomain (UnitPlanePointLocalRing25 u v hr) := Classical.choose h
  letI : IsDiscreteValuationRing (UnitPlanePointLocalRing25 u v hr) := Classical.choose_spec h
  exact AlgebraicCurve.placeOfDiscreteValuationRing ℚ
    (UnitPlanePointLocalRing25 u v hr) UnitPlaneFF25

/-- The same rational point defines a place of the canonical function field
through the proved birational field isomorphism. -/
def canonicalPointPlaceOfUnitPlane25 (u v : ℚ)
    (hr : planeRelation u v = 0) (hu : u ≠ 0) :
    AlgebraicCurve.Place ℚ (CanonicalFF25 ℚ) :=
  AlgebraicCurve.Place.mapAlgEquiv canonicalUnitPlaneAlgEquiv25
    (unitPlanePointPlace25 u v hr hu)

end N25


