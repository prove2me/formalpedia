-- Prove2me | Definitions.Def_N25_CanonicalPrincipalOpenChart
-- name    : N25_CanonicalPrincipalOpenChart
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:28.372453+00:00
-- url     : https://prove2.me/theorems/e56a635d-145c-483b-b12d-4616fc914d77
-- title:
--   The normalizing principal open of the canonical projective curve
-- statement:
--   Defines the degree-zero homogeneous localization at the normalizing form $A$, its ratio coordinates, and the dehomogenization equivalence with the literal $A=1$ affine chart. It then localizes at the complementary degree-$4$ factor through the ratio $D/A^4$ and identifies this affine localization with the selected homogeneous principal open, furnishing the coordinate ring used in the function-field comparison.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! The principal open set of the normalizing form A in the canonical Proj and its identification with the affine A-chart. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable (K : Type u) [Field K]

abbrev CanonicalAProjRing25 := Away (canonicalConePiece25 K) (canonicalConeA25 K)

noncomputable instance canonicalAProjRing25_algebra : Algebra K (CanonicalAProjRing25 K) :=
  ((fromZeroRingHom (canonicalConePiece25 K) (Submonoid.powers (canonicalConeA25 K))).comp
    (algebraMap K (canonicalConePiece25 K 0))).toAlgebra

def canonicalAProjCoordinate25 (j : Fin 4) : CanonicalAProjRing25 K :=
  Away.mk (canonicalConePiece25 K) (canonicalConeA25_mem K) 1 (canonicalConeCoordinate25 K j)
    (by simpa using canonicalConeCoordinate25_mem K j)

/-- The defining equations remain zero in the affine chart quotient. -/
def canonicalConeToAChart25  :
    CanonicalConeRing25 K →ₐ[K] CanonicalAChartRing25 K :=
  Ideal.Quotient.liftₐ (canonicalConeIdeal25 K)
    (Ideal.Quotient.mkₐ K (canonicalAChartIdeal25 K)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (Ideal.span_mono (show
        ({canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)} :
          Set (CanonicalConePolynomial25 K)) ⊆
        {canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          canonicalDenominator (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) - 1} from by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *; tauto)) hp)

theorem canonicalConeToAChart25_A  :
    canonicalConeToAChart25 K (canonicalConeA25 K) = 1 := by
  change Ideal.Quotient.mk (canonicalAChartIdeal25 K)
    (canonicalDenominator (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)) = 1
  rw [← map_one (Ideal.Quotient.mk (canonicalAChartIdeal25 K)), Ideal.Quotient.eq]
  exact Ideal.subset_span (by simp)

/-- Set the chart pivot equal to one and hence extend to the ordinary localization. -/
def canonicalLocalizationToAChart25  :
    Localization.Away (canonicalConeA25 K) →+* CanonicalAChartRing25 K :=
  IsLocalization.Away.lift (S := Localization.Away (canonicalConeA25 K))
    (g := (canonicalConeToAChart25 K).toRingHom)
    (canonicalConeA25 K) (by
      change IsUnit (canonicalConeToAChart25 K (canonicalConeA25 K))
      rw [canonicalConeToAChart25_A]; exact isUnit_one)

/-- Dehomogenization restricted to the degree-zero localization. -/
def canonicalAProjToAffine25  :
    CanonicalAProjRing25 K →+* CanonicalAChartRing25 K :=
  (canonicalLocalizationToAChart25 K).comp
    (algebraMap (CanonicalAProjRing25 K)
      (Localization.Away (canonicalConeA25 K)))

@[simp] theorem canonicalAProjToAffine25_coordinate (j : Fin 4) :
    canonicalAProjToAffine25 K (canonicalAProjCoordinate25 K j) =
      Ideal.Quotient.mk (canonicalAChartIdeal25 K) (MvPolynomial.X j) := by
  simp [canonicalAProjToAffine25, canonicalLocalizationToAChart25,
    canonicalAProjCoordinate25, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  change canonicalConeToAChart25 K (canonicalConeCoordinate25 K j) =
    canonicalConeToAChart25 K (canonicalConeA25 K) * _
  rw [canonicalConeToAChart25_A, one_mul]
  rfl

theorem canonicalPrincipalOpen25_ratio_val (j : Fin 4) :
    (canonicalAProjCoordinate25 K j).val =
      algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
        (canonicalConeCoordinate25 K j) *
      IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K))
        (canonicalConeA25 K) := by
  rw [canonicalAProjCoordinate25, Away.val_mk]
  simp only [pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

/-- Normalizing A makes its linear coordinate expression equal to one. -/
theorem canonicalAProjCoordinate25_relation :
    canonicalAProjCoordinate25 K 1 + canonicalAProjCoordinate25 K 2 - canonicalAProjCoordinate25 K 3 = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_one, canonicalPrincipalOpen25_ratio_val]
  calc
    _ = algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
        (canonicalConeA25 K) * IsLocalization.Away.invSelf
          (S := Localization.Away (canonicalConeA25 K)) (canonicalConeA25 K) := by
      let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
      let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K)) (canonicalConeA25 K)
      change m (canonicalConeCoordinate25 K 1) * r + m (canonicalConeCoordinate25 K 2) * r -
        m (canonicalConeCoordinate25 K 3) * r = m (canonicalConeA25 K) * r
      rw [show m (canonicalConeA25 K) = m (canonicalConeCoordinate25 K 1) +
        m (canonicalConeCoordinate25 K 2) - m (canonicalConeCoordinate25 K 3) by
          change m (canonicalConeCoordinate25 K 1 + canonicalConeCoordinate25 K 2 -
            canonicalConeCoordinate25 K 3) = _
          exact (map_sub m _ _).trans (congrArg
            (fun z => z - m (canonicalConeCoordinate25 K 3)) (map_add m _ _))]
      ring
    _ = 1 := IsLocalization.Away.mul_invSelf (canonicalConeA25 K)

theorem canonicalPrincipalOpen25_cone_quadric :
    canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) = 0 := by
  change canonicalQuadric (canonicalConeProjection25 K (MvPolynomial.X 0))
    (canonicalConeProjection25 K (MvPolynomial.X 1))
    (canonicalConeProjection25 K (MvPolynomial.X 2))
    (canonicalConeProjection25 K (MvPolynomial.X 3)) = 0
  have h : canonicalQuadric (canonicalConeProjection25 K (MvPolynomial.X 0))
    (canonicalConeProjection25 K (MvPolynomial.X 1))
    (canonicalConeProjection25 K (MvPolynomial.X 2))
    (canonicalConeProjection25 K (MvPolynomial.X 3)) =
    canonicalConeProjection25 K (canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
      simp only [canonicalQuadric, map_add, map_sub, map_neg, map_mul, map_pow]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem canonicalPrincipalOpen25_cone_cubic :
    canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) = 0 := by
  have h : canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
    (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3) =
    canonicalConeProjection25 K (canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3)) := by
    simp [canonicalCubic, canonicalConeCoordinate25]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- The ratio coordinates satisfy the literal homogeneous quadric. -/
theorem canonicalAProjCoordinate25_quadric  :
    canonicalQuadric (canonicalAProjCoordinate25 K 0) (canonicalAProjCoordinate25 K 1)
      (canonicalAProjCoordinate25 K 2) (canonicalAProjCoordinate25 K 3) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, ← HomogeneousLocalization.algebraMap_apply]
  simp only [canonicalQuadric, map_add, map_sub, map_neg, map_mul, map_pow]
  change canonicalQuadric (canonicalAProjCoordinate25 K 0).val
    (canonicalAProjCoordinate25 K 1).val (canonicalAProjCoordinate25 K 2).val
    (canonicalAProjCoordinate25 K 3).val = 0
  simp only [canonicalPrincipalOpen25_ratio_val]
  let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
  let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K))
    (canonicalConeA25 K)
  change canonicalQuadric (m (canonicalConeCoordinate25 K 0) * r)
    (m (canonicalConeCoordinate25 K 1) * r) (m (canonicalConeCoordinate25 K 2) * r)
    (m (canonicalConeCoordinate25 K 3) * r) = 0
  calc
    _ = r^2 * m (canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3)) := by
        simp only [canonicalQuadric, map_add, map_sub, map_neg, map_mul, map_pow]; ring
    _ = 0 := by rw [canonicalPrincipalOpen25_cone_quadric, map_zero, mul_zero]

/-- The ratio coordinates satisfy the literal homogeneous cubic. -/
theorem canonicalAProjCoordinate25_cubic  :
    canonicalCubic (canonicalAProjCoordinate25 K 0) (canonicalAProjCoordinate25 K 1)
      (canonicalAProjCoordinate25 K 2) (canonicalAProjCoordinate25 K 3) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, ← HomogeneousLocalization.algebraMap_apply]
  simp only [canonicalCubic, map_add, map_sub, map_neg, map_mul, map_pow]
  change canonicalCubic (canonicalAProjCoordinate25 K 0).val
    (canonicalAProjCoordinate25 K 1).val (canonicalAProjCoordinate25 K 2).val
    (canonicalAProjCoordinate25 K 3).val = 0
  simp only [canonicalPrincipalOpen25_ratio_val]
  let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
  let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K))
    (canonicalConeA25 K)
  change canonicalCubic (m (canonicalConeCoordinate25 K 0) * r)
    (m (canonicalConeCoordinate25 K 1) * r) (m (canonicalConeCoordinate25 K 2) * r)
    (m (canonicalConeCoordinate25 K 3) * r) = 0
  calc
    _ = r^3 * m (canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3)) := by
        simp only [canonicalCubic, map_add, map_sub, map_neg, map_mul, map_pow]; ring
    _ = 0 := by rw [canonicalPrincipalOpen25_cone_cubic, map_zero, mul_zero]

/-- Polynomial substitution of the four ratios. -/
def canonicalARatioPolynomialMap25  :
    CanonicalAChartPolynomial25 K →ₐ[K] CanonicalAProjRing25 K where
  toRingHom := MvPolynomial.eval₂Hom (algebraMap K (CanonicalAProjRing25 K))
    (canonicalAProjCoordinate25 K)
  commutes' := fun a => MvPolynomial.eval₂Hom_C _ _ a

@[simp] theorem canonicalARatioPolynomialMap25_X (j : Fin 4) :
    canonicalARatioPolynomialMap25 K (MvPolynomial.X j) = canonicalAProjCoordinate25 K j := by
  change (MvPolynomial.eval₂Hom (algebraMap K (CanonicalAProjRing25 K))
    (canonicalAProjCoordinate25 K)) (MvPolynomial.X j) = _
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

theorem aChartIdeal_le_ratioKernel  :
    canonicalAChartIdeal25 K ≤ RingHom.ker (canonicalARatioPolynomialMap25 K).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | hp
  · change canonicalARatioPolynomialMap25 K _ = 0
    simpa only [canonicalQuadric, map_neg, map_sub, map_add, map_mul, map_pow,
      canonicalARatioPolynomialMap25_X] using canonicalAProjCoordinate25_quadric K
  · rcases hp with rfl | hp
    · change canonicalARatioPolynomialMap25 K _ = 0
      simpa only [canonicalCubic, map_sub, map_add, map_mul, map_pow,
        canonicalARatioPolynomialMap25_X] using canonicalAProjCoordinate25_cubic K
    · rcases hp with rfl | hp
      · change canonicalARatioPolynomialMap25 K (canonicalDenominator
          (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) - 1) = 0
        simp only [canonicalDenominator, map_sub, map_add, map_one, canonicalARatioPolynomialMap25_X]
        rw [canonicalAProjCoordinate25_relation, sub_self]

/-- Substitute coordinate ratios into the literal affine quotient. -/
def canonicalAffineToAProj25  :
    CanonicalAChartRing25 K →ₐ[K] CanonicalAProjRing25 K :=
  Ideal.Quotient.liftₐ (canonicalAChartIdeal25 K) (canonicalARatioPolynomialMap25 K)
    (fun _ hp => aChartIdeal_le_ratioKernel K hp)

@[simp] theorem canonicalAffineToAProj25_coordinate (j : Fin 4) :
    canonicalAffineToAProj25 K
      (Ideal.Quotient.mk (canonicalAChartIdeal25 K) (MvPolynomial.X j)) =
        canonicalAProjCoordinate25 K j := by
  change canonicalARatioPolynomialMap25 K (MvPolynomial.X j) = _
  exact canonicalARatioPolynomialMap25_X K j

/-- Every homogeneous coordinate monomial fraction is a product of coordinate ratios. -/
theorem canonicalAProj_monomial  (a : ℕ) (ai : Fin 4 → ℕ)
    (hai : ∑ j, ai j = a)
    (hh : (∏ j, canonicalConeCoordinate25 K j ^ ai j) ∈ canonicalConePiece25 K a) :
    Away.mk (canonicalConePiece25 K) (canonicalConeA25_mem K) a
      (∏ j, canonicalConeCoordinate25 K j ^ ai j) (by simpa using hh) =
      ∏ j, canonicalAProjCoordinate25 K j ^ ai j := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  rw [show (∏ j, canonicalAProjCoordinate25 K j ^ ai j).val =
      ∏ j, (canonicalAProjCoordinate25 K j).val ^ ai j by
    rw [← HomogeneousLocalization.algebraMap_apply]
    simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply]]
  simp only [canonicalAProjCoordinate25, Away.val_mk, Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_pow, pow_one, one_mul, Finset.prod_pow_eq_pow_sum]
  rw [hai]

/-- The four coordinate ratios generate the entire actual homogeneous chart ring. -/
theorem canonicalAffineToAProj25_surjective  :
    Function.Surjective (canonicalAffineToAProj25 K) := by
  have hadjoin := Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := canonicalConePiece25 K) (canonicalConeA25_mem K)
    (Fin 4) (canonicalConeCoordinate25 K) (canonicalConeCoordinates25_adjoin K)
    (fun _ => 1) (canonicalConeCoordinate25_mem K)
  intro z
  change z ∈ (canonicalAffineToAProj25 K).toRingHom.range
  have hz : z ∈ (⊤ : Subalgebra (canonicalConePiece25 K 0) (CanonicalAProjRing25 K)) := by trivial
  rw [← hadjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      rcases hz with ⟨a, ai, hai, _hbound, rfl⟩
      have hai' : ∑ j, ai j = a := by simpa using hai
      have hh : (∏ j, canonicalConeCoordinate25 K j ^ ai j) ∈ canonicalConePiece25 K a := by
        have ht : (∏ j : Fin 4, canonicalConeCoordinate25 K j ^ ai j) ∈
            canonicalConePiece25 K (∑ j : Fin 4, ai j • (1 : ℕ)) :=
          SetLike.prod_pow_mem_graded (canonicalConePiece25 K) (fun _ : Fin 4 => 1)
            (canonicalConeCoordinate25 K) ai (fun j _ => canonicalConeCoordinate25_mem K j)
        simpa [hai'] using ht
      refine ⟨∏ j : Fin 4, Ideal.Quotient.mk (canonicalAChartIdeal25 K) (MvPolynomial.X j) ^ ai j, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow,
        canonicalAffineToAProj25_coordinate]
      exact (canonicalAProj_monomial K a ai hai' hh).symm
  | algebraMap r =>
      obtain ⟨a, rfl⟩ := (canonicalConePieceZero25_algebraMap_bijective K).surjective r
      refine ⟨algebraMap K (CanonicalAChartRing25 K) a, ?_⟩
      exact (canonicalAffineToAProj25 K).commutes a
  | add x y hx hy hxRange hyRange =>
      exact (canonicalAffineToAProj25 K).toRingHom.range.add_mem hxRange hyRange
  | mul x y hx hy hxRange hyRange =>
      exact (canonicalAffineToAProj25 K).toRingHom.range.mul_mem hxRange hyRange

/-- Dehomogenization on the full degree-zero coefficient ring. -/
theorem canonicalAProjToAffine25_fromZero  (r : canonicalConePiece25 K 0) :
    canonicalAProjToAffine25 K (fromZeroRingHom (canonicalConePiece25 K) _ r) =
      canonicalConeToAChart25 K r.val := by
  unfold canonicalAProjToAffine25
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change canonicalLocalizationToAChart25 K (Localization.mk r.val 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.Away.lift_eq _ _ _

/-- Dehomogenization preserves the coefficient scalars selected on the actual chart. -/
@[simp] theorem canonicalAProjToAffine25_algebraMap  (a : K) :
    canonicalAProjToAffine25 K (algebraMap K (CanonicalAProjRing25 K) a) =
      algebraMap K (CanonicalAChartRing25 K) a := by
  change canonicalAProjToAffine25 K
    (fromZeroRingHom (canonicalConePiece25 K) _ (algebraMap K (canonicalConePiece25 K 0) a)) = _
  rw [canonicalAProjToAffine25_fromZero, SetLike.GradeZero.coe_algebraMap]
  exact (canonicalConeToAChart25 K).commutes a

/-- Dehomogenization is a left inverse on the literal affine chart quotient. -/
theorem canonicalAProjToAffine25_leftInverse  :
    Function.LeftInverse (canonicalAProjToAffine25 K) (canonicalAffineToAProj25 K) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (canonicalAChartIdeal25 K) x
  change canonicalAProjToAffine25 K (canonicalARatioPolynomialMap25 K p) =
    Ideal.Quotient.mk (canonicalAChartIdeal25 K) p
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show canonicalARatioPolynomialMap25 K (MvPolynomial.C a) =
        algebraMap K (CanonicalAProjRing25 K) a from (canonicalARatioPolynomialMap25 K).commutes a]
      exact canonicalAProjToAffine25_algebraMap K a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, hp, canonicalARatioPolynomialMap25_X,
        canonicalAProjToAffine25_coordinate, map_mul]

/-- The literal A=1 quotient is the homogeneous A-chart. -/
noncomputable def canonicalAChartAlgEquiv25  :
    CanonicalAChartRing25 K ≃ₐ[K] CanonicalAProjRing25 K :=
  AlgEquiv.ofBijective (canonicalAffineToAProj25 K)
    ⟨(canonicalAProjToAffine25_leftInverse K).injective, canonicalAffineToAProj25_surjective K⟩

theorem canonicalAChartAlgEquiv25_coordinate (j : Fin 4) :
    canonicalAChartAlgEquiv25 K
      (Ideal.Quotient.mk (canonicalAChartIdeal25 K) (MvPolynomial.X j)) =
      canonicalAProjCoordinate25 K j := canonicalAffineToAProj25_coordinate K j

/-- The degree-four factor complementary to A in the selected homogeneous element. -/
def canonicalConeOpenFactor25 : CanonicalConeRing25 K :=
  canonicalConeCoordinate25 K 0 * canonicalConeCoordinate25 K 2 * canonicalConeB25 K

theorem canonicalConeOpenFactor25_mem :
    canonicalConeOpenFactor25 K ∈ canonicalConePiece25 K 4 :=
  SetLike.mul_mem_graded (SetLike.mul_mem_graded (canonicalConeCoordinate25_mem K 0)
    (canonicalConeCoordinate25_mem K 2)) (canonicalConeB25_mem K)

theorem canonicalConePrincipalElement25_factor :
    canonicalConePrincipalElement25 K = canonicalConeA25 K * canonicalConeOpenFactor25 K := by
  unfold canonicalConePrincipalElement25 canonicalConeOpenFactor25
  ring

theorem aFraction_val (n : ℕ) (p : CanonicalConeRing25 K)
    (hp : p ∈ canonicalConePiece25 K (n • (1 : ℕ))) :
    (Away.mk (canonicalConePiece25 K) (canonicalConeA25_mem K) n p hp).val =
      algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K)) p *
        IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K)) (canonicalConeA25 K)^n := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
  simp only [one_pow]
  rfl

/-- The affine localization element is the homogeneous ratio D/A^4. -/
theorem canonicalAChartAlgEquiv25_openElement :
    canonicalAChartAlgEquiv25 K (canonicalAChartOpenElement25 K) =
      Away.isLocalizationElem (canonicalConeA25_mem K) (canonicalConeOpenFactor25_mem K) := by
  simp only [canonicalAChartOpenElement25, canonicalMultiplier, canonicalDenominator,
    map_mul, map_add, map_sub]
  change canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 0) *
    canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 2) *
    (canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 0) *
       canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 2) +
     canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 2) *
       (canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 1) +
        canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 2) -
        canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 3)) +
     canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 0) *
       (canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 1) +
        canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 2) -
        canonicalAChartAlgEquiv25 K (canonicalAChartCoordinate25 K 3))) = _
  simp only [canonicalAChartCoordinate25, canonicalAChartAlgEquiv25_coordinate]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_sub, canonicalPrincipalOpen25_ratio_val, Away.isLocalizationElem, aFraction_val, pow_one]
  let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))
  let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeA25 K)) (canonicalConeA25 K)
  change (m (canonicalConeCoordinate25 K 0) * r) * (m (canonicalConeCoordinate25 K 2) * r) *
    ((m (canonicalConeCoordinate25 K 0) * r) * (m (canonicalConeCoordinate25 K 2) * r) +
    (m (canonicalConeCoordinate25 K 2) * r) * (m (canonicalConeCoordinate25 K 1) * r +
      m (canonicalConeCoordinate25 K 2) * r - m (canonicalConeCoordinate25 K 3) * r) +
    (m (canonicalConeCoordinate25 K 0) * r) * (m (canonicalConeCoordinate25 K 1) * r +
      m (canonicalConeCoordinate25 K 2) * r - m (canonicalConeCoordinate25 K 3) * r)) =
      m (canonicalConeOpenFactor25 K) * r^4
  have hD : m (canonicalConeOpenFactor25 K) =
      m (canonicalConeCoordinate25 K 0) * m (canonicalConeCoordinate25 K 2) *
      (m (canonicalConeCoordinate25 K 0) * m (canonicalConeCoordinate25 K 2) +
       m (canonicalConeCoordinate25 K 2) * (m (canonicalConeCoordinate25 K 1) +
         m (canonicalConeCoordinate25 K 2) - m (canonicalConeCoordinate25 K 3)) +
       m (canonicalConeCoordinate25 K 0) * (m (canonicalConeCoordinate25 K 1) +
         m (canonicalConeCoordinate25 K 2) - m (canonicalConeCoordinate25 K 3))) := by
    change m (canonicalConeCoordinate25 K 0 * canonicalConeCoordinate25 K 2 *
      (canonicalConeCoordinate25 K 0 * canonicalConeCoordinate25 K 2 +
       canonicalConeCoordinate25 K 2 * (canonicalConeCoordinate25 K 1 +
         canonicalConeCoordinate25 K 2 - canonicalConeCoordinate25 K 3) +
       canonicalConeCoordinate25 K 0 * (canonicalConeCoordinate25 K 1 +
         canonicalConeCoordinate25 K 2 - canonicalConeCoordinate25 K 3))) = _
    simp only [map_mul, map_add, map_sub]
  rw [hD]
  ring

/-- Restricting from the A-chart to the selected principal open. -/
def canonicalAProjToPrincipal25 : CanonicalAProjRing25 K →+* CanonicalProjPrincipalRing25 K :=
  awayMap (canonicalConePiece25 K) (canonicalConeOpenFactor25_mem K)
    (canonicalConePrincipalElement25_factor K)

noncomputable instance canonicalProjPrincipalRing25_aChartAlgebra :
    Algebra (CanonicalAProjRing25 K) (CanonicalProjPrincipalRing25 K) :=
  (canonicalAProjToPrincipal25 K).toAlgebra

local instance canonicalAProjRing25_scalarAction : SMul K (CanonicalAProjRing25 K) :=
  (canonicalAProjRing25_algebra K).toSMul

local instance canonicalProjPrincipalRing25_scalarAction : SMul K (CanonicalProjPrincipalRing25 K) :=
  (canonicalProjPrincipalRing25_algebra K).toSMul

instance canonicalProjPrincipalRing25_scalarTower :
    IsScalarTower K (CanonicalAProjRing25 K) (CanonicalProjPrincipalRing25 K) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  exact (awayMap_fromZeroRingHom (canonicalConePiece25 K) (canonicalConeOpenFactor25_mem K)
    (canonicalConePrincipalElement25_factor K) (algebraMap K (canonicalConePiece25 K 0) a)).symm

instance canonicalProjPrincipalRing25_isLocalization :
    IsLocalization.Away
      (Away.isLocalizationElem (canonicalConeA25_mem K) (canonicalConeOpenFactor25_mem K))
      (CanonicalProjPrincipalRing25 K) :=
  Away.isLocalization_mul (𝒜 := canonicalConePiece25 K) (canonicalConeA25_mem K)
    (canonicalConeOpenFactor25_mem K) (canonicalConePrincipalElement25_factor K) (by decide)

/-- The literal affine principal localization is the degree-zero homogeneous localization at s. -/
noncomputable def canonicalPrincipalOpenAlgEquiv25 :
    CanonicalOpenChartRing25 K ≃ₐ[K] CanonicalProjPrincipalRing25 K :=
  IsLocalization.algEquivOfAlgEquiv (CanonicalOpenChartRing25 K) (CanonicalProjPrincipalRing25 K)
    (canonicalAChartAlgEquiv25 K) (by
      rw [Submonoid.map_powers, canonicalAChartAlgEquiv25_openElement])

end N25


