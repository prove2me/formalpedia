-- Prove2me | Definitions.Def_N25_CanonicalChartDehomogenization
-- name    : N25_CanonicalChartDehomogenization
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:23.056081+00:00
-- url     : https://prove2.me/theorems/d062b543-9bd5-4113-a860-a1f6bc5fe872
-- title:
--   Dehomogenization on the four canonical projective charts
-- statement:
--   Defines, for each coordinate chart $D_+(X_i)$, the maps from the homogeneous cone and its localization to the affine quotient, the coordinate ratios $X_j/X_i$, the inverse substitution map, and the resulting $K$-algebra equivalence. It also packages the four-chart cover and the chart immersions into the canonical projective curve, linking homogeneous geometry with explicit affine coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCharts
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Literal dehomogenization on the four canonical projective charts: the chart algebra equivalences and the open chart immersions. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable (K : Type u) [Field K]

/-- The diagonal coordinate ratio is one without a domain assumption. -/
theorem canonicalProjChartCoordinate25_self (i : Fin 4) :
    canonicalProjChartCoordinate25 K i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [canonicalProjChartCoordinate25, Away.val_mk, HomogeneousLocalization.val_one, pow_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp

/-- The defining equations remain zero in the affine chart quotient. -/
def canonicalConeToAffineChart25 (i : Fin 4) :
    CanonicalConeRing25 K →ₐ[K] CanonicalChartRing25 K i :=
  Ideal.Quotient.liftₐ (canonicalConeIdeal25 K)
    (Ideal.Quotient.mkₐ K (canonicalChartIdeal25 K i)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (Ideal.span_mono (show
        ({canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)} :
          Set (CanonicalConePolynomial25 K)) ⊆
        {canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3),
          MvPolynomial.X i - 1} from by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *; tauto)) hp)

theorem canonicalConeToAffineChart25_pivot (i : Fin 4) :
    canonicalConeToAffineChart25 K i (canonicalConeCoordinate25 K i) = 1 := by
  change Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X i) = 1
  rw [← map_one (Ideal.Quotient.mk (canonicalChartIdeal25 K i)), Ideal.Quotient.eq]
  exact Ideal.subset_span (by simp)

/-- Set the chart pivot equal to one and hence extend to the ordinary localization. -/
def canonicalLocalizationToAffineChart25 (i : Fin 4) :
    Localization.Away (canonicalConeCoordinate25 K i) →+* CanonicalChartRing25 K i :=
  IsLocalization.Away.lift (S := Localization.Away (canonicalConeCoordinate25 K i))
    (g := (canonicalConeToAffineChart25 K i).toRingHom)
    (canonicalConeCoordinate25 K i) (by
      change IsUnit (canonicalConeToAffineChart25 K i (canonicalConeCoordinate25 K i))
      rw [canonicalConeToAffineChart25_pivot]; exact isUnit_one)

/-- Dehomogenization restricted to the degree-zero localization. -/
def canonicalProjChartToAffine25 (i : Fin 4) :
    CanonicalProjChartRing25 K i →+* CanonicalChartRing25 K i :=
  (canonicalLocalizationToAffineChart25 K i).comp
    (algebraMap (CanonicalProjChartRing25 K i)
      (Localization.Away (canonicalConeCoordinate25 K i)))

@[simp] theorem canonicalProjChartToAffine25_coordinate (i j : Fin 4) :
    canonicalProjChartToAffine25 K i (canonicalProjChartCoordinate25 K i j) =
      Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j) := by
  simp [canonicalProjChartToAffine25, canonicalLocalizationToAffineChart25,
    canonicalProjChartCoordinate25, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  change canonicalConeToAffineChart25 K i (canonicalConeCoordinate25 K j) =
    canonicalConeToAffineChart25 K i (canonicalConeCoordinate25 K i) * _
  rw [canonicalConeToAffineChart25_pivot, one_mul]
  rfl

theorem canonicalProjChart25_ratio_val (i j : Fin 4) :
    (canonicalProjChartCoordinate25 K i j).val =
      algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeCoordinate25 K i))
        (canonicalConeCoordinate25 K j) *
      IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeCoordinate25 K i))
        (canonicalConeCoordinate25 K i) := by
  rw [canonicalProjChartCoordinate25, Away.val_mk]
  simp only [pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  rfl

theorem canonicalProjChart25_cone_quadric :
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

theorem canonicalProjChart25_cone_cubic :
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
theorem canonicalProjChartCoordinate25_quadric (i : Fin 4) :
    canonicalQuadric (canonicalProjChartCoordinate25 K i 0) (canonicalProjChartCoordinate25 K i 1)
      (canonicalProjChartCoordinate25 K i 2) (canonicalProjChartCoordinate25 K i 3) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, ← HomogeneousLocalization.algebraMap_apply]
  simp only [canonicalQuadric, map_add, map_sub, map_neg, map_mul, map_pow]
  change canonicalQuadric (canonicalProjChartCoordinate25 K i 0).val
    (canonicalProjChartCoordinate25 K i 1).val (canonicalProjChartCoordinate25 K i 2).val
    (canonicalProjChartCoordinate25 K i 3).val = 0
  simp only [canonicalProjChart25_ratio_val]
  let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeCoordinate25 K i))
  let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeCoordinate25 K i))
    (canonicalConeCoordinate25 K i)
  change canonicalQuadric (m (canonicalConeCoordinate25 K 0) * r)
    (m (canonicalConeCoordinate25 K 1) * r) (m (canonicalConeCoordinate25 K 2) * r)
    (m (canonicalConeCoordinate25 K 3) * r) = 0
  calc
    _ = r^2 * m (canonicalQuadric (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3)) := by
        simp only [canonicalQuadric, map_add, map_sub, map_neg, map_mul, map_pow]; ring
    _ = 0 := by rw [canonicalProjChart25_cone_quadric, map_zero, mul_zero]

/-- The ratio coordinates satisfy the literal homogeneous cubic. -/
theorem canonicalProjChartCoordinate25_cubic (i : Fin 4) :
    canonicalCubic (canonicalProjChartCoordinate25 K i 0) (canonicalProjChartCoordinate25 K i 1)
      (canonicalProjChartCoordinate25 K i 2) (canonicalProjChartCoordinate25 K i 3) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, ← HomogeneousLocalization.algebraMap_apply]
  simp only [canonicalCubic, map_add, map_sub, map_neg, map_mul, map_pow]
  change canonicalCubic (canonicalProjChartCoordinate25 K i 0).val
    (canonicalProjChartCoordinate25 K i 1).val (canonicalProjChartCoordinate25 K i 2).val
    (canonicalProjChartCoordinate25 K i 3).val = 0
  simp only [canonicalProjChart25_ratio_val]
  let m := algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeCoordinate25 K i))
  let r := IsLocalization.Away.invSelf (S := Localization.Away (canonicalConeCoordinate25 K i))
    (canonicalConeCoordinate25 K i)
  change canonicalCubic (m (canonicalConeCoordinate25 K 0) * r)
    (m (canonicalConeCoordinate25 K 1) * r) (m (canonicalConeCoordinate25 K 2) * r)
    (m (canonicalConeCoordinate25 K 3) * r) = 0
  calc
    _ = r^3 * m (canonicalCubic (canonicalConeCoordinate25 K 0) (canonicalConeCoordinate25 K 1)
      (canonicalConeCoordinate25 K 2) (canonicalConeCoordinate25 K 3)) := by
        simp only [canonicalCubic, map_add, map_sub, map_neg, map_mul, map_pow]; ring
    _ = 0 := by rw [canonicalProjChart25_cone_cubic, map_zero, mul_zero]

/-- Polynomial substitution of the four ratios. -/
def canonicalRatioPolynomialMap25 (i : Fin 4) :
    CanonicalChartPolynomial25 K →ₐ[K] CanonicalProjChartRing25 K i where
  toRingHom := MvPolynomial.eval₂Hom (algebraMap K (CanonicalProjChartRing25 K i))
    (canonicalProjChartCoordinate25 K i)
  commutes' := fun a => MvPolynomial.eval₂Hom_C _ _ a

@[simp] theorem canonicalRatioPolynomialMap25_X (i j : Fin 4) :
    canonicalRatioPolynomialMap25 K i (MvPolynomial.X j) = canonicalProjChartCoordinate25 K i j := by
  change (MvPolynomial.eval₂Hom (algebraMap K (CanonicalProjChartRing25 K i))
    (canonicalProjChartCoordinate25 K i)) (MvPolynomial.X j) = _
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]

theorem chartIdeal_le_ratioKernel (i : Fin 4) :
    canonicalChartIdeal25 K i ≤ RingHom.ker (canonicalRatioPolynomialMap25 K i).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | hp
  · change canonicalRatioPolynomialMap25 K i _ = 0
    simpa only [canonicalQuadric, map_neg, map_sub, map_add, map_mul, map_pow,
      canonicalRatioPolynomialMap25_X] using canonicalProjChartCoordinate25_quadric K i
  · rcases hp with rfl | hp
    · change canonicalRatioPolynomialMap25 K i _ = 0
      simpa only [canonicalCubic, map_sub, map_add, map_mul, map_pow,
        canonicalRatioPolynomialMap25_X] using canonicalProjChartCoordinate25_cubic K i
    · rcases hp with rfl | hp
      · change canonicalRatioPolynomialMap25 K i (MvPolynomial.X i - 1) = 0
        rw [map_sub, map_one]
        rw [canonicalRatioPolynomialMap25_X, canonicalProjChartCoordinate25_self, sub_self]

/-- Substitute coordinate ratios into the literal affine quotient. -/
def canonicalAffineToProjChart25 (i : Fin 4) :
    CanonicalChartRing25 K i →ₐ[K] CanonicalProjChartRing25 K i :=
  Ideal.Quotient.liftₐ (canonicalChartIdeal25 K i) (canonicalRatioPolynomialMap25 K i)
    (fun _ hp => chartIdeal_le_ratioKernel K i hp)

@[simp] theorem canonicalAffineToProjChart25_coordinate (i j : Fin 4) :
    canonicalAffineToProjChart25 K i
      (Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j)) =
        canonicalProjChartCoordinate25 K i j := by
  change canonicalRatioPolynomialMap25 K i (MvPolynomial.X j) = _
  exact canonicalRatioPolynomialMap25_X K i j

/-- The cone is generated over its degree-zero piece by the four literal coordinates. -/
theorem canonicalConeCoordinates25_adjoin :
    Algebra.adjoin (canonicalConePiece25 K 0) (Set.range (canonicalConeCoordinate25 K)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (canonicalConeIdeal25 K) x
  induction p using MvPolynomial.induction_on with
  | C a =>
      have ha := (Algebra.adjoin (canonicalConePiece25 K 0)
        (Set.range (canonicalConeCoordinate25 K))).algebraMap_mem (algebraMap K (canonicalConePiece25 K 0) a)
      change algebraMap K (CanonicalConeRing25 K) a ∈ _
      simpa only [SetLike.GradeZero.algebraMap_apply, SetLike.GradeZero.coe_algebraMap] using ha
  | add p q hp hq =>
      simpa only [map_add] using (Algebra.adjoin (canonicalConePiece25 K 0)
        (Set.range (canonicalConeCoordinate25 K))).add_mem hp hq
  | mul_X p j hp =>
      rw [map_mul]
      exact (Algebra.adjoin (canonicalConePiece25 K 0)
        (Set.range (canonicalConeCoordinate25 K))).mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

/-- Every homogeneous coordinate monomial fraction is a product of coordinate ratios. -/
theorem canonicalProjChart25_monomial (i : Fin 4) (a : ℕ) (ai : Fin 4 → ℕ)
    (hai : ∑ j, ai j = a)
    (hh : (∏ j, canonicalConeCoordinate25 K j ^ ai j) ∈ canonicalConePiece25 K a) :
    Away.mk (canonicalConePiece25 K) (canonicalConeCoordinate25_mem K i) a
      (∏ j, canonicalConeCoordinate25 K j ^ ai j) (by simpa using hh) =
      ∏ j, canonicalProjChartCoordinate25 K i j ^ ai j := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  rw [show (∏ j, canonicalProjChartCoordinate25 K i j ^ ai j).val =
      ∏ j, (canonicalProjChartCoordinate25 K i j).val ^ ai j by
    rw [← HomogeneousLocalization.algebraMap_apply]
    simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply]]
  simp only [canonicalProjChartCoordinate25, Away.val_mk, Localization.mk_pow, Localization.mk_prod]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, SubmonoidClass.coe_pow, pow_one, one_mul, Finset.prod_pow_eq_pow_sum]
  rw [hai]

/-- The four coordinate ratios generate the entire actual homogeneous chart ring. -/
theorem canonicalAffineToProjChart25_surjective (i : Fin 4) :
    Function.Surjective (canonicalAffineToProjChart25 K i) := by
  have hadjoin := Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := canonicalConePiece25 K) (canonicalConeCoordinate25_mem K i)
    (Fin 4) (canonicalConeCoordinate25 K) (canonicalConeCoordinates25_adjoin K)
    (fun _ => 1) (canonicalConeCoordinate25_mem K)
  intro z
  change z ∈ (canonicalAffineToProjChart25 K i).toRingHom.range
  have hz : z ∈ (⊤ : Subalgebra (canonicalConePiece25 K 0) (CanonicalProjChartRing25 K i)) := by trivial
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
      refine ⟨∏ j : Fin 4, Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j) ^ ai j, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow,
        canonicalAffineToProjChart25_coordinate]
      exact (canonicalProjChart25_monomial K i a ai hai' hh).symm
  | algebraMap r =>
      obtain ⟨a, rfl⟩ := (canonicalConePieceZero25_algebraMap_bijective K).surjective r
      refine ⟨algebraMap K (CanonicalChartRing25 K i) a, ?_⟩
      exact (canonicalAffineToProjChart25 K i).commutes a
  | add x y hx hy hxRange hyRange =>
      exact (canonicalAffineToProjChart25 K i).toRingHom.range.add_mem hxRange hyRange
  | mul x y hx hy hxRange hyRange =>
      exact (canonicalAffineToProjChart25 K i).toRingHom.range.mul_mem hxRange hyRange

/-- Dehomogenization on the full degree-zero coefficient ring. -/
theorem canonicalProjChartToAffine25_fromZero (i : Fin 4) (r : canonicalConePiece25 K 0) :
    canonicalProjChartToAffine25 K i (fromZeroRingHom (canonicalConePiece25 K) _ r) =
      canonicalConeToAffineChart25 K i r.val := by
  unfold canonicalProjChartToAffine25
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change canonicalLocalizationToAffineChart25 K i (Localization.mk r.val 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.Away.lift_eq _ _ _

/-- Dehomogenization preserves the coefficient scalars selected on the actual chart. -/
@[simp] theorem canonicalProjChartToAffine25_algebraMap (i : Fin 4) (a : K) :
    canonicalProjChartToAffine25 K i (algebraMap K (CanonicalProjChartRing25 K i) a) =
      algebraMap K (CanonicalChartRing25 K i) a := by
  change canonicalProjChartToAffine25 K i
    (fromZeroRingHom (canonicalConePiece25 K) _ (algebraMap K (canonicalConePiece25 K 0) a)) = _
  rw [canonicalProjChartToAffine25_fromZero, SetLike.GradeZero.coe_algebraMap]
  exact (canonicalConeToAffineChart25 K i).commutes a

/-- Dehomogenization is a left inverse on the literal affine chart quotient. -/
theorem canonicalProjChartToAffine25_leftInverse (i : Fin 4) :
    Function.LeftInverse (canonicalProjChartToAffine25 K i) (canonicalAffineToProjChart25 K i) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (canonicalChartIdeal25 K i) x
  change canonicalProjChartToAffine25 K i (canonicalRatioPolynomialMap25 K i p) =
    Ideal.Quotient.mk (canonicalChartIdeal25 K i) p
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show canonicalRatioPolynomialMap25 K i (MvPolynomial.C a) =
        algebraMap K (CanonicalProjChartRing25 K i) a from (canonicalRatioPolynomialMap25 K i).commutes a]
      exact canonicalProjChartToAffine25_algebraMap K i a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, map_mul, hp, canonicalRatioPolynomialMap25_X,
        canonicalProjChartToAffine25_coordinate, map_mul]

/-- The affine-to-homogeneous chart equivalence for all four charts. -/
noncomputable def canonicalChartAlgEquiv25 (i : Fin 4) :
    CanonicalChartRing25 K i ≃ₐ[K] CanonicalProjChartRing25 K i :=
  AlgEquiv.ofBijective (canonicalAffineToProjChart25 K i)
    ⟨(canonicalProjChartToAffine25_leftInverse K i).injective, canonicalAffineToProjChart25_surjective K i⟩

theorem canonicalChartAlgEquiv25_coordinate (i j : Fin 4) :
    canonicalChartAlgEquiv25 K i
      (Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j)) =
      canonicalProjChartCoordinate25 K i j := canonicalAffineToProjChart25_coordinate K i j

/-- The four coordinate basic opens cover the literal Proj. -/
theorem canonicalProjChartOpen25_cover :
    (⨆ i : Fin 4, canonicalProjChartOpen25 K i) = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' (canonicalConePiece25 K) (canonicalConeCoordinate25 K)
    (fun i => ⟨1, canonicalConeCoordinate25_mem K i⟩) (canonicalConeCoordinates25_adjoin K)

/-- The selected affine chart map into the literal canonical projective curve. -/
def canonicalChartι25 (i : Fin 4) :
    Spec (CommRingCat.of (CanonicalChartRing25 K i)) ⟶ CanonicalProjectiveCurve25 K :=
  Spec.map (CommRingCat.ofHom (canonicalChartAlgEquiv25 K i).symm.toRingHom) ≫
    Proj.awayι (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)
      (canonicalConeCoordinate25_mem K i) (by decide)

theorem canonicalChartSpecMap25_isIso (i : Fin 4) :
    IsIso (Spec.map (CommRingCat.ofHom (canonicalChartAlgEquiv25 K i).symm.toRingHom)) := by
  haveI : IsIso (CommRingCat.ofHom (canonicalChartAlgEquiv25 K i).symm.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (canonicalChartAlgEquiv25 K i).symm.bijective
  infer_instance

theorem canonicalChartι25_isOpenImmersion (i : Fin 4) : IsOpenImmersion (canonicalChartι25 K i) := by
  haveI := canonicalChartSpecMap25_isIso K i
  unfold canonicalChartι25
  exact IsOpenImmersion.comp _ _

theorem canonicalChartι25_toSpec (i : Fin 4) :
    canonicalChartι25 K i ≫ canonicalProjectiveCurveToSpec25 K =
      Spec.map (CommRingCat.ofHom (algebraMap K (CanonicalChartRing25 K i))) := by
  unfold canonicalChartι25 canonicalProjectiveCurveToSpec25
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact (canonicalChartAlgEquiv25 K i).symm.commutes a

theorem canonicalChartι25_opensRange (i : Fin 4) :
    letI : IsOpenImmersion (canonicalChartι25 K i) := canonicalChartι25_isOpenImmersion K i
    (canonicalChartι25 K i).opensRange = canonicalProjChartOpen25 K i := by
  haveI := canonicalChartSpecMap25_isIso K i
  exact (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (CommRingCat.ofHom (canonicalChartAlgEquiv25 K i).symm.toRingHom))
    (Proj.awayι (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)
      (canonicalConeCoordinate25_mem K i) (by decide))).trans
    (Proj.opensRange_awayι (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)
      (canonicalConeCoordinate25_mem K i) (by decide))

end N25


