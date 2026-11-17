-- Prove2me | Definitions.Def_N25_CanonicalSchemePointCharts
-- name    : N25_CanonicalSchemePointCharts
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:17.076713+00:00
-- url     : https://prove2.me/theorems/df718bcf-d487-486b-8eee-0f1eac99693f
-- title:
--   Normalized coordinates and rational scheme points
-- statement:
--   Defines scheme sections from affine-chart points, the double-chart localizations and transition maps, field evaluations of homogeneous charts, first-nonzero-coordinate normalization, and recovery of chart points from coefficient-preserving maps. It culminates in an equivalence between normalized homogeneous solutions of the canonical quadric–cubic equations and $K$-rational scheme sections, bridging executable point enumeration and scheme-theoretic points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalSchemePoints
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_NormalizedProjectiveCoordinates
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Scheme sections of the literal canonical Proj correspond to normalized projective points through the four affine charts. -/

noncomputable section

universe u

namespace N25.Endgame

open AlgebraicGeometry CategoryTheory N25

variable (K : Type u) [Field K]

/-- Evaluation at any affine chart point gives a section of the selected projective structure map. -/
def canonicalSchemePointOfChart25 (i : Fin 4) (P : CanonicalChartPoint25 K i) :
    CanonicalSchemePoint25 K :=
  ⟨Spec.map (CommRingCat.ofHom (canonicalChartEvaluation25 P).toRingHom) ≫ canonicalChartι25 K i, by
    rw [Category.assoc, canonicalChartι25_toSpec, ← Spec.map_comp]
    have hc : CommRingCat.ofHom (algebraMap K (CanonicalChartRing25 K i)) ≫
        CommRingCat.ofHom (canonicalChartEvaluation25 P).toRingHom = 𝟙 (CommRingCat.of K) := by
      ext a
      exact (canonicalChartEvaluation25 P).commutes a
    rw [hc]
    exact Spec.map_id _⟩

theorem canonicalSchemePointOfChart25_val (i : Fin 4) (P : CanonicalChartPoint25 K i) :
    (canonicalSchemePointOfChart25 K i P).val =
      Spec.map (CommRingCat.ofHom (canonicalChartEvaluation25 P).toRingHom) ≫ canonicalChartι25 K i := rfl

/-- A normalized canonical vector determines its section through its distinguished pivot chart. -/
def canonicalNormalizedToScheme25 (P : CanonicalPoint25 K) : CanonicalSchemePoint25 K :=
  canonicalSchemePointOfChart25 K (normalizedPivot25 P.val)
    (canonicalChartPointOfHomogeneous25 (normalizedCoordinates25 P.val) (normalizedPivot25 P.val)
      (by rw [normalizedCoordinates25_pivot]; exact one_ne_zero) P.property.1 P.property.2)

end N25.Endgame

namespace N25.CanonicalChartPointMaps25

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable (K : Type u) [Field K]

abbrev chartIntersection (i j : Fin 4) :=
  Away (canonicalConePiece25 K) (canonicalConeCoordinate25 K i * canonicalConeCoordinate25 K j)

abbrev mapFirst (i j : Fin 4) : CanonicalProjChartRing25 K i →+* chartIntersection K i j :=
  awayMap (canonicalConePiece25 K) (canonicalConeCoordinate25_mem K j) rfl

abbrev mapSecond (i j : Fin 4) : CanonicalProjChartRing25 K j →+* chartIntersection K i j :=
  awayMap (canonicalConePiece25 K) (canonicalConeCoordinate25_mem K i) (mul_comm _ _)

theorem crossRatio (i j l : Fin 4) :
    mapSecond K i j (canonicalProjChartCoordinate25 K j l) *
      mapFirst K i j (canonicalProjChartCoordinate25 K i j) =
      mapFirst K i j (canonicalProjChartCoordinate25 K i l) := by
  apply HomogeneousLocalization.val_injective
  simp only [mapFirst, mapSecond, canonicalProjChartCoordinate25, val_mul, awayMap_mk, Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

theorem localizationElement (i j : Fin 4) :
    Away.isLocalizationElem (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j) =
      canonicalProjChartCoordinate25 K i j := by
  apply HomogeneousLocalization.val_injective
  simp [canonicalProjChartCoordinate25, Away.val_mk]

theorem mapScalars (i j : Fin 4) (a : K) :
    mapFirst K i j (algebraMap K (CanonicalProjChartRing25 K i) a) =
      mapSecond K i j (algebraMap K (CanonicalProjChartRing25 K j) a) := by
  change awayMap (canonicalConePiece25 K) _ _
      (fromZeroRingHom (canonicalConePiece25 K) _ (algebraMap K (canonicalConePiece25 K 0) a)) =
    awayMap (canonicalConePiece25 K) _ _
      (fromZeroRingHom (canonicalConePiece25 K) _ (algebraMap K (canonicalConePiece25 K 0) a))
  rw [awayMap_fromZeroRingHom, awayMap_fromZeroRingHom]

variable (a : Fin 4 → K) (i j : Fin 4) (hj : IsUnit (a j))
  (ψi : CanonicalProjChartRing25 K i →ₐ[K] K)
  (hψi : ∀ l, ψi (canonicalProjChartCoordinate25 K i l) * a i = a l)

include hj hψi in
theorem ratioIsUnit : IsUnit (ψi (canonicalProjChartCoordinate25 K i j)) := by
  have h : IsUnit (ψi (canonicalProjChartCoordinate25 K i j) * a i) := by rw [hψi]; exact hj
  exact (IsUnit.mul_iff.mp h).1

include hj hψi in
theorem elementIsUnit :
    IsUnit (ψi.toRingHom (Away.isLocalizationElem
      (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j))) := by
  rw [localizationElement]
  exact ratioIsUnit K a i j hj ψi hψi

noncomputable def liftIntersection (a : Fin 4 → K) (i j : Fin 4) (hj : IsUnit (a j))
    (ψi : CanonicalProjChartRing25 K i →ₐ[K] K)
    (hψi : ∀ l, ψi (canonicalProjChartCoordinate25 K i l) * a i = a l) :
    chartIntersection K i j →+* K :=
  letI := (mapFirst K i j).toAlgebra
  letI := Away.isLocalization_mul (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j)
    (rfl : canonicalConeCoordinate25 K i * canonicalConeCoordinate25 K j = _)
    (by decide : (1 : ℕ) ≠ 0)
  IsLocalization.Away.lift (Away.isLocalizationElem
    (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j))
    (g := ψi.toRingHom) (elementIsUnit K a i j hj ψi hψi)

theorem liftFirst (z : CanonicalProjChartRing25 K i) :
    liftIntersection K a i j hj ψi hψi (mapFirst K i j z) = ψi z := by
  letI := (mapFirst K i j).toAlgebra
  letI := Away.isLocalization_mul (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j)
    (rfl : canonicalConeCoordinate25 K i * canonicalConeCoordinate25 K j = _) (by decide : (1 : ℕ) ≠ 0)
  exact IsLocalization.Away.lift_eq
    (S := chartIntersection K i j)
    (Away.isLocalizationElem (canonicalConeCoordinate25_mem K i) (canonicalConeCoordinate25_mem K j))
    (elementIsUnit K a i j hj ψi hψi) z

theorem liftSecondRatio
    (ψj : CanonicalProjChartRing25 K j →ₐ[K] K)
    (hψj : ∀ l, ψj (canonicalProjChartCoordinate25 K j l) * a j = a l) (l : Fin 4) :
    liftIntersection K a i j hj ψi hψi (mapSecond K i j (canonicalProjChartCoordinate25 K j l)) =
      ψj (canonicalProjChartCoordinate25 K j l) := by
  rw [← hj.mul_left_inj, hψj l]
  have hk : liftIntersection K a i j hj ψi hψi
      (mapSecond K i j (canonicalProjChartCoordinate25 K j l)) *
      (ψi (canonicalProjChartCoordinate25 K i j) * a i) = a l := by
    rw [← mul_assoc, ← liftFirst K a i j hj ψi hψi (canonicalProjChartCoordinate25 K i j),
      ← map_mul, crossRatio, liftFirst, hψi]
  rwa [hψi j] at hk

theorem liftSecond
    (ψj : CanonicalProjChartRing25 K j →ₐ[K] K)
    (hψj : ∀ l, ψj (canonicalProjChartCoordinate25 K j l) * a j = a l)
    (z : CanonicalProjChartRing25 K j) :
    liftIntersection K a i j hj ψi hψi (mapSecond K i j z) = ψj z := by
  obtain ⟨r, rfl⟩ := canonicalAffineToProjChart25_surjective K j z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (canonicalChartIdeal25 K j) r
  change liftIntersection K a i j hj ψi hψi (mapSecond K i j (canonicalRatioPolynomialMap25 K j p)) =
    ψj (canonicalRatioPolynomialMap25 K j p)
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [show canonicalRatioPolynomialMap25 K j (MvPolynomial.C r) =
        algebraMap K (CanonicalProjChartRing25 K j) r from (canonicalRatioPolynomialMap25 K j).commutes r]
      rw [← mapScalars, liftFirst, AlgHom.commutes, AlgHom.commutes]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p l hp =>
      simp only [map_mul, hp, canonicalRatioPolynomialMap25_X, liftSecondRatio K a i j hj ψi hψi ψj hψj]

include hj hψi in
theorem chartSpecMap_eq
    (ψj : CanonicalProjChartRing25 K j →ₐ[K] K)
    (hψj : ∀ l, ψj (canonicalProjChartCoordinate25 K j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫ Proj.awayι (canonicalConePiece25 K)
        (canonicalConeCoordinate25 K i) (canonicalConeCoordinate25_mem K i) (by decide) =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫ Proj.awayι (canonicalConePiece25 K)
        (canonicalConeCoordinate25 K j) (canonicalConeCoordinate25_mem K j) (by decide) := by
  have hfi : ψi.toRingHom = (liftIntersection K a i j hj ψi hψi).comp (mapFirst K i j) :=
    RingHom.ext fun z => (liftFirst K a i j hj ψi hψi z).symm
  have hfj : ψj.toRingHom = (liftIntersection K a i j hj ψi hψi).comp (mapSecond K i j) :=
    RingHom.ext fun z => (liftSecond K a i j hj ψi hψi ψj hψj z).symm
  rw [hfi, hfj, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
    Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap (canonicalConePiece25 K) _ _)) ≫
      Proj.awayι (canonicalConePiece25 K) _ _ _ =
    Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap (canonicalConePiece25 K) _ _)) ≫
      Proj.awayι (canonicalConePiece25 K) _ _ _
  rw [Proj.SpecMap_awayMap_awayι (canonicalConePiece25 K) (canonicalConeCoordinate25_mem K i)
      (by decide : 0 < (1 : ℕ)) (canonicalConeCoordinate25_mem K j) rfl,
    Proj.SpecMap_awayMap_awayι (canonicalConePiece25 K) (canonicalConeCoordinate25_mem K j)
      (by decide : 0 < (1 : ℕ)) (canonicalConeCoordinate25_mem K i) (mul_comm _ _)]

end N25.CanonicalChartPointMaps25

namespace N25.Endgame

open AlgebraicGeometry CategoryTheory N25 HomogeneousLocalization

variable (K : Type u) [Field K]

/-- Evaluation of the actual homogeneous chart through its literal affine presentation. -/
def canonicalChartToField25 (i : Fin 4) (P : CanonicalChartPoint25 K i) :
    CanonicalProjChartRing25 K i →ₐ[K] K :=
  (canonicalChartEvaluation25 P).comp (canonicalChartAlgEquiv25 K i).symm.toAlgHom

@[simp] theorem canonicalChartToField25_coordinate (i : Fin 4) (P : CanonicalChartPoint25 K i) (j : Fin 4) :
    canonicalChartToField25 K i P (canonicalProjChartCoordinate25 K i j) = P.coordinates j := by
  unfold canonicalChartToField25
  rw [AlgHom.comp_apply]
  change canonicalChartEvaluation25 P
    ((canonicalChartAlgEquiv25 K i).symm (canonicalProjChartCoordinate25 K i j)) = _
  rw [← canonicalChartAlgEquiv25_coordinate K i j, AlgEquiv.symm_apply_apply]
  change MvPolynomial.aeval P.coordinates (MvPolynomial.X j) = P.coordinates j
  exact MvPolynomial.aeval_X _ _

theorem canonicalSchemePointOfChart25_homogeneous_val (i : Fin 4) (P : CanonicalChartPoint25 K i) :
    (canonicalSchemePointOfChart25 K i P).val =
      Spec.map (CommRingCat.ofHom (canonicalChartToField25 K i P).toRingHom) ≫
        Proj.awayι (canonicalConePiece25 K) (canonicalConeCoordinate25 K i)
          (canonicalConeCoordinate25_mem K i) (by decide) := by
  rw [canonicalSchemePointOfChart25_val, canonicalChartι25, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem canonicalChartToField25_homogeneous_coordinate
    (v : Fin 4 → K) (hq : canonicalQuadric (v 0) (v 1) (v 2) (v 3) = 0)
    (hc : canonicalCubic (v 0) (v 1) (v 2) (v 3) = 0) (i : Fin 4) (hi : v i ≠ 0) (j : Fin 4) :
    canonicalChartToField25 K i (canonicalChartPointOfHomogeneous25 v i hi hq hc)
      (canonicalProjChartCoordinate25 K i j) * v i = v j := by
  rw [canonicalChartToField25_coordinate]
  change ((v i)⁻¹ * v j) * v i = v j
  calc
    _ = ((v i)⁻¹ * v i) * v j := by ring
    _ = _ := by rw [inv_mul_cancel₀ hi, one_mul]

/-- A nonzero homogeneous canonical vector gives the same section in every available chart. -/
theorem canonicalSchemePointOfHomogeneous25_eq
    (v : Fin 4 → K) (hq : canonicalQuadric (v 0) (v 1) (v 2) (v 3) = 0)
    (hc : canonicalCubic (v 0) (v 1) (v 2) (v 3) = 0)
    (i j : Fin 4) (hi : v i ≠ 0) (hj : v j ≠ 0) :
    canonicalSchemePointOfChart25 K i (canonicalChartPointOfHomogeneous25 v i hi hq hc) =
      canonicalSchemePointOfChart25 K j (canonicalChartPointOfHomogeneous25 v j hj hq hc) := by
  apply Subtype.ext
  rw [canonicalSchemePointOfChart25_homogeneous_val, canonicalSchemePointOfChart25_homogeneous_val]
  exact CanonicalChartPointMaps25.chartSpecMap_eq K v i j (isUnit_iff_ne_zero.mpr hj)
    (canonicalChartToField25 K i (canonicalChartPointOfHomogeneous25 v i hi hq hc))
    (canonicalChartToField25_homogeneous_coordinate K v hq hc i hi)
    (canonicalChartToField25 K j (canonicalChartPointOfHomogeneous25 v j hj hq hc))
    (canonicalChartToField25_homogeneous_coordinate K v hq hc j hj)

/-- The forward normalized-point map has the prescribed value on every nonzero coordinate chart. -/
theorem canonicalNormalizedToScheme25_on_chart (P : CanonicalPoint25 K) (i : Fin 4)
    (hi : normalizedCoordinates25 P.val i ≠ 0) :
    canonicalNormalizedToScheme25 K P =
      canonicalSchemePointOfChart25 K i
        (canonicalChartPointOfHomogeneous25 (normalizedCoordinates25 P.val) i hi
          P.property.1 P.property.2) := by
  exact canonicalSchemePointOfHomogeneous25_eq K _ P.property.1 P.property.2 _ i
    (by rw [normalizedCoordinates25_pivot]; exact one_ne_zero) hi

/-- The unique point of Spec K, written with its zero prime ideal. -/
def canonicalSpecPoint25 : Spec (CommRingCat.of K) := ⟨⊥, inferInstance⟩

/-- The value of an affine chart section belongs to the j-th open exactly when its j-th coordinate is nonzero. -/
theorem canonicalSchemePointOfChart25_mem_basicOpen (i : Fin 4) (P : CanonicalChartPoint25 K i) (j : Fin 4) :
    (canonicalSchemePointOfChart25 K i P).val (canonicalSpecPoint25 K) ∈ canonicalProjChartOpen25 K j ↔
      P.coordinates j ≠ 0 := by
  change canonicalSpecPoint25 K ∈
    (canonicalSchemePointOfChart25 K i P).val ⁻¹ᵁ canonicalProjChartOpen25 K j ↔ _
  rw [canonicalSchemePointOfChart25_homogeneous_val, Scheme.Hom.comp_preimage,
    canonicalProjChartOpen25, Proj.awayι_preimage_basicOpen (𝒜 := canonicalConePiece25 K)
      (canonicalConeCoordinate25_mem K i) (by decide : 0 < (1 : ℕ))
      (canonicalConeCoordinate25_mem K j) (by decide : 0 < (1 : ℕ)),
    CanonicalChartPointMaps25.localizationElement]
  change canonicalChartToField25 K i P (canonicalProjChartCoordinate25 K i j) ∉ (⊥ : Ideal K) ↔ _
  rw [canonicalChartToField25_coordinate, Ideal.mem_bot]

end N25.Endgame

namespace N25.Endgame

open N25 MazurProof.RationalPointsN25QuotientWeil

variable (K : Type u) [Field K]

/-- Normalize at the first nonzero coordinate, in the fixed four-constructor carrier. -/
def normalizeProjectiveVector25 (v : Fin 4 → K) : NormalizedProjective4 K := by
  classical
  exact if v 0 ≠ 0 then .xChart ((v 0)⁻¹*v 1) ((v 0)⁻¹*v 2) ((v 0)⁻¹*v 3)
  else if v 1 ≠ 0 then .yChart ((v 1)⁻¹*v 2) ((v 1)⁻¹*v 3)
  else if v 2 ≠ 0 then .zChart ((v 2)⁻¹*v 3)
  else .wChart

theorem normalizeProjectiveVector25_pivot_nonzero (v : Fin 4 → K) (hv : ∃ i, v i ≠ 0) :
    v (normalizedPivot25 (normalizeProjectiveVector25 K v)) ≠ 0 := by
  classical
  unfold normalizeProjectiveVector25
  split_ifs with hzero hone htwo
  · exact hzero
  · exact hone
  · exact htwo
  · change v 3 ≠ 0
    intro hthree
    obtain ⟨j, hj⟩ := hv
    fin_cases j <;> simp_all

/-- Every normalized coordinate is obtained by one common nonzero scalar division. -/
theorem normalizeProjectiveVector25_coordinates (v : Fin 4 → K) (hv : ∃ i, v i ≠ 0) (j : Fin 4) :
    normalizedCoordinates25 (normalizeProjectiveVector25 K v) j =
      (v (normalizedPivot25 (normalizeProjectiveVector25 K v)))⁻¹ * v j := by
  classical
  have hn := normalizeProjectiveVector25_pivot_nonzero K v hv
  classical
  unfold normalizeProjectiveVector25
  split_ifs with hzero hone htwo <;> fin_cases j <;>
    simp_all [normalizedCoordinates25, normalizedPivot25, normalizeProjectiveVector25]

/-- Normalization is unchanged by multiplying all coordinates by one nonzero scalar. -/
theorem normalizeProjectiveVector25_smul (v : Fin 4 → K) (r : K) (hr : r ≠ 0) :
    normalizeProjectiveVector25 K (fun j => r*v j) = normalizeProjectiveVector25 K v := by
  have hc (j : Fin 4) : r*v j ≠ 0 ↔ v j ≠ 0 := by simp [hr]
  have hm (i j : Fin 4) : (r*v i)⁻¹*(r*v j) = (v i)⁻¹*v j := by
    rw [mul_inv_rev]
    calc
      _ = (v i)⁻¹*((r⁻¹*r)*v j) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hr, one_mul]
  classical
  simp only [normalizeProjectiveVector25, hm]
  by_cases hzero : v 0 ≠ 0
  · rw [if_pos ((hc 0).mpr hzero), if_pos hzero]
  · rw [if_neg (fun h => hzero ((hc 0).mp h)), if_neg hzero]
    by_cases hone : v 1 ≠ 0
    · rw [if_pos ((hc 1).mpr hone), if_pos hone]
    · rw [if_neg (fun h => hone ((hc 1).mp h)), if_neg hone]
      by_cases htwo : v 2 ≠ 0
      · rw [if_pos ((hc 2).mpr htwo), if_pos htwo]
      · rw [if_neg (fun h => htwo ((hc 2).mp h)), if_neg htwo]

theorem normalizeProjectiveVector25_of_normalized (P : NormalizedProjective4 K) :
    normalizeProjectiveVector25 K (normalizedCoordinates25 P) = P := by
  classical
  cases P <;> simp [normalizeProjectiveVector25, normalizedCoordinates25]

/-- Normalize an actual nonzero vector satisfying both literal homogeneous equations. -/
def normalizeCanonicalVector25 (v : Fin 4 → K) (hv : ∃ i, v i ≠ 0)
    (hq : canonicalQuadric (v 0) (v 1) (v 2) (v 3) = 0)
    (hc : canonicalCubic (v 0) (v 1) (v 2) (v 3) = 0) : CanonicalPoint25 K := by
  refine ⟨normalizeProjectiveVector25 K v, ?_, ?_⟩
  · change canonicalQuadric (normalizedCoordinates25 _ 0) (normalizedCoordinates25 _ 1)
      (normalizedCoordinates25 _ 2) (normalizedCoordinates25 _ 3) = 0
    simp only [normalizeProjectiveVector25_coordinates K v hv]
    let r := (v (normalizedPivot25 (normalizeProjectiveVector25 K v)))⁻¹
    change canonicalQuadric (r*v 0) (r*v 1) (r*v 2) (r*v 3) = 0
    calc
      _ = r^2*canonicalQuadric (v 0) (v 1) (v 2) (v 3) := by unfold canonicalQuadric; ring
      _ = 0 := by rw [hq, mul_zero]
  · change canonicalCubic (normalizedCoordinates25 _ 0) (normalizedCoordinates25 _ 1)
      (normalizedCoordinates25 _ 2) (normalizedCoordinates25 _ 3) = 0
    simp only [normalizeProjectiveVector25_coordinates K v hv]
    let r := (v (normalizedPivot25 (normalizeProjectiveVector25 K v)))⁻¹
    change canonicalCubic (r*v 0) (r*v 1) (r*v 2) (r*v 3) = 0
    calc
      _ = r^3*canonicalCubic (v 0) (v 1) (v 2) (v 3) := by unfold canonicalCubic; ring
      _ = 0 := by rw [hc, mul_zero]

end N25.Endgame

namespace N25.Endgame

open AlgebraicGeometry CategoryTheory N25

variable (K : Type u) [Field K]

/-- Recover all affine coordinates from a coefficient-preserving map into the base field. -/
def canonicalChartPointOfAlgHom25 (i : Fin 4) (f : CanonicalChartRing25 K i →ₐ[K] K) :
    CanonicalChartPoint25 K i where
  coordinates j := f (Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j))
  quadric := by
    have h : Ideal.Quotient.mk (canonicalChartIdeal25 K i)
        (canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hh := congrArg f h
    simpa only [canonicalQuadric, map_sub, map_add, map_mul, map_neg, map_pow, map_zero] using hh
  cubic := by
    have h : Ideal.Quotient.mk (canonicalChartIdeal25 K i)
        (canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hh := congrArg f h
    simpa only [canonicalCubic, map_sub, map_add, map_mul, map_pow, map_zero] using hh
  pivot := by
    have h : Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X i - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hx : Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X i) = 1 := by
      apply sub_eq_zero.mp
      simpa only [map_sub, map_one] using h
    exact (congrArg f hx).trans (map_one f)

@[simp] theorem canonicalChartEvaluation25_pointOfAlgHom (i : Fin 4) (f : CanonicalChartRing25 K i →ₐ[K] K) :
    canonicalChartEvaluation25 (canonicalChartPointOfAlgHom25 K i f) = f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  simp [canonicalChartEvaluation25, canonicalChartPointOfAlgHom25,
    Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]

/-- Every actual scheme section factors through one of the four literal affine charts. -/
theorem canonicalSchemePoint25_chart_exists (s : CanonicalSchemePoint25 K) :
    ∃ (i : Fin 4) (P : CanonicalChartPoint25 K i), canonicalSchemePointOfChart25 K i P = s := by
  have hx : s.val (canonicalSpecPoint25 K) ∈ (⨆ i : Fin 4, canonicalProjChartOpen25 K i) := by
    rw [canonicalProjChartOpen25_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  letI := canonicalChartι25_isOpenImmersion K i
  have hr : Set.range s.val ⊆ Set.range (canonicalChartι25 K i) := by
    rintro y ⟨x, rfl⟩
    change s.val x ∈ (canonicalChartι25 K i).opensRange
    rw [canonicalChartι25_opensRange]
    simpa only [Subsingleton.elim x (canonicalSpecPoint25 K)] using hi
  let l := IsOpenImmersion.lift (canonicalChartι25 K i) s.val hr
  have hl : l ≫ canonicalChartι25 K i = s.val := IsOpenImmersion.lift_fac _ _ _
  have hlbase : l ≫ Spec.map (CommRingCat.ofHom (algebraMap K (CanonicalChartRing25 K i))) = 𝟙 _ := by
    rw [← canonicalChartι25_toSpec, ← Category.assoc, hl]
    exact s.property
  let φ := (Spec.preimage l).hom
  have hs : Spec.map (CommRingCat.ofHom φ) = l := Spec.map_preimage l
  have hcat : CommRingCat.ofHom (algebraMap K (CanonicalChartRing25 K i)) ≫ Spec.preimage l =
      𝟙 (CommRingCat.of K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact hlbase
  let f : CanonicalChartRing25 K i →ₐ[K] K :=
    { toRingHom := φ
      commutes' := fun a => congrArg
        (fun q : CommRingCat.of K ⟶ CommRingCat.of K => q.hom a) hcat }
  refine ⟨i, canonicalChartPointOfAlgHom25 K i f, ?_⟩
  apply Subtype.ext
  rw [canonicalSchemePointOfChart25_val, canonicalChartEvaluation25_pointOfAlgHom]
  change Spec.map (CommRingCat.ofHom φ) ≫ canonicalChartι25 K i = _
  rw [hs, hl]

end N25.Endgame

namespace N25.Endgame

open AlgebraicGeometry CategoryTheory N25

variable (K : Type u) [Field K]

theorem canonicalChartPoint25_ext {i : Fin 4} (P Q : CanonicalChartPoint25 K i)
    (h : P.coordinates = Q.coordinates) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Normalize the nonzero coordinate vector of an arbitrary affine chart point. -/
def normalizeCanonicalChartPoint25 (i : Fin 4) (P : CanonicalChartPoint25 K i) : CanonicalPoint25 K :=
  normalizeCanonicalVector25 K P.coordinates ⟨i, by rw [P.pivot]; exact one_ne_zero⟩ P.quadric P.cubic

theorem canonicalNormalizedToScheme25_normalizeChart (i : Fin 4) (P : CanonicalChartPoint25 K i) :
    canonicalNormalizedToScheme25 K (normalizeCanonicalChartPoint25 K i P) =
      canonicalSchemePointOfChart25 K i P := by
  let v := P.coordinates
  have hv : ∃ j, v j ≠ 0 := ⟨i, by change P.coordinates i ≠ 0; rw [P.pivot]; exact one_ne_zero⟩
  let Q := normalizeCanonicalChartPoint25 K i P
  have hi : normalizedCoordinates25 Q.val i ≠ 0 := by
    change normalizedCoordinates25 (normalizeProjectiveVector25 K v) i ≠ 0
    rw [normalizeProjectiveVector25_coordinates K v hv i]
    change _ * P.coordinates i ≠ 0
    rw [P.pivot, mul_one]
    exact inv_ne_zero (normalizeProjectiveVector25_pivot_nonzero K v hv)
  have hP : canonicalChartPointOfHomogeneous25 (normalizedCoordinates25 Q.val) i hi
      Q.property.1 Q.property.2 = P := by
    apply canonicalChartPoint25_ext K
    funext j
    change (normalizedCoordinates25 (normalizeProjectiveVector25 K v) i)⁻¹ *
      normalizedCoordinates25 (normalizeProjectiveVector25 K v) j = v j
    rw [normalizeProjectiveVector25_coordinates K v hv i, normalizeProjectiveVector25_coordinates K v hv j]
    have hvi : v i = 1 := P.pivot
    rw [hvi, mul_one]
    exact inv_mul_cancel_left₀ (inv_ne_zero (normalizeProjectiveVector25_pivot_nonzero K v hv)) _
  exact (canonicalNormalizedToScheme25_on_chart K Q i hi).trans (congrArg (canonicalSchemePointOfChart25 K i) hP)

theorem canonicalNormalizedToScheme25_surjective : Function.Surjective (canonicalNormalizedToScheme25 K) := by
  intro s
  obtain ⟨i, P, hp⟩ := canonicalSchemePoint25_chart_exists K s
  exact ⟨normalizeCanonicalChartPoint25 K i P, (canonicalNormalizedToScheme25_normalizeChart K i P).trans hp⟩

theorem canonicalNormalizedToScheme25_mem_basicOpen (P : CanonicalPoint25 K) (i : Fin 4) :
    (canonicalNormalizedToScheme25 K P).val (canonicalSpecPoint25 K) ∈ canonicalProjChartOpen25 K i ↔
      normalizedCoordinates25 P.val i ≠ 0 := by
  unfold canonicalNormalizedToScheme25
  rw [canonicalSchemePointOfChart25_mem_basicOpen]
  change (normalizedCoordinates25 P.val (normalizedPivot25 P.val))⁻¹ * normalizedCoordinates25 P.val i ≠ 0 ↔ _
  rw [normalizedCoordinates25_pivot, inv_one, one_mul]

theorem canonicalNormalizedToScheme25_injective : Function.Injective (canonicalNormalizedToScheme25 K) := by
  intro P Q h
  let i := normalizedPivot25 P.val
  have hiP : normalizedCoordinates25 P.val i ≠ 0 := by
    change normalizedCoordinates25 P.val (normalizedPivot25 P.val) ≠ 0
    rw [normalizedCoordinates25_pivot]
    exact one_ne_zero
  have hmP := (canonicalNormalizedToScheme25_mem_basicOpen K P i).mpr hiP
  have hmQ : (canonicalNormalizedToScheme25 K Q).val (canonicalSpecPoint25 K) ∈ canonicalProjChartOpen25 K i := by
    rwa [h] at hmP
  have hiQ := (canonicalNormalizedToScheme25_mem_basicOpen K Q i).mp hmQ
  let CP := canonicalChartPointOfHomogeneous25 (normalizedCoordinates25 P.val) i hiP P.property.1 P.property.2
  let CQ := canonicalChartPointOfHomogeneous25 (normalizedCoordinates25 Q.val) i hiQ Q.property.1 Q.property.2
  have hs := congrArg Subtype.val h
  rw [canonicalNormalizedToScheme25_on_chart K P i hiP, canonicalNormalizedToScheme25_on_chart K Q i hiQ,
    canonicalSchemePointOfChart25_val, canonicalSchemePointOfChart25_val] at hs
  letI := canonicalChartι25_isOpenImmersion K i
  have he : Spec.map (CommRingCat.ofHom (canonicalChartEvaluation25 CP).toRingHom) =
      Spec.map (CommRingCat.ofHom (canonicalChartEvaluation25 CQ).toRingHom) :=
    (cancel_mono (canonicalChartι25 K i)).mp hs
  have hcat := Spec.map_injective he
  have hev : (canonicalChartEvaluation25 CP).toRingHom = (canonicalChartEvaluation25 CQ).toRingHom :=
    congrArg (fun f : CommRingCat.of (CanonicalChartRing25 K i) ⟶ CommRingCat.of K => f.hom) hcat
  have hcoords : CP.coordinates = CQ.coordinates := by
    funext j
    have hh := congrArg (fun f : CanonicalChartRing25 K i →+* K =>
      f (Ideal.Quotient.mk (canonicalChartIdeal25 K i) (MvPolynomial.X j))) hev
    change MvPolynomial.aeval CP.coordinates (MvPolynomial.X j) =
      MvPolynomial.aeval CQ.coordinates (MvPolynomial.X j) at hh
    simpa only [MvPolynomial.aeval_X] using hh
  apply Subtype.ext
  calc
    P.val = normalizeProjectiveVector25 K CP.coordinates := by
      have hp : CP.coordinates = normalizedCoordinates25 P.val := by
        funext j
        change (normalizedCoordinates25 P.val (normalizedPivot25 P.val))⁻¹*normalizedCoordinates25 P.val j = _
        rw [normalizedCoordinates25_pivot, inv_one, one_mul]
      rw [hp, normalizeProjectiveVector25_of_normalized]
    _ = normalizeProjectiveVector25 K CQ.coordinates := congrArg (normalizeProjectiveVector25 K) hcoords
    _ = Q.val := by
      change normalizeProjectiveVector25 K (fun j => (normalizedCoordinates25 Q.val i)⁻¹ *
        normalizedCoordinates25 Q.val j) = Q.val
      rw [normalizeProjectiveVector25_smul K _ _ (inv_ne_zero hiQ), normalizeProjectiveVector25_of_normalized]

/-- Full rational scheme sections are exactly the fixed normalized homogeneous point carrier. -/
def canonicalNormalizedSchemePointEquiv25 : CanonicalPoint25 K ≃ CanonicalSchemePoint25 K :=
  Equiv.ofBijective (canonicalNormalizedToScheme25 K)
    ⟨canonicalNormalizedToScheme25_injective K, canonicalNormalizedToScheme25_surjective K⟩

end N25.Endgame


