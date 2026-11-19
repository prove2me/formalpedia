-- Prove2me | Definitions.Def_RPLib_S4_CDPack28b
-- name    : RPLib_S4_CDPack28b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:45:09.535307+00:00
-- url     : https://prove2.me/theorems/79f05de1-2c5d-4055-a07f-6733378416d1
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 28b of 71
-- statement:
--   Part 28b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack28

/-!
# Curve-duality library package, part 28b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Nu =====
section

/-!
# S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`

For choice data `D : NuData K F d` (`N = d + g`), `D.Rg = Sym^d(B)[1/good]` is the coordinate ring of the basic
open `D(good)`. At a point `x` of it with image `y = yOf x` in `Sym^d`, `A = liftTuple y` are `d` distinct
points, `s = sec y` spans `L(N P∞ - A)` and has `N` simple zeros `zeroFin s ⊇ A`; `ν(A) = Z(s) - A` is the
finset `nuSet x` of `g` points. The norms `N(w)(ν(A)) = ∏_{P ∈ ν(A)} w(P)` are the regular functions
`nrm w = (-1)^g coeff_0 ((Δ_1⁻¹ Δ_{X-w}) /ₘ ∏_{i}(X - w(a_i)))` on `D(good)` (`apply_nrm`), so the morphism
criterion (`liftPts`) gives `nuMap : Sym^g(B) →ₐ D.Rg` with points `nuPt x = ν(A)` (`comp_nuMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

/-- Value at a point of `(-1)^#T coeff_0 ((u⁻¹ P) /ₘ M)` when `P = u ∏_Z (X - v)` and `M = ∏_a (X - v)` there. -/
theorem apply_divByMonic_coeff {k R ι : Type*} [Field k] [CommRing R] [Algebra k R] [DecidableEq ι]
    (x : R →ₐ[k] k) (u : Rˣ) (P M : R[X]) (hM : M.Monic) (Z : Finset ι) {n : ℕ} (a : Fin n → ι)
    (ha : Function.Injective a) (haZ : ∀ i, a i ∈ Z) (v : ι → k)
    (hP : P.map x.toRingHom = C (x u) * ∏ φ ∈ Z, (X - C (v φ)))
    (hMx : M.map x.toRingHom = ∏ i, (X - C (v (a i)))) :
    x ((-1) ^ (Z \ Finset.univ.image a).card * ((C (↑u⁻¹ : R) * P) /ₘ M).coeff 0) =
      ∏ φ ∈ Z \ Finset.univ.image a, v φ := by
  have h1 : x.toRingHom ↑u⁻¹ * x u = 1 := by
    change x ↑u⁻¹ * x u = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hP' : (C (↑u⁻¹ : R) * P).map x.toRingHom = ∏ φ ∈ Z, (X - C (v φ)) := by
    rw [Polynomial.map_mul, Polynomial.map_C, hP, ← mul_assoc, ← C_mul, h1, C_1, one_mul]
  have hc : x (((C (↑u⁻¹ : R) * P) /ₘ M).coeff 0) =
      (((C (↑u⁻¹ : R) * P) /ₘ M).map x.toRingHom).coeff 0 := (Polynomial.coeff_map _ _).symm
  rw [map_mul, map_pow, map_neg, map_one, hc, Polynomial.map_divByMonic _ hM, hP', hMx,
    prod_divByMonic_sdiff Z a ha haZ v]
  exact (prod_eq_sign_coeff_zero _ v).symm

section Nu

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- The coordinate ring of the good open `D(good) ⊂ Sym^d`. -/
abbrev Rg : Type _ := Localization.Away D.good

instance (priority := high) finiteType_Rg : Algebra.FiniteType K D.Rg := finiteType_away D.good

/-- The point of `Sym^d` below a point of `D(good)`. -/
noncomputable def yOf (x : D.Rg →ₐ[K] K) : SymRing K (Places.Rfin K F) d →ₐ[K] K :=
  x.comp (IsScalarTower.toAlgHom K _ D.Rg)

theorem yOf_apply (x : D.Rg →ₐ[K] K) (s : SymRing K (Places.Rfin K F) d) :
    D.yOf x s = x (algebraMap _ D.Rg s) := rfl

theorem yOf_good (x : D.Rg →ₐ[K] K) : D.yOf x D.good ≠ 0 := by
  rw [yOf_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := D.Rg) D.good).map x).ne_zero

/-- Every point of `Sym^d` with `good ≠ 0` lies below a point of `D(good)`. -/
theorem exists_yOf (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) (hy : y D.good ≠ 0) :
    ∃ x : D.Rg →ₐ[K] K, D.yOf x = y := by
  have hf : ∀ m : Submonoid.powers D.good, IsUnit (y m) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (y (D.good ^ n))
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr hy).pow n
  refine ⟨IsLocalization.liftAlgHom (S := D.Rg) hf, ?_⟩
  ext s
  rw [yOf_apply, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem isUnit_pres (w : Places.Rfin K F) : IsUnit (algebraMap _ D.Rg (D.pres w)) :=
  isUnit_of_forall_ne_zero (k := K) _ fun x => pres_ne_zero (D.yOf_good x) w

theorem apply_inv_mul (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    x ↑(D.isUnit_pres w).unit⁻¹ * D.yOf x (D.pres w) = 1 := by
  rw [yOf_apply, ← map_mul, IsUnit.val_inv_mul, map_one]

/-- The regular function `N(w) ∘ ν` on `D(good)`. -/
noncomputable def nrm (w : Places.Rfin K F) : D.Rg :=
  (-1) ^ genusFK K F * ((C (↑(D.isUnit_pres w).unit⁻¹ : D.Rg) * (D.det w).map (algebraMap _ D.Rg)) /ₘ
    (monPoly (k := K) (g := d) w).map (algebraMap _ D.Rg)).coeff 0

open Classical in
/-- `ν(A) = Z(s) - A` at the point `x` of `D(good)`. -/
noncomputable def nuSet (x : D.Rg →ₐ[K] K) : Finset (Places.Rfin K F →ₐ[K] K) :=
  zeroFin (k := K) (D.sec (D.yOf x)) \ Finset.univ.image (liftTuple (D.yOf x))

theorem image_sub_zeroFin (x : D.Rg →ₐ[K] K) [DecidableEq (Places.Rfin K F →ₐ[K] K)] :
    Finset.univ.image (liftTuple (D.yOf x)) ⊆ zeroFin (k := K) (D.sec (D.yOf x)) := by
  intro φ hφ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hφ
  exact lift_mem_zeroFin (D.yOf_good x) i

theorem card_nuSet (x : D.Rg →ₐ[K] K) : (D.nuSet x).card = genusFK K F := by
  classical
  have hy := D.yOf_good x
  rw [nuSet, Finset.card_sdiff_of_subset (D.image_sub_zeroFin x), (zero_spec hy).2.1,
    Finset.card_image_of_injective _ (injective_lift hy), Finset.card_univ, Fintype.card_fin]
  omega

theorem mem_nuSet (x : D.Rg →ₐ[K] K) (φ : Places.Rfin K F →ₐ[K] K) :
    φ ∈ D.nuSet x ↔ φ (D.sec (D.yOf x)) = 0 ∧ ∀ i, liftTuple (D.yOf x) i ≠ φ := by
  classical
  rw [nuSet, Finset.mem_sdiff, (zero_spec (D.yOf_good x)).1, Finset.mem_image]
  simp only [Finset.mem_univ, true_and, not_exists]

theorem comp_algebraMap (x : D.Rg →ₐ[K] K) :
    x.toRingHom.comp (algebraMap (SymRing K (Places.Rfin K F) d) D.Rg) = (D.yOf x).toRingHom :=
  RingHom.ext fun _ => rfl

theorem map_det_Rg (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    ((D.det w).map (algebraMap _ D.Rg)).map x.toRingHom =
      C (x ↑(D.isUnit_pres w).unit) * ∏ φ ∈ zeroFin (k := K) (D.sec (D.yOf x)), (X - C (φ w)) := by
  rw [Polynomial.map_map, comp_algebraMap, map_det (D.yOf_good x) w, yOf_apply, IsUnit.unit_spec]

theorem map_monPoly_Rg (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    ((monPoly (k := K) (g := d) w).map (algebraMap _ D.Rg)).map x.toRingHom =
      ∏ i, (X - C (liftTuple (D.yOf x) i w)) := by
  have h1 := map_symPt_monPoly (k := K) (liftTuple (D.yOf x)) w
  rw [symPt_liftTuple] at h1
  rw [Polynomial.map_map, comp_algebraMap, h1]

theorem apply_nrm (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) : x (D.nrm w) = ∏ φ ∈ D.nuSet x, φ w := by
  classical
  have hy := D.yOf_good x
  have h := apply_divByMonic_coeff x (D.isUnit_pres w).unit _ _ ((monic_monPoly w).map _) _ _ (injective_lift hy)
    (lift_mem_zeroFin hy) (fun φ => φ w) (D.map_det_Rg x w) (D.map_monPoly_Rg x w)
  have e : zeroFin (k := K) (D.sec (D.yOf x)) \ Finset.univ.image (liftTuple (D.yOf x)) = D.nuSet x := rfl
  rw [e, card_nuSet] at h
  rw [nrm]
  exact h

/-- The point `ν(A) ∈ Sym^g` at the point `x` of `D(good)`. -/
noncomputable def nuPt (x : D.Rg →ₐ[K] K) : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K :=
  symPt (enumF (D.nuSet x) (D.card_nuSet x))

theorem nuPt_normS (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    D.nuPt x (normS K w) = ∏ φ ∈ D.nuSet x, φ w := by
  rw [nuPt, symPt_normS]
  exact prod_enumF (D.nuSet x) (D.card_nuSet x) (fun φ => φ w)

theorem exists_nrm (w : Places.Rfin K F) : ∃ r : D.Rg, ∀ x, x r = D.nuPt x (normS K w) :=
  ⟨D.nrm w, fun x => by rw [apply_nrm, nuPt_normS]⟩

/-- **The negation map** `ν : D(good) → Sym^g`, `A ↦ Z(s_A) - A`. -/
noncomputable def nuMap : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] D.Rg :=
  liftPts D.nuPt D.exists_nrm

theorem comp_nuMap (x : D.Rg →ₐ[K] K) : x.comp D.nuMap = D.nuPt x :=
  comp_liftPts _ _ x

end NuData

end Nu

end RamanujanPetersson.JacLaw

end


