-- Prove2me | Definitions.Def_RPLib_S4_CDPack41w
-- name    : RPLib_S4_CDPack41w
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T14:09:10.963519+00:00
-- url     : https://prove2.me/theorems/239ab4f3-db26-4f90-b418-143ee6adac96
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 41w of 71
-- statement:
--   Part 41w of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack41
import Definitions.Def_RPLib_S4_CDPack41u
import Definitions.Def_RPLib_S4_CDPack41t
import Definitions.Def_RPLib_S4_CDPack41v
import Definitions.Def_RPLib_S4_CDPack36c

/-!
# Curve-duality library package, part 41w of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJVal =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values

* `specO K R`, `kptO x` (the `K`-point of `Spec R` at `x : R →ₐ[K] K`), `SpecMap_closedPoint`.
* `jMap φ : Spec R ⟶ J` (`Spec φ ≫ jX0`); its `K`-points have value `ψ(x ∘ φ)` (`jacPicEquiv_jMap`).
* `ajCls P0 Q = [Q] - [P0] ∈ Pic⁰`, `ajK P0 Q = jacPicEquiv⁻¹ (ajCls P0 Q)`, `ajPt P0 Q` (its point of `J`).
* **`ajMap P0 φ κ = const (κ - [Θ] - [P0]) * (jMap φ)⁻¹`** (group law on `Spec R ⟶ J`), with value
  `ajK P0 Q` at every `K`-point `x` with `ψ(x ∘ φ) = κ - [Θ] - [Q]` (`kptO_ajMap`, `ajMap_kpt`).
* **`ajPiece P0 c0 D c := ajMap P0 (lawMapP c0 D c) (kapP c0 D c)`** on the piece `Spec LocR`: value `ajPt P0 Q`
  (value lemmas for the piece: next file; see NOTES session 19).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section SpecPt

variable {K : Type u} [Field K]

theorem SpecMap_sR {A B : Type u} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ sR K A = sR K B := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap]

variable (K) in
/-- `Spec R` as an object over `Spec K`. -/
noncomputable abbrev specO (R : Type u) [CommRing R] [Algebra K R] : Over (Spec (.of K)) := Over.mk (sR K R)

/-- The `K`-point of `Spec R` at `x : R →ₐ[K] K`. -/
noncomputable def kptO {R : Type u} [CommRing R] [Algebra K R] (x : R →ₐ[K] K) :
    𝟙_ (Over (Spec (.of K))) ⟶ specO K R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (x : R →+* K))) (by
    refine (SpecMap_sR x).trans ?_
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])

theorem SpecMap_closedPoint {A : Type u} [CommRing A] [Algebra K A] (x : A →ₐ[K] K) :
    Spec.map (CommRingCat.ofHom (x : A →+* K)) (IsLocalRing.closedPoint K) = kpt x :=
  PrimeSpectrum.ext (R := A) (Ideal.ext fun a => by
    rw [kpt_asIdeal, RingHom.mem_ker]
    change (x : A →+* K) a ∈ IsLocalRing.maximalIdeal K ↔ _
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    rfl)

end SpecPt

section JMap

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `Spec R → X0 → J` for a `K`-algebra map `φ : LawRing K F → R`. -/
noncomputable def jMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) :
    specO K R ⟶ Jac K F :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : LawRing K F →+* R)) ≫ jX0 K F) (by
    rw [Category.assoc, jX0_over]
    exact SpecMap_sR φ)

theorem kval_jMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (x : R →ₐ[K] K) :
    (lawChunk K F).kval (kptO x ≫ jMap K F φ) =
      (lawChunk K F).lamB (kpt (x.comp φ)) (JacLaw.isClosed_kpt _) := by
  have e : (kptO x ≫ jMap K F φ).left (IsLocalRing.closedPoint K) =
      JacChunk.ι (lawChunk K F).H 1 (kpt (x.comp φ)) := by
    show jX0 K F (Spec.map (CommRingCat.ofHom (φ : LawRing K F →+* R))
      (Spec.map (CommRingCat.ofHom (x : R →+* K)) (IsLocalRing.closedPoint K))) = _
    rw [SpecMap_closedPoint, SpecMap_kpt]
    rfl
  show (lawChunk K F).PtT ((kptO x ≫ jMap K F φ).left (IsLocalRing.closedPoint K)) = _
  rw [e, (lawChunk K F).PtT_ι 1 _ (JacLaw.isClosed_kpt _), (lawChunk K F).lamT_eq _ (JacLaw.isClosed_kpt _),
    ]
  exact one_mul _

/-- The value of `Spec R ⟶ J` at a `K`-point is `ψ(x ∘ φ)`. -/
theorem jacPicEquiv_jMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (x : R →ₐ[K] K) :
    ((Multiplicative.toAdd (jacPicEquiv K F (kptO x ≫ jMap K F φ)) : Pic0K K F) : PicK K F) =
      psiJ K F (kpt (x.comp φ)) := by
  have e : kptEquiv K F (kptO x ≫ jMap K F φ) =
      ⟨(lawChunk K F).lamB (kpt (x.comp φ)) (JacLaw.isClosed_kpt _),
        (lawChunk K F).lamB_mem_H _ (JacLaw.isClosed_kpt _)⟩ :=
    Subtype.ext (kval_jMap K F φ x)
  rw [jacPicEquiv_apply, e]
  exact jacPic0_lamB K F _ _

/-- `[Θ]`. -/
noncomputable abbrev thetaK : PicK K F :=
  clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1)

variable (P0 : Place K F)

/-- **`[Q] - [P0] ∈ Pic⁰`**. -/
noncomputable def ajCls (Q : Place K F) : Pic0K K F :=
  ⟨clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1), by
    rw [← clsK_sub]
    exact clsK_mem_Pic0K K F (by rw [PlacesK.Divisor.deg_sub, deg_single_one, deg_single_one, sub_self])⟩

/-- The `K`-point `jacPicEquiv⁻¹ ([Q] - [P0])` of `J`. -/
noncomputable def ajK (Q : Place K F) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd (ajCls K F P0 Q))

/-- **The Abel-Jacobi point** of `Q`: the closed point of `J` with class `[Q] - [P0]`. -/
noncomputable def ajPt (Q : Place K F) : (Jac K F).left := (ajK K F P0 Q).left (IsLocalRing.closedPoint K)

open Classical in
/-- The constant `κ - [Θ] - [P0]` (in `Pic⁰` as soon as the piece has a `K`-point). -/
noncomputable def ajC (κ : PicK K F) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd
    (if h : κ - thetaK K F - clsK K F (Finsupp.single P0 1) ∈ Pic0K K F then ⟨_, h⟩ else 0))

/-- **The Abel-Jacobi map on `Spec R`**: `const (κ - [Θ] - [P0]) * (Spec φ ≫ jX0)⁻¹`. -/
noncomputable def ajMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F) :
    specO K R ⟶ Jac K F :=
  (toUnit (specO K R) ≫ ajC K F P0 κ) * (jMap K F φ)⁻¹

theorem ajMap_over {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F) :
    (ajMap K F P0 φ κ).left ≫ (Jac K F).hom = sR K R :=
  Over.w (ajMap K F P0 φ κ)

/-- **Value of the AJ map**: `ajK P0 Q` at a `K`-point `x` with `ψ(x ∘ φ) = κ - [Θ] - [Q]`. -/
theorem kptO_ajMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F)
    (x : R →ₐ[K] K) (Q : Place K F)
    (hx : psiJ K F (kpt (x.comp φ)) = κ - thetaK K F - clsK K F (Finsupp.single Q 1)) :
    kptO x ≫ ajMap K F P0 φ κ = ajK K F P0 Q := by
  have h1 : psiJ K F (kpt (x.comp φ)) ∈ Pic0K K F := by
    rw [← jacPicEquiv_jMap K F φ x]
    exact (Multiplicative.toAdd (jacPicEquiv K F (kptO x ≫ jMap K F φ))).2
  have hmem : κ - thetaK K F - clsK K F (Finsupp.single P0 1) ∈ Pic0K K F := by
    have e : κ - thetaK K F - clsK K F (Finsupp.single P0 1) =
        psiJ K F (kpt (x.comp φ)) + (ajCls K F P0 Q : PicK K F) := by
      rw [hx]
      show _ = _ + (clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1))
      abel
    rw [e]
    exact add_mem h1 (ajCls K F P0 Q).2
  rw [ajMap, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    toUnit_unique (kptO x ≫ toUnit (specO K R)) (𝟙 _), Category.id_comp]
  apply (jacPicEquiv K F).injective
  rw [map_mul, map_inv, ajC, ajK, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, dif_pos hmem]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
  apply Subtype.ext
  rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, jacPicEquiv_jMap K F φ x, hx]
  show κ - thetaK K F - clsK K F (Finsupp.single P0 1) + -(κ - thetaK K F - clsK K F (Finsupp.single Q 1)) =
    clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1)
  abel

/-- **Value of the AJ map at a closed point** `kpt x`. -/
theorem ajMap_kpt {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F)
    (x : R →ₐ[K] K) (Q : Place K F)
    (hx : psiJ K F (kpt (x.comp φ)) = κ - thetaK K F - clsK K F (Finsupp.single Q 1)) :
    (ajMap K F P0 φ κ).left (kpt x) = ajPt K F P0 Q := by
  rw [ajPt, ← kptO_ajMap K F P0 φ κ x Q hx]
  show _ = (ajMap K F P0 φ κ).left (Spec.map (CommRingCat.ofHom (x : R →+* K)) (IsLocalRing.closedPoint K))
  rw [SpecMap_closedPoint]

end JMap

section Piece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **The AJ piece** `Spec LocR ⟶ J` (an open of the chart `Spec B'`, `B' = Rfin (SynF K F c0)`). -/
noncomputable def ajPiece : specO K (LocR c0 D c) ⟶ Jac K F :=
  ajMap K F P0 (lawMapP c0 D c) (kapP c0 D c)

theorem ajPiece_over : (ajPiece P0 c0 D c).left ≫ (Jac K F).hom = sR K (LocR c0 D c) :=
  ajMap_over K F P0 _ _

end Piece

end RamanujanPetersson.JacComplete

end


