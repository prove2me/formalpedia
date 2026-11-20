-- Prove2me | Definitions.Def_RPLib_F2_080
-- name    : RPLib_F2_080
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T17:47:56.112363+00:00
-- url     : https://prove2.me/theorems/071c9eba-a630-4bea-9053-ca2b8d2e39fd
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 080 (part 1 of file 044 of 70)
-- statement:
--   File 080 (part 1 of file 044 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
--   * `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
--   * `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
--   * `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_043

/-!
# Ramanujan-Petersson curve library (flat edition), file 080 (part 1 of file 044 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
* `S4.Def_RP_JacComplete_AJPiece`: The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`
* `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
* `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_PicLaw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)

* `psiJ K F : X0 → PicK`, additive (`chunkAdd_lawChunk`) and rigid (`chunkRigid_lawChunk`); `card_lawPt`, `deg_psiJ`;
* **`jacPic0 K F : H →* Multiplicative (Pic0K K F)`**, `jacPic0_injective`, `jacPic0_lamB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem deg_psiJ (p : X0 K F) (hp : IsClosed ({p} : Set (X0 K F))) :
    degPicK K F (psiJ K F p) = (genusFK K F : ℤ) -
      (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1).deg := by
  obtain ⟨yR, rfl⟩ := exists_kpt (K := K) p hp
  rw [psiJ, psiS_kpt, psiA, psiL, map_sub, degPicK_clsK, degPicK_clsK, deg_Zdiv, card_lawPt]

end Jac

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJPiece =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJPiece`: a local piece of the chart `{c0}` into `X0`

In `F' = SynF K F c0` (coordinate `x' = 1/(x - c0)`), the `ν`-piece `pieceMap D c : Sym^g(B') → B'[1/f]` of
`AJLoc` is localized at `N(x')` (`ConvR`), converted to `F`-coordinates by `convSym` (`convS`), and localized at
the image of `u0` (`LocR`). This gives **`lawMapP : LawRing K F → LocR`**, i.e. `Spec LocR → X0`, on the open
`Spec LocR ⊆ Spec B'` (`pieceIn`), with the class formula **`psiJ_lawMapP`**: `ψ(piece(Q)) = κ - [Θ] - [Q]`.
`exists_pieceIn`: a point `Q` of `B'` lies on the piece when `f`, `N(x')` and `u0` do not vanish there.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AwayPt

variable {K : Type u} [Field K] [IsAlgClosed K]

end AwayPt

section AJPiece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **The coordinate ring of the piece**. -/
abbrev LocR : Type u := Localization.Away (convU c0 D c)

/-- `B' → LocR` (`Spec LocR` is an open of `Spec B'`). -/
noncomputable def pieceIn : Rfin K (SynF K F c0) →ₐ[K] LocR c0 D c :=
  (awayι (K := K) (convU c0 D c)).comp ((awayι (K := K) (pieceN c0 D c)).comp (pieceι D c))

theorem isUnit_convU : IsUnit (((awayι (K := K) (convU c0 D c)).comp (convS c0 D c)) (lawPre K F).u0) :=
  IsLocalization.Away.algebraMap_isUnit (convU c0 D c)

/-- **The piece `Spec LocR → X0`** as `LawRing K F → LocR`. -/
noncomputable def lawMapP : LawRing K F →ₐ[K] LocR c0 D c :=
  IsLocalization.Away.liftAlgHom (f := (awayι (K := K) (convU c0 D c)).comp (convS c0 D c)) (lawPre K F).u0
    (isUnit_convU c0 D c)

theorem lawMapP_comp : (lawMapP c0 D c).comp (awayι (K := K) (lawPre K F).u0) =
    (awayι (K := K) (convU c0 D c)).comp (convS c0 D c) :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply, lawMapP, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    rfl

theorem comp_lawMapP (x : LocR c0 D c →ₐ[K] K) :
    (x.comp (lawMapP c0 D c)).comp (awayι (K := K) (lawPre K F).u0) =
      (x.comp (awayι (K := K) (convU c0 D c))).comp (convS c0 D c) := by
  rw [AlgHom.comp_assoc, lawMapP_comp, ← AlgHom.comp_assoc]

/-- **The class function on the piece**: `ψ(piece(Q)) = κ - [Θ] - [Q]`. -/
theorem psiJ_lawMapP (x : LocR c0 D c →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapP c0 D c))) = kapP c0 D c -
      clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1) -
      clsK K F (Finsupp.single ((synPlace c0).symm (Sum.inl (ptP (x.comp (pieceIn c0 D c))))) 1) := by
  have e : x.comp (pieceIn c0 D c) =
      ((x.comp (awayι (K := K) (convU c0 D c))).comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) := rfl
  rw [e, psiJ, psiS_kpt, psiA, comp_lawMapP, psiL, clsK_convS]
  abel

/-- **A point of `B'` lies on the piece** when `f`, `N(x')` and `u0` do not vanish there. -/
theorem exists_pieceIn (Q : Rfin K (SynF K F c0) →ₐ[K] K) (hf : Q (pieceF D c) ≠ 0)
    (hN : ∀ z : PieceR D c →ₐ[K] K, z.comp (pieceι D c) = Q →
      ∀ e ∈ ptSet (z.comp (pieceMap D c)), e (xS K F c0) ≠ 0)
    (hu : ∀ y : ConvR c0 D c →ₐ[K] K, (y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) = Q →
      y (convU c0 D c) ≠ 0) :
    ∃ x : LocR c0 D c →ₐ[K] K, x.comp (pieceIn c0 D c) = Q := by
  obtain ⟨z, hz⟩ : ∃ z : PieceR D c →ₐ[K] K, z.comp (pieceι D c) = Q := exists_away_pt Q (pieceF D c) hf
  obtain ⟨y, hy⟩ := exists_away_pt z (pieceN c0 D c) (pieceN_ne_zero c0 D c z (hN z hz))
  have hyQ : (y.comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) = Q := by rw [hy, hz]
  obtain ⟨x, hx⟩ := exists_away_pt y (convU c0 D c) (hu y hyQ)
  refine ⟨x, ?_⟩
  have e : x.comp (pieceIn c0 D c) =
      ((x.comp (awayι (K := K) (convU c0 D c))).comp (awayι (K := K) (pieceN c0 D c))).comp (pieceι D c) := rfl
  rw [e, hx, hyQ]

end AJPiece

end RamanujanPetersson.JacComplete


end

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

/-- `[Θ]`. -/
noncomputable abbrev thetaK : PicK K F :=
  clsK K F (ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1)

variable (P0 : Place K F)

/-- **`[Q] - [P0] ∈ Pic⁰`**. -/
noncomputable def ajCls (Q : Place K F) : Pic0K K F :=
  ⟨clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1), by
    rw [← clsK_sub]
    exact clsK_mem_Pic0K K F (by rw [PlacesK.Divisor.deg_sub, deg_single_one, deg_single_one, sub_self])⟩

end JMap

section Piece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

end Piece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJVal2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`

* `plC c0 Q` (the place of `F` at a `K`-point `Q` of `B'`), `plP c0 D c x`, `psiJ_plP`.
* **`kptO_ajPiece`**, **`ajPiece_kpt`**: the piece takes the value `ajPt P0 (plP c0 D c x)` (class `[Q] - [P0]`).
* `isOpenImmersion_pieceIn`: `Spec LocR → Spec B'` is an open immersion; `pieceIn_over`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`,
  **`ajChart_kpt`**: value `ajPt P0 (plC c0 Q)` at every closed point `kpt Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section PlP

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

variable {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- The place of `F` at a `K`-point of the piece. -/
noncomputable def plP (x : LocR c0 D c →ₐ[K] K) : Place K F :=
  plC c0 (x.comp (pieceIn c0 D c))

end PlP

section PieceVal

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

theorem pieceIn_over :
    Spec.map (CommRingCat.ofHom (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c)) ≫
      sR K (Rfin K (SynF K F c0)) = sR K (LocR c0 D c) :=
  SpecMap_sR _

end PieceVal

end RamanujanPetersson.JacComplete


end


