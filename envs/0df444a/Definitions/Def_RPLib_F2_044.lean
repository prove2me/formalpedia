-- Prove2me | Definitions.Def_RPLib_F2_044
-- name    : RPLib_F2_044
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T18:09:20.522082+00:00
-- url     : https://prove2.me/theorems/6d972825-3df8-4133-bb69-6ae1d30e9f80
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 044 of 70
-- statement:
--   File 044 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--   * `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
--   * `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_043
import Definitions.Def_RPLib_F2_080

/-!
# Ramanujan-Petersson curve library (flat edition), file 044 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
* `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
* `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
-/

set_option autoImplicit false

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

-- (flat edition, G0 11-19) as in lib AJVal2B: the kernel check of this instance costs ~230k heartbeats under
-- Elab.async=false (whnf timeout at 200000 in RPLib_F2_044)
set_option maxHeartbeats 1000000 in
/-- `Spec LocR → Spec B'` is an open immersion (three successive localizations away from one element). -/
instance isOpenImmersion_pieceIn :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 D c)
      (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c))) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (convU c0 D c) : ConvR c0 D c →+* LocR c0 D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (ConvR c0 D c)) (convU c0 D c)
  have h2 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (pieceN c0 D c) : PieceR D c →+* ConvR c0 D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (PieceR D c)) (pieceN c0 D c)
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (pieceι D c : Rfin K (SynF K F c0) →+* PieceR D c))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (Rfin K (SynF K F c0))) (pieceF D c)
  have e : Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 D c)
      (pieceIn c0 D c : Rfin K (SynF K F c0) →+* LocR c0 D c)) =
      Spec.map (CommRingCat.ofHom (awayι (K := K) (convU c0 D c) : ConvR c0 D c →+* LocR c0 D c)) ≫
        Spec.map (CommRingCat.ofHom (awayι (K := K) (pieceN c0 D c) : PieceR D c →+* ConvR c0 D c)) ≫
          Spec.map (CommRingCat.ofHom (pieceι D c : Rfin K (SynF K F c0) →+* PieceR D c)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  rw [e]
  infer_instance

end PieceVal

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGen =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`

* `exists_pool`: arbitrarily large finite sets of points off the roots of `b(x)`.
* `PtY K F c0` (points of `B' = Rfin F'` off `x = ∞`), `tpY` (their `F`-points, injective).
* `goodY_ext`: nonspecial `b`-generic sets of such points extend off any finite set.
* `symPt_convPt_eq`: the converted point depends only on the support.
* **`exists_piece_through`**: every closed point `Q0` of `B'` lies on some piece `Spec LocR c0 D c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJGen

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

set_option maxHeartbeats 1000000 in
/-- The greedy choice of `E` (`exists_greedy` with `GoodY`, from a point of `X0`). -/
theorem exists_goodTuple {b : K[X]} (hb0 : b ≠ 0) : ∃ a : Fin (genusFK K F) → PtY K F c0,
    Function.Injective a ∧ GoodY c0 b (Finset.univ.image a) ∧ symPt (tpY c0 ∘ a) (lawPre K F).u0 ≠ 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0R, -⟩ := exists_algHom_ker_eq (k := K) m
  have hy0 : (y0R.comp (awayι (K := K) (lawPre K F).u0)) (lawPre K F).u0 ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (lawPre K F).u0).map y0R).ne_zero
  have ht0 : symPt (liftTuple (y0R.comp (awayι (K := K) (lawPre K F).u0))) (lawPre K F).u0 ≠ 0 := by
    rw [symPt_liftTuple]; exact hy0
  exact exists_greedy (tpY c0) (tpY_injective c0) (fun w hw => finite_zero hw) (GoodY c0 b)
    (goodY_empty c0 b) (goodY_ext c0 hb0) (lawPre K F).u0 _ ht0

theorem convU_ne_zero {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))
    (y : ConvR c0 D c →ₐ[K] K) (a : Fin (genusFK K F) → PtY K F c0) (ha : Function.Injective a)
    (hpt : ptSet (y.comp (convφ c0 D c)) = (Finset.univ.image a).map (Function.Embedding.subtype _))
    (hau : symPt (tpY c0 ∘ a) (lawPre K F).u0 ≠ 0) : y (convU c0 D c) ≠ 0 := by
  have e := AlgHom.congr_fun (comp_convS c0 D c y) (lawPre K F).u0
  rw [symPt_convPt_eq c0 _ _ _ y a ha hpt] at e
  rw [← e] at hau
  exact hau

end AJGen

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
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

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

/-- The open immersion of the piece `i` into `Spec B'`. -/
noncomputable abbrev pj (i : PIdx K F c0) :
    Spec (.of (LocR c0 i.2.1 i.2.2)) ⟶ Spec (.of (Rfin K (SynF K F c0))) :=
  Spec.map (CommRingCat.ofHom (R := Rfin K (SynF K F c0)) (S := LocR c0 i.2.1 i.2.2)
    (pieceIn c0 i.2.1 i.2.2 : Rfin K (SynF K F c0) →+* LocR c0 i.2.1 i.2.2))

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Ext =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)

Weil's extension theorem (S4-JacDivisors, Milne I.3.2) applied to the proper group `J` (L19, `isProper_Jac`):
* `domain_eq_top_Jac`: a rational map over `K` from a smooth `V` (with `V`, `V ×_K V` integral) to `J` is defined
  everywhere;
* `extJ f hf : V ⟶ J`, `ι_extJ` (it restricts to `f` on the domain of `f`), `eq_extJ` (unique);
* `UO V U`, `ιU V U` (a dense open `U ⊆ V` over `K`) and `eq_of_kpt_eq`: maps `V ⟶ J` from a reduced `V` locally of
  finite type are determined by their values at the `K`-points of a dense open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacLaw

universe u

section Ext

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {V : Over (Spec (.of K))} [IsReduced V.left]

theorem ι_extL (f : V.left.PartialMap (Jac K F).left) (h : f.toRationalMap.domain = ⊤) :
    f.domain.ι ≫ extL f h = f.hom := by
  have e : V.left.homOfLE (show f.domain ≤ f.toRationalMap.toPartialMap.domain from f.le_domain_toRationalMap) ≫
      f.toRationalMap.toPartialMap.hom = f.hom :=
    f.toPartialMap_toRationalMap_restrict
  rw [← e, extL, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (f.toRationalMap.toPartialMap.domain.ι), Category.assoc, Scheme.homOfLE_ι,
    Category.assoc, Scheme.toIso_inv_ι, Category.comp_id, Scheme.homOfLE_ι]

theorem extL_over (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom)
    (h : f.toRationalMap.domain = ⊤) : extL f h ≫ (Jac K F).hom = V.hom := by
  rw [extL, Category.assoc, Category.assoc, JacDivisors.toPartialMap_comp V.hom (Jac K F).hom f hf,
    ← Category.assoc (V.left.homOfLE _), Scheme.homOfLE_ι, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

/-- Two maps `V ⟶ J` over `K` that agree on a dense open are equal. -/
theorem eq_of_comp_eq {U : V.left.Opens} (hU : Dense (U : Set V.left)) (φ ψ : V ⟶ Jac K F)
    (h : U.ι ≫ φ.left = U.ι ≫ ψ.left) : φ = ψ := by
  haveI := AlgebraicGeometry.Opens.isDominant_ι hU
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (Jac K F).hom (by rw [Over.w φ, Over.w ψ])
    U.ι h)

/-- **Maps `V ⟶ J` are determined by their values at the `K`-points of a dense open.** -/
theorem eq_of_kpt_eq [LocallyOfFiniteType V.hom] {U : V.left.Opens} (hU : Dense (U : Set V.left))
    (φ ψ : V ⟶ Jac K F)
    (h : ∀ u : 𝟙_ (Over (Spec (.of K))) ⟶ UO V U, u ≫ ιU V U ≫ φ = u ≫ ιU V U ≫ ψ) : φ = ψ := by
  have e : ιU V U ≫ φ = ιU V U ≫ ψ := by
    haveI : LocallyOfFiniteType (UO V U).hom := show LocallyOfFiniteType (U.ι ≫ V.hom) from inferInstance
    haveI : IsReduced (UO V U).left := show IsReduced U.toScheme from inferInstance
    exact (lawChunk K F).hom_ext_kpt inferInstance inferInstance _ _ fun u => congrArg _ (h u)
  exact eq_of_comp_eq hU φ ψ (congrArg CommaMorphism.left e)

end Ext

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Ne =====
section

/-!
# Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`

* `not_clsK_eq_eff`: for a nonspecial `g`-set `C` and a point `R ∉ C`, the class of `Zdiv C - [R]` (degree `g - 1`)
  contains no effective divisor (an `f` with `div f + Zdiv C - [R] ≥ 0` lies in `L(Zdiv C)`, so is constant);
* `exists_not_mem_W`: for `g ≥ 1` the `K`-point with class `Σ_{φ ∈ C} ([φ] - [P0]) - ([R] - [P0])` is not on `W`
  (Riemann's theorem `mem_W_iff`);
* `one_le_coheight_zTheta`: `1 ≤ coheight (zTheta P0)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Ne

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem coe_ajCls (Q : Place K F) : ((ajCls K F P0 Q : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1) := rfl

end Ne

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Pts =====
section

/-!
# Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`

Input for `coheight (zTheta P0) ≤ 1` (file `Codim`, Krull on the chart `X0`):
* `kJ yR`: the `K`-point of `J` at the closed point `yR` of `X0`; `pt_kJ` (it is `jX0 (kpt yR)`) and `cls_kJ`
  (its class is `[Zdiv A] - [Θ]`, `A` the `g` points of `yR`); `deg_thetaK : deg [Θ] = g`;
* `exists_cJ`: the `K`-point `c_φ` with class `[φ] + (g-1)[P0] - [Θ]`;
* `mem_W_of_cls`: a class `[Zdiv S] - (g-1)[P0]` with `#S = g-1` lies on `W`;
* `mem_transl_W`: if `φ` is one of the points of `yR`, then `jX0 (kpt yR) - c_φ ∈ W`;
* `finite_zeros`: a nonzero `u ∈ Rfin` has finitely many zeros.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB

universe u

section Pts

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The `K`-point of `J` at the closed point `yR` of the chart `X0`. -/
noncomputable def kJ (yR : LawRing K F →ₐ[K] K) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  kptO yR ≫ jMap K F (AlgHom.id K (LawRing K F))

theorem pt_kJ (yR : LawRing K F →ₐ[K] K) : (kJ yR).left (IsLocalRing.closedPoint K) = jX0 K F (kpt yR) := by
  show jX0 K F (Spec.map (CommRingCat.ofHom ((AlgHom.id K (LawRing K F)) : LawRing K F →+* LawRing K F))
    (Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) (IsLocalRing.closedPoint K))) = _
  rw [SpecMap_closedPoint, SpecMap_kpt, AlgHom.comp_id]

end Pts

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_ThetaX0 =====
section

/-!
# Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`

* `pullback_openImm`: the pull-back of a Weil divisor along an open immersion is its restriction;
* `tauX d`, an open immersion, dominant; `pullback_tauX_apply`: `τ_d^* Θ` is the indicator of `τ_d⁻¹ (zTheta)`;
* `exists_eta`: if `τ_d y ∈ W`, then `zTheta = τ_d η'` for some `η' ⤳ y`;
* `exists_sep`: finitely many `K`-points of `Rfin` off a finite set `S` are common zeros of an `s` that has no zero on `S`;
* `normS_mem_eta` (the upper-bound input of the plus-curve trick): if `φ(t) = 0` and some chart point `A` contains `φ`
  but no other zero of `t`, then `Nm(t)` vanishes at the point `η'` with `τ_{c_φ⁻¹} η' = zTheta`. Proof: a minimal prime
  `q ⊆ m_A` of `(Nm t)` has height `≤ 1` (Krull); every closed point of `V(Nm t)` contains a zero of `t`, so it lies on
  `τ⁻¹ W` (if that zero is `φ`, `mem_transl_W`) or on `V(Nm s)` (`s` vanishing at the other zeros, none on `A`); by
  Jacobson `q ∈ τ⁻¹ W`, and `coheight zTheta = 1` forces `τ q = zTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section General

open CategoryTheory AlgebraicGeometry

variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  [∀ y : C, UniqueFactorizationMonoid (C.presheaf.stalk y)] (ι : U ⟶ C) [IsOpenImmersion ι] [IsDominant ι]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

instance isNoetherianRing_lawRingT : IsNoetherianRing (LawRing K F) := Algebra.FiniteType.isNoetherianRing K _

end ThetaX0

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve7 =====
section

/-!
# Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)

* `kapM cK : J ⟶ J`, `e ↦ c_K e⁻¹`; `mu1 P0 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`; `mu2 P0 c2`, `(e, q) ↦ AJ(q)² e c_2`;
* `Bad P0 c2 := mu1⁻¹ W ∩ mu2⁻¹ (J \ jX0 (X0))`, closed in `J × X1`;
* **`Ogood P0 cK c2 := Wᶜ ∩ kapM⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`**, open (`isOpen_Ogood`: `pr_J` is closed, `X1` proper);
* **`isGoodFor_of_mem`**: every `K`-point of `Ogood` is good;
* `not_mem_image_Bad`, `mem_Ogood_of`: the converse criterion (all `K`-points `(e, q)` off `Bad`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve7

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem isOpen_range_jX0 : IsOpen (Set.range (jX0 K F)) := (jX0 K F).isOpenEmbedding.isOpen_range

end Curve7

end RamanujanPetersson.ThetaSquare


end


