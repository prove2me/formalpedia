-- Prove2me | Definitions.Def_RPLib_F2_058
-- name    : RPLib_F2_058
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T21:08:57.937621+00:00
-- url     : https://prove2.me/theorems/a0d379ca-67ef-475f-ad87-c3bfb9e315ed
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 058 of 70
-- statement:
--   File 058 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
--   * `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
--   * `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
--   * `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
--   * `S4.Def_RP_ThetaSquare_Riem`: Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)
--   * `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--   * `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
--   * `S4.Def_RP_ThetaCube_Lines`: S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection
--   * `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
--   * `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
--   * `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
--   * `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
--   * `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
--   * `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
--   * `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
--   * `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
--   * `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
--   * `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
--   * `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_057

/-!
# Ramanujan-Petersson curve library (flat edition), file 058 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
* `S4.Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
* `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
* `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
* `S4.Def_RP_ThetaSquare_Riem`: Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)
* `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
* `S4.Def_RP_ThetaSquare_Curve8`: Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)
* `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
* `S4.Def_RP_ThetaCube_Lines`: S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection
* `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
* `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Proper =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**

Route AJ (NOTES, session 6 decision): the Abel-Jacobi map `ajX1 P0 : X1 = Sym¹ X ⟶ J` (AJCo) gives
`Φ_n : X1^n ⟶ J`, `(Q_1, …, Q_n) ↦ Σ ([Q_i] - [P0])` (products in `Over (Spec K)`, hom-group law of `J`).
* `exists_inl`, `exists_plc`, `exists_chartPt`: every place of `F` is the center of a `K`-point of a chart of `X1`;
* `X1O`, `ιO`, `ajO P0 : X1O ⟶ J`, `exists_kX1`: every `ajK P0 Q` is the image of a `K`-point of `X1`;
* `PP n = X1^n` (`isProper_PP`), `PhiN P0 n : PP n ⟶ J`, `exists_pt`: the value `Σ ajCls P0 (t i)` is attained;
* `surjective_PhiN`: `Φ_g` is surjective (closed image, contains every closed point by `exists_eff_rep`, `J` Jacobson);
* **`isProper_Jac : IsProper (Jac K F).hom`** (`UniversallyClosed.of_comp_surjective`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Proper

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

instance universallyClosed_PhiN (n : ℕ) : UniversallyClosed (PhiN P0 n).left := by
  haveI : UniversallyClosed ((PhiN P0 n).left ≫ (Jac K F).hom) := by
    rw [Over.w (PhiN P0 n)]; infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated (PhiN P0 n).left (Jac K F).hom

/-- **`Φ_g` is surjective.** -/
theorem surjective_PhiN : Function.Surjective (PhiN P0 (genusFK K F)).left := by
  haveI : JacobsonSpace (Jac K F).left := LocallyOfFiniteType.jacobsonSpace (Jac K F).hom
  have hcl : closedPoints (Jac K F).left ⊆ Set.range (PhiN P0 (genusFK K F)).left := by
    intro j hj
    let a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
      Over.homMk (pointOfClosedPoint (Jac K F).hom j hj) (pointOfClosedPoint_comp _ _ _)
    obtain ⟨t, ht⟩ := exists_eff_rep P0 (Multiplicative.toAdd (jacPicEquiv K F a)).2
    obtain ⟨p, hp⟩ := exists_pt P0 (genusFK K F) t
    have hs : ((∑ i, ajCls K F P0 (t i) : Pic0K K F) : PicK K F) =
        ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) := by
      rw [ht, AddSubmonoidClass.coe_finsetSum]
      show ∑ i, (clsK K F (Finsupp.single (t i) 1) - clsK K F (Finsupp.single P0 1)) = _
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, natCast_zsmul]
    have e : p ≫ PhiN P0 (genusFK K F) = a := by
      apply (jacPicEquiv K F).injective
      rw [hp, show (∑ i, ajCls K F P0 (t i)) = Multiplicative.toAdd (jacPicEquiv K F a) from Subtype.ext hs]
      rfl
    refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
    have h2 : (p ≫ PhiN P0 (genusFK K F)).left (IsLocalRing.closedPoint K) = j := by
      rw [e]
      exact pointOfClosedPoint_apply (Jac K F).hom j hj _
    exact h2
  have h := closure_minimal hcl (PhiN P0 (genusFK K F)).left.isClosedMap.isClosed_range
  rw [closure_closedPoints] at h
  exact fun j => h (Set.mem_univ j)

variable (K F) in
/-- **L19: the Jacobian is proper over `K`.** -/
instance isProper_Jac : IsProper (Jac K F).hom := by
  obtain ⟨Q⟩ := PlacesK.nonempty_infPlace K F
  haveI hs : Surjective (PhiN (Sum.inr Q : Place K F) (genusFK K F)).left := ⟨surjective_PhiN _⟩
  haveI : UniversallyClosed ((PhiN (Sum.inr Q : Place K F) (genusFK K F)).left ≫ (Jac K F).hom) := by
    rw [Over.w (PhiN (Sum.inr Q : Place K F) (genusFK K F))]; infer_instance
  haveI := UniversallyClosed.of_comp_surjective (PhiN (Sum.inr Q : Place K F) (genusFK K F)).left (Jac K F).hom
  exact {}

end Proper

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_CoreB_Dim =====
section

/-!
# Core B, O1: the heights on the Jacobian are bounded

* `ringKrullDim_le_of_finiteType`: a finite type algebra over a field has finite Krull dimension.
* `exists_coheight_le_of_isAffineOpen`: on an affine open of a scheme locally of finite type over a field,
  the coheights are bounded.
* `exists_height_le`: a quasi-compact scheme locally of finite type over a field has bounded heights
  (for the specialization order).
* `exists_height_max`: a bound on heights is attained by a least bound `g`.
* `exists_dim_Jac`: `∃ g, (∀ x, height x ≤ g) ∧ ∃ x, g ≤ height x` on `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open CategoryTheory AlgebraicGeometry Order

universe u

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open RamanujanPetersson.JacComplete in
theorem exists_dim_Jac :
    ∃ g : ℕ, (∀ x : (Jac K F).left, height x ≤ g) ∧ ∃ x : (Jac K F).left, (g : ℕ∞) ≤ height x := by
  have : CompactSpace (Jac K F).left := QuasiCompact.compactSpace_of_compactSpace (Jac K F).hom
  obtain ⟨N, hN⟩ := exists_height_le (Jac K F).hom
  exact exists_height_max N hN

end RamanujanPetersson.CoreB


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

/-- **Weil extension for `J`**: a rational map over `K` from a smooth `V` to `J` is defined everywhere. -/
theorem domain_eq_top_Jac {V : Over (Spec (.of K))} [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ :=
  JacDivisors.domain_eq_top_of_smooth_of_isProper (G := Jac K F) f hf

variable {V : Over (Spec (.of K))} [IsReduced V.left]

/-- **The extension `V ⟶ J`** of a partial map over `K` from a smooth `V`. -/
noncomputable def extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) : V ⟶ Jac K F :=
  Over.homMk (extL f (domain_eq_top_Jac f hf)) (extL_over f hf (domain_eq_top_Jac f hf))

theorem ι_extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) :
    f.domain.ι ≫ (extJ f hf).left = f.hom :=
  ι_extL f (domain_eq_top_Jac f hf)

end Ext

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Def =====
section

/-!
# Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)

* `irreducibleSpace_X1`, `isIntegral_X1`: the curve `X1 = Sym¹ X` is integral (its charts are domains and pairwise meet);
* `isIntegral_PP n`: `X1^n` is integral (`IntersectA.isIntegral_pullback`);
* `W P0 := Φ_{g-1}(X1^{g-1}) ⊆ J` (`isClosed_W`, `isIrreducible_W`), `zTheta P0` its generic point;
* `Theta P0 : AlgebraicCycle J ℤ`, the prime cycle `[W_{g-1}]`.
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

section Def

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem isClosed_W : IsClosed (W P0) := (PhiN P0 (n0 K F)).left.isClosedMap.isClosed_range

theorem isIrreducible_W : IsIrreducible (W P0) := by
  rw [W, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (PP K F (n0 K F)).left).image _
    (PhiN P0 (n0 K F)).left.continuous.continuousOn

/-- The generic point of `W_{g-1}`. -/
noncomputable def zTheta : (Jac K F).left := (isIrreducible_W P0).genericPoint

theorem isGenericPoint_zTheta : IsGenericPoint (zTheta P0) (W P0) :=
  (isIrreducible_W P0).isGenericPoint_genericPoint (isClosed_W P0)

theorem closure_zTheta : closure {zTheta P0} = W P0 := isGenericPoint_zTheta P0

/-- **The theta divisor** `Θ = [W_{g-1}]`, as a prime cycle on `J`. -/
noncomputable def Theta : AlgebraicCycle (Jac K F).left ℤ := Function.locallyFinsuppWithin.single (zTheta P0) 1

theorem Theta_apply (z : (Jac K F).left) : Theta P0 z = if z = zTheta P0 then 1 else 0 :=
  Function.locallyFinsuppWithin.single_apply

theorem Theta_nonneg : 0 ≤ Theta P0 := Function.locallyFinsuppWithin.single_nonneg.mpr zero_le_one

end Def

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Riem =====
section

/-!
# Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)

**`mem_W_iff`**: a `K`-point `x` of `J` lies on `W_{g-1}` iff its class is `Σ_{i<g-1} ([t_i] - [P0])` for some places
`t_i`, i.e. iff `x + (g-1)[P0]` is the class of an effective divisor of degree `g - 1`.
(→: the fibre of the proper map `Φ_{g-1}` over the closed point `x` is a nonempty closed subset of the Jacobson
scheme `X1^{g-1}`, so it has a closed point, i.e. a `K`-point `p`, and `PhiN_val` computes `Φ(p)`; ←: `exists_pt`.)
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

section Riem

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- A point of `W = Φ_n(X1^n)` that is closed is the image of a `K`-point of `X1^n`. -/
theorem exists_kpt_of_mem_range (n : ℕ) (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx : x.left (IsLocalRing.closedPoint K) ∈ Set.range (PhiN P0 n).left) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p ≫ PhiN P0 n = x := by
  obtain ⟨y, hy⟩ := hx
  have hcl : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set (Jac K F).left) :=
    (pointEquivClosedPoint (Jac K F).hom ⟨x.left, Over.w x⟩).2
  haveI : JacobsonSpace (PP K F n).left := LocallyOfFiniteType.jacobsonSpace (PP K F n).hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := (PhiN P0 n).left ⁻¹' {x.left (IsLocalRing.closedPoint K)}) ⟨y, hy⟩
    (hcl.preimage (PhiN P0 n).left.continuous).isLocallyClosed
  let p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n :=
    Over.homMk (pointOfClosedPoint (PP K F n).hom z hzc) (pointOfClosedPoint_comp _ _ _)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have h2 : (p ≫ PhiN P0 n).left (IsLocalRing.closedPoint K) = (PhiN P0 n).left z := by
    show (PhiN P0 n).left (pointOfClosedPoint (PP K F n).hom z hzc (IsLocalRing.closedPoint K)) = _
    exact congrArg (PhiN P0 n).left (pointOfClosedPoint_apply (PP K F n).hom z hzc _)
  rw [h2]
  exact hz

/-- **Riemann's theorem, point form** (Milne III.5.2): `x ∈ W_{g-1}` iff `x = Σ_{i<g-1} ([t_i] - [P0])`. -/
theorem mem_W_iff (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    x.left (IsLocalRing.closedPoint K) ∈ W P0 ↔
      ∃ t : Fin (n0 K F) → Place K F, jacPicEquiv K F x = Multiplicative.ofAdd (∑ i, ajCls K F P0 (t i)) := by
  constructor
  · intro hx
    obtain ⟨p, e⟩ := exists_kpt_of_mem_range P0 (n0 K F) x hx
    exact ⟨fun i => kPl (p ≫ prj K F (n0 K F) i), by rw [← e, PhiN_val]⟩
  · rintro ⟨t, ht⟩
    obtain ⟨p, hp⟩ := exists_pt P0 (n0 K F) t
    have e : p ≫ PhiN P0 (n0 K F) = x := (jacPicEquiv K F).injective (hp.trans ht.symm)
    exact ⟨p.left (IsLocalRing.closedPoint K), by rw [← e]; rfl⟩

end Riem

end RamanujanPetersson.ThetaSquare


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

/-- **`W_{g-1} ≠ J`** (`g ≥ 1`): the class `Σ_{φ∈C}([φ]-[P0]) - ([R]-[P0])` is not on `W`. -/
theorem exists_not_mem_W (hg : 0 < genusFK K F) :
    ∃ x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, x.left (IsLocalRing.closedPoint K) ∉ W P0 := by
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (2 * genusFK K F + 1)
  obtain ⟨R, -⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨C, -, hCR, hCc, hC⟩ := exists_nonspecial_avoid T {R} (by rw [Finset.card_singleton]; omega)
  have hR : R ∉ C := Finset.disjoint_singleton_right.1 hCR
  let c : Pic0K K F := ∑ φ ∈ C, ajCls K F P0 (Sum.inl (ptP φ)) - ajCls K F P0 (Sum.inl (ptP R))
  refine ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd c), fun hx => ?_⟩
  obtain ⟨t, ht⟩ := (mem_W_iff P0 _).1 hx
  rw [MulEquiv.apply_symm_apply] at ht
  have hc := congrArg (fun z : Pic0K K F => (z : PicK K F)) (Multiplicative.ofAdd.injective ht)
  simp only [c, AddSubgroup.coe_sub, AddSubmonoidClass.coe_finsetSum, coe_ajCls] at hc
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hCc, ← clsK_sum, ← clsK_sum] at hc
  have hgn : genusFK K F = n0 K F + 1 := by simp only [n0]; omega
  rw [hgn, succ_nsmul] at hc
  refine not_clsK_eq_eff hC hR (E := ∑ i, Finsupp.single (t i) 1)
    (Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one) ?_
  rw [clsK_sub, ← sub_eq_zero]
  have hZ : clsK K F (Zdiv C) = clsK K F (∑ φ ∈ C, Finsupp.single (Sum.inl (ptP φ)) 1) := rfl
  rw [hZ]
  set a := clsK K F (Finsupp.single P0 1)
  set z := clsK K F (∑ φ ∈ C, Finsupp.single (Sum.inl (ptP φ) : Place K F) (1 : ℤ))
  set r := clsK K F (Finsupp.single (Sum.inl (ptP R) : Place K F) (1 : ℤ))
  set e := clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ))
  have : z - r - e = (z - (n0 K F • a + a) - (r - a)) - (e - n0 K F • a) := by abel
  rw [this, hc, sub_self]

/-- **`Θ` has codimension `≥ 1`.** -/
theorem one_le_coheight_zTheta (hg : 0 < genusFK K F) : 1 ≤ Order.coheight (zTheta P0) := by
  obtain ⟨x, hx⟩ := exists_not_mem_W P0 hg
  have hne : zTheta P0 ≠ genericPoint (Jac K F).left := by
    intro h
    apply hx
    rw [← closure_zTheta P0, h, (genericPoint_spec (Jac K F).left).def]
    trivial
  have hle : zTheta P0 ≤ genericPoint (Jac K F).left := genericPoint_specializes (zTheta P0)
  have hlt : zTheta P0 < genericPoint (Jac K F).left := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show zTheta P0 ⤳ genericPoint (Jac K F).left from h) hle).eq
  exact le_trans le_add_self (Order.coheight_add_one_le hlt)

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

/-- A class `[Zdiv S] - (g-1)[P0]` with `#S = g - 1` lies on `W`. -/
theorem mem_W_of_cls (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (S : Finset (Rfin K F →ₐ[K] K))
    (hS : S.card = n0 K F)
    (h : ((Multiplicative.toAdd (jacPicEquiv K F x) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1)) :
    x.left (IsLocalRing.closedPoint K) ∈ W P0 := by
  let e : Fin (n0 K F) ≃ S := (finCongr hS.symm).trans S.equivFin.symm
  refine (mem_W_iff P0 x).2 ⟨fun i => Sum.inl (ptP (e i).1), ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [toAdd_ofAdd, h, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_ajCls]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Zdiv, clsK_sum, ← Finset.sum_coe_sort S]
  exact (e.sum_comp (fun z : S => clsK K F (Finsupp.single (Sum.inl (ptP z.1) : Place K F) (1 : ℤ)))).symm

end Pts

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Sep =====
section

/-!
# Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)

* **`eq_one_of_stab`**: a `K`-point `c` of `J` with `W(K) · c ⊆ W` is `1` (Riemann's theorem `mem_W_iff` and the
  divisor form `mem_PrincK_of_stab`);
* `hsep_W`: translates of `W` separate `K`-points: for `b ≠ b'` some `a` has `b a ∈ W`, `b' a ∉ W`;
* `support_effI_Theta`: the support of the ideal sheaf `effI Θ` is `W`; `support_effI_Theta_ne_top`;
* **`hsep_Theta`**: the `hsep` hypothesis of `inum_pos` for `D = Θ`.
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
open RamanujanPetersson.IntersectC

universe u

section Sep

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Trivial stabiliser of `W_{g-1}`**: a `K`-point `c` with `W(K) · c ⊆ W` is `1`. -/
theorem eq_one_of_stab (hg : 0 < genusFK K F) (c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hc : ∀ w : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, w.left (IsLocalRing.closedPoint K) ∈ W P0 →
      (w * c).left (IsLocalRing.closedPoint K) ∈ W P0) : c = 1 := by
  obtain ⟨B, hB⟩ : ∃ B : Places.Divisor K F,
      clsK K F B = ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) :=
    QuotientAddGroup.mk_surjective _
  have hd : B.deg = 0 := by
    have := (mem_Pic0K K F).1 (Multiplicative.toAdd (jacPicEquiv K F c)).2
    rwa [← hB, degPicK_clsK] at this
  have hP : B ∈ PrincK K F := by
    refine mem_PrincK_of_stab hg B hd fun S hS => ?_
    have hm : clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) ∈ Pic0K K F := by
      rw [mem_Pic0K, map_sub, map_nsmul, degPicK_clsK, degPicK_clsK, deg_Zdiv, deg_single_one, hS]
      simp
    obtain ⟨w, hwc⟩ : ∃ w : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
        ((Multiplicative.toAdd (jacPicEquiv K F w) : Pic0K K F) : PicK K F) =
          clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) :=
      ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨_, hm⟩), by rw [MulEquiv.apply_symm_apply]; rfl⟩
    obtain ⟨t, ht⟩ := (mem_W_iff P0 (w * c)).1 (hc w (mem_W_of_cls P0 w S hS hwc))
    refine ⟨∑ i, Finsupp.single (t i) 1,
      Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one, ?_⟩
    rw [map_mul] at ht
    have h1 := congrArg (fun z : Multiplicative (Pic0K K F) => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) ht
    simp only [toAdd_mul, toAdd_ofAdd, AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, coe_ajCls] at h1
    rw [hwc, ← hB, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← clsK_sum] at h1
    rw [clsK_add (K := K) (F := F)]
    calc clsK K F (∑ i, Finsupp.single (t i) 1)
        = (clsK K F (∑ i, Finsupp.single (t i) 1) - n0 K F • clsK K F (Finsupp.single P0 1)) +
            n0 K F • clsK K F (Finsupp.single P0 1) := by abel
      _ = (clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) + clsK K F B) +
            n0 K F • clsK K F (Finsupp.single P0 1) := by rw [h1]
      _ = clsK K F (Zdiv S) + clsK K F B := by abel
  have h0 : Multiplicative.toAdd (jacPicEquiv K F c) = 0 := by
    apply Subtype.ext
    rw [← hB, ZeroMemClass.coe_zero]
    exact (QuotientAddGroup.eq_zero_iff B).2 hP
  apply (jacPicEquiv K F).injective
  rw [map_one]
  exact toAdd_eq_zero.1 h0

theorem finite_support_Theta : (Function.support (Theta P0)).Finite :=
  (Set.finite_singleton (zTheta P0)).subset fun z hz => by
    rw [Function.mem_support, Theta_apply] at hz
    split_ifs at hz with h
    · exact h
    · exact absurd rfl hz

end Sep

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve1 =====
section

/-!
# Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)

* `fe P0 e = AJ ≫ transl e : X1 → J` (`p ↦ AJ(p) · e`), `feX` its underlying scheme map, `comp_fe`, `mem_W_fe`;
* **`Dc P0 e := cpull (feX P0 e) Θ`**, a cycle on the curve `X1`; `Dc_nonneg`, `Dc_eq_zero` (support in `f_e⁻¹ W`);
* `plusX` is an open immersion (`ι2`), and `plusX ≫ f_{cE · d} = τ_d ∘ κ` (`plusX_fe`);
* **`Dc_plusX_eq_one`**: `D_e` has multiplicity exactly one at the point `plusX (kpt x)` when `e = cE · c_φ⁻¹`.
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

section Curve1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The curve cycle** `D_e := f_e^* Θ` on `X1`. -/
noncomputable def Dc (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : AlgebraicCycle (X1 K F) ℤ :=
  cpull (feX P0 e) (Theta P0)

variable (hg : 0 < genusFK K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

end Curve1

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

theorem comp_mu2 (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    lift e q ≫ mu2 P0 c2 = (q ≫ ajO P0) * (q ≫ ajO P0) * e * c2 := by
  rw [mu2, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, lift_snd_assoc, lift_fst, ← Category.assoc,
    toUnit_unique (lift e q ≫ toUnit _) (𝟙 _), Category.id_comp]

/-- The bad pairs `(e, q)`: `AJ(q) e ∈ W` but `AJ(q)² e c_2 ∉ jX0 (X0)`. -/
def Bad : Set (Jac K F ⊗ X1O K F).left :=
  (mu1 P0).left ⁻¹' W P0 ∩ (mu2 P0 c2).left ⁻¹' (Set.range (jX0 K F))ᶜ

/-- **The open set of good points**: `Wᶜ ∩ κ⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`. -/
def Ogood : Set (Jac K F).left :=
  (W P0)ᶜ ∩ (kapM cK).left ⁻¹' Set.range (jX0 K F) ∩ ((fst (Jac K F) (X1O K F)).left '' Bad P0 c2)ᶜ

end Curve7

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve8 =====
section

/-!
# Unit S4-ThetaSquare, file Curve8: points of `X1^g` (T4c (D), nonemptiness, part 1)

* `exists_pt_coord`: a `K`-point of `X1^n` with prescribed coordinates;
* `coe_sum_ajCls`, `deg_sum_single`: classes and degrees of `Σ [t_i]`;
* `exists_c3`: the constant `c_3` of class `[W0] - (g-2)[P0] - g[P0]`;
* `eM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)⁻¹`, of class `[W0 - Σ [p_i]] - (g-2)[P0]` (`cls_eM`), surjective on
  `K`-points (`eM_surj`);
* `ell_eq_one_of_not_mem`: `ℓ(G) = 1` when the class `[W0 - G] - (g-2)[P0]` is off `W`;
* `exists_t_swap`: the Riemann-Roch step for the chart condition at a coordinate.
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

section Curve8

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) in
/-- `e_M : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)⁻¹`. -/
noncomputable def eM (c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : PP K F (genusFK K F) ⟶ Jac K F :=
  toUnit (PP K F (genusFK K F)) ≫ c3 * (PhiN P0 (genusFK K F))⁻¹

theorem comp_eM (P0 : Place K F) (c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F)) :
    p ≫ eM P0 c3 = c3 * (p ≫ PhiN P0 (genusFK K F))⁻¹ := by
  rw [eM, MonObj.comp_mul, ← Category.assoc, toUnit_unique (p ≫ toUnit _) (𝟙 _), Category.id_comp,
    GrpObj.comp_inv]

theorem cls_eM (P0 : Place K F) {W0 : Places.Divisor K F} {c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc3 : ((Multiplicative.toAdd (jacPicEquiv K F c3) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
          (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F)) :
    ((Multiplicative.toAdd (jacPicEquiv K F (p ≫ eM P0 c3)) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - ∑ i, Finsupp.single (kPl (p ≫ prj K F (genusFK K F) i)) 1) -
        ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) := by
  rw [comp_eM]
  simp only [_root_.map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg]
  rw [PhiN_val, toAdd_ofAdd, coe_sum_ajCls, hc3, clsK_sub]
  abel

/-- `e_M` is surjective on `K`-points. -/
theorem eM_surj (P0 : Place K F) (c3 x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F), p ≫ eM P0 c3 = x := by
  obtain ⟨t, ht⟩ := exists_eff_rep P0
    (Multiplicative.toAdd (jacPicEquiv K F c3) - Multiplicative.toAdd (jacPicEquiv K F x)).2
  obtain ⟨p, hp⟩ := exists_pt P0 (genusFK K F) t
  have hs : (∑ i, ajCls K F P0 (t i) : Pic0K K F) =
      Multiplicative.toAdd (jacPicEquiv K F c3) - Multiplicative.toAdd (jacPicEquiv K F x) := by
    apply Subtype.ext
    rw [coe_sum_ajCls, clsK_sum, ← ht]
  refine ⟨p, (jacPicEquiv K F).injective ?_⟩
  rw [comp_eM, _root_.map_mul, map_inv, hp, hs]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

end Curve8

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve9 =====
section

/-!
# Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)

On `X1^g` (irreducible) the three open conditions on `p`, with `e := e_M(p) = c_3 Φ_g(p)⁻¹`:
* `Ua`: `c_K e⁻¹ ∈ jX0 (X0)`; `Ub`: `e ∉ W`; `Uj j`: `AJ(p_j)² e c_2 ∈ jX0 (X0)` (each nonempty);
* `mem_Ogood_of_U`: a `K`-point `p` in all of them gives `e ∈ Ogood` (`f_e (q) ∈ W` forces `q = p_j` for some `j`);
* **`exists_kpt_Ogood`**, **`nonempty_Ogood`**, **`dense_Ogood`**: `Ogood P0 cK c2` has a `K`-point and is dense in `J`.
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

section Curve9

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

/-- `c_K e_M(p)⁻¹ ∈ jX0 (X0)`. -/
def Ua : Set (PP K F (genusFK K F)).left :=
  (eM P0 c3).left ⁻¹' ((kapM cK).left ⁻¹' Set.range (jX0 K F))

/-- `e_M(p) ∉ W`. -/
def Ub : Set (PP K F (genusFK K F)).left := (eM P0 c3).left ⁻¹' (W P0)ᶜ

/-- `AJ(p_j)² e_M(p) c_2 ∈ jX0 (X0)`. -/
def Uj (j : Fin (genusFK K F)) : Set (PP K F (genusFK K F)).left :=
  (lift (eM P0 c3) (prj K F (genusFK K F) j) ≫ mu2 P0 c2).left ⁻¹' Set.range (jX0 K F)

theorem isOpen_Ua : IsOpen (Ua P0 cK c3) :=
  (isOpen_range_jX0.preimage (kapM cK).left.continuous).preimage (eM P0 c3).left.continuous

theorem isOpen_Ub : IsOpen (Ub P0 c3) :=
  (isClosed_W P0).isOpen_compl.preimage (eM P0 c3).left.continuous

theorem isOpen_Uj (j : Fin (genusFK K F)) : IsOpen (Uj P0 c2 c3 j) :=
  isOpen_range_jX0.preimage (lift (eM P0 c3) (prj K F (genusFK K F) j) ≫ mu2 P0 c2).left.continuous

theorem nonempty_Ua : (Ua P0 cK c3).Nonempty := by
  obtain ⟨y0⟩ := exists_y0 (K := K) (F := F)
  obtain ⟨p, hp⟩ := eM_surj P0 c3 ((kJ y0)⁻¹ * cK)
  refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
  show (kapM cK).left ((p ≫ eM P0 c3).left (IsLocalRing.closedPoint K)) ∈ Set.range (jX0 K F)
  rw [← pt_comp_kapM, hp, mul_inv_rev, inv_inv, mul_inv_cancel_left, pt_kJ]
  exact ⟨_, rfl⟩

end Curve9

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Lines =====
section

/-!
# S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection

For objects `W`, `C` over `Spec K` (`K` a field):
* `isOpenMap_fst`: the projection `W ⊗ C ⟶ W` is open (Mathlib: every morphism to `Spec K` is universally open);
* `cline W C w : C ⟶ W ⊗ C`, `c ↦ (w, c)` for a `K`-point `w` of `W`; `isPullback_cline`: it is the fibre of the
  projection over `w`; **`mem_range_cline`**: every point of `W ⊗ C` over `w` lies on it.
For `PP n = X1^n` (unit JacComplete):
* `line n i p : X1 ⟶ X1^n`, the `i`-th coordinate line through the `K`-point `p`; `line_val`: it passes through `p`;
  `line_castSucc_fst`: projecting a line of `X1^(n+1)` in a direction `< n` gives a line of `X1^n`;
  `mem_range_line_last`: the fibre of `X1^(n+1) ⟶ X1^n` through `p` is the last line through `p`;
* `exists_kpt_of_closed`: every closed point of `X1^n` is the value of a `K`-point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacComplete
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

section CLine

variable {K : Type u} [Field K]

end CLine

section Lines

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

lemma prj_last (n : ℕ) : prj K F (n + 1) (Fin.last n) = snd (PP K F n) (X1O K F) := by
  rw [prj]; exact Fin.lastCases_last

lemma prj_castSucc (n : ℕ) (j : Fin n) :
    prj K F (n + 1) j.castSucc = fst (PP K F n) (X1O K F) ≫ prj K F n j := by
  rw [prj]; exact Fin.lastCases_castSucc j

lemma line_val_cast (n : ℕ) (j : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n ⊗ X1O K F)
    (ih : ((p ≫ fst _ _) ≫ prj K F n j) ≫ line K F n j (p ≫ fst _ _) = p ≫ fst _ _) :
    (p ≫ fst _ _ ≫ prj K F n j) ≫ lift (line K F n j (p ≫ fst _ _)) (toUnit _ ≫ p ≫ snd _ _) = p := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, lift_fst, ← Category.assoc p, ih]
  · rw [Category.assoc, lift_snd, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (𝟙 _), Category.id_comp]

/-- **The `i`-th line through `p` passes through `p`** (at the parameter `p_i`). -/
theorem line_val : (n : ℕ) → (i : Fin n) → (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) →
    (p ≫ prj K F n i) ≫ line K F n i p = p
  | 0, i, _ => i.elim0
  | n + 1, i, p => by
    induction i using Fin.lastCases with
    | last =>
      rw [line_last, prj_last]
      exact line_val_last n p
    | cast j =>
      rw [line_castSucc, prj_castSucc]
      exact line_val_cast n j p (line_val n j _)

end Lines

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Slice =====
section

/-!
# S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `line_prj_self`, `line_prj_ne`: a line against the projections;
* `cval q g` (the constant `g(q)` as an element of `F`), **`cval_mem`**: it lies in `K`;
* `exists_stalk_of_ord`: nonnegative place order at `q` ⇒ regular at the point `q`;
* `zPP`, `detPP` (the determinant `det_k`), `sliceRow`;
* **`slice_detPP`**: `PsiX (fpull line (detPP ..)) = det (sliceRow ..)`; **`avoid_detPP`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Slice

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem line_prj_self : (n : ℕ) → (i : Fin n) → (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) →
    line K F n i p ≫ prj K F n i = 𝟙 _
  | 0, i, _ => i.elim0
  | n + 1, i, p => by
    induction i using Fin.lastCases with
    | last =>
      rw [line_last, prj_last]
      exact cline_snd _ _ _
    | cast j =>
      rw [prj_castSucc]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ prj K F n j) (line_castSucc_fst n j p)).trans (line_prj_self n j _))

theorem line_prj_ne : (n : ℕ) → (i j : Fin n) → j ≠ i → (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) →
    line K F n i p ≫ prj K F n j = toUnit _ ≫ p ≫ prj K F n j
  | 0, i, _, _, _ => i.elim0
  | n + 1, i, j, hji, p => by
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hji
      | cast j =>
        rw [line_last, prj_castSucc]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ prj K F n j) (cline_fst _ _ _)).trans
            ((Category.assoc _ _ _).trans (congrArg (toUnit (X1O K F) ≫ ·) (Category.assoc _ _ _))))
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [line_castSucc, prj_last]
        exact lift_snd _ _
      | cast j =>
        rw [prj_castSucc]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ prj K F n j) (line_castSucc_fst n i p)).trans
            ((line_prj_ne n i j (fun h => hji (congrArg Fin.castSucc h)) _).trans
              (congrArg (toUnit (X1O K F) ≫ ·) (Category.assoc _ _ _))))

variable (K F) in
/-- The rows of `det_k`: coordinates `τ j` of `X1^n`, then constant maps to the fixed points `m i`. -/
noncomputable def zPP (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) :
    Fin N ⊕ Fin r → ((PP K F n).left ⟶ (X1O K F).left) :=
  Sum.elim (fun j => (prj K F n (τ j)).left) (fun i => (toUnit (PP K F n) ≫ m i).left)

lemma line_zPP_self (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j : Fin N) (hj : τ j = i0) :
    (line K F n i0 p).left ≫ zPP K F n τ m (Sum.inl j) = 𝟙 _ := by
  show (line K F n i0 p).left ≫ (prj K F n (τ j)).left = 𝟙 _
  rw [← Over.comp_left, hj, line_prj_self]
  rfl

lemma line_zPP_ne (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j : Fin N) (hj : τ j ≠ i0) :
    (line K F n i0 p).left ≫ zPP K F n τ m (Sum.inl j) = (toUnit (X1O K F) ≫ (p ≫ prj K F n (τ j))).left := by
  show (line K F n i0 p).left ≫ (prj K F n (τ j)).left = _
  rw [← Over.comp_left, line_prj_ne n i0 (τ j) hj]

lemma line_zPP_inr (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (i : Fin r) :
    (line K F n i0 p).left ≫ zPP K F n τ m (Sum.inr i) = (toUnit (X1O K F) ≫ m i).left := by
  show (line K F n i0 p).left ≫ (toUnit (PP K F n) ≫ m i).left = _
  rw [← Over.comp_left, ← Category.assoc, toUnit_unique (line K F n i0 p ≫ toUnit (PP K F n)) (toUnit (X1O K F))]

end Slice

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cof =====
section

/-!
# S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `det_mem_range`: a matrix with entries in `K` has its determinant in `K`;
* **`slice_mem_LFK`** (Laplace along the variable row): the slice lies in `L(D)` when every `h l` does;
* `ptRow` (the point of each row, `q` in the variable rows), `comp_line_zPP`;
* **`ord_slice_pos`**: the slice vanishes at `q` when two rows sit at `q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cof

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The point of each row of the slice, with `q` in the variable rows. -/
noncomputable def ptRow (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    Fin N ⊕ Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :=
  Sum.elim (fun j => if τ j = i0 then q else p ≫ prj K F n (τ j)) m

/-- The rows of `det_k` restricted to the point `q` of the line. -/
lemma comp_line_zPP (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (a : Fin N ⊕ Fin r) :
    ((toUnit (X1O K F) ≫ q).left ≫ (line K F n i0 p).left) ≫ zPP K F n τ m a =
      (toUnit (X1O K F) ≫ ptRow K F n τ m i0 p q a).left := by
  rw [Category.assoc]
  rcases a with j | i
  · by_cases hj : τ j = i0
    · rw [line_zPP_self n τ m i0 p j hj, Category.comp_id]
      simp only [ptRow, Sum.elim_inl, if_pos hj]
    · rw [line_zPP_ne n τ m i0 p j hj, ← Over.comp_left, ← Category.assoc,
        toUnit_unique ((toUnit (X1O K F) ≫ q) ≫ toUnit (X1O K F)) (toUnit (X1O K F))]
      simp only [ptRow, Sum.elim_inl, if_neg hj]
  · rw [line_zPP_inr n τ m i0 p i, ← Over.comp_left, ← Category.assoc,
      toUnit_unique ((toUnit (X1O K F) ≫ q) ≫ toUnit (X1O K F)) (toUnit (X1O K F))]
    rfl

end Cof

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Eff =====
section

/-!
# S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `ptC`, `Zsl` (the points of the constant rows and their divisor), `ptRow_of_ne`;
* `ord_nonneg_of_mem_LFK`, `deg_finsetSum_single`, `deg_Zsl`;
* **`slice_mem_LFK_sub`**: the slice lies in `L(H - Zsl)`;
* **`slice_eff`**: `G := div f + H - Zsl` is effective of degree `deg H - (N + r - 1)`;
* **`eq_of_ell_one`**: effective, linearly equivalent, `ℓ(G) = 1` ⇒ equal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Eff

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The points of the constant rows (the value at the variable row is unused). -/
noncomputable def ptC (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) : Fin N ⊕ Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :=
  Sum.elim (fun j => p ≫ prj K F n (τ j)) m

variable (K F) in
/-- The divisor of the constant rows (all rows but `inl j0`). -/
noncomputable def Zsl (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) : Places.Divisor K F :=
  ∑ a ∈ Finset.univ.erase (Sum.inl j0), Finsupp.single (kPl (ptC K F n τ m p a)) 1

lemma ptRow_of_ne (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {j0 : Fin N} (hj0 : ∀ j, τ j = i0 → j = j0)
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) {a : Fin N ⊕ Fin r} (ha : a ≠ Sum.inl j0) :
    ptRow K F n τ m i0 p q a = ptC K F n τ m p a := by
  rcases a with j | i
  · have hj : τ j ≠ i0 := fun e => ha (by rw [hj0 j e])
    simp only [ptRow, ptC, Sum.elim_inl, if_neg hj]
  · rfl

theorem deg_Zsl (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) :
    (Zsl K F n τ m p j0).deg + 1 = N + r := by
  rw [Zsl, deg_finsetSum_single, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have : 1 ≤ N + r := by have := j0.2; omega
  omega

end Eff

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZ =====
section

/-!
# S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `ellFK_add_div`, `ellFK_of_clsK_eq`: `ℓ` only depends on the divisor class;
* `sliceRow_of_ne`: the constant rows of a slice are the values at `ptC`;
* **`slice_ne_zero`**: the slice with one variable row is nonzero when `ℓ(H - Zsl) ≤ 1`;
* **`slice_ne_zero_const`**: the all-constant slice is nonzero when `ℓ(H - Zall) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section NZ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The divisor of all rows (used when no row is variable). -/
noncomputable def Zall (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) : Places.Divisor K F :=
  ∑ a, Finsupp.single (kPl (ptC K F n τ m p a)) 1

end NZ

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Maps =====
section

/-!
# S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `cpull_pbTh_X1`, **`cpull_cubeZ_X1`**: the cube divisor pulled back along any `f : X1 ⟶ J^3`;
* `comp_finprod`: composition distributes over finite products in the hom-group;
* `psiS P0 n β S := Π_{k : β k ∈ S} pr_k ≫ aj` (blocks given by `β : Fin n → Fin 3`), `psiS_mul`;
* `Phi3 P0 n β := (psiS {0}, psiS {1}, psiS {2})`, `Phi3_q1`, `Phi3_q2`, `Phi3_q3`;
* **`line_psiS_transl`**: along the `i0`-th line through `p`, `psiS S ≫ τ_{x0}` is `f_e` (if `β i0 ∈ S`) or the
  constant `e`, for `e = (p ≫ psiE S i0) * x0`;
* `cpull_const_Theta`: a constant map off `W` pulls `Θ` back to `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Maps

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `ψ_S := Π_{k : β k ∈ S} pr_k ≫ aj : X1^n ⟶ J`. -/
noncomputable def psiS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) : PP K F n ⟶ Jac K F :=
  ∏ k ∈ Finset.univ.filter (fun k => β k ∈ S), prj K F n k ≫ ajO P0

/-- The same product without the coordinate `i0`. -/
noncomputable def psiE (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n) : PP K F n ⟶ Jac K F :=
  ∏ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0, prj K F n k ≫ ajO P0

theorem psiS_mul (n : ℕ) (β : Fin n → Fin 3) {S T : Finset (Fin 3)} (hST : Disjoint S T) :
    psiS P0 n β S * psiS P0 n β T = psiS P0 n β (S ∪ T) := by
  rw [psiS, psiS, psiS, ← Finset.prod_union]
  · congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  · rw [Finset.disjoint_filter]
    intro k _ hS hT
    exact Finset.disjoint_left.mp hST hS hT

theorem comp_psiS_mul {X : Over (Spec (.of K))} {n : ℕ} (L : X ⟶ PP K F n) (β : Fin n → Fin 3) {S T : Finset (Fin 3)}
    (hST : Disjoint S T) : (L ≫ psiS P0 n β S) * (L ≫ psiS P0 n β T) = L ≫ psiS P0 n β (S ∪ T) := by
  rw [← MonObj.comp_mul, psiS_mul P0 n β hST]

/-- `Φ3 := (ψ_{0}, ψ_{1}, ψ_{2}) : X1^n ⟶ J^3`. -/
noncomputable def Phi3 (n : ℕ) (β : Fin n → Fin 3) : PP K F n ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F) :=
  lift (psiS P0 n β {0}) (lift (psiS P0 n β {1}) (psiS P0 n β {2}))

lemma Phi3_q1 (n : ℕ) (β : Fin n → Fin 3) : Phi3 P0 n β ≫ q1 K F = psiS P0 n β {0} := lift_fst _ _

lemma Phi3_q2 (n : ℕ) (β : Fin n → Fin 3) : Phi3 P0 n β ≫ q2 K F = psiS P0 n β {1} := by
  rw [q2, ← Category.assoc, Phi3, lift_snd, lift_fst]

lemma Phi3_q3 (n : ℕ) (β : Fin n → Fin 3) : Phi3 P0 n β ≫ q3 K F = psiS P0 n β {2} := by
  rw [q3, ← Category.assoc, Phi3, lift_snd, lift_snd]

/-- **`ψ_S` along the `i0`-th line through `p`.** -/
theorem line_comp_psiS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    line K F n i0 p ≫ psiS P0 n β S =
      (if β i0 ∈ S then ajO P0 else 1) * (toUnit (X1O K F) ≫ p ≫ psiE P0 n β S i0) := by
  have hc : ∀ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0,
      line K F n i0 p ≫ prj K F n k ≫ ajO P0 = toUnit (X1O K F) ≫ p ≫ prj K F n k ≫ ajO P0 := by
    intro k hk
    rw [← Category.assoc, line_prj_ne n i0 k (Finset.ne_of_mem_erase hk) p]
    simp only [Category.assoc]
  have hE : toUnit (X1O K F) ≫ p ≫ psiE P0 n β S i0 =
      ∏ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0, line K F n i0 p ≫ prj K F n k ≫ ajO P0 := by
    rw [Finset.prod_congr rfl hc, psiE, comp_finprod, comp_finprod]
  unfold psiS
  rw [comp_finprod, hE]
  by_cases hS : β i0 ∈ S
  · have hmem : i0 ∈ Finset.univ.filter (fun k => β k ∈ S) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
    rw [if_pos hS, ← Finset.mul_prod_erase _ _ hmem,
      ← Category.assoc, line_prj_self, Category.id_comp]
  · have hnm : i0 ∉ Finset.univ.filter (fun k => β k ∈ S) := fun h => hS (Finset.mem_filter.mp h).2
    rw [if_neg hS, _root_.one_mul, Finset.erase_eq_of_notMem hnm]

/-- **`ψ_S ≫ τ_{x0}` along a line**: `f_e` or the constant `e`, `e = ψ_S'(p) · x0`. -/
theorem line_psiS_transl (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    (line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0 =
      if β i0 ∈ S then fe P0 ((p ≫ psiE P0 n β S i0) * x0)
      else toUnit (X1O K F) ≫ ((p ≫ psiE P0 n β S i0) * x0) := by
  rw [line_comp_psiS, comp_transl]
  by_cases hS : β i0 ∈ S
  · rw [if_pos hS, if_pos hS, fe, comp_transl, MonObj.comp_mul, _root_.mul_assoc]
  · rw [if_neg hS, if_neg hS, _root_.one_mul, MonObj.comp_mul]

end Maps

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Test =====
section

/-!
# S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
At `z = p_{i0}` on the `i0`-th line through `p`:
* `cpull_detPP_kpt`: the determinant side is `ord_{p_{i0}}` of the slice;
* `ord_slice_const`: an all-constant slice has order `0` everywhere;
* `ord_slice_eq`: the order of a one-variable slice is `G (p_{i0})` once `G ∼ H - Zsl`, `ℓ(G) = 1`;
* `cube_side_mem`, `cube_side_not_mem`: the `Θ` side via `line_psiS_transl`, `Dc_kpt_eq`, `cpull_const_Theta`;
* **`test_mem`**, **`test_not_mem`**: the two sides agree at `z` (both avoid);
* `Zsl_eq`, `jacPic_psiE`, `cls_good_eq`, **`cls_test`**: the class bookkeeping `[G_S] = [H - Zsl_S]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Test

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- Regularity of the basis at the constant rows, from `H = 0` there. -/
lemma reg_of_H (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (h : Fin N ⊕ Fin r → F) (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N)
    (hτ0 : τ j0 = i0) (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0) :
    (∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l)) ∧ (∀ i l, 0 ≤ (kPl (m i)).ord (h l)) :=
  ⟨fun j hj l => ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inl j) fun e => hj (by rw [Sum.inl_injective e, hτ0])),
    fun i l => ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inr i) (by simp))⟩

/-- `Zsl` for a block enumeration `τ` of `{k | β k ∈ S}` with `τ j0 = i0`. -/
theorem Zsl_eq (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (i0 : Fin n)
    (j0 : Fin N) (hτ0 : τ j0 = i0) (hτi : Function.Injective τ) (hτS : ∀ k, β k ∈ S ↔ ∃ j, τ j = k) :
    Zsl K F n τ m p j0 = ∑ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0,
        Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ) + ∑ i, Finsupp.single (kPl (m i)) (1 : ℤ) := by
  have him : Finset.univ.image τ = Finset.univ.filter (fun k => β k ∈ S) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, hτS k]
  have hi0 : i0 ∈ Finset.univ.filter (fun k => β k ∈ S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hτS i0).mpr ⟨j0, hτ0⟩⟩
  have hall : Finsupp.single (kPl (p ≫ prj K F n i0)) (1 : ℤ) + Zsl K F n τ m p j0 =
      ∑ a, Finsupp.single (kPl (ptC K F n τ m p a)) (1 : ℤ) := by
    rw [Zsl, ← Finset.add_sum_erase _ _ (Finset.mem_univ (Sum.inl j0 : Fin N ⊕ Fin r)), ← hτ0]
    all_goals rfl
  have hsplit : ∑ a, Finsupp.single (kPl (ptC K F n τ m p a)) (1 : ℤ) =
      Finsupp.single (kPl (p ≫ prj K F n i0)) (1 : ℤ) +
        (∑ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0, Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ) +
          ∑ i, Finsupp.single (kPl (m i)) (1 : ℤ)) := by
    rw [← add_assoc, Finset.add_sum_erase _ (fun k => Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ)) hi0, ← him,
      Finset.sum_image (fun x _ y _ e => hτi e), Fintype.sum_sum_type]
    all_goals rfl
  exact add_left_cancel (hall.trans hsplit)

/-- The class of `p ≫ ψ'_S`: `Σ_{k ∈ T} ([p_k] - [P0])`. -/
theorem jacPic_psiE (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    jacPicEquiv K F (p ≫ psiE P0 n β S i0) = Multiplicative.ofAdd
      (∑ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0, ajCls K F P0 (kPl (p ≫ prj K F n k))) := by
  rw [psiE, comp_finprod, map_prod, ofAdd_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Category.assoc, jacPicEquiv_ajO]

/-- **Class bookkeeping**: `[G] = [H - Σ_T [p_k] - Σ [m_i]]` from `IsGoodFor.cls` and the class of `x0`. -/
theorem cls_good_eq {W0 G H : Places.Divisor K F} (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hH : clsK K F H = ((genusFK K F : ℤ) + r + ((Finset.univ.filter (fun k => β k ∈ S)).erase i0).card) •
      clsK K F (Finsupp.single P0 1))
    (hcls : ((Multiplicative.toAdd (jacPicEquiv K F ((p ≫ psiE P0 n β S i0) * x0)) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1)) :
    clsK K F G = clsK K F (H - (∑ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0,
        Finsupp.single (kPl (p ≫ prj K F n k)) 1 + ∑ i, Finsupp.single (kPl (m i)) 1)) := by
  rw [map_mul, jacPic_psiE, toAdd_mul, toAdd_ofAdd, AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, hx0,
    clsK_sub] at hcls
  simp only [coe_ajCls] at hcls
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← clsK_sum, clsK_add] at hcls
  rw [clsK_sub, clsK_add, hH]
  have key : clsK K F G = clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
      (clsK K F W0 - clsK K F G - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1)) := by abel
  rw [key, ← hcls]
  module

end Test

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Good =====
section

/-!
# S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `IsSat n i B`: `B` contains the `i`-th line through each of its `K`-points; `isSat_iUnion`, `isSat_empty`;
* `ConstAlong n i φ`: `φ` is constant along the `i`-th lines; `isSat_preimage`, closure under `≫`, `*`, `⁻¹`,
  constants, `psiE`, `epsS := psiE · x0`;
* `ne_univ_of_compl`: finitely many closed sets with nonempty complements do not cover an irreducible space;
* `exists_ne_place`: every place has a different one;
* **`bad P0 n β i x0 cK c2 A`** `= ⋃ badC`: `e_S(p) ∉ Ogood` (all `S`), `p_k = A l` (`k ≠ i`), `p_k = p_k'`
  (`k ≠ k'`, both `≠ i`), in Abel-Jacobi coordinates; **`isClosed_bad`**, **`isSat_bad`**, **`bad_ne_univ`** (when
  `x0 ∈ Ogood`), **`of_not_mem_bad`** (the three conditions at a good `K`-point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Good

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem constAlong_prj {n : ℕ} {i k : Fin n} (hk : k ≠ i) : ConstAlong n i (prj K F n k) :=
  fun p => line_prj_ne n i k hk p

theorem constAlong_psiE (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i : Fin n) :
    ConstAlong n i (psiE P0 n β S i) := fun p => by
  unfold psiE
  simp only [comp_finprod]
  exact Finset.prod_congr rfl fun k hk =>
    constAlong_comp (constAlong_prj (Finset.ne_of_mem_erase hk)) (ajO P0) p

/-- `e_S := ψ_{S - i} · x0 : X1^n ⟶ J`. -/
noncomputable def epsS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i : Fin n)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : PP K F n ⟶ Jac K F :=
  psiE P0 n β S i * (toUnit (PP K F n) ≫ x0)

theorem comp_epsS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i : Fin n)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    p ≫ epsS P0 n β S i x0 = (p ≫ psiE P0 n β S i) * x0 := by
  rw [epsS, MonObj.comp_mul, ← Category.assoc, toUnit_unique (p ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem constAlong_epsS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i : Fin n)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : ConstAlong n i (epsS P0 n β S i x0) :=
  constAlong_mul (constAlong_psiE P0 n β S i) (constAlong_const n i x0)

/-- At the point with all coordinates `P0`, `ψ_{S - i} = 1`. -/
theorem psiE_of_P0 (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i : Fin n)
    (p0 : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (hp0 : ∀ k, kPl (p0 ≫ prj K F n k) = P0) :
    p0 ≫ psiE P0 n β S i = 1 := by
  unfold psiE
  rw [comp_finprod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← Category.assoc, kPl_spec P0, hp0 k, ajK_self]

variable (n : ℕ) (β : Fin n → Fin 3) (i : Fin n) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {s : ℕ}
  (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))

/-- The pieces of the bad set for direction `i`. -/
noncomputable def badC : Finset (Fin 3) ⊕ (Fin n × Fin s) ⊕ (Fin n × Fin n) → Set (PP K F n).left
  | Sum.inl S => (epsS P0 n β S i x0).left ⁻¹' (Ogood P0 cK c2)ᶜ
  | Sum.inr (Sum.inl kl) => if kl.1 = i then ∅ else
      (prj K F n kl.1 ≫ ajO P0).left ⁻¹' {pt (Jac K F) (A kl.2 ≫ ajO P0)}
  | Sum.inr (Sum.inr kk) => if kk.1 = i ∨ kk.2 = i ∨ kk.1 = kk.2 then ∅ else
      ((prj K F n kk.1 ≫ ajO P0) * (prj K F n kk.2 ≫ ajO P0)⁻¹).left ⁻¹' {pt (Jac K F) 1}

/-- **The bad set for direction `i`.** -/
noncomputable def bad : Set (PP K F n).left := ⋃ c, badC P0 n β i x0 cK c2 A c

lemma badC_inl (S : Finset (Fin 3)) :
    badC P0 n β i x0 cK c2 A (Sum.inl S) = (epsS P0 n β S i x0).left ⁻¹' (Ogood P0 cK c2)ᶜ := rfl

lemma badC_mid (k : Fin n) (l : Fin s) : badC P0 n β i x0 cK c2 A (Sum.inr (Sum.inl (k, l))) =
    if k = i then ∅ else (prj K F n k ≫ ajO P0).left ⁻¹' {pt (Jac K F) (A l ≫ ajO P0)} := rfl

lemma badC_pair (k k' : Fin n) : badC P0 n β i x0 cK c2 A (Sum.inr (Sum.inr (k, k'))) =
    if k = i ∨ k' = i ∨ k = k' then ∅ else
      ((prj K F n k ≫ ajO P0) * (prj K F n k' ≫ ajO P0)⁻¹).left ⁻¹' {pt (Jac K F) 1} := rfl

theorem isSat_badC (c : Finset (Fin 3) ⊕ (Fin n × Fin s) ⊕ (Fin n × Fin n)) :
    IsSat n i (badC P0 n β i x0 cK c2 A c) := by
  rcases c with S | ⟨k, l⟩ | ⟨k, k'⟩
  · exact isSat_preimage (constAlong_epsS P0 n β S i x0) _
  · rw [badC_mid]
    split_ifs with h
    · exact isSat_empty n i
    · exact isSat_preimage (constAlong_comp (constAlong_prj h) _) _
  · rw [badC_pair]
    split_ifs with h
    · exact isSat_empty n i
    · simp only [not_or] at h
      exact isSat_preimage (constAlong_mul (constAlong_comp (constAlong_prj h.1) _)
        (constAlong_inv (constAlong_comp (constAlong_prj h.2.1) _))) _

/-- **The conditions at a `K`-point off the bad set.** -/
theorem of_not_mem_bad (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hp : p.left (IsLocalRing.closedPoint K) ∉ bad P0 n β i x0 cK c2 A) :
    (∀ S, pt (Jac K F) ((p ≫ psiE P0 n β S i) * x0) ∈ Ogood P0 cK c2) ∧
      (∀ k l, k ≠ i → kPl (p ≫ prj K F n k) ≠ kPl (A l)) ∧
      (∀ k k', k ≠ i → k' ≠ i → k ≠ k' → kPl (p ≫ prj K F n k) ≠ kPl (p ≫ prj K F n k')) := by
  have hc : ∀ c, p.left (IsLocalRing.closedPoint K) ∉ badC P0 n β i x0 cK c2 A c :=
    fun c h => hp (Set.mem_iUnion.mpr ⟨c, h⟩)
  refine ⟨fun S => ?_, fun k l hk => ?_, fun k k' hk hk' hkk => ?_⟩
  · have h := hc (Sum.inl S)
    rw [badC_inl] at h
    have h' : (p ≫ epsS P0 n β S i x0).left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2 := not_not.mp h
    rw [comp_epsS] at h'
    exact h'
  · have h := hc (Sum.inr (Sum.inl (k, l)))
    rw [badC_mid, if_neg hk] at h
    intro e
    apply h
    show (p ≫ prj K F n k ≫ ajO P0).left (IsLocalRing.closedPoint K) = pt (Jac K F) (A l ≫ ajO P0)
    rw [← Category.assoc, kPl_spec P0 (p ≫ prj K F n k), kPl_spec P0 (A l), e]
    rw [pt, pt0]
  · have h := hc (Sum.inr (Sum.inr (k, k')))
    have hn : ¬ (k = i ∨ k' = i ∨ k = k') := by simp only [not_or]; exact ⟨hk, hk', hkk⟩
    rw [badC_pair, if_neg hn] at h
    intro e
    apply h
    show (p ≫ ((prj K F n k ≫ ajO P0) * (prj K F n k' ≫ ajO P0)⁻¹)).left (IsLocalRing.closedPoint K) =
      pt (Jac K F) 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, kPl_spec P0 (p ≫ prj K F n k),
      kPl_spec P0 (p ≫ prj K F n k'), e, mul_inv_cancel]
    rw [pt, pt0]

end Good

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Asm1 =====
section

/-!
# S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `tauS`, `j0S`: the enumeration of the block `{k | β k ∈ S}`;
* `HS`, `YS`, `Vp`, `VS`: the correction divisors; **`cancel_VS`**: their signed cube sum is `0`;
* **`test_S`**: off `bad i0`, both sides avoid and `cpull det_S = cpull Θ_S + VS_S (p_{i0})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Asm1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `Y_S := Σ_{k ∈ block S, k ≠ i0} [p_k] + Σ [m_l]` (`= Zsl_S` when `β i0 ∈ S`). -/
noncomputable def YS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {r : ℕ} (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) :
    Places.Divisor K F :=
  ∑ k ∈ (Finset.univ.filter (fun k => β k ∈ S)).erase i0, Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ) +
    ∑ i, Finsupp.single (kPl (m i)) (1 : ℤ)

/-- The correction `Y_S - H_S`. -/
noncomputable def Vp (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {r : ℕ} (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) :
    Places.Divisor K F :=
  YS n β S i0 p m - HS P0 n β S r

/-- The correction of the line test for `S` in direction `i0` (`0` when `β i0 ∉ S`). -/
noncomputable def VS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {r : ℕ} (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) :
    Places.Divisor K F :=
  if β i0 ∈ S then Vp P0 n β S i0 p m else 0

theorem Vp_union (n : ℕ) (β : Fin n → Fin 3) (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) {S T : Finset (Fin 3)} (hST : Disjoint S T) :
    Vp P0 n β (S ∪ T) i0 p m = Vp P0 n β S i0 p m + Vp P0 n β T i0 p m - Vp P0 n β ∅ i0 p m := by
  have hU : Finset.univ.filter (fun k => β k ∈ S ∪ T) =
      Finset.univ.filter (fun k => β k ∈ S) ∪ Finset.univ.filter (fun k => β k ∈ T) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  have hD : Disjoint (Finset.univ.filter (fun k => β k ∈ S)) (Finset.univ.filter (fun k => β k ∈ T)) :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 => Finset.disjoint_left.mp hST h1 h2
  have hE : Finset.univ.filter (fun k : Fin n => β k ∈ (∅ : Finset (Fin 3))) = ∅ := by
    ext k
    simp
  have hD' : Disjoint ((Finset.univ.filter (fun k => β k ∈ S)).erase i0)
      ((Finset.univ.filter (fun k => β k ∈ T)).erase i0) :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hD)
  simp only [Vp, YS, HS]
  rw [hU, hE, Finset.erase_union_distrib, Finset.sum_union hD', Finset.card_union_of_disjoint hD,
    Finset.erase_empty, Finset.sum_empty, Finset.card_empty]
  push_cast
  module

/-- **The corrections cancel in the signed cube sum.** -/
theorem cancel_VS (n : ℕ) (β : Fin n → Fin 3) (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) :
    VS P0 n β {0, 1, 2} i0 p m - VS P0 n β {0, 1} i0 p m - VS P0 n β {0, 2} i0 p m - VS P0 n β {1, 2} i0 p m +
      VS P0 n β {0} i0 p m + VS P0 n β {1} i0 p m + VS P0 n β {2} i0 p m = 0 := by
  have hu : ∀ (a : Fin 3) (s : Finset (Fin 3)), a ∉ s →
      Vp P0 n β (insert a s) i0 p m = Vp P0 n β {a} i0 p m + Vp P0 n β s i0 p m - Vp P0 n β ∅ i0 p m := by
    intro a s ha
    rw [Finset.insert_eq]
    exact Vp_union P0 n β i0 p m (Finset.disjoint_singleton_left.mpr ha)
  have h12 := hu 1 {2} (by decide)
  have h012 := hu 0 {1, 2} (by decide)
  have h01 := hu 0 {1} (by decide)
  have h02 := hu 0 {2} (by decide)
  have hb : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases hb (β i0) with h | h | h <;> simp +decide [VS, h, h012, h01, h02, h12] <;> abel

theorem facts_of_not_mem_bad (n : ℕ) (β : Fin n → Fin 3) (i0 : Fin n)
    (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ} (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (q0 : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (hq0 : kPl q0 = P0) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hp : p.left (IsLocalRing.closedPoint K) ∉ bad P0 n β i0 x0 cK c2 (Matrix.vecCons q0 m)) :
    (∀ S, pt (Jac K F) ((p ≫ psiE P0 n β S i0) * x0) ∈ Ogood P0 cK c2) ∧
      (∀ k, k ≠ i0 → kPl (p ≫ prj K F n k) ≠ P0) ∧
      (∀ k l, k ≠ i0 → kPl (p ≫ prj K F n k) ≠ kPl (m l)) ∧
      (∀ k k', k ≠ i0 → k' ≠ i0 → k ≠ k' → kPl (p ≫ prj K F n k) ≠ kPl (p ≫ prj K F n k')) := by
  obtain ⟨h1, h2, h3⟩ := of_not_mem_bad P0 n β i0 x0 cK c2 (Matrix.vecCons q0 m) p hp
  refine ⟨h1, fun k hk => ?_, fun k l hk => ?_, h3⟩
  · have h := h2 k 0 hk
    rwa [Matrix.cons_val_zero, hq0] at h
  · have h := h2 k l.succ hk
    rwa [Matrix.cons_val_succ] at h

theorem H0_ptC (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (i0 : Fin n)
    (hP0 : ∀ k, k ≠ i0 → kPl (p ≫ prj K F n k) ≠ P0) (hm0 : ∀ l, kPl (m l) ≠ P0) (a : Fin N ⊕ Fin r)
    (ha : ∀ j, a = Sum.inl j → τ j ≠ i0) : HS P0 n β S r (kPl (ptC K F n τ m p a)) = 0 := by
  classical
  have hne : kPl (ptC K F n τ m p a) ≠ P0 := by
    rcases a with j | l
    · exact hP0 _ (ha j rfl)
    · exact hm0 l
  rw [HS, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hne), smul_zero]

theorem inj_ptC (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (i0 : Fin n) (hτi : Function.Injective τ)
    (hpm : ∀ k l, k ≠ i0 → kPl (p ≫ prj K F n k) ≠ kPl (m l))
    (hpp : ∀ k k', k ≠ i0 → k' ≠ i0 → k ≠ k' → kPl (p ≫ prj K F n k) ≠ kPl (p ≫ prj K F n k'))
    (hmm : ∀ l l', kPl (m l) = kPl (m l') → l = l') (a b : Fin N ⊕ Fin r)
    (ha : ∀ j, a = Sum.inl j → τ j ≠ i0) (hb : ∀ j, b = Sum.inl j → τ j ≠ i0)
    (e : kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b)) : a = b := by
  rcases a with j | l <;> rcases b with j' | l'
  · by_cases hjj : τ j = τ j'
    · rw [hτi hjj]
    · exact absurd e (hpp _ _ (ha j rfl) (hb j' rfl) hjj)
  · exact absurd e (hpm _ l' (ha j rfl))
  · exact absurd e.symm (hpm _ l (hb j' rfl))
  · rw [hmm l l' e]

theorem Zall_split (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτi : Function.Injective τ) (hτS : ∀ k, β k ∈ S ↔ ∃ j, τ j = k) :
    Zall K F n τ m p = ∑ k ∈ Finset.univ.filter (fun k => β k ∈ S),
        Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ) + ∑ i, Finsupp.single (kPl (m i)) (1 : ℤ) := by
  have him : Finset.univ.image τ = Finset.univ.filter (fun k => β k ∈ S) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, hτS k]
  rw [Zall, Fintype.sum_sum_type, ← him, Finset.sum_image (fun x _ y _ e => hτi e)]
  all_goals rfl

theorem deg_Zall (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n) (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) : (Zall K F n τ m p).deg = (N : ℤ) + r := by
  have h := degPicK_clsK (K := K) (F := F) (Zall K F n τ m p)
  rw [Zall, clsK_sum, map_sum] at h
  simp only [degPicK_clsK, deg_single_one, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin, nsmul_eq_mul, _root_.mul_one] at h
  push_cast at h
  rw [Zall]
  exact h.symm

end Asm1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Pick =====
section

/-!
# S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `xM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)` (class `[W0 + Σ [p_i]] - (3g-2)[P0]`, `cls_xM`), onto on `K`-points;
* `badM`: the closed conditions "`x0 ∉ Ogood`", "`p_l = P0`", "`p_l = p_l'`" on `X1^g`, each missing a point;
* **`exists_m_x0`**: `g` distinct points `m_l ≠ P0` with `x0 := c_3 Φ_g(m) ∈ Ogood` of the class `cube_PP` needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Pick

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `x_M : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)`. -/
noncomputable def xM (c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : PP K F (genusFK K F) ⟶ Jac K F :=
  toUnit (PP K F (genusFK K F)) ≫ c3 * PhiN P0 (genusFK K F)

theorem comp_xM (c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F)) :
    p ≫ xM P0 c3 = c3 * (p ≫ PhiN P0 (genusFK K F)) := by
  rw [xM, MonObj.comp_mul, ← Category.assoc, toUnit_unique (p ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem cls_xM {W0 : Places.Divisor K F} {c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F}
    (hc3 : ((Multiplicative.toAdd (jacPicEquiv K F c3) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) -
          (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1))
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F)) :
    ((Multiplicative.toAdd (jacPicEquiv K F (p ≫ xM P0 c3)) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (p ≫ prj K F (genusFK K F) i)) 1) -
        (2 * (genusFK K F : ℤ) + (genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) := by
  rw [comp_xM, _root_.map_mul, toAdd_mul, AddSubgroup.coe_add, PhiN_val, toAdd_ofAdd, coe_sum_ajCls, hc3,
    clsK_add]
  module

theorem xM_surj (c3 x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (genusFK K F), p ≫ xM P0 c3 = x := by
  obtain ⟨p, hp⟩ := eM_surj P0 1 (x⁻¹ * c3)
  refine ⟨p, ?_⟩
  rw [comp_eM, _root_.one_mul] at hp
  have h2 : p ≫ PhiN P0 (genusFK K F) = c3⁻¹ * x := by
    rw [← inv_inv (p ≫ PhiN P0 (genusFK K F)), hp, mul_inv_rev, inv_inv]
  rw [comp_xM, h2, mul_inv_cancel_left]

variable (cK c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

/-- The closed conditions to avoid on `X1^g`. -/
noncomputable def badM : Unit ⊕ Fin (genusFK K F) ⊕ (Fin (genusFK K F) × Fin (genusFK K F)) →
    Set (PP K F (genusFK K F)).left
  | Sum.inl _ => (xM P0 c3).left ⁻¹' (Ogood P0 cK c2)ᶜ
  | Sum.inr (Sum.inl l) => (prj K F (genusFK K F) l ≫ ajO P0).left ⁻¹' {pt (Jac K F) 1}
  | Sum.inr (Sum.inr ll) => if ll.1 = ll.2 then ∅ else
      ((prj K F (genusFK K F) ll.1 ≫ ajO P0) * (prj K F (genusFK K F) ll.2 ≫ ajO P0)⁻¹).left ⁻¹'
        {pt (Jac K F) 1}

end Pick

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrOpen =====
section

/-!
# S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `jacPic_psiS`, `cls_psiS`: the class of `p ≫ ψ_S` is `[Σ_{k ∈ blk} p_k] - #blk [P0]`;
* `ell_one_of_cls`: off `W`, a degree-`g` divisor in the class `[e] + g[P0]` has `ℓ = 1`;
* `blocks_of_Zdiv`: `Zdiv T = Σ_{k ∈ s} [v k]` with `#s = #T` makes `v` a bijection onto the points of `T`;
* `VJ P0 d := {x | x d⁻¹ ∈ jX0 (X0)} \ W` (open), `exists_yR_of_mem_VJ`;
* **`hH_of_mem`**: hypothesis (H) of `trPP` at every `K`-point of `ψ_S⁻¹ VJ` (`#blk = g`, `[d] = [Θ] - g[P0]`);
* **`trPP_open`**: the block trace identity once `ψ_S⁻¹ VJ` is nonempty.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section TrOpen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The class of `p ≫ ψ_S`: `Σ_{k ∈ blk} ([p_k] - [P0])`. -/
theorem jacPic_psiS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    jacPicEquiv K F (p ≫ psiS P0 n β S) = Multiplicative.ofAdd
      (∑ k ∈ blk n β S, ajCls K F P0 (kPl (p ≫ prj K F n k))) := by
  rw [psiS, comp_finprod, map_prod, ofAdd_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Category.assoc, jacPicEquiv_ajO]

theorem cls_psiS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    ((Multiplicative.toAdd (jacPicEquiv K F (p ≫ psiS P0 n β S)) : Pic0K K F) : PicK K F) =
      clsK K F (∑ k ∈ blk n β S, Finsupp.single (kPl (p ≫ prj K F n k)) (1 : ℤ)) -
        ((blk n β S).card : ℤ) • clsK K F (Finsupp.single P0 1) := by
  rw [jacPic_psiS, toAdd_ofAdd, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_ajCls]
  rw [Finset.sum_sub_distrib, Finset.sum_const, clsK_sum, natCast_zsmul]

/-- The open of `J` where the trace identity is checked: `x d⁻¹` on the chart and `x ∉ W`. -/
def VJ (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : Set (Jac K F).left :=
  (transl (Jac K F) d⁻¹).left ⁻¹' Set.range (jX0 K F) ∩ (W P0)ᶜ

theorem exists_yR_of_mem_VJ (d e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : e.left (IsLocalRing.closedPoint K) ∈ VJ P0 d) :
    ∃ yR : LawRing K F →ₐ[K] K, e.left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d ∧
      kJ yR * d = e := by
  obtain ⟨yR, hy⟩ := exists_kJ (e * d⁻¹) (by
    rw [← point_comp_transl (Jac K F) e d⁻¹]
    exact he.1)
  have h2 : kJ yR * d = e := by rw [hy, inv_mul_cancel_right]
  exact ⟨yR, by rw [← kJ_transl_left d yR, point_comp_transl, h2], h2⟩

end TrOpen

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrA =====
section

/-!
# S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `fpull_eq_ffMap`, `fpull_comp_dom`: along dominant maps `fpull` is the field map `ffMap`;
* `surjective_hom_of_nonempty`, `surjective_fst_left`, `surjective_snd_left`; `surjective_prj`, `isDominant_prj`;
* `qb b` (the three projections `J^3 ⟶ J`), `isDominant_qb`, `Phi3_qb`;
* **`ffMap_Phi3_fpull`**: `Φ3^# (q_b^# G) = ψ_{b}^# G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Dom

variable {C P Y : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral Y]

end Dom

section GrA

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem Phi3_qb (n : ℕ) (β : Fin n → Fin 3) (b : Fin 3) : Phi3 P0 n β ≫ qb K F b = psiS P0 n β {b} := by
  fin_cases b
  · exact Phi3_q1 P0 n β
  · exact Phi3_q2 P0 n β
  · exact Phi3_q3 P0 n β

end GrA

end RamanujanPetersson.ThetaCube


end


