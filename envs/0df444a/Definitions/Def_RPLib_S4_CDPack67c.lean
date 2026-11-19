-- Prove2me | Definitions.Def_RPLib_S4_CDPack67c
-- name    : RPLib_S4_CDPack67c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:28:29.101833+00:00
-- url     : https://prove2.me/theorems/b187d382-6b67-4cdd-b6f5-ade6acd937a8
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 67c of 71
-- statement:
--   Part 67c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack67b

/-!
# Curve-duality library package, part 67c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacFrob_Val =====
section

/-!
# S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`):
* `kptEquiv_of_jX0`, `jacPicEquiv_of_jX0`: a `K`-point `a` of `J` with closed point `jX0 x` (`x` closed in `X0`) has value
  `lamB x` in `H` and class `psiJ x` in `Pic⁰`;
* `eJ_kpt`, `mor_kpt`: `mor φ hφ` sends `jX0 (kpt (z ∘ ι))` to `jX0 (kpt (z ∘ rho φ))` for `z : S_g[1/u0][1/φ u0] →ₐ[K] K`;
* `jacPicEquiv_mor`: the class of `a ≫ mor φ hφ` is `psiJ (kpt (z ∘ rho φ))`;
* `zOf`, `zOf_comp`: every `y` with `y (φ u0) ≠ 0` factors through `S_g[1/u0][1/φ u0]`;
* `comp_rho_S`: on `S_g`, `z ∘ rho φ` is `(z ∘ ι) ∘ φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Val

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem kptEquiv_of_jX0 (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (x : X0 K F) (hx : IsClosed ({x} : Set (X0 K F)))
    (ha : a.left (IsLocalRing.closedPoint K) = jX0 K F x) :
    kptEquiv K F a = ⟨(lawChunk K F).lamB x hx, (lawChunk K F).lamB_mem_H x hx⟩ := by
  apply Subtype.ext
  rw [kptEquiv_apply]
  show (lawChunk K F).PtT (a.left (IsLocalRing.closedPoint K)) = _
  rw [ha, jX0, (lawChunk K F).PtT_ι 1 x hx, OneMemClass.coe_one, one_mul]
  exact (lawChunk K F).lamT_eq x hx

theorem jacPicEquiv_of_jX0 (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (x : X0 K F) (hx : IsClosed ({x} : Set (X0 K F)))
    (ha : a.left (IsLocalRing.closedPoint K) = jX0 K F x) :
    ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) = psiJ K F x := by
  rw [jacPicEquiv_apply, kptEquiv_of_jX0 a x hx ha]
  exact jacPic0_lamB (K := K) (F := F) x hx

theorem left_comp_closedPoint (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ψ : Jac K F ⟶ Jac K F) :
    (a ≫ ψ).left (IsLocalRing.closedPoint K) = ψ.left (a.left (IsLocalRing.closedPoint K)) := by
  rw [Over.comp_left]
  rfl

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

theorem eJ_kpt (z : BRing φ →ₐ[K] K) :
    eJ φ (kpt z) = jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)))) := by
  rw [eJ, Scheme.Hom.comp_apply]
  exact congrArg (fun p => jX0 K F p) (SpecMap_kpt (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)) z)

theorem mor_kpt (hφ : φ (lawPre K F).u0 ≠ 0) (z : BRing φ →ₐ[K] K) :
    (mor φ hφ).left (jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) =
      jX0 K F (kpt (z.comp (rho φ))) := by
  have h := congrArg (fun f : Spec (.of (BRing φ)) ⟶ (Jac K F).left => f (kpt z)) (eJ_mor φ hφ)
  simp only [Scheme.Hom.comp_apply] at h
  rw [eJ_kpt] at h
  rw [h]
  exact congrArg (fun p => jX0 K F p) (SpecMap_kpt (rho φ) z)

/-- **Values of `mor φ hφ`**: a `K`-point with closed point `jX0 (kpt (z ∘ ι))` goes to the class `psiJ (kpt (z ∘ rho φ))`. -/
theorem jacPicEquiv_mor (hφ : φ (lawPre K F).u0 ≠ 0) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (z : BRing φ →ₐ[K] K)
    (ha : a.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ mor φ hφ)) : Pic0K K F) : PicK K F) =
      psiJ K F (kpt (z.comp (rho φ))) :=
  jacPicEquiv_of_jX0 _ _ (JacLaw.isClosed_kpt _) (by rw [left_comp_closedPoint, ha, mor_kpt])

/-- A `K`-point `y` of `S_g[1/u0]` with `y (φ u0) ≠ 0` as a `K`-point of `S_g[1/u0][1/φ u0]`. -/
noncomputable def zOf (y : LawRing K F →ₐ[K] K) (hy : y (vA φ) ≠ 0) : BRing φ →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (A := K) (S := BRing φ) (vA φ) (f := y) (isUnit_iff_ne_zero.2 hy)

theorem zOf_comp (y : LawRing K F →ₐ[K] K) (hy : y (vA φ) ≠ 0) :
    (zOf φ y hy).comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)) = y := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', zOf, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- On `S_g`: `z ∘ rho φ` restricts to `(z ∘ ι) ∘ φ`. -/
theorem comp_rho_S (z : BRing φ →ₐ[K] K) :
    (z.comp (rho φ)).comp (IsScalarTower.toAlgHom K _ (LawRing K F)) =
      ((z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))).comp
        (IsScalarTower.toAlgHom K _ (LawRing K F))).comp φ := by
  ext s
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', rho_algebraMap, gB_apply]

end Val

end RamanujanPetersson.JacFrob

end


