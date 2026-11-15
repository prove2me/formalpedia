-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPCFB
-- name    : RPLib_S3_Wt2RPCFB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:26:53.754421+00:00
-- url     : https://prove2.me/theorems/d0a8a634-a6b9-4412-a477-4555b6a1c36e
-- title:
--   Weight-two Ramanujan-Petersson library: a function field over its full constant field
-- statement:
--   A function field over its full constant field.
--
--   For a function field `F / Fq`, let `k = KF Fq F` be the full constant field (`constField Fq F`) and
--   `x = algebraMap Fq[X] F X`. The scoped instances of namespace `CF` make `F` a function field over `k` with the
--   same coordinate `x`: `k[X] → F` is `aeval x`, `k(X) → F` its lift (`x` is transcendental over `k`), `Fq(X) → k(X)`
--   the coefficientwise map; finiteness and separability come down the tower `Fq(X) ⊆ k(X) ⊆ F`.
--   * `hxk`: the coordinates agree; `transcendental_x_KF`: `x` is transcendental over `k`.
--   * `constField_KF_eq_bot`: `k` is the full constant field of `F / k`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_Wt2RPCFA

/-!
# S3-Wt2RP, O2 part B: a function field over its full constant field

For a function field `F / Fq`, let `k = KF Fq F` be the full constant field (`constField Fq F`) and
`x = algebraMap Fq[X] F X`. The scoped instances of namespace `CF` make `F` a function field over `k` with the
same coordinate `x`: `k[X] → F` is `aeval x`, `k(X) → F` its lift (`x` is transcendental over `k`), `Fq(X) → k(X)`
the coefficientwise map; finiteness and separability come down the tower `Fq(X) ⊆ k(X) ⊆ F`.
* `hxk`: the coordinates agree; `transcendental_x_KF`: `x` is transcendental over `k`.
* `constField_KF_eq_bot`: `k` is the full constant field of `F / k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.S3.Wt2

open RamanujanPetersson.Places

section CFsec

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The full constant field, as a type. -/
abbrev KF : Type := constField Fq F

theorem transcendental_x : Transcendental Fq (algebraMap Fq[X] F X) :=
  (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective Fq[X] F)).mpr (Polynomial.transcendental_X Fq)

theorem transcendental_x_KF : Transcendental (KF Fq F) (algebraMap Fq[X] F X) := fun h =>
  transcendental_x Fq F (h.restrictScalars Fq)

namespace CF

noncomputable scoped instance instFintypeKF : Fintype (KF Fq F) :=
  haveI : Finite (KF Fq F) := Module.finite_of_finite Fq
  Fintype.ofFinite _

noncomputable scoped instance instDecEqRatKF : DecidableEq (RatFunc (KF Fq F)) := Classical.decEq _

noncomputable scoped instance instAlgPolyKF : Algebra (KF Fq F)[X] F :=
  (Polynomial.aeval (R := KF Fq F) (algebraMap Fq[X] F X)).toRingHom.toAlgebra

scoped instance instTowerKF : IsScalarTower (KF Fq F) (KF Fq F)[X] F :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [Polynomial.algebraMap_eq]
    exact (aeval_C _ c).symm

theorem hxk : algebraMap (KF Fq F)[X] F X = algebraMap Fq[X] F X := aeval_X _

theorem injective_poly_KF : Function.Injective (algebraMap (KF Fq F)[X] F) :=
  transcendental_iff_injective.mp (transcendental_x_KF Fq F)

noncomputable scoped instance instAlgRatKF : Algebra (RatFunc (KF Fq F)) F :=
  (IsFractionRing.lift (A := (KF Fq F)[X]) (K := RatFunc (KF Fq F)) (injective_poly_KF Fq F)).toAlgebra

scoped instance instTowerRatKF : IsScalarTower (KF Fq F)[X] (RatFunc (KF Fq F)) F :=
  IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap (injective_poly_KF Fq F) p).symm

theorem injective_map_KF :
    Function.Injective ((algebraMap (KF Fq F)[X] (RatFunc (KF Fq F))).comp (mapRingHom (algebraMap Fq (KF Fq F)))) :=
  (IsFractionRing.injective _ _).comp (Polynomial.map_injective _ (algebraMap Fq (KF Fq F)).injective)

noncomputable scoped instance instAlgRatRat : Algebra (RatFunc Fq) (RatFunc (KF Fq F)) :=
  (IsFractionRing.lift (A := Fq[X]) (K := RatFunc Fq) (injective_map_KF Fq F)).toAlgebra

scoped instance instTowerRatRat : IsScalarTower (RatFunc Fq) (RatFunc (KF Fq F)) F := by
  refine IsScalarTower.of_algebraMap_eq'
    (IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_))
  have h1 : algebraMap (RatFunc Fq) (RatFunc (KF Fq F)) (algebraMap Fq[X] (RatFunc Fq) p) =
      algebraMap (KF Fq F)[X] (RatFunc (KF Fq F)) (p.map (algebraMap Fq (KF Fq F))) :=
    IsFractionRing.lift_algebraMap (injective_map_KF Fq F) p
  simp only [RingHom.comp_apply]
  rw [h1, ← IsScalarTower.algebraMap_apply (KF Fq F)[X] (RatFunc (KF Fq F)) F,
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F]
  exact RingHom.congr_fun (algebraMap_poly_eq Fq F (KF Fq F) (hxk Fq F)) p

scoped instance instFFKF : FunctionField (KF Fq F) F :=
  Module.Finite.of_restrictScalars_finite (RatFunc Fq) (RatFunc (KF Fq F)) F

scoped instance instSepKF : Algebra.IsSeparable (RatFunc (KF Fq F)) F :=
  Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) (RatFunc (KF Fq F)) F

/-- `k` is the full constant field of `F / k`. -/
theorem constField_KF_eq_bot : constField (KF Fq F) F = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have h1 : IsIntegral (KF Fq F) y := mem_algebraicClosure_iff'.mp hy
  have h2 : IsIntegral Fq y := isIntegral_trans y h1
  exact IntermediateField.mem_bot.mpr ⟨⟨y, mem_algebraicClosure_iff'.mpr h2⟩, rfl⟩

end CF

end CFsec

end RamanujanPetersson.S3.Wt2


