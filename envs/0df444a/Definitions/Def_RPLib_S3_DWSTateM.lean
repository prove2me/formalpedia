-- Prove2me | Definitions.Def_RPLib_S3_DWSTateM
-- name    : RPLib_S3_DWSTateM
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:45:24.766244+00:00
-- url     : https://prove2.me/theorems/db14f302-af3a-47ce-b81a-a44ba5c25b55
-- title:
--   Weight-two Ramanujan-Petersson library: base change of function fields `K_F(E) → L(E)`
-- statement:
--   Base change of function fields `K_F(E) → L(E)`.
--
--   `W` an elliptic curve over the finite field `F`, `L ⊇ F` algebraically closed, `FF W L = L(E)`.
--
--   * `jCR W L : F[E] →+* L[E]` (Mathlib `CoordinateRing.map`), injective, `jCR_mk`.
--   * `jA W L : F[E] →ₐ[F] L(E)`, injective.
--   * **`jFF W L : K_F(E) →ₐ[F] L(E)`** (`IsFractionRing.liftAlgHom`), injective on the generators:
--     `jFF_x : jFF (x) = gx W L`, `jFF_y : jFF (y) = gy W L`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateL
import Definitions.Def_RPLib_S3_TateStmtP

/-!
# S3-DWS-Tate, file M (BR1, part 1): base change of function fields `K_F(E) → L(E)`

`W` an elliptic curve over the finite field `F`, `L ⊇ F` algebraically closed, `FF W L = L(E)`.

* `jCR W L : F[E] →+* L[E]` (Mathlib `CoordinateRing.map`), injective, `jCR_mk`.
* `jA W L : F[E] →ₐ[F] L(E)`, injective.
* **`jFF W L : K_F(E) →ₐ[F] L(E)`** (`IsFractionRing.liftAlgHom`), injective on the generators:
  `jFF_x : jFF (x) = gx W L`, `jFF_y : jFF (y) = gy W L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section BaseChange

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable (W L) in
/-- `F[E] → L[E]`. -/
noncomputable def jCR : W.toAffine.CoordinateRing →+* CR W L :=
  CoordinateRing.map W.toAffine (algebraMap F L)

lemma jCR_injective : Function.Injective (jCR W L) :=
  CoordinateRing.map_injective (W' := W.toAffine) (algebraMap F L).injective

lemma jCR_mk (p : F[X][Y]) :
    jCR W L (CoordinateRing.mk W.toAffine p) =
      CoordinateRing.mk (W.baseChange L).toAffine (p.map (mapRingHom (algebraMap F L))) :=
  CoordinateRing.map_mk (W' := W.toAffine) (algebraMap F L) p

lemma algebraMap_CR_F (c : F) :
    algebraMap F W.toAffine.CoordinateRing c = CoordinateRing.mk W.toAffine (C (C c)) := rfl

variable (W L) in
/-- `F[E] → L(E)` as an `F`-algebra map. -/
noncomputable def jA : W.toAffine.CoordinateRing →ₐ[F] FF W L where
  toRingHom := (algebraMap (CR W L) (FF W L)).comp (jCR W L)
  commutes' c := by
    show algebraMap (CR W L) (FF W L) (jCR W L (algebraMap F W.toAffine.CoordinateRing c)) =
      algebraMap F (FF W L) c
    rw [algebraMap_CR_F, jCR_mk, IsScalarTower.algebraMap_apply F L (FF W L),
      IsScalarTower.algebraMap_apply L (CR W L) (FF W L)]
    congr 1
    simp only [Polynomial.map_C, coe_mapRingHom]
    rfl

lemma jA_apply (r : W.toAffine.CoordinateRing) :
    jA W L r = algebraMap (CR W L) (FF W L) (jCR W L r) := rfl

lemma jA_injective : Function.Injective (jA W L) := fun a b h => by
  rw [jA_apply, jA_apply] at h
  exact jCR_injective (IsFractionRing.injective (CR W L) (FF W L) h)

variable (W L) in
/-- **`K_F(E) → L(E)`**, the base change of function fields. -/
noncomputable def jFF : W.toAffine.FunctionField →ₐ[F] FF W L :=
  IsFractionRing.liftAlgHom (A := W.toAffine.CoordinateRing) (K := W.toAffine.FunctionField)
    (g := jA W L) jA_injective

lemma jFF_algebraMap (r : W.toAffine.CoordinateRing) :
    jFF W L (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r) = jA W L r := by
  rw [jFF, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

lemma jFF_injective : Function.Injective (jFF W L) := (jFF W L).toRingHom.injective

lemma jFF_x : jFF W L (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (CoordinateRing.mk W.toAffine (C X))) = gx W L := by
  rw [jFF_algebraMap, jA_apply, jCR_mk, Polynomial.map_C, coe_mapRingHom, Polynomial.map_X]
  rfl

lemma jFF_y : jFF W L (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
    (CoordinateRing.mk W.toAffine X)) = gy W L := by
  rw [jFF_algebraMap, jA_apply, jCR_mk, Polynomial.map_X]
  rfl

end BaseChange

end RPLib.DWS


