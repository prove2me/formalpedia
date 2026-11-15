-- Prove2me | Definitions.Def_RPLib_S3_DWSTateN
-- name    : RPLib_S3_DWSTateN
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:48:02.224006+00:00
-- url     : https://prove2.me/theorems/e0c8558e-1594-46c9-aad3-77a6ba88c0d5
-- title:
--   Weight-two Ramanujan-Petersson library: the Tate data over `L`
-- statement:
--   The Tate data over `L`.
--
--   `W, W'` elliptic curves over the finite field `F`, `L ⊇ F` algebraically closed and algebraic over `F`.
--
--   * `x0 W, y0 W`, `P0 W` : the generic point of `W` over `K_F(E)` (the point of `TateIsogenyPrimeToP`).
--   * `algHom_ext_gen0` : `F`-algebra maps out of `K_F(E)` are determined by `x0, y0`.
--   * `transcendental_x0` : `x0` is transcendental over `F`.
--   * `PhiF L f ∈ W'(L(E))` for `f : K_F(E') →ₐ[F] K_F(E)`; nonconstant (`PhiF_ne_ιQ`).
--   * `fL L f := pull2 (PhiF L f) : L(E') →ₐ[L] L(E)`, `fL_jFF : fL f ∘ jFF = jFF ∘ f`.
--   * **`map_fL_PhiF`** : if `(f ∘ g)(P0) = N • P0` then `fL f (PhiF g) = N • G`; `fL_fL_gx`, `fL_fL_gy`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateM

/-!
# S3-DWS-Tate, file N (BR1, part 2): the Tate data over `L`

`W, W'` elliptic curves over the finite field `F`, `L ⊇ F` algebraically closed and algebraic over `F`.

* `x0 W, y0 W`, `P0 W` : the generic point of `W` over `K_F(E)` (the point of `TateIsogenyPrimeToP`).
* `algHom_ext_gen0` : `F`-algebra maps out of `K_F(E)` are determined by `x0, y0`.
* `transcendental_x0` : `x0` is transcendental over `F`.
* `PhiF L f ∈ W'(L(E))` for `f : K_F(E') →ₐ[F] K_F(E)`; nonconstant (`PhiF_ne_ιQ`).
* `fL L f := pull2 (PhiF L f) : L(E') →ₐ[L] L(E)`, `fL_jFF : fL f ∘ jFF = jFF ∘ f`.
* **`map_fL_PhiF`** : if `(f ∘ g)(P0) = N • P0` then `fL f (PhiF g) = N • G`; `fL_fL_gx`, `fL_fL_gy`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Gen0

variable {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- The generic `x` over `F`. -/
noncomputable def x0 : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine (C X))

/-- The generic `y` over `F`. -/
noncomputable def y0 : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine X)

lemma gen0_nonsingular :
    (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular (x0 W) (y0 W) := by
  classical
  have h := gen_nonsingular W (AlgebraicClosure F)
  have hx : jFF W (AlgebraicClosure F) (x0 W) = gx W (AlgebraicClosure F) := jFF_x
  have hy : jFF W (AlgebraicClosure F) (y0 W) = gy W (AlgebraicClosure F) := jFF_y
  rw [← hx, ← hy] at h
  exact (baseChange_nonsingular (W := W.toAffine) (f := jFF W (AlgebraicClosure F)) jFF_injective _ _).mp h

/-- The generic point `(x0, y0) ∈ W(K_F(E))`. -/
noncomputable def P0 : (W.baseChange W.toAffine.FunctionField).toAffine.Point :=
  Point.some _ _ (gen0_nonsingular W)

lemma algHom_ext_gen0 {M : Type*} [Field M] [Algebra F M] {f g : W.toAffine.FunctionField →ₐ[F] M}
    (hx : f (x0 W) = g (x0 W)) (hy : f (y0 W) = g (y0 W)) : f = g := by
  have hR : f.comp (IsScalarTower.toAlgHom F W.toAffine.CoordinateRing W.toAffine.FunctionField) =
      g.comp (IsScalarTower.toAlgHom F W.toAffine.CoordinateRing W.toAffine.FunctionField) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simpa [x0, AdjoinRoot.mk_C] using hx
    · simpa [y0, AdjoinRoot.mk_X] using hy
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing)
  intro r
  exact AlgHom.congr_fun hR r

lemma transcendental_x0 : Transcendental F (x0 W) := by
  classical
  intro halg
  have h1 := (isAlgebraic_algHom_iff (jFF W (AlgebraicClosure F)) jFF_injective).mpr halg
  have hx : jFF W (AlgebraicClosure F) (x0 W) = gx W (AlgebraicClosure F) := jFF_x
  rw [hx] at h1
  exact transcendental_of_ne_ιQ (W := W) (W' := W) (L := AlgebraicClosure F)
    (fun C => G_ne_ιP W (AlgebraicClosure F) C) (h1.tower_top (AlgebraicClosure F))

end Gen0

section Phi

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma map_jFF_P0 : Point.map (W' := W.toAffine) (jFF W L) (P0 W) = G W L := by
  rw [P0, G, Point.map_some]
  exact some_eq_some jFF_x jFF_y

variable (L) in
/-- The point `u ∈ W'(L(E))` of `f : K_F(E') → K_F(E)`. -/
noncomputable def PhiF (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    (W'.baseChange (FF W L)).toAffine.Point :=
  Point.map (W' := W'.toAffine) ((jFF W L).comp f) (P0 W')

lemma px_PhiF (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    px (PhiF L f) = jFF W L (f (x0 W')) := by
  classical
  rw [PhiF, px_map]
  rfl

lemma py_PhiF (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    py (PhiF L f) = jFF W L (f (y0 W')) := by
  classical
  rw [PhiF, py_map]
  rfl

lemma PhiF_ne_ιQ [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (C : Pt W' L) : PhiF L f ≠ ιQ W W' L C := by
  classical
  intro hC
  have h1 := congrArg px hC
  rw [px_PhiF, ιQ, px_map, ιF_apply] at h1
  apply transcendental_x0 W'
  have h2 : IsAlgebraic F (jFF W L (f (x0 W'))) := by
    rw [h1]
    exact (Algebra.IsAlgebraic.isAlgebraic (px C)).algebraMap
  have h3 := (isAlgebraic_algHom_iff (jFF W L) jFF_injective).mp h2
  exact (isAlgebraic_algHom_iff f f.toRingHom.injective).mp h3

variable (L) in
/-- `u^* : L(E') → L(E)`, the `L`-linear extension of `f`. -/
noncomputable def fL [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) : FF W' L →ₐ[L] FF W L :=
  pull2 (PhiF L f) (PhiF_ne_ιQ f)

lemma fL_jFF [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (k : W'.toAffine.FunctionField) : fL L f (jFF W' L k) = jFF W L (f k) := by
  have e : ((fL L f).restrictScalars F).comp (jFF W' L) = (jFF W L).comp f := by
    apply algHom_ext_gen0 W'
    · have hx : jFF W' L (x0 W') = gx W' L := jFF_x
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, hx, fL, pull2_gx, px_PhiF]
    · have hy : jFF W' L (y0 W') = gy W' L := jFF_y
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply, hy, fL, pull2_gy, py_PhiF]
  exact AlgHom.congr_fun e k

lemma map_fL_PhiF_gen [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) :
    Point.map (W' := W.toAffine) ((fL L f).restrictScalars F) (PhiF L g) =
      Point.map (W' := W.toAffine) (jFF W L) (Point.map (W' := W.toAffine) (f.comp g) (P0 W)) := by
  have e : ((fL L f).restrictScalars F).comp ((jFF W' L).comp g) = (jFF W L).comp (f.comp g) := by
    apply AlgHom.ext
    intro k
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply]
    exact fL_jFF (L := L) f (g k)
  rw [PhiF, Point.map_map, Point.map_map, e]

/-- **`u ∘ w = [N]` on generic points**: `(f ∘ g)(P0) = N • P0` gives `fL f (PhiF g) = N • G`. -/
theorem map_fL_PhiF [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) :
    Point.map (W' := W.toAffine) ((fL L f).restrictScalars F) (PhiF L g) = N • G W L := by
  rw [map_fL_PhiF_gen, hfg, map_nsmul, map_jFF_P0]

theorem fL_fL_gx [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) :
    fL L f (fL L g (gx W L)) = px (N • G W L) := by
  have h := congrArg px (map_fL_PhiF (L := L) f g N hfg)
  rw [px_map, AlgHom.restrictScalars_apply] at h
  have e : fL L g (gx W L) = px (PhiF L g) := pull2_gx _ _
  rw [e]
  exact h

theorem fL_fL_gy [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) :
    fL L f (fL L g (gy W L)) = py (N • G W L) := by
  have h := congrArg py (map_fL_PhiF (L := L) f g N hfg)
  rw [py_map, AlgHom.restrictScalars_apply] at h
  have e : fL L g (gy W L) = py (PhiF L g) := pull2_gy _ _
  rw [e]
  exact h

end Phi

end RPLib.DWS


