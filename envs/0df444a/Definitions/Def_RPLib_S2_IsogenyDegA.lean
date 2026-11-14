-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegA
-- name    : RPLib_S2_IsogenyDegA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:09:23.954166+00:00
-- url     : https://prove2.me/theorems/13a017f6-f36e-4fe7-8504-6347d4f9f9bb
-- title:
--   Degrees of $r + s\pi$, part A: pullback along a point of $E(L(E))$
-- statement:
--   For a nonconstant point $\Phi$ of $E$ over the function field, the pullback $L$-algebra map sending $x, y$ to the coordinates of $\Phi$, and its compatibility with translations.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section III.4

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairing

/-!
# S2-IsogenyDeg part A: pullback of functions along a non-constant point of `W(F)`

For a point `Φ ∈ W(F)` (`F` the function field of `W⁄L`) that is not a constant point `ιP C`, the
`L`-algebra map `pull Φ : F → F` sends `x, y` to the coordinates of `Φ`. If translating `Φ` by `S` adds the
constant point `φ S`, then `τ_S ∘ pull Φ = pull Φ ∘ τ_{φ S}`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

section Pull

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
  (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ne_zero_of_ne_ιP {Φ : (W.baseChange (FF W L)).toAffine.Point}
    (h : ∀ C, Φ ≠ ιP W L C) : Φ ≠ 0 := by
  intro h0
  exact h 0 (by rw [h0, map_zero])

lemma transcendental_of_ne_ιP {Φ : (W.baseChange (FF W L)).toAffine.Point}
    (h : ∀ C, Φ ≠ ιP W L C) : Transcendental L (px Φ) := by
  have hΦ := ne_zero_of_ne_ιP W L h
  intro halg
  obtain ⟨a, ha⟩ := mem_range_of_isAlgebraic halg
  obtain ⟨b, hb⟩ := exists_y_alg (W.baseChange L) a
  have hnsb : (W.baseChange L).toAffine.Nonsingular a b := equation_iff_nonsingular.mp hb
  have hnsb' : (W.baseChange L).toAffine.Nonsingular a ((W.baseChange L).toAffine.negY a b) :=
    (nonsingular_neg ..).mpr hnsb
  have hns := nonsingular_px_py hΦ
  have e1 := hns.1
  rw [← ha] at e1
  have e2 : (W.baseChange (FF W L)).toAffine.Equation (ιF W L a) (ιF W L b) :=
    Equation.baseChange (W := W.toAffine) (ιF W L) hb
  rw [ιF_apply, ιF_apply] at e2
  rw [equation_iff] at e1 e2
  rw [bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L),
    bc_a₆ W L (FF W L)] at e1 e2
  have hfac : (py Φ - algebraMap L (FF W L) b) *
      (py Φ - algebraMap L (FF W L) ((W.baseChange L).toAffine.negY a b)) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul]
    linear_combination e1 - e2
  have key : ∀ (y : L) (hy : (W.baseChange L).toAffine.Nonsingular a y),
      py Φ = algebraMap L (FF W L) y → False := by
    intro y hy hpy
    apply h (Point.some a y hy)
    exact (eq_some_px_py hΦ).trans (some_eq_some ha.symm hpy)
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact key b hnsb (sub_eq_zero.mp h')
  · exact key _ hnsb' (sub_eq_zero.mp h')

variable (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C)

/-- The ring map `R → F`, `x ↦ x(Φ)`, `y ↦ y(Φ)`. -/
noncomputable def pullR : (CR W L) →ₐ[L] (FF W L) :=
  AdjoinRoot.liftAlgHom (W.baseChange L).toAffine.polynomial (aeval (px Φ))
    (py Φ) (eval₂_polynomial W L _ _ (nonsingular_px_py (ne_zero_of_ne_ιP W L h)).1)

lemma pullR_of (p : L[X]) :
    pullR W L Φ h (algebraMap L[X] (CR W L) p) = aeval (px Φ) p := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ p

lemma pullR_injective : Function.Injective (pullR W L Φ h) := by
  haveI : Algebra.IsIntegral L[X] (CR W L) := Algebra.IsIntegral.of_finite _ _
  have hker : RingHom.ker (pullR W L Φ h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := L[X])
    rw [eq_bot_iff]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker] at hp
    rw [Ideal.mem_bot]
    by_contra hp0
    exact transcendental_of_ne_ιP W L h ⟨p, hp0, by rw [← pullR_of W L Φ h]; exact hp⟩
  intro a b hab
  have : a - b ∈ RingHom.ker (pullR W L Φ h) := by
    rw [RingHom.mem_ker, map_sub, hab, sub_self]
  rw [hker, Ideal.mem_bot] at this
  exact sub_eq_zero.mp this

/-- The pullback `f ↦ f ∘ Φ` on the function field. -/
noncomputable def pull : (FF W L) →ₐ[L] (FF W L) :=
  IsFractionRing.liftAlgHom (pullR_injective W L Φ h)

lemma pull_algebraMap (r : (CR W L)) :
    pull W L Φ h (algebraMap (CR W L) (FF W L) r) = pullR W L Φ h r := by
  rw [pull, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

lemma pull_gx : pull W L Φ h (gx W L) = px Φ := by
  rw [gx, pull_algebraMap]
  show pullR W L Φ h (AdjoinRoot.mk _ (C X)) = _
  rw [AdjoinRoot.mk_C, pullR, AdjoinRoot.liftAlgHom_of, aeval_X]

lemma pull_gy : pull W L Φ h (gy W L) = py Φ := by
  rw [gy, pull_algebraMap]
  show pullR W L Φ h (AdjoinRoot.mk _ X) = _
  rw [AdjoinRoot.mk_X, pullR, AdjoinRoot.liftAlgHom_root]

lemma pull_injective : Function.Injective (pull W L Φ h) := (pull W L Φ h).toRingHom.injective

lemma map_pull_ιP (C : (W.baseChange L).toAffine.Point) :
    Point.map (W' := W.toAffine) ((pull W L Φ h).restrictScalars k) (ιP W L C) = ιP W L C := by
  have hcomp : ((pull W L Φ h).restrictScalars k).comp (ιF W L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact (pull W L Φ h).commutes a
  rw [ιP, Point.map_map, hcomp]

lemma map_pull_G :
    Point.map (W' := W.toAffine) ((pull W L Φ h).restrictScalars k) (G W L) = Φ := by
  rw [G, Point.map_some]
  conv_rhs => rw [eq_some_px_py (ne_zero_of_ne_ιP W L h)]
  exact some_eq_some (pull_gx W L Φ h) (pull_gy W L Φ h)

lemma map_pull_pS (S : (W.baseChange L).toAffine.Point) :
    Point.map (W' := W.toAffine) ((pull W L Φ h).restrictScalars k) (pS W L S) = Φ + ιP W L S := by
  rw [pS, map_add, map_pull_G, map_pull_ιP]

/-- Translation rule: if `τ_S Φ = Φ + φ S`, then `τ_S ∘ pull Φ = pull Φ ∘ τ_{φ S}`. -/
theorem tau_comp_pull (φ : (W.baseChange L).toAffine.Point → (W.baseChange L).toAffine.Point)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ = Φ + ιP W L (φ S))
    (S : (W.baseChange L).toAffine.Point) :
    (tauHom W L S).comp (pull W L Φ h) = (pull W L Φ h).comp (tauHom W L (φ S)) := by
  apply algHom_ext_gen W L
  · have h1 := px_map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ
    have h2 := px_map (W' := W.toAffine) ((pull W L Φ h).restrictScalars k) (pS W L (φ S))
    rw [hE] at h1
    rw [map_pull_pS] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, pull_gx, tauHom_gx]
    exact h1.symm.trans h2
  · have h1 := py_map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ
    have h2 := py_map (W' := W.toAffine) ((pull W L Φ h).restrictScalars k) (pS W L (φ S))
    rw [hE] at h1
    rw [map_pull_pS] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, pull_gy, tauHom_gy]
    exact h1.symm.trans h2

theorem tau_pull (φ : (W.baseChange L).toAffine.Point → (W.baseChange L).toAffine.Point)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ = Φ + ιP W L (φ S))
    (S : (W.baseChange L).toAffine.Point) (f : FF W L) :
    tau W L S (pull W L Φ h f) = pull W L Φ h (tau W L (φ S) f) := by
  rw [tau_apply, tau_apply]
  exact AlgHom.congr_fun (tau_comp_pull W L Φ h φ hE S) f

end Pull

end RPLib.Isog


