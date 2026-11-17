-- Prove2me | Definitions.Def_RPLib_S4T_FFBridgeC
-- name    : RPLib_S4T_FFBridgeC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:22:47.49793+00:00
-- url     : https://prove2.me/theorems/9b6ea416-e783-4aff-8f2e-bffd7107735c
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: pullbacks of rationally represented maps
-- statement:
--   Pullbacks of rationally represented maps.
--
--   * `HV_rep` : values of the coordinate functions of a rationally represented map;
--   * `wu_apply`, `ker_finite_of_comp`, `ne_zero_of_comp` : consequences of `w ∘ u = [N]`;
--   * `phiC`, `jFF_mk`, `mk_eq_zero_of_inf` : evaluation maps out of coordinate rings;
--   * **`exists_pullback`** : a rationally represented `α : W₁ → W₂` with infinite image of its good set has an
--     `F`-algebra pullback `f : K_F(W₂) → K_F(W₁)` with `f(x0) = nX/dX (x0, y0)`, `f(y0) = nY/dY (x0, y0)`.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_FFBridgeB

/-!
# S4T-FFBridge, part C: pullbacks of rationally represented maps

* `HV_rep` : values of the coordinate functions of a rationally represented map;
* `wu_apply`, `ker_finite_of_comp`, `ne_zero_of_comp` : consequences of `w ∘ u = [N]`;
* `phiC`, `jFF_mk`, `mk_eq_zero_of_inf` : evaluation maps out of coordinate rings;
* **`exists_pullback`** : a rationally represented `α : W₁ → W₂` with infinite image of its good set has an
  `F`-algebra pullback `f : K_F(W₂) → K_F(W₁)` with `f(x0) = nX/dX (x0, y0)`, `f(y0) = nY/dY (x0, y0)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.S4T.FFB

open RPLib.Weil RPLib.DWS

lemma wu_apply {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂] {u : G₁ →+ G₂} {w : G₂ →+ G₁} {N : ℕ}
    (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id G₁) (P : G₁) : w (u P) = N • P := by
  have := DFunLike.congr_fun hwu P
  simpa using this

lemma ker_finite_of_comp {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂] {u : G₁ →+ G₂}
    {w : G₂ →+ G₁} {N : ℕ} (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id G₁)
    (hfin : {P : G₁ | N • P = 0}.Finite) : {P | u P = 0}.Finite :=
  hfin.subset (fun P (hP : u P = 0) => by
    show N • P = 0
    rw [← wu_apply hwu P, hP, map_zero])

section Eval

variable {F : Type*} [Field F] {M : Type*} [Field M] [Algebra F M]

lemma eval₂_eq_ev (a b : M) (p : F[X][Y]) :
    p.eval₂ ((aeval a : F[X] →ₐ[F] M) : F[X] →+* M) b = ev M a b p := by
  have e : eval₂RingHom ((aeval a : F[X] →ₐ[F] M) : F[X] →+* M) b = ev (F := F) M a b :=
    ringHom_ext2 (fun r => by simp) (by simp) (by simp)
  exact RingHom.congr_fun e p

lemma equation_iff_ev {W₂ : WeierstrassCurve F} (a b : M) :
    (W₂.baseChange M).toAffine.Equation a b ↔ ev M a b W₂.toAffine.polynomial = 0 := by
  show ((W₂.map (algebraMap F M)).toAffine.polynomial).evalEval a b = 0 ↔ _
  rw [WeierstrassCurve.Affine.map_polynomial]
  rfl

/-- Evaluation `F[W₂] → M` at a point `(a, b)` of `W₂(M)`. -/
noncomputable def phiC {W₂ : WeierstrassCurve F} {a b : M} (h : (W₂.baseChange M).toAffine.Equation a b) :
    W₂.toAffine.CoordinateRing →ₐ[F] M :=
  AdjoinRoot.liftAlgHom W₂.toAffine.polynomial (aeval a) b
    ((eval₂_eq_ev a b _).trans ((equation_iff_ev a b).mp h))

lemma phiC_mk {W₂ : WeierstrassCurve F} {a b : M} (h : (W₂.baseChange M).toAffine.Equation a b)
    (p : F[X][Y]) : phiC h (CoordinateRing.mk W₂.toAffine p) = ev M a b p :=
  (AdjoinRoot.liftAlgHom_mk _ _ _ _ p).trans (eval₂_eq_ev a b p)

end Eval

section Curves

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- Values of the coordinates of a rationally represented map. -/
lemma HV_rep {W : WeierstrassCurve F} [W.IsElliptic] {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange L).toAffine.Point →+ (W₂.baseChange L).toAffine.Point}
    {nX dX nY dY : F[X][Y]} {B : Set L}
    (hα : ∀ (x y : L) (h : (W₁.baseChange L).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC L dX x y ≠ 0 ∧ evalEvalBC L dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) = .some (evalEvalBC L nX x y / evalEvalBC L dX x y)
          (evalEvalBC L nY x y / evalEvalBC L dY x y) h')
    {Q : (W₁.baseChange L).toAffine.Point} (hQ : Q ≠ 0) (hQB : px Q ∉ B)
    {P : Pt W L} {hP : P ≠ 0} {a b : FF W L} (ha : HV W L P hP a (px Q)) (hb : HV W L P hP b (py Q)) :
    α Q ≠ 0 ∧ HV W L P hP (ev (FF W L) a b nX / ev (FF W L) a b dX) (px (α Q)) ∧
      HV W L P hP (ev (FF W L) a b nY / ev (FF W L) a b dY) (py (α Q)) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some x y h =>
    obtain ⟨hdX, hdY, h', e⟩ := hα x y h hQB
    rw [e]
    exact ⟨Point.some_ne_zero _, (HV_ev nX ha hb).div (HV_ev dX ha hb) hdX,
      (HV_ev nY ha hb).div (HV_ev dY ha hb) hdY⟩

lemma ne_zero_of_comp {W W' : WeierstrassCurve F} [W.IsElliptic] {u : Pt W L →+ Pt W' L}
    {w : Pt W' L →+ Pt W L} {N : ℕ} (hN : (N : L) ≠ 0)
    (hwu : w.comp u = (N : ℤ) • AddMonoidHom.id (Pt W L)) : u ≠ 0 ∧ w ≠ 0 := by
  obtain ⟨P, -, hnP, -⟩ := exists_good (W := W) hN Set.finite_empty
  refine ⟨fun h0 => hnP ?_, fun h0 => hnP ?_⟩
  · rw [← wu_apply hwu P, h0, AddMonoidHom.zero_apply, map_zero]
  · rw [← wu_apply hwu P, h0, AddMonoidHom.zero_apply]

variable [Fintype F]

lemma jFF_x0 {W : WeierstrassCurve F} [W.IsElliptic] : jFF W L (x0 W) = gx W L := jFF_x

lemma jFF_y0 {W : WeierstrassCurve F} [W.IsElliptic] : jFF W L (y0 W) = gy W L := jFF_y

lemma jFF_ev {W : WeierstrassCurve F} [W.IsElliptic] (p : F[X][Y]) :
    jFF W L (ev W.toAffine.FunctionField (x0 W) (y0 W) p) = ev (FF W L) (gx W L) (gy W L) p := by
  have := evalEvalBC_algHom (jFF W L) p (x0 W) (y0 W)
  rw [jFF_x0, jFF_y0] at this
  exact this

lemma mk_CC {W : WeierstrassCurve F} (r : F) :
    CoordinateRing.mk W.toAffine (C (C r)) = algebraMap F W.toAffine.CoordinateRing r := rfl

lemma jFF_mk {W : WeierstrassCurve F} [W.IsElliptic] (p : F[X][Y]) :
    jFF W L (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (CoordinateRing.mk W.toAffine p)) =
      ev (FF W L) (gx W L) (gy W L) p := by
  have e : ((jFF W L).toRingHom.comp (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)).comp
      (CoordinateRing.mk W.toAffine) = ev (F := F) (FF W L) (gx W L) (gy W L) := by
    refine ringHom_ext2 (fun r => ?_) ?_ ?_
    · show jFF W L (algebraMap _ _ (CoordinateRing.mk W.toAffine (C (C r)))) = _
      rw [ev_CC, mk_CC, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    · show jFF W L (algebraMap _ _ (CoordinateRing.mk W.toAffine (C X))) = _
      rw [ev_CX]; exact jFF_x
    · show jFF W L (algebraMap _ _ (CoordinateRing.mk W.toAffine X)) = _
      rw [ev_X]; exact jFF_y
  exact RingHom.congr_fun e p

/-- A polynomial vanishing at infinitely many points of `W(L)` is `0` in `F[W]`. -/
lemma mk_eq_zero_of_inf {W : WeierstrassCurve F} [W.IsElliptic] {p : F[X][Y]} {S : Set (Pt W L)}
    (hS : S.Infinite) (h : ∀ Q ∈ S, Q ≠ 0 ∧ ev L (px Q) (py Q) p = 0) : CoordinateRing.mk W.toAffine p = 0 := by
  have h0 : ev (FF W L) (gx W L) (gy W L) p = 0 := eq_zero_of_HV_inf hS (fun Q hQ hQS =>
    (HV_ev p (HV_gx W L Q hQ) (HV_gy W L Q hQ)).congr rfl (h Q hQS).2)
  rw [← jFF_mk] at h0
  have h1 := (map_eq_zero_iff (jFF W L) jFF_injective).mp h0
  exact IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField (h1.trans (map_zero _).symm)

lemma phiC_injective_of {W₂ : WeierstrassCurve F} [W₂.IsElliptic] {K₁ : Type*} [Field K₁] [Algebra F K₁]
    {a b : K₁} (h : (W₂.baseChange K₁).toAffine.Equation a b)
    (hv : ∀ p : F[X][Y], ev K₁ a b p = 0 →
      ∃ S : Set (Pt W₂ L), S.Infinite ∧ ∀ Q ∈ S, Q ≠ 0 ∧ ev L (px Q) (py Q) p = 0) :
    Function.Injective (phiC h) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, rfl⟩ : ∃ p, CoordinateRing.mk W₂.toAffine p = r := AdjoinRoot.mk_surjective r
  rw [phiC_mk] at hr
  obtain ⟨S, hS, hS'⟩ := hv p hr
  exact mk_eq_zero_of_inf hS hS'

/-- **Pullback** of a rationally represented map with infinite image of its good set. -/
theorem exists_pullback {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt W₁ L →+ Pt W₂ L} {nX dX nY dY : F[X][Y]} {B : Set L} (hB : B.Finite)
    (hα : ∀ (x y : L) (h : (W₁.baseChange L).toAffine.Nonsingular x y), x ∉ B →
      evalEvalBC L dX x y ≠ 0 ∧ evalEvalBC L dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) = .some (evalEvalBC L nX x y / evalEvalBC L dX x y)
          (evalEvalBC L nY x y / evalEvalBC L dY x y) h')
    (hinf : (α '' {P | P ≠ 0 ∧ px P ∉ B}).Infinite) :
    ∃ f : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField,
      f (x0 W₂) = ev _ (x0 W₁) (y0 W₁) nX / ev _ (x0 W₁) (y0 W₁) dX ∧
      f (y0 W₂) = ev _ (x0 W₁) (y0 W₁) nY / ev _ (x0 W₁) (y0 W₁) dY := by
  obtain ⟨a, ha⟩ : ∃ a : W₁.toAffine.FunctionField,
    a = ev _ (x0 W₁) (y0 W₁) nX / ev _ (x0 W₁) (y0 W₁) dX := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : W₁.toAffine.FunctionField,
    b = ev _ (x0 W₁) (y0 W₁) nY / ev _ (x0 W₁) (y0 W₁) dY := ⟨_, rfl⟩
  have ja : jFF W₁ L a = ev (FF W₁ L) (gx W₁ L) (gy W₁ L) nX / ev (FF W₁ L) (gx W₁ L) (gy W₁ L) dX := by
    rw [ha, map_div₀, jFF_ev, jFF_ev]
  have jb : jFF W₁ L b = ev (FF W₁ L) (gx W₁ L) (gy W₁ L) nY / ev (FF W₁ L) (gx W₁ L) (gy W₁ L) dY := by
    rw [hb, map_div₀, jFF_ev, jFF_ev]
  have hval : ∀ (P : Pt W₁ L) (hP : P ≠ 0), px P ∉ B → α P ≠ 0 ∧
      HV W₁ L P hP (jFF W₁ L a) (px (α P)) ∧ HV W₁ L P hP (jFF W₁ L b) (py (α P)) := by
    intro P hP hPB
    rw [ja, jb]
    exact HV_rep hα hP hPB (HV_gx W₁ L P hP) (HV_gy W₁ L P hP)
  have hjev : ∀ p, jFF W₁ L (ev _ a b p) = ev (FF W₁ L) (jFF W₁ L a) (jFF W₁ L b) p :=
    fun p => evalEvalBC_algHom (jFF W₁ L) p a b
  have hE : (W₂.baseChange W₁.toAffine.FunctionField).toAffine.Equation a b := by
    rw [equation_iff_ev]
    apply jFF_injective (W := W₁) (L := L)
    rw [map_zero, hjev]
    refine eq_zero_of_HV (finite_px hB) (fun P hP hPT => ?_)
    obtain ⟨h0, hx, hy⟩ := hval P hP (fun h => hPT ⟨hP, h⟩)
    exact (HV_ev _ hx hy).congr rfl ((equation_iff_ev _ _).mp (nonsingular_px_py h0).1)
  have hinj : Function.Injective (phiC hE) := by
    refine phiC_injective_of (L := L) hE (fun p hp => ⟨_, hinf, ?_⟩)
    rintro _ ⟨P, ⟨hP, hPB⟩, rfl⟩
    obtain ⟨h0, hx, hy⟩ := hval P hP hPB
    refine ⟨h0, ?_⟩
    have hz : ev (FF W₁ L) (jFF W₁ L a) (jFF W₁ L b) p = 0 := by rw [← hjev, hp, map_zero]
    have h1 := (HV_ev p hx hy).congr hz rfl
    by_contra hne
    exact h1.ne_zero hne rfl
  refine ⟨IsFractionRing.liftAlgHom hinj, ?_, ?_⟩
  · rw [← ha, x0, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    exact (phiC_mk hE (C X)).trans (ev_CX a b)
  · rw [← hb, y0, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    exact (phiC_mk hE X).trans (ev_X a b)

end Curves

end RPLib.S4T.FFB


