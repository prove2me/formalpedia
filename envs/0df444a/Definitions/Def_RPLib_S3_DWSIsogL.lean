-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogL
-- name    : RPLib_S3_DWSIsogL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:50:42.559622+00:00
-- url     : https://prove2.me/theorems/364b64bb-e657-4095-a752-b9254fc29c84
-- title:
--   Weight-two Ramanujan-Petersson library: the quotient isogeny `E → E/G`
-- statement:
--   The quotient isogeny `E → E/G`.
--
--   * `qfun`, `qmap` : `S ↦ C(S)` with `τ_S Ψ = Ψ + ι(C(S))`; additive by `tauHom_comp`.
--   * `hasGenI_qmap`, **`qmap_eq_zero_iff`** (`ker = G`), **`qmap_frob`** (commutes with Frobenius),
--     `qmap_ne_zero`, `isIsogenous_quot`.
--   * **`exists_quot_isog`** : for a Frobenius-stable finite `G` with `p ∤ #G` there is an elliptic `W'/F_q` and an
--     isogeny `E → E'` over `F_q` with kernel exactly `G`; in particular `trace W' = trace W`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogK

/-!
# S3-DWS-Isog, part L: the quotient isogeny `E → E/G`

* `qfun`, `qmap` : `S ↦ C(S)` with `τ_S Ψ = Ψ + ι(C(S))`; additive by `tauHom_comp`.
* `hasGenI_qmap`, **`qmap_eq_zero_iff`** (`ker = G`), **`qmap_frob`** (commutes with Frobenius),
  `qmap_ne_zero`, `isIsogenous_quot`.
* **`exists_quot_isog`** : for a Frobenius-stable finite `G` with `p ∤ #G` there is an elliptic `W'/F_q` and an
  isogeny `E → E'` over `F_q` with kernel exactly `G`; in particular `trace W' = trace W`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section QMap

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- The constant `C(S)` with `τ_S Ψ = Ψ + ι(C(S))`. -/
noncomputable def qfun (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (S : Pt W L) : Pt W' L :=
  (rigid hG hW' S).choose

lemma qfun_spec (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (S : Pt W L) :
    Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') =
      qPt hW' + ιQ W W' L (qfun hG hW' S) :=
  (rigid hG hW' S).choose_spec

lemma qfun_unique (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {S : Pt W L} {C : Pt W' L}
    (h : Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') =
      qPt hW' + ιQ W W' L C) : qfun hG hW' S = C :=
  ιQ_injective (add_left_cancel ((qfun_spec hG hW' S).symm.trans h))

lemma map_tau_tau (S T : Pt W L) (Φ : (W'.baseChange (FF W L)).toAffine.Point) :
    Point.map (W' := W'.toAffine) ((tauHom W L (S + T)).restrictScalars F) Φ =
      Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F)
        (Point.map (W' := W'.toAffine) ((tauHom W L T).restrictScalars F) Φ) := by
  have h : ((tauHom W L S).comp (tauHom W L T)).restrictScalars F =
      ((tauHom W L S).restrictScalars F).comp ((tauHom W L T).restrictScalars F) :=
    AlgHom.ext fun _ => rfl
  rw [Point.map_map, ← tauHom_comp, h]

lemma qfun_add (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (S T : Pt W L) :
    qfun hG hW' (S + T) = qfun hG hW' S + qfun hG hW' T := by
  apply qfun_unique
  rw [map_tau_tau, qfun_spec hG hW' T, map_add, qfun_spec hG hW' S, map_ιQ_of_algHom,
    map_add (ιQ W W' L)]
  abel

/-- **The quotient map `E → E/G`.** -/
noncomputable def qmap (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : Pt W L →+ Pt W' L :=
  AddMonoidHom.mk' (qfun hG hW') (qfun_add hG hW')

lemma qmap_apply (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (S : Pt W L) :
    qmap hG hW' S = qfun hG hW' S := rfl

theorem hasGenI_qmap (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    HasGenI (qmap hG hW') (qPt hW') := fun S => qfun_spec hG hW' S

lemma map_tau_qPt_of_mem (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    {S : Pt W L} (hS : S ∈ G) :
    Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') = qPt hW' := by
  have hQ0 : Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') ≠ 0 := by
    rw [qPt, Point.map_some]; exact Point.some_ne_zero _
  refine eq_of_px_py hQ0 (qPt_ne_zero hW') ?_ ?_
  · rw [px_map]; exact (goodQ_qx (G := G)).1 S hS
  · rw [py_map]; exact (goodQ_qy (G := G)).1 S hS

/-- **The kernel of the quotient map is `G`.** -/
theorem qmap_eq_zero_iff (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {S : Pt W L} :
    qmap hG hW' S = 0 ↔ S ∈ G := by
  constructor
  · intro h
    by_contra hS
    have h1 := qfun_spec hG hW' S
    rw [← qmap_apply, h, map_zero, add_zero] at h1
    have h2 := congrArg px h1
    rw [px_map] at h2
    exact tau_qx_ne hS (by rw [tau_apply]; exact h2)
  · intro hS
    rw [qmap_apply]
    exact qfun_unique hG hW' (by rw [map_zero, add_zero]; exact map_tau_qPt_of_mem hW' hS)

lemma qmap_ne_zero (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : qmap hG hW' ≠ 0 := by
  intro h
  have hfin : (Set.univ : Set (Pt W L)).Finite := by
    refine (Set.finite_range (fun T : G => (T : Pt W L))).subset fun S _ => ?_
    exact ⟨⟨S, (qmap_eq_zero_iff hG hW').mp (by rw [h]; rfl)⟩, rfl⟩
  have := infinite_pt (W := W) (L := L)
  exact Set.infinite_univ hfin

lemma map_sig_ιQ (σ : L ≃ₐ[F] L) (C : Pt W' L) :
    Point.map (W' := W'.toAffine) (sig W σ).toAlgHom (ιQ W W' L C) =
      ιQ W W' L (Point.map (W' := W'.toAffine) σ.toAlgHom C) := by
  have h : (sig W σ).toAlgHom.comp (ιF W L) = (ιF W L).comp σ.toAlgHom := by
    apply AlgHom.ext; intro a; exact sig_L σ a
  rw [ιQ, Point.map_map, Point.map_map, h]

lemma map_sig_qPt (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    Point.map (W' := W'.toAffine) (sig W (frobAut (F := F) L)).toAlgHom (qPt hW') = qPt hW' := by
  rw [qPt, Point.map_some]; exact some_eq_some (sig_qx hFr) (sig_qy hFr)

lemma sig_comp_tau (σ : L ≃ₐ[F] L) (S : Pt W L) :
    (sig W σ).toAlgHom.comp ((tauHom W L S).restrictScalars F) =
      ((tauHom W L (ptMap σ S)).restrictScalars F).comp (sig W σ).toAlgHom :=
  AlgHom.ext fun f => sig_tau σ S f

/-- **The quotient map commutes with Frobenius.** -/
theorem qmap_frob (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) (S : Pt W L) :
    qmap hG hW' (RPLib.EllFq.frob W L S) = RPLib.EllFq.frob W' L (qmap hG hW' S) := by
  rw [frob_eq_ptMap, frob_eq_ptMap, qmap_apply, qmap_apply]
  apply qfun_unique hG hW'
  have h := congrArg (Point.map (W' := W'.toAffine) (sig W (frobAut (F := F) L)).toAlgHom)
    (qfun_spec hG hW' S)
  rw [Point.map_map, sig_comp_tau, ← Point.map_map, map_sig_qPt hW' hFr, map_add,
    map_sig_qPt hW' hFr, map_sig_ιQ] at h
  exact h

theorem isIsogenous_quot (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) : IsIsogenous W W' L :=
  ⟨qmap hG hW', ⟨qPt hW', hasGenI_qmap hG hW'⟩, qmap_ne_zero hG hW', qmap_frob hG hW' hFr⟩

end QMap

section Headline

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **Vélu quotient over `F_q`.** A finite Frobenius-stable subgroup `G` of `E(L)` with `p ∤ #G` is the kernel
of an isogeny `E → E'` defined over `F_q`; the two curves have the same trace. -/
theorem exists_quot_isog (G : AddSubgroup (Pt W L)) [Fintype G] (hG : (Fintype.card G : L) ≠ 0)
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ W' : WeierstrassCurve F, W'.IsElliptic ∧ ∃ φ : Pt W L →+ Pt W' L, IsIsog φ ∧
      (∀ S, φ S = 0 ↔ S ∈ G) ∧ (∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)) ∧
      RPLib.EllFq.trace W' = RPLib.EllFq.trace W := by
  obtain ⟨W', hE, hW'⟩ := exists_quotient hG hFr
  have := hE
  exact ⟨W', hE, qmap hG hW', ⟨qPt hW', hasGenI_qmap hG hW'⟩, fun S => qmap_eq_zero_iff hG hW',
    qmap_frob hG hW' hFr, (isIsogenous_quot hG hW' hFr).trace_eq.symm⟩

end Headline

end RPLib.DWS


