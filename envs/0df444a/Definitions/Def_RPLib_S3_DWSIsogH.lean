-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogH
-- name    : RPLib_S3_DWSIsogH
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:37:58.190185+00:00
-- url     : https://prove2.me/theorems/9f0e11cf-4651-42e1-92bf-ed2aecb96115
-- title:
--   Weight-two Ramanujan-Petersson library: descent of the quotient curve to `F_q`
-- statement:
--   Descent of the quotient curve to `F_q`.
--
--   For a finite subgroup `G` of `E(L)` that is stable under the `q`-Frobenius (and `p ∤ #G`):
--   * `sig_trG` : a Galois automorphism preserving `G` commutes with the translation sum `trG G`.
--   * `exists_quotient` : there is an elliptic curve `W'` over `F` with `(X_G, Y_G) ∈ W'(L(E))`.
--   * `qPt` : the generic point `(X_G, Y_G)` of `W'`, `qPt_ne_ιQ` : it is not a constant point.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogG

/-!
# S3-DWS-Isog, part H: descent of the quotient curve to `F_q`

For a finite subgroup `G` of `E(L)` that is stable under the `q`-Frobenius (and `p ∤ #G`):
* `sig_trG` : a Galois automorphism preserving `G` commutes with the translation sum `trG G`.
* `exists_quotient` : there is an elliptic curve `W'` over `F` with `(X_G, Y_G) ∈ W'(L(E))`.
* `qPt` : the generic point `(X_G, Y_G)` of `W'`, `qPt_ne_ιQ` : it is not a constant point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Descent

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G]

lemma ptMap_injective' (σ : L ≃ₐ[F] L) : Function.Injective (ptMap (W := W) σ) := by
  intro P Q h
  unfold ptMap at h
  exact Point.map_injective _ h

/-- A Galois automorphism preserving `G` commutes with the translation sum over `G`. -/
lemma sig_trG (σ : L ≃ₐ[F] L) (hσ : ∀ T ∈ G, ptMap σ T ∈ G) (f : FF W L) :
    sig W σ (trG G f) = trG G (sig W σ f) := by
  unfold trG
  rw [map_sum]
  simp_rw [sig_tau]
  let e : G → G := fun T => ⟨ptMap σ (T : Pt W L), hσ T T.2⟩
  have he : Function.Injective e := fun T T' h =>
    Subtype.ext (ptMap_injective' σ (congrArg Subtype.val h))
  exact Fintype.sum_bijective e he.bijective_of_finite _ _ (fun T => rfl)

lemma frobStable_ptMap (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∀ T ∈ G, ptMap (frobAut (F := F) L) T ∈ G := fun T hT => by
  rw [← frob_eq_ptMap]; exact hFr T hT

lemma sig_qx (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    sig W (frobAut (F := F) L) (qx G) = qx G := by
  show sig W _ (trG G (gx W L)) = trG G (gx W L)
  rw [sig_trG _ (frobStable_ptMap hFr), sig_gx]

lemma sig_qy (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    sig W (frobAut (F := F) L) (qy G) = qy G := by
  show sig W _ (trG G (gy W L)) = trG G (gy W L)
  rw [sig_trG _ (frobStable_ptMap hFr), sig_gy]

/-- The quotient curve is fixed by any `σ` fixing `X_G` and `Y_G`. -/
lemma qcurve_map_eq (σ : L ≃ₐ[F] L) (hx : sig W σ (qx G) = qx G) (hy : sig W σ (qy G) = qy G)
    {V : WeierstrassCurve L} (hV : (V.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    V.map (σ : L →+* L) = V := by
  refine qcurve_unique ?_ hV
  have e := (equation_iff _ _).mp hV
  change qy G ^ 2 + algebraMap L (FF W L) V.a₁ * qx G * qy G + algebraMap L (FF W L) V.a₃ * qy G =
    qx G ^ 3 + algebraMap L (FF W L) V.a₂ * qx G ^ 2 + algebraMap L (FF W L) V.a₄ * qx G +
      algebraMap L (FF W L) V.a₆ at e
  have e2 := congrArg (sig W σ) e
  simp only [map_add, map_mul, map_pow, sig_L, hx, hy] at e2
  rw [equation_iff]
  change qy G ^ 2 + algebraMap L (FF W L) (σ V.a₁) * qx G * qy G +
      algebraMap L (FF W L) (σ V.a₃) * qy G =
    qx G ^ 3 + algebraMap L (FF W L) (σ V.a₂) * qx G ^ 2 + algebraMap L (FF W L) (σ V.a₄) * qx G +
      algebraMap L (FF W L) (σ V.a₆)
  exact e2

lemma frob_fixed_mem {a : L} (h : frobAut (F := F) L a = a) : a ∈ (algebraMap F L).range :=
  (RPLib.EllFq.pow_card_eq_self_iff (L := F) a).mp (by rw [← frobAut_apply]; exact h)

/-- **Descent.** For a Frobenius-stable `G` with `p ∤ #G`, the quotient curve is defined over `F`. -/
theorem exists_quotient (hG : (Fintype.card G : L) ≠ 0)
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ W' : WeierstrassCurve F, W'.IsElliptic ∧
      (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G) := by
  obtain ⟨V, hV⟩ := exists_qcurve hG
  have hm := qcurve_map_eq (frobAut (F := F) L) (sig_qx hFr) (sig_qy hFr) hV
  obtain ⟨c₁, h₁⟩ := RingHom.mem_range.mp (frob_fixed_mem (congrArg WeierstrassCurve.a₁ hm))
  obtain ⟨c₂, h₂⟩ := RingHom.mem_range.mp (frob_fixed_mem (congrArg WeierstrassCurve.a₂ hm))
  obtain ⟨c₃, h₃⟩ := RingHom.mem_range.mp (frob_fixed_mem (congrArg WeierstrassCurve.a₃ hm))
  obtain ⟨c₄, h₄⟩ := RingHom.mem_range.mp (frob_fixed_mem (congrArg WeierstrassCurve.a₄ hm))
  obtain ⟨c₆, h₆⟩ := RingHom.mem_range.mp (frob_fixed_mem (congrArg WeierstrassCurve.a₆ hm))
  let W' : WeierstrassCurve F := ⟨c₁, c₂, c₃, c₄, c₆⟩
  have hW'V : W'.baseChange L = V := by
    ext
    exacts [h₁, h₂, h₃, h₄, h₆]
  have hΔ : W'.Δ ≠ 0 := by
    intro h0
    apply qcurve_Δ_ne_zero hG hV
    rw [← hW'V]
    show (W'.map (algebraMap F L)).Δ = 0
    rw [map_Δ, h0, map_zero]
  have hbc : W'.baseChange (FF W L) = V.baseChange (FF W L) := by
    rw [← hW'V]
    ext
    · exact IsScalarTower.algebraMap_apply F L (FF W L) c₁
    · exact IsScalarTower.algebraMap_apply F L (FF W L) c₂
    · exact IsScalarTower.algebraMap_apply F L (FF W L) c₃
    · exact IsScalarTower.algebraMap_apply F L (FF W L) c₄
    · exact IsScalarTower.algebraMap_apply F L (FF W L) c₆
  refine ⟨W', ?_, ?_⟩
  · rw [isElliptic_iff]; exact isUnit_iff_ne_zero.mpr hΔ
  · rw [hbc]; exact hV

variable {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- The generic point `(X_G, Y_G)` of the quotient curve. -/
noncomputable def qPt (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    (W'.baseChange (FF W L)).toAffine.Point :=
  Point.some (qx G) (qy G) (equation_iff_nonsingular.mp hW')

lemma px_qPt (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    px (qPt hW') = qx G := rfl

lemma py_qPt (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    py (qPt hW') = qy G := rfl

/-- The generic point of the quotient is not constant. -/
lemma qPt_ne_ιQ (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (C : Pt W' L) : qPt hW' ≠ ιQ W W' L C := by
  intro h
  rcases C with _ | ⟨a, b, hab⟩
  · rw [show (Point.zero : Pt W' L) = 0 from rfl, map_zero] at h
    exact Point.some_ne_zero _ h
  · rw [ιQ, Point.map_some] at h
    have hx : qx G = algebraMap L (FF W L) a := (Point.some.inj h).1
    have hc := Ge.const (W := W) a 0
    rw [← hx] at hc
    obtain ⟨h0, hord⟩ := ord_qx_zero (G := G)
    rcases hc with hc | hc
    · exact h0 hc
    · rw [hord] at hc; norm_num at hc

end Descent

end RPLib.DWS


