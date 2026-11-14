-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingJ
-- name    : RPLib_S2_WeilPairingJ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:04:38.998776+00:00
-- url     : https://prove2.me/theorems/886a5e33-38cb-4294-809e-21aaf48551e0
-- title:
--   Weil pairing, part J: Galois equivariance
-- statement:
--   For a field automorphism $\sigma$ of $L$ over the base field: its action on the coordinate ring, function field and points, and $e_n(\sigma S, \sigma T) = \sigma(e_n(S,T))$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition III.8.1(d)

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingI

/-!
# WPJ: equivariance of the Weil pairing (unit S2-WeilPairing, O9)

For a field automorphism `σ : L ≃ₐ[k] L`:
* `psi W σ : CR ≃+* CR`, coefficientwise action on the coordinate ring;
* `sig W σ : FF ≃ₐ[k] FF`, its extension to the function field;
* `ptMap σ : Pt → Pt`, the action on points;
* `sig_tau` : `σ ∘ τ_S = τ_{σS} ∘ σ`;
* `ord_sig` : `ord (σ f) (σ P) = ord f P`;
* `ePair_sig` : `e_n(σS, σT) = σ (e_n(S, T))`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section Equivariance

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-! ### The coordinate ring -/

lemma poly_map_eq (σ : L ≃ₐ[k] L) :
    (W.baseChange L).toAffine.polynomial.map (mapRingHom (σ.toAlgHom : L →+* L)) =
      (W.baseChange L).toAffine.polynomial := by
  rw [← WeierstrassCurve.Affine.map_polynomial]
  exact congrArg WeierstrassCurve.Affine.polynomial
    (WeierstrassCurve.Affine.map_baseChange (W := W.toAffine) σ.toAlgHom)

variable (W) in
/-- `σ` acting coefficientwise on the coordinate ring. -/
noncomputable def psi (σ : L ≃ₐ[k] L) : CR W L ≃+* CR W L :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv))
    (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      rw [Set.singleton_eq_singleton_iff]
      exact (poly_map_eq σ).symm)

variable (W) in
lemma psi_mk (σ : L ≃ₐ[k] L) (q : L[X][Y]) :
    psi W σ (mk (W.baseChange L).toAffine q) =
      mk (W.baseChange L).toAffine (q.map (mapRingHom (σ.toAlgHom : L →+* L))) :=
  rfl

variable (W) in
lemma psi_CC (σ : L ≃ₐ[k] L) (a : L) :
    psi W σ (mk (W.baseChange L).toAffine (C (C a))) = mk (W.baseChange L).toAffine (C (C (σ a))) := by
  rw [psi_mk]; simp

variable (W) in
lemma psi_X (σ : L ≃ₐ[k] L) :
    psi W σ (mk (W.baseChange L).toAffine (C X)) = mk (W.baseChange L).toAffine (C X) := by
  rw [psi_mk]; simp

variable (W) in
lemma psi_Y (σ : L ≃ₐ[k] L) :
    psi W σ (mk (W.baseChange L).toAffine Y) = mk (W.baseChange L).toAffine Y := by
  rw [psi_mk]; simp

variable (W) in
lemma psi_XClass (σ : L ≃ₐ[k] L) (x : L) :
    psi W σ (XClass (W.baseChange L).toAffine x) = XClass (W.baseChange L).toAffine (σ x) := by
  rw [XClass, XClass, psi_mk]; simp

variable (W) in
lemma psi_YClass (σ : L ≃ₐ[k] L) (y : L) :
    psi W σ (YClass (W.baseChange L).toAffine (C y)) = YClass (W.baseChange L).toAffine (C (σ y)) := by
  rw [YClass, YClass, psi_mk]; simp

/-! ### The function field -/

variable (W) in
/-- `σ` on the function field, as a ring isomorphism. -/
noncomputable def sigR (σ : L ≃ₐ[k] L) : FF W L ≃+* FF W L :=
  IsFractionRing.ringEquivOfRingEquiv (psi W σ)

lemma sigR_alg (σ : L ≃ₐ[k] L) (r : CR W L) :
    sigR W σ (algebraMap (CR W L) (FF W L) r) = algebraMap (CR W L) (FF W L) (psi W σ r) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

lemma sigR_L (σ : L ≃ₐ[k] L) (a : L) :
    sigR W σ (algebraMap L (FF W L) a) = algebraMap L (FF W L) (σ a) := by
  rw [← alg_mk_CC W L a, sigR_alg, psi_CC, alg_mk_CC]

variable (W) in
/-- `σ` on the function field, a `k`-algebra automorphism. -/
noncomputable def sig (σ : L ≃ₐ[k] L) : FF W L ≃ₐ[k] FF W L :=
  AlgEquiv.ofRingEquiv (f := sigR W σ) (fun c => by
    rw [IsScalarTower.algebraMap_apply k L (FF W L), sigR_L, AlgEquiv.commutes])

lemma sig_apply (σ : L ≃ₐ[k] L) (f : FF W L) : sig W σ f = sigR W σ f := rfl

lemma sig_algCR (σ : L ≃ₐ[k] L) (r : CR W L) :
    sig W σ (algebraMap (CR W L) (FF W L) r) = algebraMap (CR W L) (FF W L) (psi W σ r) :=
  sigR_alg σ r

lemma sig_L (σ : L ≃ₐ[k] L) (a : L) :
    sig W σ (algebraMap L (FF W L) a) = algebraMap L (FF W L) (σ a) :=
  sigR_L σ a

lemma sig_symm_L (σ : L ≃ₐ[k] L) (a : L) :
    (sig W σ).symm (algebraMap L (FF W L) a) = algebraMap L (FF W L) (σ.symm a) := by
  rw [AlgEquiv.symm_apply_eq, sig_L, AlgEquiv.apply_symm_apply]

lemma sig_gx (σ : L ≃ₐ[k] L) : sig W σ (gx W L) = gx W L := by
  rw [gx, sig_algCR, psi_X]

lemma sig_gy (σ : L ≃ₐ[k] L) : sig W σ (gy W L) = gy W L := by
  rw [gy, sig_algCR, psi_Y]

/-! ### Points -/

/-- `σ` acting on points. -/
noncomputable def ptMap (σ : L ≃ₐ[k] L) (P : Pt W L) : Pt W L :=
  Point.map (W' := W.toAffine) σ.toAlgHom P

lemma ptMap_zero (σ : L ≃ₐ[k] L) : ptMap σ (0 : Pt W L) = 0 := rfl

lemma ptMap_add (σ : L ≃ₐ[k] L) (P Q : Pt W L) : ptMap σ (P + Q) = ptMap σ P + ptMap σ Q :=
  map_add _ P Q

lemma ptMap_neg (σ : L ≃ₐ[k] L) (P : Pt W L) : ptMap σ (-P) = -ptMap σ P :=
  map_neg _ P

lemma ptMap_nsmul (σ : L ≃ₐ[k] L) (m : ℕ) (P : Pt W L) : ptMap σ (m • P) = m • ptMap σ P :=
  map_nsmul _ m P

lemma ptMap_injective (σ : L ≃ₐ[k] L) : Function.Injective (ptMap (W := W) σ) :=
  Point.map_injective (W' := W.toAffine) σ.toAlgHom

lemma ptMap_eq_zero (σ : L ≃ₐ[k] L) {P : Pt W L} : ptMap σ P = 0 ↔ P = 0 := by
  exact (ptMap_injective σ).eq_iff' (ptMap_zero σ)

lemma ptMap_symm_apply (σ : L ≃ₐ[k] L) (P : Pt W L) : ptMap σ.symm (ptMap σ P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [ptMap, Point.map_some]
    exact some_eq_some (σ.symm_apply_apply x) (σ.symm_apply_apply y)

lemma ptMap_apply_symm (σ : L ≃ₐ[k] L) (P : Pt W L) : ptMap σ (ptMap σ.symm P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [ptMap, Point.map_some]
    exact some_eq_some (σ.apply_symm_apply x) (σ.apply_symm_apply y)

lemma px_ptMap (σ : L ≃ₐ[k] L) (P : Pt W L) : px (ptMap σ P) = σ (px P) :=
  px_map (W' := W.toAffine) σ.toAlgHom P

lemma py_ptMap (σ : L ≃ₐ[k] L) (P : Pt W L) : py (ptMap σ P) = σ (py P) :=
  py_map (W' := W.toAffine) σ.toAlgHom P

lemma map_sig_G (σ : L ≃ₐ[k] L) :
    Point.map (W' := W.toAffine) (sig W σ).toAlgHom (G W L) = G W L := by
  rw [G, Point.map_some]
  exact some_eq_some (sig_gx σ) (sig_gy σ)

lemma map_sig_ιP (σ : L ≃ₐ[k] L) (S : Pt W L) :
    Point.map (W' := W.toAffine) (sig W σ).toAlgHom (ιP W L S) = ιP W L (ptMap σ S) := by
  have hcomp : (sig W σ).toAlgHom.comp (ιF W L) = (ιF W L).comp σ.toAlgHom := by
    apply AlgHom.ext
    intro a
    exact sig_L σ a
  rw [ιP, ptMap, Point.map_map, Point.map_map, hcomp]

lemma map_sig_pS (σ : L ≃ₐ[k] L) (S : Pt W L) :
    Point.map (W' := W.toAffine) (sig W σ).toAlgHom (pS W L S) = pS W L (ptMap σ S) := by
  rw [pS, pS, map_add, map_sig_G, map_sig_ιP]

/-! ### Translations -/

variable (W) in
/-- `σ⁻¹ ∘ τ_{σS} ∘ σ`, an `L`-algebra map. -/
noncomputable def conj (σ : L ≃ₐ[k] L) (S : Pt W L) : FF W L →ₐ[L] FF W L where
  toRingHom := ((sig W σ).symm : FF W L →+* FF W L).comp
    (((tau W L (ptMap σ S)) : FF W L →+* FF W L).comp ((sig W σ) : FF W L →+* FF W L))
  commutes' a := by
    show (sig W σ).symm (tau W L (ptMap σ S) (sig W σ (algebraMap L (FF W L) a))) =
      algebraMap L (FF W L) a
    rw [sig_L, AlgEquiv.commutes, sig_symm_L, σ.symm_apply_apply]

lemma conj_apply (σ : L ≃ₐ[k] L) (S : Pt W L) (f : FF W L) :
    conj W σ S f = (sig W σ).symm (tau W L (ptMap σ S) (sig W σ f)) := rfl

lemma conj_eq (σ : L ≃ₐ[k] L) (S : Pt W L) : conj W σ S = tauHom W L S := by
  apply algHom_ext_gen W L
  · rw [conj_apply, sig_gx, tau_gx, tauHom_gx, AlgEquiv.symm_apply_eq, ← map_sig_pS, px_map]
    rfl
  · rw [conj_apply, sig_gy, tau_gy, tauHom_gy, AlgEquiv.symm_apply_eq, ← map_sig_pS, py_map]
    rfl

/-- `σ ∘ τ_S = τ_{σS} ∘ σ`. -/
theorem sig_tau (σ : L ≃ₐ[k] L) (S : Pt W L) (f : FF W L) :
    sig W σ (tau W L S f) = tau W L (ptMap σ S) (sig W σ f) := by
  have h := congrArg (fun φ : FF W L →ₐ[L] FF W L => φ f) (conj_eq σ S)
  rw [conj_apply, AlgEquiv.symm_apply_eq] at h
  rw [h]
  rfl

/-! ### Valuations and orders -/

lemma ptMap_ne_zero (σ : L ≃ₐ[k] L) {P : Pt W L} (hP : P ≠ 0) : ptMap σ P ≠ 0 :=
  fun h => hP ((ptMap_eq_zero σ).mp h)

lemma map_hosP (σ : L ≃ₐ[k] L) {P : Pt W L} (hP : P ≠ 0) :
    (hosP W L P hP).asIdeal.map (psi W σ : CR W L →+* CR W L) =
      (hosP W L (ptMap σ P) (ptMap_ne_zero σ hP)).asIdeal := by
  rw [hosP, hosP, hos_asIdeal, hos_asIdeal, XYIdeal, XYIdeal, Ideal.map_span, Set.image_pair,
    px_ptMap, py_ptMap]
  simp only [RingEquiv.coe_toRingHom, psi_XClass, psi_YClass]

lemma mem_hosP_iff (σ : L ≃ₐ[k] L) {P : Pt W L} (hP : P ≠ 0) (b : CR W L) :
    psi W σ b ∈ (hosP W L (ptMap σ P) (ptMap_ne_zero σ hP)).asIdeal ↔ b ∈ (hosP W L P hP).asIdeal := by
  rw [← map_hosP σ hP, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem nu_sig (σ : L ≃ₐ[k] L) {P : Pt W L} (hP : P ≠ 0) (f : FF W L) :
    nu W L (ptMap σ P) (ptMap_ne_zero σ hP) (sig W σ f) = nu W L P hP f := by
  have key : (nu W L (ptMap σ P) (ptMap_ne_zero σ hP)).comap
      ((sig W σ : FF W L ≃+* FF W L) : FF W L →+* FF W L) = nu W L P hP := by
    obtain ⟨π', hπ'⟩ :=
      (hosP W L (ptMap σ P) (ptMap_ne_zero σ hP)).valuation_exists_uniformizer (FF W L)
    obtain ⟨π, hπ⟩ := (hosP W L P hP).valuation_exists_uniformizer (FF W L)
    refine valuation_eq_of_le_one_iff _ _ (fun g => ?_) (t₁ := (sig W σ).symm π') ?_ hπ
    · show nu W L (ptMap σ P) (ptMap_ne_zero σ hP) (sig W σ g) ≤ 1 ↔ nu W L P hP g ≤ 1
      rw [nu_eq_valuation, nu_eq_valuation, valuation_le_one_iff_exists,
        valuation_le_one_iff_exists]
      constructor
      · rintro ⟨a, b, hb, hab⟩
        refine ⟨(psi W σ).symm a, (psi W σ).symm b, fun h => hb ?_, ?_⟩
        · rw [← (psi W σ).apply_symm_apply b, mem_hosP_iff]
          exact h
        · apply (sig W σ).injective
          rw [map_mul, sig_algCR, sig_algCR, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
          exact hab
      · rintro ⟨a, b, hb, hab⟩
        refine ⟨psi W σ a, psi W σ b, by rwa [mem_hosP_iff], ?_⟩
        rw [← sig_algCR, ← sig_algCR, ← map_mul, hab]
    · show nu W L (ptMap σ P) (ptMap_ne_zero σ hP) (sig W σ ((sig W σ).symm π')) = _
      rw [AlgEquiv.apply_symm_apply]
      exact hπ'
  exact congrArg (fun ν : Valuation (FF W L) (WithZero (Multiplicative ℤ)) => ν f) key

lemma ord_sig_ne (σ : L ≃ₐ[k] L) {P : Pt W L} (hP : P ≠ 0) (f : FF W L) :
    ord W L (sig W σ f) (ptMap σ P) = ord W L f P := by
  rw [ord_eq (ptMap_ne_zero σ hP), ord_eq hP, nu_sig]

/-- Orders are transported by `σ`. -/
theorem ord_sig (σ : L ≃ₐ[k] L) (f : FF W L) (P : Pt W L) :
    ord W L (sig W σ f) (ptMap σ P) = ord W L f P := by
  by_cases hP : P = 0
  · subst hP
    have hB : -base W L ≠ 0 := neg_ne_zero.mpr (base_ne W L)
    have e1 : ord W L f 0 = ord W L (tau W L (base W L) f) (-base W L) := by
      rw [ord_tau, neg_add_cancel]
    rw [e1, ← ord_sig_ne σ hB, sig_tau, ord_tau, ptMap_neg, neg_add_cancel, ptMap_zero]
  · exact ord_sig_ne σ hP f

/-! ### Equivariance of the pairing -/

/-- **Equivariance** of the Weil pairing under field automorphisms: `e_n(σS, σT) = σ (e_n(S, T))`. -/
theorem ePair_sig (σ : L ≃ₐ[k] L) {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0)
    (hT : n • T = 0) : ePair W L n (ptMap σ S) (ptMap σ T) = σ (ePair W L n S T) := by
  have hS' : n • ptMap σ S = 0 := by rw [← ptMap_nsmul, hS, ptMap_zero]
  have hT' : n • ptMap σ T = 0 := by rw [← ptMap_nsmul, hT, ptMap_zero]
  have hsig0 : sig W σ (gT W L n T) ≠ 0 := by
    intro h
    exact gT_ne_zero n T ((sig W σ).injective (h.trans (map_zero _).symm))
  obtain ⟨c, hc, hcg⟩ := exists_const_of_ord_eq hsig0 (gT_ne_zero n (ptMap σ T)) (fun Q _ => by
    obtain ⟨Q', rfl⟩ : ∃ Q', ptMap σ Q' = Q := ⟨ptMap σ.symm Q, ptMap_apply_symm σ Q⟩
    rw [ord_sig, ord_gT hn hT, ord_gT hn hT']
    simp only [dT, ← ptMap_nsmul, (ptMap_injective σ).eq_iff, ptMap_eq_zero])
  have h1 : tau W L (ptMap σ S) (sig W σ (gT W L n T)) =
      algebraMap L (FF W L) (σ (ePair W L n S T)) * sig W σ (gT W L n T) := by
    rw [← sig_tau, tau_gT hn hS hT, map_mul, sig_L]
  rw [hcg, map_mul, AlgEquiv.commutes, tau_gT hn hS' hT'] at h1
  have hc' : algebraMap L (FF W L) c ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap L (FF W L)).injective]
    exact hc
  apply alg_cancel (gT_ne_zero n (ptMap σ T))
  exact mul_left_cancel₀ hc' (h1.trans (by ring))

end Equivariance

end RPLib.Weil


