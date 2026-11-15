-- Prove2me | Definitions.Def_RPLib_S3_DWSTateU
-- name    : RPLib_S3_DWSTateU
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:17:11.683585+00:00
-- url     : https://prove2.me/theorems/88206ae3-0288-47de-bc49-a4d4584c7750
-- title:
--   Weight-two Ramanujan-Petersson library: an isomorphism of function fields carries points to points
-- statement:
--   An isomorphism of function fields carries points to points.
--
--   `ψ : L(E') ≃ₐ[L] L(E)` (two curves over the same finite field).
--
--   * `Tr ψ P Q` : `ord_P (ψ f) = ord_Q f` for every `f ≠ 0`; `Tr.symm`, `Tr.unique`, `Tr.inj`
--     (`eq_of_ord_eq` : points are separated by their order functions).
--   * **`tr_of_ge`** : if `ψ x'` is regular at `P`, then `Tr ψ P Q` for some affine `Q` (`e = 1` for an isomorphism).
--   * `pole_y_of_pole_x` : on `W'` over `L(E)`, a pole of `x` of order `-n` forces `ord y ≥ 3n/2`.
--   * `ge_add_pole'` : the addition law at a pole of any order.
--   * **`exists_tr`** : every point `P ∈ E` has a partner `Q ∈ E'` with `Tr ψ P Q`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateT

/-!
# S3-DWS-Tate, part U: an isomorphism of function fields carries points to points

`ψ : L(E') ≃ₐ[L] L(E)` (two curves over the same finite field).

* `Tr ψ P Q` : `ord_P (ψ f) = ord_Q f` for every `f ≠ 0`; `Tr.symm`, `Tr.unique`, `Tr.inj`
  (`eq_of_ord_eq` : points are separated by their order functions).
* **`tr_of_ge`** : if `ψ x'` is regular at `P`, then `Tr ψ P Q` for some affine `Q` (`e = 1` for an isomorphism).
* `pole_y_of_pole_x` : on `W'` over `L(E)`, a pole of `x` of order `-n` forces `ord y ≥ 3n/2`.
* `ge_add_pole'` : the addition law at a pole of any order.
* **`exists_tr`** : every point `P ∈ E` has a partner `Q ∈ E'` with `Tr ψ P Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Tr

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- `ψ` carries the place `Q` of `E'` to the place `P` of `E`. -/
def Tr (ψ : FF W' L ≃ₐ[L] FF W L) (P : Pt W L) (Q : Pt W' L) : Prop :=
  ∀ f, f ≠ 0 → ord W L (ψ f) P = ord W' L f Q

lemma Tr.symm {ψ : FF W' L ≃ₐ[L] FF W L} {P : Pt W L} {Q : Pt W' L} (h : Tr ψ P Q) :
    Tr ψ.symm Q P := by
  intro g hg
  have hg' : ψ.symm g ≠ 0 := (_root_.map_ne_zero ψ.symm).mpr hg
  have := h (ψ.symm g) hg'
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

/-- Points are separated by their order functions. -/
lemma eq_of_ord_eq {P P' : Pt W L} (h : ∀ f : FF W L, f ≠ 0 → ord W L f P = ord W L f P') : P = P' := by
  have h1 := h (tau W L (-P) (gx W L)) (tau_ne_zero _ (gx_ne_zero' (W := W) (L := L)))
  rw [ord_tau, ord_tau, add_neg_cancel] at h1
  have h2 : ord W L (gx W L) (P' + -P) < 0 := by rw [← h1]; exact ord_gx_zero_neg
  exact (add_neg_eq_zero.mp (eq_zero_of_ord_gx_neg h2)).symm

lemma Tr.unique {ψ : FF W' L ≃ₐ[L] FF W L} {P : Pt W L} {Q Q' : Pt W' L} (h : Tr ψ P Q)
    (h' : Tr ψ P Q') : Q = Q' :=
  eq_of_ord_eq (fun f hf => by rw [← h f hf, h' f hf])

lemma Tr.inj {ψ : FF W' L ≃ₐ[L] FF W L} {P P' : Pt W L} {Q : Pt W' L} (h : Tr ψ P Q)
    (h' : Tr ψ P' Q) : P = P' :=
  h.symm.unique h'.symm

/-- **Regular points have partners.** If `ψ x'` is regular at `P`, `ψ` carries some affine `Q` to `P`. -/
theorem tr_of_ge (ψ : FF W' L ≃ₐ[L] FF W L) {P : Pt W L} (h : Ge 0 (ψ (gx W' L)) P) :
    ∃ Q : Pt W' L, Q ≠ 0 ∧ Tr ψ P Q := by
  have hord : ∀ g : FF W L, ord W L (tau W L (P - base W L) g) (base W L) = ord W L g P := fun g => by
    rw [ord_tau, add_sub_cancel]
  have hx0 : ψ (gx W' L) ≠ 0 := (_root_.map_ne_zero ψ).mpr (gx_ne_zero' (W := W') (L := L))
  obtain ⟨ψP, hψP⟩ : ∃ ψP : FF W' L ≃ₐ[L] FF W L, ψP = ψ.trans (tau W L (P - base W L)) := ⟨_, rfl⟩
  have hψPa : ∀ f, ψP f = tau W L (P - base W L) (ψ f) := fun f => by rw [hψP]; rfl
  have hx : nu W L (base W L) (base_ne W L) (ψP.toAlgHom (gx W' L)) ≤ 1 := by
    refine nu_le_one_of_ge (base_ne W L) ((_root_.map_ne_zero ψP).mpr (gx_ne_zero' (W := W') (L := L))) ?_
    show 0 ≤ ord W L (ψP (gx W' L)) (base W L)
    rw [hψPa, hord]; exact h.resolve_left hx0
  obtain ⟨Q, hQ, -, -, e, -, he⟩ := exists_place2 ψP.toAlgHom (base_ne W L) hx
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
    (K := FF W L) (v := hosP W L (base W L) (base_ne W L))
  have ht0 : t ≠ 0 := by
    rintro rfl; rw [map_zero] at ht; exact WithZero.exp_ne_zero ht.symm
  have hto : ord W L t (base W L) = 1 := by
    rw [ord_eq (base_ne W L), nu_eq_valuation, ht, WithZero.log_exp]; norm_num
  have h1 : ord W L (ψP (ψP.symm t)) (base W L) = e * ord W' L (ψP.symm t) Q :=
    he (ψP.symm t) ((_root_.map_ne_zero _).mpr ht0)
  rw [AlgEquiv.apply_symm_apply, hto] at h1
  have he' : (e : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm
  refine ⟨Q, hQ, fun f hf => ?_⟩
  have h2 : ord W L (ψP f) (base W L) = e * ord W' L f Q := he f hf
  rw [he', one_mul, hψPa, hord] at h2
  exact h2

/-- A pole of `x` forces a pole of `y` of at most `3/2` the order (`(x, y)` on `W'` over `L(E)`). -/
lemma pole_y_of_pole_x {x y : FF W L} (h : (W'.baseChange (FF W L)).toAffine.Equation x y) {P : Pt W L}
    (hx : x ≠ 0) {n : ℤ} (ho : ord W L x P = n) (hn : n < 0) :
    ∃ m : ℤ, 3 * n ≤ 2 * m ∧ m ≤ n ∧ Ge m y P := by
  by_cases hy : y = 0
  · exact ⟨n, by omega, le_rfl, Or.inl hy⟩
  by_cases hkn : 3 * n ≤ 2 * ord W L y P
  · exact ⟨min (ord W L y P) n, by omega, min_le_right _ _, Or.inr (min_le_left _ _)⟩
  exfalso
  push_neg at hkn
  have e := eqn_FF h
  have hc : ∀ a : L, Ge 0 (algebraMap L (FF W L) a) P := fun a => Ge.const a P
  have hgx : Ge n x P := Or.inr ho.ge
  have hgy : Ge (ord W L y P) y P := Or.inr le_rfl
  have hy2 : ord W L (y ^ 2) P = 2 * ord W L y P := by rw [pow_two, ord_mul hy hy]; ring
  have hrest : Ge (2 * ord W L y P + 1)
      (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x * y +
        algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃ * y) P :=
    ((((hc _).mul hgx).mul hgy).mono (by omega)).add (((hc _).mul hgy).mono (by omega))
  obtain ⟨hL0, hLo⟩ := ge_lead (pow_ne_zero 2 hy) hy2 hrest
  have hR : Ge (3 * n) (x ^ 3 + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ * x +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆) P :=
    ((((hgx.pow 3).mono (by push_cast; omega)).add (((hc _).mul (hgx.pow 2)).mono (by push_cast; omega))).add
      (((hc _).mul hgx).mono (by omega))).add ((hc _).mono (by omega))
  rw [← e, add_assoc] at hR
  rcases hR with h0 | h0
  · exact hL0 h0
  · rw [hLo] at h0; omega

/-- **Pole case of the addition law, any order.** -/
theorem ge_add_pole' {x₁ y₁ x₂ y₂ : FF W L} (h₁ : (W'.baseChange (FF W L)).toAffine.Equation x₁ y₁)
    {P : Pt W L} (hx₁ : x₁ ≠ 0) {n m : ℤ} (ho : ord W L x₁ P = n) (hn : n < 0) (hm : 3 * n ≤ 2 * m)
    (hmn : m ≤ n) (hy₁ : Ge m y₁ P) (hx₂ : Ge 0 x₂ P) (hy₂ : Ge 0 y₂ P) :
    x₁ ≠ x₂ ∧ Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) P ∧
      Ge 0 ((W'.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) P := by
  obtain ⟨hd0, hdo⟩ : x₁ - x₂ ≠ 0 ∧ ord W L (x₁ - x₂) P = n := by
    rw [sub_eq_add_neg]; exact ge_lead hx₁ ho (hx₂.neg.mono (by omega))
  have hio : Ge (-n) (x₁ - x₂)⁻¹ P := Or.inr (by rw [ord_inv, hdo])
  have hc : ∀ a : L, Ge 0 (algebraMap L (FF W L) a) P := fun a => Ge.const a P
  have hX := pole_alg (y₂ := y₂) hd0 (eqn_FF h₁)
  have hk2 : Ge 0 (2 * y₂ + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃) P :=
    (((Ge.ofNat 2 P).mul0 hy₂).add ((hc _).mul0 hx₂)).add (hc _)
  have hk1 : Ge 0 (3 * x₂ ^ 2 + 2 * algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * y₂) P :=
    ((((Ge.ofNat 3 P).mul0 hx₂.sq0).add (((Ge.ofNat 2 P).mul0 (hc _)).mul0 hx₂)).add (hc _)).sub
      ((hc _).mul0 hy₂)
  have hk0 : Ge 0 (algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ + y₂ ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * x₂ * y₂ - 2 * x₂ ^ 3 -
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * x₂ ^ 2) P :=
    ((((hc _).add hy₂.sq0).add (((hc _).mul0 hx₂).mul0 hy₂)).sub
      ((Ge.ofNat 2 P).mul0 ((hx₂.pow 3).mono (by norm_num)))).sub ((hc _).mul0 hx₂.sq0)
  have hN := (((hy₁.neg.mul hk2).mono (by omega : m ≤ m + 0)).add
    ((Ge.mul (Or.inr ho.ge) hk1).mono (by omega : m ≤ n + 0))).add (hk0.mono (by omega : m ≤ 0))
  have hNi := hN.mul (hio.pow 2)
  have hX3 : Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) P := by
    rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX]
    exact hx₂.add (hNi.mono (by push_cast; omega))
  refine ⟨sub_ne_zero.mp hd0, hX3, ?_⟩
  rw [addY, negY, negAddY, negAddY_alg hd0]
  rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX]
  rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), hX] at hX3
  have hu : Ge m (y₁ - y₂) P := hy₁.sub (hy₂.mono (by omega))
  rw [add_sub_cancel_left, bc_a₃ W' L (FF W L)]
  exact (((((hu.mul hio).mul hNi).mono (by push_cast; omega)).add hy₂).neg.sub ((hc _).mul0 hX3)).sub (hc _)

/-- `ψ` maps `G' + D` to `Θ + ι(D)`. -/
lemma map_pS2 (ψ : FF W' L →ₐ[L] FF W L) (D : Pt W' L) :
    Point.map (W' := W'.toAffine) (ψ.restrictScalars F) (pS W' L D) =
      Point.map (W' := W'.toAffine) (ψ.restrictScalars F) (G W' L) + ιQ W W' L D := by
  have hcomp : (ψ.restrictScalars F).comp (ιF W' L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact ψ.commutes a
  rw [pS, map_add, ιP, ιQ, Point.map_map, hcomp]

/-- **Every point has a partner.** -/
theorem exists_tr (ψ : FF W' L ≃ₐ[L] FF W L) (P : Pt W L) : ∃ Q : Pt W' L, Tr ψ P Q := by
  have hx0 : ψ (gx W' L) ≠ 0 := (_root_.map_ne_zero ψ).mpr (gx_ne_zero' (W := W') (L := L))
  by_cases hreg : 0 ≤ ord W L (ψ (gx W' L)) P
  · obtain ⟨Q, -, hQ⟩ := tr_of_ge ψ (Or.inr hreg)
    exact ⟨Q, hQ⟩
  push_neg at hreg
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = Point.map (W' := W'.toAffine) (ψ.toAlgHom.restrictScalars F) (G W' L) :=
    ⟨_, rfl⟩
  have hΘ0 : Θ ≠ 0 := by rw [hΘ, G, Point.map_some]; exact Point.some_ne_zero _
  have hpx : px Θ = ψ (gx W' L) := by rw [hΘ, px_map]; rfl
  have hpy : py Θ = ψ (gy W' L) := by rw [hΘ, py_map]; rfl
  obtain ⟨D, hD⟩ := exists_affine W' L
  obtain ⟨C, hC⟩ : ∃ C, C = ιQ W W' L D := ⟨_, rfl⟩
  have hC0 : C ≠ 0 := by
    rw [hC]; intro h0; apply hD; apply ιQ_injective (W := W) (W' := W') (L := L); rw [h0, map_zero]
  have hpxC : px C = algebraMap L (FF W L) (px D) := by rw [hC, ιQ, px_map]; rfl
  have hpyC : py C = algebraMap L (FF W L) (py D) := by rw [hC, ιQ, py_map]; rfl
  have hx0' : px Θ ≠ 0 := by rw [hpx]; exact hx0
  obtain ⟨m, hm, hmn, hym⟩ := pole_y_of_pole_x (nonsingular_px_py hΘ0).1 hx0' rfl
    (by rw [hpx]; exact hreg)
  obtain ⟨hne, hX, -⟩ := ge_add_pole' (x₂ := px C) (y₂ := py C) (nonsingular_px_py hΘ0).1 hx0' rfl
    (by rw [hpx]; exact hreg) hm hmn hym (by rw [hpxC]; exact Ge.const _ P) (by rw [hpyC]; exact Ge.const _ P)
  have hsum : ψ (tau W' L D (gx W' L)) = px (Θ + C) := by
    rw [tau_gx, hΘ, hC, ← map_pS2 ψ.toAlgHom D, px_map]
    rfl
  have hge : Ge 0 (((tau W' L D).trans ψ) (gx W' L)) P := by
    show Ge 0 (ψ (tau W' L D (gx W' L))) P
    rw [hsum, px_add' hΘ0 hC0 hne]
    exact hX
  obtain ⟨Q, -, hQ⟩ := tr_of_ge ((tau W' L D).trans ψ) hge
  refine ⟨Q + -D, fun g hg => ?_⟩
  have h1 := hQ _ (tau_ne_zero (-D) hg)
  have e : ((tau W' L D).trans ψ) (tau W' L (-D) g) = ψ g := by
    rw [AlgEquiv.trans_apply, ← tau_add_apply, add_neg_cancel, tau_zero_apply]
  rw [e, ord_tau] at h1
  exact h1

end Tr

end RPLib.DWS


