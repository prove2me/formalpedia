-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegE
-- name    : RPLib_S2_IsogenyDegE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:21:29.287603+00:00
-- url     : https://prove2.me/theorems/41c82922-f531-4a00-8e15-2ee60b16dbb2
-- title:
--   Degrees of $r + s\pi$, part E: $1 - \pi$ is separable
-- statement:
--   $1 - \pi$ has ramification index 1, hence $\deg(1 - \pi) = \#E(\mathbb{F}_q)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Corollary III.5.5

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegD

/-!
# S2-IsogenyDeg part E: `1 - π` is separable, `deg (1 - π) = N`

* `exists_isPull_of_global`, `exists_isPull_one` : a function `f` with `ord_P (pull f) = 1` forces `e = 1`.
* `CongM2 P f g` : `f ≡ g mod m_P^2` (both integral); closure lemmas; `congM2_all` (generators ⇒ all of `CR`).
* `exists_isPull_one_sub_frob` : `1 - π` has a pullback with `e = 1`: near a point `P0 = (u, v)` with `u^q ≠ u`,
  `G - πG ≡ G + C mod m_{P0}^2` for the constant point `C = π(-P0)` (chord formula), so a uniformizer at
  `P0 + C` pulls back to a function of order `1` at `P0`.
* **`deg_one_sub_frob : deg (1 - π) = N`**.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

section Glob

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- `exists_pull'` from given global place data (keeps `e`). -/
theorem exists_isPull_of_global (Φ : (W.baseChange (FF W L)).toAffine.Point)
    (h : ∀ C, Φ ≠ ιP W L C) (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S))
    {P0 Q0 : Pt W L} {e : ℕ} (he1 : 1 ≤ e)
    (he : ∀ f, f ≠ 0 → ∀ P, ord W L (pull W L Φ h f) P = e * ord W L f (Q0 + φ (P - P0))) :
    ∃ ψ : FF W L →ₐ[L] FF W L, IsPull ψ e φ := by
  have hgx0 : gx W L ≠ 0 := by have := gx_ne W L 0; rwa [map_zero] at this
  have hnc : ∀ c : L, pull W L Φ h (gx W L) ≠ algebraMap L (FF W L) c := by
    intro c hc
    rw [← (pull W L Φ h).commutes c] at hc
    exact gx_ne W L c (pull_injective W L Φ h hc)
  obtain ⟨P2, hP2⟩ := exists_pole ((_root_.map_ne_zero _).mpr hgx0) hnc
  have hz : Q0 + φ (P2 - P0) = 0 := by
    by_contra hQ
    rw [he _ hgx0] at hP2
    have h1 := ord_nonneg_of_nu_le hQ hgx0 (HV_gx W L _ hQ).nu_le
    have h2 : (0 : ℤ) ≤ e * ord W L (gx W L) (Q0 + φ (P2 - P0)) := mul_nonneg (by positivity) h1
    exact absurd hP2 (not_lt.mpr h2)
  refine ⟨(tau W L P2).toAlgHom.comp (pull W L Φ h), ⟨he1,
    ((tau W L P2).toAlgHom.comp (pull W L Φ h)).toRingHom.injective, ?_, ?_⟩⟩
  · intro f hf P
    show ord W L (tau W L P2 (pull W L Φ h f)) P = _
    rw [ord_tau, he f hf, show Q0 + φ (P + P2 - P0) = φ P by
      rw [show P + P2 - P0 = (P2 - P0) + P by abel, map_add, ← add_assoc, hz, zero_add]]
  · intro S f
    show tau W L S (tau W L P2 (pull W L Φ h f)) = tau W L P2 (pull W L Φ h (tau W L (φ S) f))
    rw [← tau_pull W L Φ h φ hE, ← tau_add_apply, ← tau_add_apply, add_comm]

/-- A function whose pullback has order `1` somewhere forces ramification index `1`. -/
theorem exists_isPull_one (Φ : (W.baseChange (FF W L)).toAffine.Point)
    (h : ∀ C, Φ ≠ ιP W L C) (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S))
    {f : FF W L} (hf : f ≠ 0) {P1 : Pt W L} (h1 : ord W L (pull W L Φ h f) P1 = 1) :
    ∃ ψ : FF W L →ₐ[L] FF W L, IsPull ψ 1 φ := by
  obtain ⟨P0, Q0, e, he1, he⟩ := ord_pull_global Φ h φ hE
  have hk := he f hf P1
  rw [h1] at hk
  have he' : (e : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) hk.symm
  have he'' : e = 1 := by exact_mod_cast he'
  subst he''
  exact exists_isPull_of_global Φ h φ hE he1 he

end Glob

section Cong

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    exact WithZero.exp_le_exp.mpr (by omega)

lemma pow_le_exp_neg_two {x : WithZero (Multiplicative ℤ)} (h : x < 1) {n : ℕ} (hn : 2 ≤ n) :
    x ^ n ≤ WithZero.exp (-2) := by
  have h1 : x ≤ WithZero.exp (-1) := le_exp_neg_one h
  calc x ^ n = x ^ 2 * x ^ (n - 2) := by rw [← pow_add]; congr 1; omega
    _ ≤ WithZero.exp (-1) ^ 2 * 1 := mul_le_mul' (pow_le_pow_left' h1 2) (pow_le_one' h.le _)
    _ = WithZero.exp (-2) := by rw [mul_one, ← WithZero.exp_nsmul]; norm_num

lemma exp_neg_two_lt_one : WithZero.exp (-2 : ℤ) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

/-- `f ≡ g mod m_P^2`, both integral at `P`. -/
def CongM2 (P : Pt W L) (hP : P ≠ 0) (f g : FF W L) : Prop :=
  nu W L P hP (f - g) ≤ WithZero.exp (-2) ∧ nu W L P hP f ≤ 1 ∧ nu W L P hP g ≤ 1

variable {P : Pt W L} {hP : P ≠ 0} {f g f' g' : FF W L}

lemma CongM2.refl (hf : nu W L P hP f ≤ 1) : CongM2 P hP f f :=
  ⟨by rw [sub_self, map_zero]; exact zero_le', hf, hf⟩

lemma CongM2.alg (c : L) : CongM2 P hP (algebraMap L (FF W L) c) (algebraMap L (FF W L) c) :=
  CongM2.refl (nu_alg_le c)

lemma CongM2.add (h : CongM2 P hP f g) (h' : CongM2 P hP f' g') :
    CongM2 P hP (f + f') (g + g') := by
  refine ⟨?_, (Valuation.map_add _ _ _).trans (max_le h.2.1 h'.2.1),
    (Valuation.map_add _ _ _).trans (max_le h.2.2 h'.2.2)⟩
  rw [show f + f' - (g + g') = (f - g) + (f' - g') by ring]
  exact (Valuation.map_add _ _ _).trans (max_le h.1 h'.1)

lemma CongM2.neg (h : CongM2 P hP f g) : CongM2 P hP (-f) (-g) := by
  refine ⟨?_, by rw [Valuation.map_neg]; exact h.2.1, by rw [Valuation.map_neg]; exact h.2.2⟩
  rw [show -f - -g = -(f - g) by ring, Valuation.map_neg]
  exact h.1

lemma CongM2.sub (h : CongM2 P hP f g) (h' : CongM2 P hP f' g') :
    CongM2 P hP (f - f') (g - g') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg

lemma CongM2.mul (h : CongM2 P hP f g) (h' : CongM2 P hP f' g') :
    CongM2 P hP (f * f') (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show f * f' - g * g' = f * (f' - g') + (f - g) * g' by ring]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_mul]
      calc nu W L P hP f * nu W L P hP (f' - g') ≤ 1 * WithZero.exp (-2) := mul_le_mul' h.2.1 h'.1
        _ = WithZero.exp (-2) := one_mul _
    · rw [Valuation.map_mul]
      calc nu W L P hP (f - g) * nu W L P hP g' ≤ WithZero.exp (-2) * 1 := mul_le_mul' h.1 h'.2.2
        _ = WithZero.exp (-2) := mul_one _
  · rw [Valuation.map_mul]
    calc nu W L P hP f * nu W L P hP f' ≤ 1 * 1 := mul_le_mul' h.2.1 h'.2.1
      _ = 1 := one_mul _
  · rw [Valuation.map_mul]
    calc nu W L P hP g * nu W L P hP g' ≤ 1 * 1 := mul_le_mul' h.2.2 h'.2.2
      _ = 1 := one_mul _

lemma CongM2.pow (h : CongM2 P hP f g) (n : ℕ) : CongM2 P hP (f ^ n) (g ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact CongM2.refl (by rw [Valuation.map_one])
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

lemma CongM2.nu_eq_one (h : CongM2 P hP f g) (hg : nu W L P hP g = 1) : nu W L P hP f = 1 := by
  have hlt : nu W L P hP (f - g) < nu W L P hP g := by
    rw [hg]; exact lt_of_le_of_lt h.1 exp_neg_two_lt_one
  have := Valuation.map_add_eq_of_lt_left (nu W L P hP) hlt
  rwa [add_sub_cancel, hg] at this

lemma CongM2.inv (h : CongM2 P hP f g) (hf : nu W L P hP f = 1) (hg : nu W L P hP g = 1) :
    CongM2 P hP f⁻¹ g⁻¹ := by
  have hf0 : f ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hf]; exact one_ne_zero)
  have hg0 : g ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hg]; exact one_ne_zero)
  refine ⟨?_, by rw [map_inv₀, hf, inv_one], by rw [map_inv₀, hg, inv_one]⟩
  rw [inv_sub_inv hf0 hg0, map_div₀, Valuation.map_mul, hf, hg, mul_one, div_one,
    Valuation.map_sub_swap]
  exact h.1

lemma CongM2.div (h : CongM2 P hP f g) (h' : CongM2 P hP f' g') (hf' : nu W L P hP f' = 1)
    (hg' : nu W L P hP g' = 1) : CongM2 P hP (f / f') (g / g') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul (h'.inv hf' hg')

lemma CongM2.addX {x₁ x₂ l x₁' x₂' l' : FF W L} (h₁ : CongM2 P hP x₁ x₁') (h₂ : CongM2 P hP x₂ x₂')
    (hl : CongM2 P hP l l') :
    CongM2 P hP ((W.baseChange (FF W L)).toAffine.addX x₁ x₂ l)
      ((W.baseChange (FF W L)).toAffine.addX x₁' x₂' l') :=
  ((((hl.pow 2).add ((CongM2.refl (HV_a₁ (W := W) (L := L)).nu_le).mul hl)).sub
    (CongM2.refl (HV_a₂ (W := W) (L := L)).nu_le)).sub h₁).sub h₂

lemma CongM2.addY {x₁ x₂ y₁ l x₁' x₂' y₁' l' : FF W L} (h₁ : CongM2 P hP x₁ x₁')
    (h₂ : CongM2 P hP x₂ x₂') (hy : CongM2 P hP y₁ y₁') (hl : CongM2 P hP l l') :
    CongM2 P hP ((W.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ l)
      ((W.baseChange (FF W L)).toAffine.addY x₁' x₂' y₁' l') := by
  have h3 := CongM2.addX h₁ h₂ hl
  exact (((hl.mul (h3.sub h₁)).add hy).neg.sub
    ((CongM2.refl (HV_a₁ (W := W) (L := L)).nu_le).mul h3)).sub
    (CongM2.refl (HV_a₃ (W := W) (L := L)).nu_le)

/-- Two `L`-algebra maps `CR → F` congruent mod `m_P^2` on `x, y` are congruent everywhere. -/
lemma congM2_all (ψ₁ ψ₂ : CR W L →ₐ[L] FF W L)
    (hx : CongM2 P hP (ψ₁ (mk (W.baseChange L).toAffine (C X)))
      (ψ₂ (mk (W.baseChange L).toAffine (C X))))
    (hy : CongM2 P hP (ψ₁ (mk (W.baseChange L).toAffine Y)) (ψ₂ (mk (W.baseChange L).toAffine Y)))
    (r : CR W L) : CongM2 P hP (ψ₁ r) (ψ₂ r) := by
  have halg : ∀ b : L, CongM2 P hP (ψ₁ (algebraMap L (CR W L) b)) (ψ₂ (algebraMap L (CR W L) b)) := by
    intro b; rw [ψ₁.commutes, ψ₂.commutes]; exact CongM2.alg b
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · simp only [map_add]; exact hp.add hq
  · rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    refine CongM2.mul ?_ (hy.pow n)
    refine Polynomial.induction_on' a (fun p q hp hq => ?_) (fun m b => ?_)
    · simp only [map_add]; exact hp.add hq
    · rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow]
      exact (halg b).mul (hx.pow m)

end Cong

section OneSubFrob

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable (F L) in
lemma exists_not_fixed : ∃ u : L, u ^ Fintype.card F ≠ u := by
  by_contra! h
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  apply FiniteField.X_pow_card_sub_X_ne_zero (K' := L) hq
  apply Polynomial.zero_of_eval_zero
  intro x
  simp [h x]

/-- `f ≡ c` at `P` ⇒ `f^q ≡ c^q mod m_P^2`. -/
lemma congM2_frob {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c : L} (h : HV W L P hP f c) :
    CongM2 P hP (frobFF W L f) (algebraMap L (FF W L) (c ^ Fintype.card F)) := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  refine ⟨?_, ?_, nu_alg_le _⟩
  · have e1 : frobFF W L f - algebraMap L (FF W L) (c ^ Fintype.card F) =
        (f - algebraMap L (FF W L) c) ^ Fintype.card F := by
      rw [map_pow, ← frobFF_apply, ← frobFF_apply, ← map_sub]
    rw [e1, map_pow]
    exact pow_le_exp_neg_two h hq
  · rw [frobFF_apply, map_pow]
    exact pow_le_one' h.nu_le _

/-- **`1 - π` has a pullback with ramification index `1`.** -/
theorem exists_isPull_one_sub_frob :
    ∃ ψ : FF W L →ₐ[L] FF W L, IsPull ψ 1 (rsHom W L 1 (-1)) := by
  classical
  obtain ⟨u, hu⟩ := exists_not_fixed F L
  obtain ⟨v, hv, -⟩ := exists_pt_x W u
  have hP0 : (Point.some _ _ hv : Pt W L) ≠ 0 := Point.some_ne_zero hv
  have hnv : (W.baseChange L).toAffine.Nonsingular u ((W.baseChange L).toAffine.negY u v) :=
    (nonsingular_neg ..).mpr hv
  obtain ⟨hC, hCeq⟩ := RPLib.EllFq.frob_some W L hnv
  have hφP0 : rsHom W L 1 (-1) (Point.some _ _ hv) =
      Point.some _ _ hv + Point.some _ _ hC := by
    rw [rsHom_apply, one_smul, neg_one_smul, ← map_neg, Point.neg_some, hCeq]
  have hQ : (Point.some _ _ hv : Pt W L) + Point.some _ _ hC ≠ 0 := by
    rw [← hφP0, rsHom_apply, one_smul, neg_one_smul]
    intro h
    rw [add_neg_eq_zero] at h
    obtain ⟨h', h''⟩ := RPLib.EllFq.frob_some W L hv
    rw [h''] at h
    exact hu (Point.some.inj h).1.symm
  have hφ : rsHom W L 1 (-1) ≠ 0 := fun h0 => hQ (by rw [← hφP0, h0]; rfl)
  have h := ne_ιP_of_hE (PhiRS W L 1 (-1)) _ (hE_rs 1 (-1)) hφ
  -- the local data at `P0 = (u, v)`
  have hgx : HV W L _ hP0 (gx W L) u := HV_gx W L _ hP0
  have hgy : HV W L _ hP0 (gy W L) v := HV_gy W L _ hP0
  have hnY : HV W L _ hP0 ((W.baseChange (FF W L)).toAffine.negY (gx W L) (gy W L))
      ((W.baseChange L).toAffine.negY u v) :=
    ((hgy.neg).sub (HV_a₁.mul hgx)).sub HV_a₃
  have cX := congM2_frob hgx
  have cY := congM2_frob hnY
  have cgx : CongM2 _ hP0 (gx W L) (gx W L) := CongM2.refl hgx.nu_le
  have cgy : CongM2 _ hP0 (gy W L) (gy W L) := CongM2.refl hgy.nu_le
  have cden := cgx.sub cX
  have hden2 : nu W L _ hP0 (gx W L - algebraMap L (FF W L) (u ^ Fintype.card F)) = 1 :=
    (hgx.sub (HV_alg _)).nu_eq_one (sub_ne_zero.mpr (Ne.symm hu))
  have hden1 := cden.nu_eq_one hden2
  have hxne : gx W L ≠ frobFF W L (gx W L) := by
    intro h0; rw [← h0, sub_self, map_zero] at hden1; exact zero_ne_one hden1
  have hxne' := gx_ne W L (u ^ Fintype.card F)
  have cslope := (cgy.sub cY).div cden hden1 hden2
  have hΦ : PhiRS W L 1 (-1) = G W L + Point.map (W' := W.toAffine) (frobFF W L) (-G W L) := by
    rw [PhiRS, one_smul, neg_one_smul, piG, map_neg]
  have hpx : px (PhiRS W L 1 (-1)) = (W.baseChange (FF W L)).toAffine.addX (gx W L)
      (frobFF W L (gx W L)) ((gy W L - frobFF W L ((W.baseChange (FF W L)).toAffine.negY
        (gx W L) (gy W L))) / (gx W L - frobFF W L (gx W L))) := by
    rw [hΦ, G, Point.neg_some, Point.map_some, Point.add_of_X_ne hxne]
    exact congrArg ((W.baseChange (FF W L)).toAffine.addX (gx W L) (frobFF W L (gx W L)))
      (slope_of_X_ne hxne)
  have hpy : py (PhiRS W L 1 (-1)) = (W.baseChange (FF W L)).toAffine.addY (gx W L)
      (frobFF W L (gx W L)) (gy W L) ((gy W L - frobFF W L ((W.baseChange (FF W L)).toAffine.negY
        (gx W L) (gy W L))) / (gx W L - frobFF W L (gx W L))) := by
    rw [hΦ, G, Point.neg_some, Point.map_some, Point.add_of_X_ne hxne]
    exact congrArg ((W.baseChange (FF W L)).toAffine.addY (gx W L) (frobFF W L (gx W L)) (gy W L))
      (slope_of_X_ne hxne)
  have hqx := px_pS_some (W := W) (L := L) _ _ hC
  have hqy := py_pS_some W L _ _ hC
  rw [slope_of_X_ne hxne'] at hqx hqy
  have cPX : CongM2 _ hP0 (px (PhiRS W L 1 (-1))) (px (pS W L (Point.some _ _ hC))) := by
    rw [hpx, hqx]; exact CongM2.addX cgx cX cslope
  have cPY : CongM2 _ hP0 (py (PhiRS W L 1 (-1))) (py (pS W L (Point.some _ _ hC))) := by
    rw [hpy, hqy]; exact CongM2.addY cgx cX cgy cslope
  -- congruence on all of `CR`
  have hall := congM2_all (P := Point.some _ _ hv) (hP := hP0)
    ((pull W L _ h).comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)))
    ((tauHom W L (Point.some _ _ hC)).comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)))
    (by
      show CongM2 _ hP0 (pull W L _ h (gx W L)) (tauHom W L _ (gx W L))
      rw [pull_gx, tauHom_gx]; exact cPX)
    (by
      show CongM2 _ hP0 (pull W L _ h (gy W L)) (tauHom W L _ (gy W L))
      rw [pull_gy, tauHom_gy]; exact cPY)
  -- a uniformizer at `Q = P0 + C`
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer
    (hosP W L _ hQ)
  have hνf : nu W L _ hQ (algebraMap (CR W L) (FF W L) t) = WithZero.exp (-1) := by
    rw [nu_eq_valuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hf0 : algebraMap (CR W L) (FF W L) t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hνf; exact WithZero.exp_ne_zero hνf.symm
  have hτ : nu W L _ hP0 (tau W L (Point.some _ _ hC) (algebraMap (CR W L) (FF W L) t)) =
      WithZero.exp (-1) := by
    have h1 := ord_tau (Point.some _ _ hC) (algebraMap (CR W L) (FF W L) t) (Point.some _ _ hv)
    rw [ord_eq hP0, ord_eq hQ, hνf, WithZero.log_exp, neg_inj] at h1
    have hne : nu W L _ hP0 (tau W L (Point.some _ _ hC) (algebraMap (CR W L) (FF W L) t)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hf0)
    rw [← WithZero.exp_log hne, h1]
  have hc := hall t
  change CongM2 _ hP0 (pull W L _ h (algebraMap (CR W L) (FF W L) t))
    (tauHom W L _ (algebraMap (CR W L) (FF W L) t)) at hc
  rw [← tau_apply] at hc
  have hpull : nu W L _ hP0 (pull W L _ h (algebraMap (CR W L) (FF W L) t)) = WithZero.exp (-1) := by
    have hlt : nu W L _ hP0 (pull W L _ h (algebraMap (CR W L) (FF W L) t) -
        tau W L (Point.some _ _ hC) (algebraMap (CR W L) (FF W L) t)) <
        nu W L _ hP0 (tau W L (Point.some _ _ hC) (algebraMap (CR W L) (FF W L) t)) := by
      rw [hτ]
      exact lt_of_le_of_lt hc.1 (WithZero.exp_lt_exp.mpr (by norm_num))
    have := Valuation.map_add_eq_of_lt_left (nu W L _ hP0) hlt
    rwa [add_sub_cancel, hτ] at this
  have hord : ord W L (pull W L _ h (algebraMap (CR W L) (FF W L) t)) (Point.some _ _ hv) = 1 := by
    rw [ord_eq hP0, hpull, WithZero.log_exp]; norm_num
  exact exists_isPull_one _ h _ (hE_rs 1 (-1)) hf0 hord

/-- **`deg (1 - π) = N = #W(F)`**. -/
theorem deg_one_sub_frob : deg (rsHom W L 1 (-1)) = RPLib.EllFq.numPoints W := by
  obtain ⟨ψ, hP⟩ := exists_isPull_one_sub_frob (W := W) (L := L)
  rw [hP.deg_eq, one_mul, card_ker_one_sub_frob hP]

end OneSubFrob

end RPLib.Isog


