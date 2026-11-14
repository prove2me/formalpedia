-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingC
-- name    : RPLib_S2_WeilPairingC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:52:58.099009+00:00
-- url     : https://prove2.me/theorems/62b6b588-7fca-4bd8-bcbb-4fb29c3aea6b
-- title:
--   Weil pairing, part C: valuations at points under translation
-- statement:
--   The valuation $\nu_P$ of the function field at an affine point $P$, and the transport rule $\nu_Q(\tau_S f) = \nu_{Q+S}(f)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section II.1

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingB

/-!
# WPC: valuations at affine points and their transport under translations (unit S2-WeilPairing, O5)

`nu P` is the valuation of the function field `F` of `W⁄L` at an affine point `P`.
Main result `nu_tau`: `ν_Q (τ_S f) = ν_{Q+S} f` whenever `Q` and `Q + S` are affine.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Weil

section Transport

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
  (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L]

instance isDedekindDomain_CR : IsDedekindDomain (CR W L) := isDedekindDomain (W.baseChange L)

variable [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- Points of `W⁄L`. -/
abbrev Pt := (W.baseChange L).toAffine.Point

/-- The valuation of the function field at an affine point. -/
noncomputable def nu (P : Pt W L) (hP : P ≠ 0) : Valuation (FF W L) (WithZero (Multiplicative ℤ)) :=
  (hos (W.baseChange L) (nonsingular_px_py hP)).valuation (FF W L)

/-- `f ≡ c` at `P`. -/
def HV (P : Pt W L) (hP : P ≠ 0) (f : FF W L) (c : L) : Prop :=
  nu W L P hP (f - algebraMap L (FF W L) c) < 1

variable {W L}

lemma nu_congr {P P' : Pt W L} (h : P = P') (hP : P ≠ 0) (hP' : P' ≠ 0) :
    nu W L P hP = nu W L P' hP' := by
  subst h; rfl

section HVcalc

variable {P : Pt W L} {hP : P ≠ 0} {f g : FF W L} {c d : L}

lemma nu_alg_le (a : L) : nu W L P hP (algebraMap L (FF W L) a) ≤ 1 := by
  rw [nu, ← alg_mk_CC]
  apply IsDedekindDomain.HeightOneSpectrum.valuation_le_one

lemma nu_alg_eq_one {a : L} (ha : a ≠ 0) : nu W L P hP (algebraMap L (FF W L) a) = 1 := by
  rw [nu, ← alg_mk_CC, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  exact (hos (W.baseChange L) (nonsingular_px_py hP)).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit ha).map (algebraMap L (CR W L))))

lemma nu_mul_le {x y : FF W L} (hy : nu W L P hP y ≤ 1) : nu W L P hP (x * y) ≤ nu W L P hP x := by
  rw [map_mul]; exact mul_le_of_le_one_right' hy

lemma HV.nu_le (h : HV W L P hP f c) : nu W L P hP f ≤ 1 := by
  have e : f = (f - algebraMap L (FF W L) c) + algebraMap L (FF W L) c := by ring
  rw [e]
  exact Valuation.map_add_le _ h.le (nu_alg_le c)

lemma HV_alg (a : L) : HV W L P hP (algebraMap L (FF W L) a) a := by
  simp [HV]

lemma HV.congr (h : HV W L P hP f c) (hfg : f = g) (hcd : c = d) : HV W L P hP g d :=
  hfg ▸ hcd ▸ h

lemma HV.add (hf : HV W L P hP f c) (hg : HV W L P hP g d) : HV W L P hP (f + g) (c + d) := by
  unfold HV at *
  rw [map_add, show f + g - (algebraMap L (FF W L) c + algebraMap L (FF W L) d) =
    (f - algebraMap L (FF W L) c) + (g - algebraMap L (FF W L) d) by ring]
  exact Valuation.map_add_lt _ hf hg

lemma HV.neg (hf : HV W L P hP f c) : HV W L P hP (-f) (-c) := by
  unfold HV at *
  rw [map_neg, show -f - -algebraMap L (FF W L) c = -(f - algebraMap L (FF W L) c) by ring,
    Valuation.map_neg]
  exact hf

lemma HV.sub (hf : HV W L P hP f c) (hg : HV W L P hP g d) : HV W L P hP (f - g) (c - d) := by
  have := hf.add hg.neg
  rwa [← sub_eq_add_neg, ← sub_eq_add_neg] at this

lemma HV.mul (hf : HV W L P hP f c) (hg : HV W L P hP g d) : HV W L P hP (f * g) (c * d) := by
  have h1 := hg.nu_le
  have e : f * g - algebraMap L (FF W L) (c * d) =
      (f - algebraMap L (FF W L) c) * g + algebraMap L (FF W L) c * (g - algebraMap L (FF W L) d) := by
    rw [map_mul]; ring
  unfold HV at hf hg ⊢
  rw [e]
  refine Valuation.map_add_lt _ (lt_of_le_of_lt (nu_mul_le h1) hf) ?_
  rw [mul_comm]
  exact lt_of_le_of_lt (nu_mul_le (nu_alg_le c)) hg

lemma HV.pow (hf : HV W L P hP f c) (n : ℕ) : HV W L P hP (f ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (HV_alg (P := P) (hP := hP) (1 : L))
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hf

lemma HV.nu_eq_one (hf : HV W L P hP f c) (hc : c ≠ 0) : nu W L P hP f = 1 := by
  have e : f = algebraMap L (FF W L) c + (f - algebraMap L (FF W L) c) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left, nu_alg_eq_one hc]
  rw [nu_alg_eq_one hc]; exact hf

lemma HV.ne_zero (hf : HV W L P hP f c) (hc : c ≠ 0) : f ≠ 0 := by
  intro h0
  have := hf.nu_eq_one hc
  rw [h0, map_zero] at this
  exact zero_ne_one this

lemma HV.inv (hf : HV W L P hP f c) (hc : c ≠ 0) : HV W L P hP f⁻¹ c⁻¹ := by
  have hf0 := hf.ne_zero hc
  have hc0 : algebraMap L (FF W L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have e : f⁻¹ - algebraMap L (FF W L) c⁻¹ =
      (algebraMap L (FF W L) c - f) * (f⁻¹ * (algebraMap L (FF W L) c)⁻¹) := by
    rw [map_inv₀]; field_simp <;> ring
  have h1 := hf.nu_eq_one hc
  unfold HV at hf ⊢
  rw [e, map_mul, map_mul, map_inv₀, map_inv₀, h1, nu_alg_eq_one hc, Valuation.map_sub_swap]
  simpa using hf

lemma HV.div (hf : HV W L P hP f c) (hg : HV W L P hP g d) (hd : d ≠ 0) :
    HV W L P hP (f / g) (c / d) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact hf.mul (hg.inv hd)

lemma HV_a₁ : HV W L P hP (W.baseChange (FF W L)).toAffine.a₁ (W.baseChange L).toAffine.a₁ := by
  rw [bc_a₁ W L (FF W L)]; exact HV_alg _
lemma HV_a₂ : HV W L P hP (W.baseChange (FF W L)).toAffine.a₂ (W.baseChange L).toAffine.a₂ := by
  rw [bc_a₂ W L (FF W L)]; exact HV_alg _
lemma HV_a₃ : HV W L P hP (W.baseChange (FF W L)).toAffine.a₃ (W.baseChange L).toAffine.a₃ := by
  rw [bc_a₃ W L (FF W L)]; exact HV_alg _
lemma HV_a₄ : HV W L P hP (W.baseChange (FF W L)).toAffine.a₄ (W.baseChange L).toAffine.a₄ := by
  rw [bc_a₄ W L (FF W L)]; exact HV_alg _

lemma HV_addX {x ℓ : FF W L} {cx m : L} (s : L) (hx : HV W L P hP x cx) (hl : HV W L P hP ℓ m) :
    HV W L P hP ((W.baseChange (FF W L)).toAffine.addX x (algebraMap L (FF W L) s) ℓ)
      ((W.baseChange L).toAffine.addX cx s m) := by
  simp only [WeierstrassCurve.Affine.addX]
  exact ((((hl.pow 2).add (HV_a₁.mul hl)).sub HV_a₂).sub hx).sub (HV_alg s)

lemma HV_addY {x y ℓ : FF W L} {cx cy m : L} (s : L) (hx : HV W L P hP x cx)
    (hy : HV W L P hP y cy) (hl : HV W L P hP ℓ m) :
    HV W L P hP ((W.baseChange (FF W L)).toAffine.addY x (algebraMap L (FF W L) s) y ℓ)
      ((W.baseChange L).toAffine.addY cx s cy m) := by
  have hX := HV_addX s hx hl
  have hNA : HV W L P hP ((W.baseChange (FF W L)).toAffine.negAddY x (algebraMap L (FF W L) s) y ℓ)
      ((W.baseChange L).toAffine.negAddY cx s cy m) := by
    simp only [WeierstrassCurve.Affine.negAddY]
    exact (hl.mul (hX.sub hx)).add hy
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]
  exact (hNA.neg.sub (HV_a₁.mul hX)).sub HV_a₃

end HVcalc

variable (W L) in
lemma HV_gx (Q : Pt W L) (hQ : Q ≠ 0) : HV W L Q hQ (gx W L) (px Q) := by
  unfold HV
  rw [nu, gx, ← alg_mk_CC, ← map_sub, ← map_sub, ← C_sub,
    IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact XClass_mem_XYIdeal _ _ _

variable (W L) in
lemma HV_gy (Q : Pt W L) (hQ : Q ≠ 0) : HV W L Q hQ (gy W L) (py Q) := by
  unfold HV
  rw [nu, gy, ← alg_mk_CC, ← map_sub, ← map_sub,
    IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact YClass_mem_XYIdeal _ _ _

omit [W.IsElliptic] [IsAlgClosed L] [DecidableEq L] in
variable (W L) in
lemma equation_alg {q1 q2 : L} (hq : (W.baseChange L).toAffine.Equation q1 q2) :
    (W.baseChange (FF W L)).toAffine.Equation (algebraMap L (FF W L) q1) (algebraMap L (FF W L) q2) :=
  (W.toAffine.baseChange_equation (f := ιF W L) (ιF W L).toRingHom.injective q1 q2).mpr hq

variable (W L) in
/-- The `x`-coordinate of `P_S` for affine `S`. -/
lemma px_pS_some (s1 s2 : L) (hs : (W.baseChange L).toAffine.Nonsingular s1 s2) :
    px (pS W L (.some s1 s2 hs)) = (W.baseChange (FF W L)).toAffine.addX (gx W L)
      (algebraMap L (FF W L) s1) ((W.baseChange (FF W L)).toAffine.slope (gx W L)
        (algebraMap L (FF W L) s1) (gy W L) (algebraMap L (FF W L) s2)) := by
  have hs' : (W.baseChange (FF W L)).toAffine.Nonsingular (algebraMap L (FF W L) s1)
      (algebraMap L (FF W L) s2) :=
    (W.toAffine.baseChange_nonsingular (f := ιF W L) (ιF W L).toRingHom.injective s1 s2).mpr hs
  have h := Point.add_of_X_ne (h₁ := gen_nonsingular W L) (h₂ := hs') (gx_ne W L s1)
  exact congrArg px h

variable (W L) in
lemma py_pS_some (s1 s2 : L) (hs : (W.baseChange L).toAffine.Nonsingular s1 s2) :
    py (pS W L (.some s1 s2 hs)) = (W.baseChange (FF W L)).toAffine.addY (gx W L)
      (algebraMap L (FF W L) s1) (gy W L) ((W.baseChange (FF W L)).toAffine.slope (gx W L)
        (algebraMap L (FF W L) s1) (gy W L) (algebraMap L (FF W L) s2)) := by
  have hs' : (W.baseChange (FF W L)).toAffine.Nonsingular (algebraMap L (FF W L) s1)
      (algebraMap L (FF W L) s2) :=
    (W.toAffine.baseChange_nonsingular (f := ιF W L) (ιF W L).toRingHom.injective s1 s2).mpr hs
  have h := Point.add_of_X_ne (h₁ := gen_nonsingular W L) (h₂ := hs') (gx_ne W L s1)
  exact congrArg py h

/-- The generic slope specialises to the slope of `Q` and `S` at `Q`. -/
lemma HV_slope {q1 q2 s1 s2 : L} (hq : (W.baseChange L).toAffine.Nonsingular q1 q2)
    (hs : (W.baseChange L).toAffine.Nonsingular s1 s2) (hQ : (Point.some q1 q2 hq : Pt W L) ≠ 0)
    (hxy : ¬(q1 = s1 ∧ q2 = (W.baseChange L).toAffine.negY s1 s2)) :
    HV W L (.some q1 q2 hq) hQ ((W.baseChange (FF W L)).toAffine.slope (gx W L)
        (algebraMap L (FF W L) s1) (gy W L) (algebraMap L (FF W L) s2))
      ((W.baseChange L).toAffine.slope q1 s1 q2 s2) := by
  have hgx : HV W L _ hQ (gx W L) q1 := HV_gx W L _ hQ
  have hgy : HV W L _ hQ (gy W L) q2 := HV_gy W L _ hQ
  rw [slope_of_X_ne (gx_ne W L s1)]
  by_cases hx : q1 = s1
  · have hy : q2 ≠ (W.baseChange L).toAffine.negY s1 s2 := fun h => hxy ⟨hx, h⟩
    have hq2 : q2 = s2 := Y_eq_of_Y_ne hq.1 hs.1 hx hy
    rw [← hx, ← hq2] at hy ⊢
    rw [slope_of_Y_ne rfl hy]
    have hN := (((((hgx.pow 2).add (hgx.mul (HV_alg q1))).add ((HV_alg q1).pow 2)).add
      (HV_a₂.mul (hgx.add (HV_alg q1)))).add HV_a₄).sub (HV_a₁.mul (HV_alg q2))
    have hD := ((hgy.add (HV_alg q2)).add (HV_a₁.mul hgx)).add HV_a₃
    have hd0 : q2 + q2 + (W.baseChange L).toAffine.a₁ * q1 + (W.baseChange L).toAffine.a₃ ≠ 0 := by
      intro h; apply hy; simp only [WeierstrassCurve.Affine.negY]; linear_combination h
    have hD0 := hD.ne_zero hd0
    have hX0 : gx W L - algebraMap L (FF W L) q1 ≠ 0 := sub_ne_zero.mpr (gx_ne W L q1)
    have e1 := (equation_iff _ _).mp (gen_equation W L)
    have e2 := (equation_iff _ _).mp (equation_alg W L hq.1)
    refine (hN.div hD hd0).congr ?_ ?_
    · rw [div_eq_div_iff hD0 hX0]; linear_combination e2 - e1
    · simp only [WeierstrassCurve.Affine.negY]
      congr 1 <;> ring
  · rw [slope_of_X_ne hx]
    exact (hgy.sub (HV_alg s2)).div (hgx.sub (HV_alg s1)) (sub_ne_zero.mpr hx)

/-- The coordinates of `P_S` specialise to those of `Q + S` at `Q`. -/
lemma HV_pS (Q S : Pt W L) (hQ : Q ≠ 0) (hS : S ≠ 0) (hQS : Q + S ≠ 0) :
    HV W L Q hQ (px (pS W L S)) (px (Q + S)) ∧ HV W L Q hQ (py (pS W L S)) (py (Q + S)) := by
  cases Q with
  | zero => exact absurd rfl hQ
  | some q1 q2 hq =>
  cases S with
  | zero => exact absurd rfl hS
  | some s1 s2 hs =>
  have hxy : ¬(q1 = s1 ∧ q2 = (W.baseChange L).toAffine.negY s1 s2) :=
    fun h => hQS (Point.add_of_Y_eq h.1 h.2)
  have hgx : HV W L _ hQ (gx W L) q1 := HV_gx W L _ hQ
  have hgy : HV W L _ hQ (gy W L) q2 := HV_gy W L _ hQ
  have hl := HV_slope hq hs hQ hxy
  rw [px_pS_some, py_pS_some, Point.add_some hxy]
  exact ⟨HV_addX s1 hgx hl, HV_addY s1 hgx hgy hl⟩

section Good

variable (Q S : Pt W L) (hQ : Q ≠ 0) (hT : Q + S ≠ 0)

variable (W L) in
/-- `r` has a value `c` at `Q + S`, and `φ_S r ≡ c` at `Q`. -/
def Good (r : CR W L) : Prop :=
  ∃ c : L, r - algebraMap L (CR W L) c ∈ (hos (W.baseChange L) (nonsingular_px_py hT)).asIdeal ∧
    HV W L Q hQ (phi W L S r) c

variable {Q S hQ hT}

lemma Good_add {r s : CR W L} (hr : Good W L Q S hQ hT r) (hs : Good W L Q S hQ hT s) :
    Good W L Q S hQ hT (r + s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c + d, ?_, ?_⟩
  · rw [map_add, show r + s - (algebraMap L (CR W L) c + algebraMap L (CR W L) d) =
      (r - algebraMap L (CR W L) c) + (s - algebraMap L (CR W L) d) by ring]
    exact Ideal.add_mem _ hc hd
  · rw [map_add]; exact hc'.add hd'

lemma Good_mul {r s : CR W L} (hr : Good W L Q S hQ hT r) (hs : Good W L Q S hQ hT s) :
    Good W L Q S hQ hT (r * s) := by
  obtain ⟨c, hc, hc'⟩ := hr
  obtain ⟨d, hd, hd'⟩ := hs
  refine ⟨c * d, ?_, ?_⟩
  · rw [map_mul, show r * s - algebraMap L (CR W L) c * algebraMap L (CR W L) d =
      (r - algebraMap L (CR W L) c) * s + algebraMap L (CR W L) c * (s - algebraMap L (CR W L) d) by
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_left _ _ hd)
  · rw [map_mul]; exact hc'.mul hd'

lemma Good_alg (a : L) : Good W L Q S hQ hT (algebraMap L (CR W L) a) :=
  ⟨a, by rw [sub_self]; exact Ideal.zero_mem _, by rw [AlgHom.commutes]; exact HV_alg a⟩

lemma Good_pow {r : CR W L} (hr : Good W L Q S hQ hT r) (n : ℕ) : Good W L Q S hQ hT (r ^ n) := by
  induction n with
  | zero => rw [pow_zero, ← map_one (algebraMap L (CR W L))]; exact Good_alg 1
  | succ n ih => rw [pow_succ]; exact Good_mul ih hr

lemma phi_mkX (S : Pt W L) : phi W L S (mk (W.baseChange L).toAffine (C X)) = px (pS W L S) := by
  have := tauHom_gx W L S
  rwa [gx, tauHom_algebraMap] at this

lemma phi_mkY (S : Pt W L) : phi W L S (mk (W.baseChange L).toAffine Y) = py (pS W L S) := by
  have := tauHom_gy W L S
  rwa [gy, tauHom_algebraMap] at this

lemma Good_X (hS : S ≠ 0) : Good W L Q S hQ hT (mk (W.baseChange L).toAffine (C X)) := by
  refine ⟨px (Q + S), ?_, ?_⟩
  · rw [algebraMap_Rg, ← map_sub, ← C_sub]
    exact XClass_mem_XYIdeal _ _ _
  · rw [phi_mkX]; exact (HV_pS Q S hQ hS hT).1

lemma Good_Y (hS : S ≠ 0) : Good W L Q S hQ hT (mk (W.baseChange L).toAffine Y) := by
  refine ⟨py (Q + S), ?_, ?_⟩
  · rw [algebraMap_Rg, ← map_sub]
    exact YClass_mem_XYIdeal _ _ _
  · rw [phi_mkY]; exact (HV_pS Q S hQ hS hT).2

lemma Good_all (hS : S ≠ 0) (r : CR W L) : Good W L Q S hQ hT r := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add]; exact Good_add hp hq
  · rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine Good_mul ?_ (Good_pow (Good_Y hS) n)
    refine Polynomial.induction_on' a (fun p q hp hq => ?_) (fun m b => ?_)
    · rw [map_add, map_add]; exact Good_add hp hq
    · rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      exact Good_mul (Good_alg b) (Good_pow (Good_X hS) m)

end Good

lemma nu_tau_le_one (Q S : Pt W L) (hQ : Q ≠ 0) (hT : Q + S ≠ 0) (f : FF W L)
    (hf : nu W L (Q + S) hT f ≤ 1) : nu W L Q hQ (tau W L S f) ≤ 1 := by
  by_cases hS : S = 0
  · subst hS
    rw [tau_zero_apply]
    rwa [nu_congr (add_zero Q) hT hQ] at hf
  rw [nu] at hf
  obtain ⟨a, b, hb, hab⟩ := (valuation_le_one_iff_exists _ f).mp hf
  obtain ⟨cb, hcb, hb'⟩ := Good_all (hQ := hQ) (hT := hT) hS b
  obtain ⟨ca, -, ha'⟩ := Good_all (hQ := hQ) (hT := hT) hS a
  have hcb0 : cb ≠ 0 := by
    rintro rfl; apply hb; simpa using hcb
  have e := congrArg (tau W L S) hab
  simp only [map_mul, tau_apply, tauHom_algebraMap] at e
  calc nu W L Q hQ (tau W L S f)
      = nu W L Q hQ (tau W L S f) * nu W L Q hQ (phi W L S b) := by
        rw [hb'.nu_eq_one hcb0, mul_one]
    _ = nu W L Q hQ (phi W L S a) := by rw [← map_mul, tau_apply, e]
    _ ≤ 1 := ha'.nu_le

/-- **Transport of valuations**: `ν_Q (τ_S f) = ν_{Q+S} f`. -/
theorem nu_tau (Q S : Pt W L) (hQ : Q ≠ 0) (hT : Q + S ≠ 0) (f : FF W L) :
    nu W L Q hQ (tau W L S f) = nu W L (Q + S) hT f := by
  have hT' : Q + S + -S ≠ 0 := by rwa [add_neg_cancel_right]
  obtain ⟨π₁, hπ₁⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
    (K := FF W L) (v := hos (W.baseChange L) (nonsingular_px_py hQ))
  obtain ⟨π₂, hπ₂⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer
    (K := FF W L) (v := hos (W.baseChange L) (nonsingular_px_py hT))
  have key : (nu W L Q hQ).comap (tau W L S).toAlgHom.toRingHom = nu W L (Q + S) hT := by
    refine valuation_eq_of_le_one_iff _ _ (fun g => ?_) (t₁ := tau W L (-S) π₁) (t₂ := π₂) ?_ hπ₂
    · rw [Valuation.comap_apply]
      show nu W L Q hQ (tau W L S g) ≤ 1 ↔ _
      constructor
      · intro hg
        have := nu_tau_le_one (Q + S) (-S) hT hT' (tau W L S g)
          (by rwa [nu_congr (add_neg_cancel_right Q S) hT' hQ])
        rwa [← tau_add_apply, neg_add_cancel, tau_zero_apply] at this
      · exact nu_tau_le_one Q S hQ hT g
    · rw [Valuation.comap_apply]
      show nu W L Q hQ (tau W L S (tau W L (-S) π₁)) = _
      rw [← tau_add_apply, add_neg_cancel, tau_zero_apply]
      exact hπ₁
  have := DFunLike.congr_fun key f
  rw [Valuation.comap_apply] at this
  exact this

end Transport

end RPLib.Weil


