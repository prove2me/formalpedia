-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegF
-- name    : RPLib_S2_IsogenyDegF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:23:06.482242+00:00
-- url     : https://prove2.me/theorems/4377dcb9-0a73-45a2-85e2-9a690ef48fde
-- title:
--   Degrees of $r + s\pi$, part F: separability when $p \nmid r$
-- statement:
--   For $p \nmid r$ the endomorphism $r + s\pi$ is nonzero and separable, so $\deg(r + s\pi) = \#\ker(r + s\pi)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Corollary III.5.5

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegE

/-!
# S2-IsogenyDeg part F: `r + s π` is separable when `p ∤ r`

* `torsLin_rs` : `r + s π` on `E[n]` is `r • 1 + s • π`; `det_torsLin_r` : `det [r] = r²`.
* `rsHom_ne_zero` : `r + s π ≠ 0` when `(r : L) ≠ 0`.
* `IsPull.e_eq_one_r` : `[r]` is separable (`e = 1`) when `p ∤ r` (`e * #E[r] = r² = #E[r]`).
* **`exists_isPull_rs_sep`** : for `p ∤ r`, `r + s π` has a pullback with `e = 1`: near a generic point
  `P0`, `r G + π(s G) ≡ r G + C mod m_{P0}^2` (`C` constant), and `r G + C` represents `τ ∘ [r]`.
* **`deg_rs_eq_card_ker`** : `deg (r + s π) = #ker (r + s π)` when `p ∤ r`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

section Sep

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

/-! ### `r + s π` on `E[n]` -/

lemma torsLin_rs (r s : ℤ) (n : ℕ) [NeZero n] :
    torsLin (rsHom W L r s) n =
      (r : ZMod n) • LinearMap.id + (s : ZMod n) • frobTors W L n := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  rw [torsLin_apply, rsHom_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Int.cast_smul_eq_zsmul (ZMod n), Int.cast_smul_eq_zsmul (ZMod n),
    AddSubgroup.coe_add, AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, frobTors_apply]

lemma det_smul_tors (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) (c : ZMod n)
    (f : RPLib.Torsion.tors (W.baseChange L) n →ₗ[ZMod n] RPLib.Torsion.tors (W.baseChange L) n) :
    LinearMap.det (c • f) = c ^ 2 * LinearMap.det f := by
  obtain ⟨eqv⟩ := RPLib.Torsion.tors_equiv (W := W.baseChange L) n hn
  let eL := eqv.toLinearEquiv (ZMod.map_smul (n := n) eqv)
  let b := (Module.Basis.finTwoProd (ZMod n)).map eL.symm
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b f, map_smul, Matrix.det_smul,
    Fintype.card_fin]

lemma det_torsLin_r (r : ℤ) (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin (rsHom W L r 0) n) = (r : ZMod n) ^ 2 := by
  rw [torsLin_rs, Int.cast_zero, zero_smul, add_zero, det_smul_tors n hn, LinearMap.det_id, mul_one]

lemma natAbs_sq_cast {R : Type*} [CommRing R] (r : ℤ) : ((r.natAbs ^ 2 : ℕ) : R) = (r : R) ^ 2 := by
  have := congrArg (Int.cast : ℤ → R) (Int.natAbs_sq r)
  simp only [Int.cast_pow, Int.cast_natCast] at this
  rw [Nat.cast_pow]
  exact this

lemma natAbs_sq_eq_of_rsHom_eq_zero {r s : ℤ} (h : rsHom W L r s = 0) :
    r.natAbs ^ 2 = s.natAbs ^ 2 * Fintype.card F := by
  refine nat_eq_of_zmod L fun n _ hn => ?_
  have h1 : torsLin (rsHom W L r s) n = 0 := by
    rw [h]; exact LinearMap.ext fun P => Subtype.ext (by rw [torsLin_apply]; rfl)
  rw [torsLin_rs, add_eq_zero_iff_eq_neg] at h1
  have h2 := congrArg LinearMap.det h1
  rw [det_smul_tors n hn, LinearMap.det_id, mul_one, ← neg_smul, det_smul_tors n hn,
    det_frobTors W L n hn, neg_sq] at h2
  rw [Nat.cast_mul, natAbs_sq_cast, natAbs_sq_cast, h2]

lemma natAbs_ne_zero_of_cast {r : ℤ} (hr : (r : L) ≠ 0) : (r.natAbs : L) ≠ 0 := by
  rcases Int.natAbs_eq r with h | h
  · rw [h, Int.cast_natCast] at hr; exact hr
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_ne_zero] at hr; exact hr

omit [IsAlgClosed L] [DecidableEq L] in
lemma card_cast_L : ((Fintype.card F : ℕ) : L) = 0 := by
  rw [← map_natCast (algebraMap F L), FiniteField.cast_card_eq_zero, map_zero]

/-- **`r + s π ≠ 0` when `p ∤ r`.** -/
theorem rsHom_ne_zero (r s : ℤ) (hr : (r : L) ≠ 0) : rsHom W L r s ≠ 0 := by
  intro h
  have h2 := congrArg (Nat.cast : ℕ → L) (natAbs_sq_eq_of_rsHom_eq_zero h)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, card_cast_L, mul_zero] at h2
  exact natAbs_ne_zero_of_cast hr ((pow_eq_zero_iff two_ne_zero).mp h2)

/-- `[s] ≠ 0` for `s ≠ 0` (any characteristic). -/
theorem rsHom_r0_ne_zero {s : ℤ} (hs : s ≠ 0) : rsHom W L s 0 ≠ 0 := by
  intro h
  have h1 := natAbs_sq_eq_of_rsHom_eq_zero h
  rw [Int.natAbs_zero, zero_pow two_ne_zero, zero_mul, pow_eq_zero_iff two_ne_zero,
    Int.natAbs_eq_zero] at h1
  exact hs h1

/-- **`[r]` is separable when `p ∤ r`**: `e * #E[r] = deg [r] = r² = #E[r]`. -/
theorem IsPull.e_eq_one_r {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {r : ℤ}
    (hP : IsPull ψ e (rsHom W L r 0)) (hr : (r : L) ≠ 0) : e = 1 := by
  classical
  have hm := natAbs_ne_zero_of_cast hr
  have hcard : hP.finite_ker.toFinset.card = r.natAbs ^ 2 := by
    rw [← Nat.card_eq_card_finite_toFinset hP.finite_ker,
      ← RPLib.Torsion.card_tors (W := W.baseChange L) r.natAbs hm]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
    rw [Set.mem_ofPred_eq, rsHom_apply, zero_zsmul, add_zero, RPLib.Torsion.mem_tors,
      natAbs_nsmul_eq_zero]
  have key : e * r.natAbs ^ 2 = 1 * r.natAbs ^ 2 := by
    refine nat_eq_of_zmod L fun n _ hn => ?_
    have h1 := hP.det_eq n hn
    rw [hcard, det_torsLin_r r n hn] at h1
    rw [one_mul, ← h1, natAbs_sq_cast]
  have hpos : 0 < r.natAbs ^ 2 := by
    have : r.natAbs ≠ 0 := fun h0 => hm (by rw [h0, Nat.cast_zero])
    positivity
  exact Nat.eq_of_mul_eq_mul_right hpos key

/-! ### Generic points and the chord formula over the function field -/

lemma exists_generic3 {f₁ f₂ f₃ : FF W L} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) (h₃ : f₃ ≠ 0) :
    ∃ (P : Pt W L) (hP : P ≠ 0),
      nu W L P hP f₁ = 1 ∧ nu W L P hP f₂ = 1 ∧ nu W L P hP f₃ = 1 := by
  let g : L → Pt W L := fun a => Point.some _ _
    (equation_iff_nonsingular.mp (exists_y_alg (W.baseChange L) a).choose_spec)
  have hg : Function.Injective g := fun a b hab => (Point.some.inj hab).1
  obtain ⟨P, ⟨a, rfl⟩, hP⟩ := (Set.infinite_range_of_injective hg).exists_notMem_finite
    (((ord_finite h₁).union (ord_finite h₂)).union (ord_finite h₃))
  simp only [Set.mem_union, not_or, Function.mem_support, not_not] at hP
  exact ⟨g a, Point.some_ne_zero _, nu_eq_one_of_ord _ h₁ hP.1.1, nu_eq_one_of_ord _ h₂ hP.1.2,
    nu_eq_one_of_ord _ h₃ hP.2⟩

lemma px_add_of_px_ne {P Q : (W.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : px P ≠ px Q) :
    px (P + Q) = (W.baseChange (FF W L)).toAffine.addX (px P) (px Q)
      ((py P - py Q) / (px P - px Q)) := by
  have e := Point.add_of_X_ne (h₁ := nonsingular_px_py hP) (h₂ := nonsingular_px_py hQ) h
  rw [← eq_some_px_py hP, ← eq_some_px_py hQ] at e
  rw [e, ← slope_of_X_ne h]
  rfl

lemma py_add_of_px_ne {P Q : (W.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : px P ≠ px Q) :
    py (P + Q) = (W.baseChange (FF W L)).toAffine.addY (px P) (px Q) (py P)
      ((py P - py Q) / (px P - px Q)) := by
  have e := Point.add_of_X_ne (h₁ := nonsingular_px_py hP) (h₂ := nonsingular_px_py hQ) h
  rw [← eq_some_px_py hP, ← eq_some_px_py hQ] at e
  rw [e, ← slope_of_X_ne h]
  rfl

lemma px_neg' (P : (W.baseChange (FF W L)).toAffine.Point) : px (-P) = px P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

lemma py_neg' {P : (W.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) :
    py (-P) = (W.baseChange (FF W L)).toAffine.negY (px P) (py P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

/-! ### The main congruence argument -/

/-- If `Φ = A + π(Bs)` with `A` representing `τ ∘ [r]` (`p ∤ r`), then `e(Φ) = 1`. -/
theorem exists_isPull_one_of_split {r : ℤ} (hr : (r : L) ≠ 0) (φ : Pt W L →+ Pt W L)
    (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) Φ =
      Φ + ιP W L (φ S))
    (A Bs : (W.baseChange (FF W L)).toAffine.Point)
    (hEA : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) A =
      A + ιP W L (rsHom W L r 0 S))
    (hA : ∀ C, A ≠ ιP W L C) (hBs : ∀ C, Bs ≠ ιP W L C)
    (hAB : A - Point.map (W' := W.toAffine) (frobFF W L) Bs ≠ 0)
    (hΦ : Φ = A + Point.map (W' := W.toAffine) (frobFF W L) Bs) :
    ∃ ψ : FF W L →ₐ[L] FF W L, IsPull ψ 1 φ := by
  classical
  have hΦ0 : Φ ≠ 0 := by have := h 0; rwa [map_zero] at this
  have hA0 : A ≠ 0 := by have := hA 0; rwa [map_zero] at this
  have hBs0 : Bs ≠ 0 := by have := hBs 0; rwa [map_zero] at this
  obtain ⟨B, hBdef⟩ : ∃ B, B = Point.map (W' := W.toAffine) (frobFF W L) Bs := ⟨_, rfl⟩
  rw [← hBdef] at hAB hΦ
  have hB0 : B ≠ 0 := by
    intro h0; apply hBs0
    apply Point.map_injective (W' := W.toAffine) (f := frobFF W L)
    rw [← hBdef, h0, map_zero]
  have hxne : px A ≠ px B := by
    intro hx
    rcases Y_eq_of_X_eq (nonsingular_px_py hA0).1 (nonsingular_px_py hB0).1 hx with hy | hy
    · exact hAB (sub_eq_zero.mpr (eq_of_px_py hA0 hB0 hx hy))
    · apply hΦ0
      rw [hΦ, ← sub_neg_eq_add, sub_eq_zero]
      exact eq_of_px_py hA0 (neg_ne_zero.mpr hB0) (hx.trans (px_neg' B).symm)
        (hy.trans (py_neg' hB0).symm)
  have hfA : px A ≠ 0 := fun h0 => transcendental_of_ne_ιP W L hA (by rw [h0]; exact isAlgebraic_zero)
  have hfS : px Bs ≠ 0 :=
    fun h0 => transcendental_of_ne_ιP W L hBs (by rw [h0]; exact isAlgebraic_zero)
  obtain ⟨P0, hP0, n1, n2, n3⟩ := exists_generic3 hfA hfS (sub_ne_zero.mpr hxne)
  obtain ⟨A0, -, hAx, hAy⟩ := exists_res hA0 hP0 n1.le
  obtain ⟨S0, hS00, hSx, hSy⟩ := exists_res hBs0 hP0 n2.le
  obtain ⟨hC, -⟩ := RPLib.EllFq.frob_some W L (nonsingular_px_py hS00)
  obtain ⟨C, hCdef⟩ : ∃ C : Pt W L, C = Point.some _ _ hC := ⟨_, rfl⟩
  have hιinj : Function.Injective (ιP W L) := Point.map_injective (W' := W.toAffine) (f := ιF W L)
  have hιC0 : ιP W L C ≠ 0 := fun h0 => by
    rw [hCdef] at h0
    exact Point.some_ne_zero hC (hιinj (h0.trans (map_zero _).symm))
  have hpxC : px (ιP W L C) = algebraMap L (FF W L) (px S0 ^ Fintype.card F) := by
    rw [hCdef]
    show px (Point.map (W' := W.toAffine) (ιF W L) _) = _
    rw [px_map]; rfl
  have hpyC : py (ιP W L C) = algebraMap L (FF W L) (py S0 ^ Fintype.card F) := by
    rw [hCdef]
    show py (Point.map (W' := W.toAffine) (ιF W L) _) = _
    rw [py_map]; rfl
  have hpxB : px B = frobFF W L (px Bs) := by rw [hBdef]; exact px_map (W' := W.toAffine) _ Bs
  have hpyB : py B = frobFF W L (py Bs) := by rw [hBdef]; exact py_map (W' := W.toAffine) _ Bs
  -- congruences mod `m_{P0}^2`
  have cAx : CongM2 P0 hP0 (px A) (px A) := CongM2.refl hAx.nu_le
  have cAy : CongM2 P0 hP0 (py A) (py A) := CongM2.refl hAy.nu_le
  have cX : CongM2 P0 hP0 (px B) (px (ιP W L C)) := by rw [hpxB, hpxC]; exact congM2_frob hSx
  have cY : CongM2 P0 hP0 (py B) (py (ιP W L C)) := by rw [hpyB, hpyC]; exact congM2_frob hSy
  have cden := cAx.sub cX
  have cdenS : CongM2 P0 hP0 (px A - px (ιP W L C)) (px A - px B) :=
    ⟨by rw [Valuation.map_sub_swap]; exact cden.1, cden.2.2, cden.2.1⟩
  have hden2 : nu W L P0 hP0 (px A - px (ιP W L C)) = 1 := cdenS.nu_eq_one n3
  have hxne2 : px A ≠ px (ιP W L C) := by
    intro h0; rw [h0, sub_self, map_zero] at hden2; exact zero_ne_one hden2
  have cslope := (cAy.sub cY).div cden n3 hden2
  have cPX : CongM2 P0 hP0 (px Φ) (px (A + ιP W L C)) := by
    rw [hΦ, px_add_of_px_ne hA0 hB0 hxne, px_add_of_px_ne hA0 hιC0 hxne2]
    exact CongM2.addX cAx cX cslope
  have cPY : CongM2 P0 hP0 (py Φ) (py (A + ιP W L C)) := by
    rw [hΦ, py_add_of_px_ne hA0 hB0 hxne, py_add_of_px_ne hA0 hιC0 hxne2]
    exact CongM2.addY cAx cX cAy cslope
  -- the comparison point `A + C` represents `τ ∘ [r]`, which has `e = 1`
  have hE2 : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (A + ιP W L C) =
      (A + ιP W L C) + ιP W L (rsHom W L r 0 S) := by
    intro S; rw [map_add, hEA, map_tau_ιP]; abel
  have h2 := ne_ιP_of_hE (A + ιP W L C) _ hE2 (rsHom_ne_zero r 0 hr)
  obtain ⟨P0', Q0, e, he1, he⟩ := ord_pull_global (A + ιP W L C) h2 _ hE2
  obtain ⟨ψ2, hψ2⟩ := exists_isPull_of_global (A + ιP W L C) h2 _ hE2 he1 he
  obtain rfl := hψ2.e_eq_one_r hr
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = Q0 + rsHom W L r 0 (P0 - P0') := ⟨_, rfl⟩
  have hgx0 := gx_ne_zero' (W := W) (L := L)
  have hQ : Q ≠ 0 := by
    intro hQ0
    have h1 := he _ hgx0 P0
    rw [pull_gx, ← hQdef, hQ0, Nat.cast_one, one_mul] at h1
    have hpx0 : px (A + ιP W L C) ≠ 0 := by
      rw [← pull_gx W L _ h2]; exact (_root_.map_ne_zero _).mpr hgx0
    have h3 := ord_nonneg_of_nu_le hP0 hpx0 cPX.2.2
    rw [h1] at h3
    exact absurd ord_gx_zero_neg (not_lt.mpr h3)
  -- a uniformizer at `Q`
  obtain ⟨t, ht⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer
    (hosP W L Q hQ)
  have hνf : nu W L Q hQ (algebraMap (CR W L) (FF W L) t) = WithZero.exp (-1) := by
    rw [nu_eq_valuation, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, ht]
  have hf0 : algebraMap (CR W L) (FF W L) t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hνf; exact WithZero.exp_ne_zero hνf.symm
  have hordQ : ord W L (algebraMap (CR W L) (FF W L) t) Q = 1 := by
    rw [ord_eq hQ, hνf, WithZero.log_exp]; norm_num
  have hord2 : ord W L (pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) P0 = 1 := by
    rw [he _ hf0 P0, ← hQdef, hordQ]; norm_num
  have hν2 : nu W L P0 hP0 (pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) =
      WithZero.exp (-1) := by
    have hne : nu W L P0 hP0 (pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hf0)
    rw [ord_eq hP0] at hord2
    have hl : WithZero.log (nu W L P0 hP0 (pull W L _ h2 (algebraMap (CR W L) (FF W L) t))) = -1 := by
      omega
    rw [← WithZero.exp_log hne, hl]
  -- congruence on all of `CR`
  have hall := congM2_all (P := P0) (hP := hP0)
    ((pull W L Φ h).comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)))
    ((pull W L _ h2).comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)))
    (by
      show CongM2 P0 hP0 (pull W L Φ h (gx W L)) (pull W L _ h2 (gx W L))
      rw [pull_gx, pull_gx]; exact cPX)
    (by
      show CongM2 P0 hP0 (pull W L Φ h (gy W L)) (pull W L _ h2 (gy W L))
      rw [pull_gy, pull_gy]; exact cPY)
  have hc := hall t
  change CongM2 P0 hP0 (pull W L Φ h (algebraMap (CR W L) (FF W L) t))
    (pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) at hc
  have hpull : nu W L P0 hP0 (pull W L Φ h (algebraMap (CR W L) (FF W L) t)) =
      WithZero.exp (-1) := by
    have hlt : nu W L P0 hP0 (pull W L Φ h (algebraMap (CR W L) (FF W L) t) -
        pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) <
        nu W L P0 hP0 (pull W L _ h2 (algebraMap (CR W L) (FF W L) t)) := by
      rw [hν2]
      exact lt_of_le_of_lt hc.1 (WithZero.exp_lt_exp.mpr (by norm_num))
    have := Valuation.map_add_eq_of_lt_left (nu W L P0 hP0) hlt
    rwa [add_sub_cancel, hν2] at this
  have hord : ord W L (pull W L Φ h (algebraMap (CR W L) (FF W L) t)) P0 = 1 := by
    rw [ord_eq hP0, hpull, WithZero.log_exp]; norm_num
  exact exists_isPull_one Φ h φ hE hf0 hord

lemma PhiRS_eq (r s : ℤ) : PhiRS W L r s =
    PhiRS W L r 0 + Point.map (W' := W.toAffine) (frobFF W L) (PhiRS W L s 0) := by
  simp only [PhiRS, piG, zero_zsmul, add_zero, map_zsmul]

/-- **`r + s π` is separable when `p ∤ r`**: it has a pullback with ramification index `1`. -/
theorem exists_isPull_rs_sep (r s : ℤ) (hr : (r : L) ≠ 0) :
    ∃ ψ : FF W L →ₐ[L] FF W L, IsPull ψ 1 (rsHom W L r s) := by
  by_cases hs : s = 0
  · subst hs
    obtain ⟨ψ, e, hP⟩ := exists_isPull_rs (W := W) (L := L) r 0 (rsHom_ne_zero r 0 hr)
    obtain rfl := hP.e_eq_one_r hr
    exact ⟨ψ, hP⟩
  refine exists_isPull_one_of_split hr (rsHom W L r s) (PhiRS W L r s)
    (ne_ιP_of_hE _ _ (hE_rs r s) (rsHom_ne_zero r s hr)) (hE_rs r s)
    (PhiRS W L r 0) (PhiRS W L s 0) (hE_rs r 0)
    (ne_ιP_of_hE _ _ (hE_rs r 0) (rsHom_ne_zero r 0 hr))
    (ne_ιP_of_hE _ _ (hE_rs s 0) (rsHom_r0_ne_zero hs)) ?_ (PhiRS_eq r s)
  have h1 := ne_ιP_of_hE _ _ (hE_rs (W := W) (L := L) r (-s)) (rsHom_ne_zero r (-s) hr) 0
  have e1 : PhiRS W L (-s) 0 = -PhiRS W L s 0 := by
    simp only [PhiRS, zero_zsmul, add_zero, neg_zsmul]
  rw [map_zero, PhiRS_eq, e1, map_neg, ← sub_eq_add_neg] at h1
  exact h1

/-- **`deg (r + s π) = #ker (r + s π)`** when `p ∤ r`. -/
theorem deg_rs_eq_card_ker (r s : ℤ) (hr : (r : L) ≠ 0) :
    deg (rsHom W L r s) = Nat.card {P : Pt W L | rsHom W L r s P = 0} := by
  obtain ⟨ψ, hP⟩ := exists_isPull_rs_sep (W := W) (L := L) r s hr
  rw [hP.deg_eq, one_mul, Nat.card_eq_card_finite_toFinset hP.finite_ker]

end Sep

end RPLib.Isog


