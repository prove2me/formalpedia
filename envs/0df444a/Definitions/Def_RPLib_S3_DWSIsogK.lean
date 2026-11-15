-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogK
-- name    : RPLib_S3_DWSIsogK
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:49:21.2212+00:00
-- url     : https://prove2.me/theorems/4d7a1b2a-9e2f-414a-9c6e-1e16b72ed59c
-- title:
--   Weight-two Ramanujan-Petersson library: rigidity of the quotient generic point
-- statement:
--   Rigidity of the quotient generic point.
--
--   * `slope_alg`, `ge_addXY`, **`ge_add_reg`** : the regular case of the addition law on `W'(L(E))`.
--   * `px_add'`, `py_add'` : coordinates of a sum on `W'(L(E))` when the `x`-coordinates differ.
--   * `HV_tau`, `tau_qx_ne`, `eq_const_of_ge`.
--   * **`rigid`** : `τ_S Ψ = Ψ + ι(C)` for every `S`, where `Ψ = (X_G, Y_G)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogJ

/-!
# S3-DWS-Isog, part K: rigidity of the quotient generic point

* `slope_alg`, `ge_addXY`, **`ge_add_reg`** : the regular case of the addition law on `W'(L(E))`.
* `px_add'`, `py_add'` : coordinates of a sum on `W'(L(E))` when the `x`-coordinates differ.
* `HV_tau`, `tau_qx_ne`, `eq_const_of_ge`.
* **`rigid`** : `τ_S Ψ = Ψ + ι(C)` for every `S`, where `Ψ = (X_G, Y_G)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

/-- The slope when the `y`-sum does not vanish (pure algebra). -/
lemma slope_alg {K : Type*} [Field K] {a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ : K} (hd : x₁ - x₂ ≠ 0)
    (hD : y₁ + y₂ + a₁ * x₁ + a₃ ≠ 0)
    (e₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (e₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆) :
    (y₁ - y₂) / (x₁ - x₂) =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + a₂ * (x₁ + x₂) + a₄ - a₁ * y₂) / (y₁ + y₂ + a₁ * x₁ + a₃) := by
  rw [div_eq_div_iff hd hD]
  linear_combination e₁ - e₂

section Reg

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W' : WeierstrassCurve F}

lemma ge_addXY {x₁ x₂ y₁ ℓ : FF W L} {P : Pt W L} (hx₁ : Ge 0 x₁ P) (hx₂ : Ge 0 x₂ P)
    (hy₁ : Ge 0 y₁ P) (hl : Ge 0 ℓ P) :
    Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ℓ) P ∧
      Ge 0 ((W'.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ ℓ) P := by
  have hc : ∀ a : L, Ge 0 (algebraMap L (FF W L) a) P := fun a => Ge.const a P
  have hX : Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ℓ) P := by
    rw [addX, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L)]
    exact (((hl.sq0.add ((hc _).mul0 hl)).sub (hc _)).sub hx₁).sub hx₂
  refine ⟨hX, ?_⟩
  rw [addY, negY, negAddY, bc_a₁ W' L (FF W L), bc_a₃ W' L (FF W L)]
  exact (((hl.mul0 (hX.sub hx₁)).add hy₁).neg.sub ((hc _).mul0 hX)).sub (hc _)

/-- **Regular case of the addition law.** -/
theorem ge_add_reg {x₁ y₁ x₂ y₂ : FF W L} (h₁ : (W'.baseChange (FF W L)).toAffine.Equation x₁ y₁)
    (h₂ : (W'.baseChange (FF W L)).toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) {P : Pt W L} (hP : P ≠ 0)
    {u₁ v₁ u₂ v₂ : L} (hu₁ : HV W L P hP x₁ u₁) (hv₁ : HV W L P hP y₁ v₁) (hu₂ : HV W L P hP x₂ u₂)
    (hv₂ : HV W L P hP y₂ v₂)
    (hne : u₁ ≠ u₂ ∨
      v₁ + v₂ + (W'.baseChange L).toAffine.a₁ * u₁ + (W'.baseChange L).toAffine.a₃ ≠ 0) :
    Ge 0 ((W'.baseChange (FF W L)).toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂))) P ∧
      Ge 0 ((W'.baseChange (FF W L)).toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂))) P := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hl : Ge 0 ((y₁ - y₂) / (x₁ - x₂)) P := by
    rcases hne with hne | hne
    · exact ge_of_HV ((hv₁.sub hv₂).div (hu₁.sub hu₂) (sub_ne_zero.mpr hne))
    · have hD := ((hv₁.add hv₂).add ((HV_alg (P := P) (hP := hP)
        (W'.baseChange L).toAffine.a₁).mul hu₁)).add
        (HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₃)
      rw [slope_alg hd (hD.ne_zero hne) (eqn_FF h₁) (eqn_FF h₂)]
      have hN := (((((hu₁.pow 2).add (hu₁.mul hu₂)).add (hu₂.pow 2)).add
        ((HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₂).mul (hu₁.add hu₂))).add
        (HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₄)).sub
        ((HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₁).mul hv₂)
      exact ge_of_HV (hN.div hD hne)
  exact ge_addXY (ge_of_HV hu₁) (ge_of_HV hu₂) (ge_of_HV hv₁) hl

lemma px_add' {P Q : (W'.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : px P ≠ px Q) :
    px (P + Q) = (W'.baseChange (FF W L)).toAffine.addX (px P) (px Q)
      ((py P - py Q) / (px P - px Q)) := by
  have e := Point.add_of_X_ne (h₁ := nonsingular_px_py hP) (h₂ := nonsingular_px_py hQ) h
  rw [← eq_some_px_py hP, ← eq_some_px_py hQ] at e
  rw [e, ← slope_of_X_ne h]
  rfl

lemma py_add' {P Q : (W'.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : px P ≠ px Q) :
    py (P + Q) = (W'.baseChange (FF W L)).toAffine.addY (px P) (px Q) (py P)
      ((py P - py Q) / (px P - px Q)) := by
  have e := Point.add_of_X_ne (h₁ := nonsingular_px_py hP) (h₂ := nonsingular_px_py hQ) h
  rw [← eq_some_px_py hP, ← eq_some_px_py hQ] at e
  rw [e, ← slope_of_X_ne h]
  rfl

lemma HV_tau {P S : Pt W L} {hP : P ≠ 0} {hT : P + S ≠ 0} {f : FF W L} {c : L}
    (h : HV W L (P + S) hT f c) : HV W L P hP (tau W L S f) c := by
  unfold HV at *
  have e : tau W L S f - algebraMap L (FF W L) c = tau W L S (f - algebraMap L (FF W L) c) := by
    rw [map_sub, AlgEquiv.commutes]
  rw [e, nu_tau P S hP hT]
  exact h

/-- A function regular everywhere is constant. -/
lemma eq_const_of_ge {f : FF W L} (h : ∀ P, Ge 0 f P) : ∃ c : L, f = algebraMap L (FF W L) c := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf, map_zero]⟩
  by_contra hc
  push_neg at hc
  obtain ⟨P, hP⟩ := exists_pole hf hc
  have := (h P).resolve_left hf
  omega

end Reg

section Rigid

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]

lemma tau_qx_ne {S : Pt W L} (hS : S ∉ G) : tau W L S (qx G) ≠ qx G := by
  intro h
  have h1 := ord_tau S (qx G) (-S)
  rw [h, neg_add_cancel, (ord_qx_zero (G := G)).2] at h1
  have hS' : -S ∉ G := fun h' => hS (by simpa using G.neg_mem h')
  rcases (goodQ_qx (G := G)).2 (-S) hS' with h0 | h0
  · exact (ord_qx_zero (G := G)).1 h0
  · omega

lemma qPt_ne_zero (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : qPt hW' ≠ 0 := by
  rw [qPt]; exact Point.some_ne_zero _

lemma ge_negY_qy {P : Pt W L} {n : ℤ} (hx : Ge n (qx G) P) (hy : Ge n (qy G) P) (hn : n ≤ 0) :
    Ge n ((W'.baseChange (FF W L)).toAffine.negY (qx G) (qy G)) P := by
  rw [negY, bc_a₁ W' L (FF W L), bc_a₃ W' L (FF W L)]
  exact (hy.neg.sub (((Ge.const _ P).mul hx).mono (by omega))).sub ((Ge.const _ P).mono hn)

/-- **Rigidity.** `τ_S Ψ - Ψ` is a constant point of `W'`. -/
theorem rigid (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (S : Pt W L) :
    ∃ C : Pt W' L, Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') =
      qPt hW' + ιQ W W' L C := by
  set Q₁ := Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (qPt hW') with hQ₁
  have hQ₁0 : Q₁ ≠ 0 := by rw [hQ₁, qPt, Point.map_some]; exact Point.some_ne_zero _
  have hx₁ : px Q₁ = tau W L S (qx G) := by rw [hQ₁, px_map, tau_apply]; rfl
  have hy₁ : py Q₁ = tau W L S (qy G) := by rw [hQ₁, py_map, tau_apply]; rfl
  have hinvx := (goodQ_qx (G := G)).1
  have hinvy := (goodQ_qy (G := G)).1
  by_cases hS : S ∈ G
  · refine ⟨0, ?_⟩
    rw [map_zero, add_zero]
    exact eq_of_px_py hQ₁0 (qPt_ne_zero hW') (by rw [hx₁, hinvx S hS]; rfl)
      (by rw [hy₁, hinvy S hS]; rfl)
  have hQ₂0 : -qPt hW' ≠ 0 := neg_ne_zero.mpr (qPt_ne_zero hW')
  have hpx₂ : px (-qPt hW') = qx G := rfl
  have hpy₂ : py (-qPt hW') = (W'.baseChange (FF W L)).toAffine.negY (qx G) (qy G) := rfl
  have hne : px Q₁ ≠ px (-qPt hW') := by rw [hx₁, hpx₂]; exact tau_qx_ne hS
  have e₁ := (nonsingular_px_py hQ₁0).1
  have e₂ := (nonsingular_px_py hQ₂0).1
  have hall : ∀ P, Ge 0 (px (Q₁ + -qPt hW')) P ∧ Ge 0 (py (Q₁ + -qPt hW')) P := by
    intro P
    by_cases hP : P ∈ G
    · have hPS : P + S ∉ G := fun h => hS (by simpa using G.sub_mem h hP)
      have hx0 : px (-qPt hW') ≠ 0 := by rw [hpx₂]; exact (ord_qx_zero (G := G)).1
      have ho : ord W L (px (-qPt hW')) P = -2 := by
        rw [hpx₂, hinvx.ord_mem hP, (ord_qx_zero (G := G)).2]
      have hy3 : Ge (-3) (py (-qPt hW')) P := by
        rw [hpy₂]
        refine ge_negY_qy (Or.inr ?_) (Or.inr ?_) (by norm_num)
        · rw [hinvx.ord_mem hP, (ord_qx_zero (G := G)).2]; norm_num
        · rw [hinvy.ord_mem hP, (ord_qy_zero (G := G)).2]
      have hgx : Ge 0 (px Q₁) P := by rw [hx₁]; exact Ge.tau ((goodQ_qx (G := G)).2 _ hPS)
      have hgy : Ge 0 (py Q₁) P := by rw [hy₁]; exact Ge.tau ((goodQ_qy (G := G)).2 _ hPS)
      obtain ⟨-, h1, h2⟩ := ge_add_pole e₂ hx0 ho hy3 hgx hgy
      rw [add_comm Q₁, px_add' hQ₂0 hQ₁0 hne.symm, py_add' hQ₂0 hQ₁0 hne.symm]
      exact ⟨h1, h2⟩
    by_cases hPS : P + S ∈ G
    · have hx0 : px Q₁ ≠ 0 := by rw [hx₁]; exact tau_ne_zero _ (ord_qx_zero (G := G)).1
      have ho : ord W L (px Q₁) P = -2 := by
        rw [hx₁, ord_tau, hinvx.ord_mem hPS, (ord_qx_zero (G := G)).2]
      have hy3 : Ge (-3) (py Q₁) P := by
        rw [hy₁]
        exact Ge.tau (Or.inr (le_of_eq (by rw [hinvy.ord_mem hPS, (ord_qy_zero (G := G)).2])))
      have hgx : Ge 0 (px (-qPt hW')) P := by rw [hpx₂]; exact (goodQ_qx (G := G)).2 P hP
      have hgy : Ge 0 (py (-qPt hW')) P := by
        rw [hpy₂]; exact ge_negY_qy ((goodQ_qx (G := G)).2 P hP) ((goodQ_qy (G := G)).2 P hP) le_rfl
      obtain ⟨-, h1, h2⟩ := ge_add_pole e₁ hx0 ho hy3 hgx hgy
      rw [px_add' hQ₁0 hQ₂0 hne, py_add' hQ₁0 hQ₂0 hne]
      exact ⟨h1, h2⟩
    obtain ⟨u₁, hu₁⟩ := exists_HV_of_ge (ne_zero_of_nmem hPS) ((goodQ_qx (G := G)).2 _ hPS)
    obtain ⟨v₁, hv₁⟩ := exists_HV_of_ge (ne_zero_of_nmem hPS) ((goodQ_qy (G := G)).2 _ hPS)
    obtain ⟨u₂, hu₂⟩ := exists_HV_of_ge (ne_zero_of_nmem hP) ((goodQ_qx (G := G)).2 _ hP)
    obtain ⟨v₂, hv₂⟩ := exists_HV_of_ge (ne_zero_of_nmem hP) ((goodQ_qy (G := G)).2 _ hP)
    have hU₁ : HV W L P (ne_zero_of_nmem hP) (px Q₁) u₁ := by rw [hx₁]; exact HV_tau hu₁
    have hV₁ : HV W L P (ne_zero_of_nmem hP) (py Q₁) v₁ := by rw [hy₁]; exact HV_tau hv₁
    have hU₂ : HV W L P (ne_zero_of_nmem hP) (px (-qPt hW')) u₂ := by rw [hpx₂]; exact hu₂
    have hV₂ : HV W L P (ne_zero_of_nmem hP) (py (-qPt hW'))
        (-v₂ - (W'.baseChange L).toAffine.a₁ * u₂ - (W'.baseChange L).toAffine.a₃) := by
      rw [hpy₂, negY, bc_a₁ W' L (FF W L), bc_a₃ W' L (FF W L)]
      exact (hv₂.neg.sub ((HV_alg _).mul hu₂)).sub (HV_alg _)
    have hn : u₁ ≠ u₂ ∨ v₁ + (-v₂ - (W'.baseChange L).toAffine.a₁ * u₂ -
        (W'.baseChange L).toAffine.a₃) + (W'.baseChange L).toAffine.a₁ * u₁ +
        (W'.baseChange L).toAffine.a₃ ≠ 0 := by
      by_cases hu : u₁ = u₂
      · right
        intro h0
        subst hu
        have hv : v₁ = v₂ := by linear_combination h0
        subst hv
        exact hS (by simpa using fiber hG hW' hP hPS hu₂ hv₂ hu₁ hv₁)
      · exact Or.inl hu
    obtain h := ge_add_reg e₁ e₂ hne (ne_zero_of_nmem hP) hU₁ hV₁ hU₂ hV₂ hn
    rw [px_add' hQ₁0 hQ₂0 hne, py_add' hQ₁0 hQ₂0 hne]
    exact h
  obtain ⟨a, ha⟩ := eq_const_of_ge (fun P => (hall P).1)
  obtain ⟨b, hb⟩ := eq_const_of_ge (fun P => (hall P).2)
  by_cases hD0 : Q₁ + -qPt hW' = 0
  · refine ⟨0, ?_⟩
    rw [map_zero, add_zero, ← sub_eq_add_neg] at *
    exact sub_eq_zero.mp hD0
  obtain ⟨C, hC⟩ := eq_ιQ_of_const hD0 ha hb
  exact ⟨C, by rw [← hC]; abel⟩

end Rigid

end RPLib.DWS


