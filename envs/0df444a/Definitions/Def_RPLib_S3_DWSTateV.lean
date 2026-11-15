-- Prove2me | Definitions.Def_RPLib_S3_DWSTateV
-- name    : RPLib_S3_DWSTateV
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:20:36.856547+00:00
-- url     : https://prove2.me/theorems/49923d8c-cf63-4811-a481-e9e416c70e5d
-- title:
--   Weight-two Ramanujan-Petersson library: rigidity for an isomorphism of function fields fixing the origin
-- statement:
--   Rigidity for an isomorphism of function fields fixing the origin.
--
--   * `PoleOnce Φ` : a point `Φ ∈ W'(L(E))` whose `x` has its only pole at `0` (order `-2`, `y` of order `≥ -3`)
--     and whose residues separate the affine points.
--   * **`rigidG`** : for such `Φ`, `τ_S Φ - Φ` is a constant point of `W'` (copy of `DWSIsog_K.rigid` with `G = {0}`).
--   * `rmap`, **`hasGenI_rmap`** : the resulting homomorphism `θ` with `HasGenI θ Φ`.
--   * `genPt ψ` (the generic point carried by `ψ : L(E') ≃ₐ[L] L(E)`), **`poleOnce_of_tr`** (`Tr ψ 0 0 ⇒ PoleOnce`),
--     **`exists_hasGenI_of_tr`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateU

/-!
# S3-DWS-Tate, part V: rigidity for an isomorphism of function fields fixing the origin

* `PoleOnce Φ` : a point `Φ ∈ W'(L(E))` whose `x` has its only pole at `0` (order `-2`, `y` of order `≥ -3`)
  and whose residues separate the affine points.
* **`rigidG`** : for such `Φ`, `τ_S Φ - Φ` is a constant point of `W'` (copy of `DWSIsog_K.rigid` with `G = {0}`).
* `rmap`, **`hasGenI_rmap`** : the resulting homomorphism `θ` with `HasGenI θ Φ`.
* `genPt ψ` (the generic point carried by `ψ : L(E') ≃ₐ[L] L(E)`), **`poleOnce_of_tr`** (`Tr ψ 0 0 ⇒ PoleOnce`),
  **`exists_hasGenI_of_tr`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section RigidG

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma px_negV (P : (W'.baseChange (FF W L)).toAffine.Point) : px (-P) = px P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

lemma py_negV {P : (W'.baseChange (FF W L)).toAffine.Point} (hP : P ≠ 0) :
    py (-P) = (W'.baseChange (FF W L)).toAffine.negY (px P) (py P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

lemma ge_negY' {x y : FF W L} {P : Pt W L} {n : ℤ} (hx : Ge n x P) (hy : Ge n y P) (hn : n ≤ 0) :
    Ge n ((W'.baseChange (FF W L)).toAffine.negY x y) P := by
  rw [negY, bc_a₁ W' L (FF W L), bc_a₃ W' L (FF W L)]
  exact (hy.neg.sub (((Ge.const _ P).mul hx).mono (by omega))).sub ((Ge.const _ P).mono hn)

/-- A generic point whose only pole is at the origin, with separating residues. -/
structure PoleOnce (Φ : (W'.baseChange (FF W L)).toAffine.Point) : Prop where
  ne : Φ ≠ 0
  x_ne : px Φ ≠ 0
  ord_x : ord W L (px Φ) 0 = -2
  ge_y : Ge (-3) (py Φ) 0
  reg_x : ∀ P : Pt W L, P ≠ 0 → Ge 0 (px Φ) P
  reg_y : ∀ P : Pt W L, P ≠ 0 → Ge 0 (py Φ) P
  fib : ∀ (P P' : Pt W L) (hP : P ≠ 0) (hP' : P' ≠ 0) (u v : L), HV W L P hP (px Φ) u →
    HV W L P hP (py Φ) v → HV W L P' hP' (px Φ) u → HV W L P' hP' (py Φ) v → P = P'

/-- **Rigidity.** `τ_S Φ - Φ` is a constant point of `W'`. -/
theorem rigidG {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) (S : Pt W L) :
    ∃ C : Pt W' L, Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ =
      Φ + ιQ W W' L C := by
  set Q₁ := Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ with hQ₁
  have hQ₁0 : Q₁ ≠ 0 := by
    rw [hQ₁, eq_some_px_py hΦ.ne, Point.map_some]; exact Point.some_ne_zero _
  have hx₁ : px Q₁ = tau W L S (px Φ) := by rw [hQ₁, px_map, tau_apply]; rfl
  have hy₁ : py Q₁ = tau W L S (py Φ) := by rw [hQ₁, py_map, tau_apply]; rfl
  by_cases hS : S = 0
  · refine ⟨0, ?_⟩
    rw [map_zero, add_zero]
    exact eq_of_px_py hQ₁0 hΦ.ne (by rw [hx₁, hS, tau_zero_apply]) (by rw [hy₁, hS, tau_zero_apply])
  have hΦ0 : -Φ ≠ 0 := neg_ne_zero.mpr hΦ.ne
  have hpx₂ : px (-Φ) = px Φ := px_negV Φ
  have hpy₂ : py (-Φ) = (W'.baseChange (FF W L)).toAffine.negY (px Φ) (py Φ) := py_negV hΦ.ne
  have hne : px Q₁ ≠ px (-Φ) := by
    rw [hx₁, hpx₂]
    intro h
    have h1 := ord_tau S (px Φ) 0
    rw [h, zero_add, hΦ.ord_x] at h1
    have h2 := (hΦ.reg_x S hS).resolve_left hΦ.x_ne
    omega
  have e₁ := (nonsingular_px_py hQ₁0).1
  have e₂ := (nonsingular_px_py hΦ0).1
  have hall : ∀ P, Ge 0 (px (Q₁ + -Φ)) P ∧ Ge 0 (py (Q₁ + -Φ)) P := by
    intro P
    by_cases hP : P = 0
    · subst hP
      have hx0 : px (-Φ) ≠ 0 := by rw [hpx₂]; exact hΦ.x_ne
      have ho : ord W L (px (-Φ)) 0 = -2 := by rw [hpx₂, hΦ.ord_x]
      have hy3 : Ge (-3) (py (-Φ)) 0 := by
        rw [hpy₂]
        exact ge_negY' (Or.inr (by rw [hΦ.ord_x]; norm_num)) hΦ.ge_y (by norm_num)
      have hgx : Ge 0 (px Q₁) 0 := by
        rw [hx₁]; exact Ge.tau (by rw [zero_add]; exact hΦ.reg_x S hS)
      have hgy : Ge 0 (py Q₁) 0 := by
        rw [hy₁]; exact Ge.tau (by rw [zero_add]; exact hΦ.reg_y S hS)
      obtain ⟨-, h1, h2⟩ := ge_add_pole e₂ hx0 ho hy3 hgx hgy
      rw [add_comm Q₁, px_add' hΦ0 hQ₁0 hne.symm, py_add' hΦ0 hQ₁0 hne.symm]
      exact ⟨h1, h2⟩
    by_cases hPS : P + S = 0
    · have hx0 : px Q₁ ≠ 0 := by rw [hx₁]; exact tau_ne_zero _ hΦ.x_ne
      have ho : ord W L (px Q₁) P = -2 := by rw [hx₁, ord_tau, hPS, hΦ.ord_x]
      have hy3 : Ge (-3) (py Q₁) P := by
        rw [hy₁]; exact Ge.tau (by rw [hPS]; exact hΦ.ge_y)
      have hgx : Ge 0 (px (-Φ)) P := by rw [hpx₂]; exact hΦ.reg_x P hP
      have hgy : Ge 0 (py (-Φ)) P := by
        rw [hpy₂]; exact ge_negY' (hΦ.reg_x P hP) (hΦ.reg_y P hP) le_rfl
      obtain ⟨-, h1, h2⟩ := ge_add_pole e₁ hx0 ho hy3 hgx hgy
      rw [px_add' hQ₁0 hΦ0 hne, py_add' hQ₁0 hΦ0 hne]
      exact ⟨h1, h2⟩
    obtain ⟨u₁, hu₁⟩ := exists_HV_of_ge hPS (hΦ.reg_x _ hPS)
    obtain ⟨v₁, hv₁⟩ := exists_HV_of_ge hPS (hΦ.reg_y _ hPS)
    obtain ⟨u₂, hu₂⟩ := exists_HV_of_ge hP (hΦ.reg_x _ hP)
    obtain ⟨v₂, hv₂⟩ := exists_HV_of_ge hP (hΦ.reg_y _ hP)
    have hU₁ : HV W L P hP (px Q₁) u₁ := by rw [hx₁]; exact HV_tau hu₁
    have hV₁ : HV W L P hP (py Q₁) v₁ := by rw [hy₁]; exact HV_tau hv₁
    have hU₂ : HV W L P hP (px (-Φ)) u₂ := by rw [hpx₂]; exact hu₂
    have hV₂ : HV W L P hP (py (-Φ))
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
        have h3 := hΦ.fib (P + S) P hPS hP u₁ v₁ hu₁ hv₁ hu₂ hv₂
        exact hS (by simpa using h3)
      · exact Or.inl hu
    obtain h := ge_add_reg e₁ e₂ hne hP hU₁ hV₁ hU₂ hV₂ hn
    rw [px_add' hQ₁0 hΦ0 hne, py_add' hQ₁0 hΦ0 hne]
    exact h
  obtain ⟨a, ha⟩ := eq_const_of_ge (fun P => (hall P).1)
  obtain ⟨b, hb⟩ := eq_const_of_ge (fun P => (hall P).2)
  by_cases hD0 : Q₁ + -Φ = 0
  · refine ⟨0, ?_⟩
    rw [map_zero, add_zero]
    rw [← sub_eq_add_neg] at hD0
    exact sub_eq_zero.mp hD0
  obtain ⟨C, hC⟩ := eq_ιQ_of_const hD0 ha hb
  exact ⟨C, by rw [← hC]; abel⟩

/-- The constant `C(S)` with `τ_S Φ = Φ + ι(C(S))`. -/
noncomputable def rfun {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) (S : Pt W L) :
    Pt W' L :=
  (rigidG hΦ S).choose

lemma rfun_spec {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) (S : Pt W L) :
    Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ = Φ + ιQ W W' L (rfun hΦ S) :=
  (rigidG hΦ S).choose_spec

lemma rfun_unique {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) {S : Pt W L}
    {C : Pt W' L} (h : Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ =
      Φ + ιQ W W' L C) : rfun hΦ S = C :=
  ιQ_injective (add_left_cancel ((rfun_spec hΦ S).symm.trans h))

lemma rfun_add {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) (S T : Pt W L) :
    rfun hΦ (S + T) = rfun hΦ S + rfun hΦ T := by
  apply rfun_unique
  rw [map_tau_tau, rfun_spec hΦ T, map_add, rfun_spec hΦ S, map_ιQ_of_algHom, map_add (ιQ W W' L)]
  abel

/-- The homomorphism `θ` attached to a rigid generic point. -/
noncomputable def rmap {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) :
    Pt W L →+ Pt W' L :=
  AddMonoidHom.mk' (rfun hΦ) (rfun_add hΦ)

theorem hasGenI_rmap {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) :
    HasGenI (rmap hΦ) Φ := fun S => rfun_spec hΦ S

end RigidG

section TrPole

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- The generic point of `E'` carried into `W'(L(E))` by `ψ`. -/
noncomputable def genPt (ψ : FF W' L ≃ₐ[L] FF W L) : (W'.baseChange (FF W L)).toAffine.Point :=
  Point.map (W' := W'.toAffine) (ψ.toAlgHom.restrictScalars F) (G W' L)

lemma genPt_ne (ψ : FF W' L ≃ₐ[L] FF W L) : genPt ψ ≠ 0 := by
  rw [genPt, G, Point.map_some]; exact Point.some_ne_zero _

lemma px_genPt (ψ : FF W' L ≃ₐ[L] FF W L) : px (genPt ψ) = ψ (gx W' L) := by
  rw [genPt, px_map]; rfl

lemma py_genPt (ψ : FF W' L ≃ₐ[L] FF W L) : py (genPt ψ) = ψ (gy W' L) := by
  rw [genPt, py_map]; rfl

lemma tr_ne_zero {ψ : FF W' L ≃ₐ[L] FF W L} (h0 : Tr ψ 0 0) {P : Pt W L} {Q : Pt W' L} (hP : P ≠ 0)
    (h : Tr ψ P Q) : Q ≠ 0 := by
  rintro rfl; exact hP (h.inj h0)

lemma ge_tr {ψ : FF W' L ≃ₐ[L] FF W L} {P : Pt W L} {Q : Pt W' L} (h : Tr ψ P Q) {n : ℤ}
    {f : FF W' L} (hf : Ge n f Q) : Ge n (ψ f) P := by
  by_cases hf0 : f = 0
  · left; rw [hf0, map_zero]
  · right; rw [h f hf0]; exact hf.resolve_left hf0

lemma HV_tr {ψ : FF W' L ≃ₐ[L] FF W L} {P : Pt W L} {Q : Pt W' L} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : Tr ψ P Q) {f : FF W' L} {c : L} (hf : HV W' L Q hQ f c) : HV W L P hP (ψ f) c := by
  by_cases hfc : f - algebraMap L (FF W' L) c = 0
  · have e : f = algebraMap L (FF W' L) c := sub_eq_zero.mp hfc
    rw [e, AlgEquiv.commutes]; exact HV_alg c
  have h1 : 1 ≤ ord W' L (f - algebraMap L (FF W' L) c) Q := one_le_ord_of_HV (HV_sub_self hf) hfc
  have h2 : Ge 1 (ψ f - algebraMap L (FF W L) c) P := by
    right
    rw [← AlgEquiv.commutes ψ c, ← map_sub, h _ hfc]; exact h1
  exact ((HV_of_ge_one h2).add (HV_alg c)).congr (sub_add_cancel _ _) (zero_add c)

/-- **`Tr ψ 0 0` makes the carried generic point rigid.** -/
theorem poleOnce_of_tr {ψ : FF W' L ≃ₐ[L] FF W L} (h0 : Tr ψ 0 0) : PoleOnce (genPt ψ) := by
  have hx0 : ψ (gx W' L) ≠ 0 := (_root_.map_ne_zero ψ).mpr (gx_ne_zero' (W := W') (L := L))
  have hpart : ∀ P : Pt W L, P ≠ 0 → ∃ Q : Pt W' L, ∃ hQ : Q ≠ 0, Tr ψ P Q := fun P hP => by
    obtain ⟨Q, hQ⟩ := exists_tr ψ P
    exact ⟨Q, tr_ne_zero h0 hP hQ, hQ⟩
  refine ⟨genPt_ne ψ, by rw [px_genPt]; exact hx0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [px_genPt, h0 _ (gx_ne_zero' (W := W') (L := L)), ord_gx_zero]
  · rw [py_genPt]
    right
    exact (by rw [h0 _ (gy_ne_zero' (W := W') (L := L)), ord_gy_zero] :
      ord W L (ψ (gy W' L)) 0 = -3).ge
  · intro P hP
    obtain ⟨Q, hQ, hT⟩ := hpart P hP
    rw [px_genPt]; exact ge_tr hT (ge_gx hQ)
  · intro P hP
    obtain ⟨Q, hQ, hT⟩ := hpart P hP
    rw [py_genPt]; exact ge_tr hT (ge_gy hQ)
  · intro P P' hP hP' u v hu hv hu' hv'
    obtain ⟨Q, hQ, hT⟩ := hpart P hP
    obtain ⟨Q', hQ', hT'⟩ := hpart P' hP'
    rw [px_genPt] at hu hu'
    rw [py_genPt] at hv hv'
    have e1 := HV_unique (HV_tr hP hQ hT (HV_gx W' L Q hQ)) hu
    have e2 := HV_unique (HV_tr hP hQ hT (HV_gy W' L Q hQ)) hv
    have e3 := HV_unique (HV_tr hP' hQ' hT' (HV_gx W' L Q' hQ')) hu'
    have e4 := HV_unique (HV_tr hP' hQ' hT' (HV_gy W' L Q' hQ')) hv'
    have hQQ : Q = Q' := eq_of_px_py hQ hQ' (e1.trans e3.symm) (e2.trans e4.symm)
    subst hQQ
    exact hT.inj hT'

/-- **Rigidity for an isomorphism fixing the origin.** -/
theorem exists_hasGenI_of_tr {ψ : FF W' L ≃ₐ[L] FF W L} (h0 : Tr ψ 0 0) :
    ∃ θ : Pt W L →+ Pt W' L, HasGenI θ (genPt ψ) :=
  ⟨rmap (poleOnce_of_tr h0), hasGenI_rmap _⟩

end TrPole

end RPLib.DWS


