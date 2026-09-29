-- Prove2me | solution 1 for AlgebraicGeometry.tendsto_appLE_pullbackLift_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c0f0cc9d-bf8d-5a95-9fc9-44acc2221261

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology TensorProduct

namespace SVProd

variable {Z : Scheme.{0}}

def val (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appLE U ⊤ h s) else 0

theorem val_of_le (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    val p U s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appLE U ⊤ h s) := by
  classical
  unfold val; rw [dif_pos h]

theorem val_zero (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) : val p U 0 = 0 := by
  classical
  unfold val; split_ifs <;> simp

theorem val_add (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s t : Γ(Z, U)) :
    val p U (s + t) = val p U s + val p U t := by
  classical
  unfold val; split_ifs <;> simp

theorem val_mul (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s t : Γ(Z, U)) :
    val p U (s * t) = val p U s * val p U t := by
  classical
  unfold val; split_ifs <;> simp

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h; rfl

theorem val_appLE_of_comp_eq {X Y : Scheme.{0}} (φ : X ⟶ Y) (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (q : Spec (CommRingCat.of ℂ) ⟶ Y) (hq : p ≫ φ = q)
    (U : Y.Opens) (W : X.Opens) (hW : W ≤ φ ⁻¹ᵁ U) (hp : ⊤ ≤ p ⁻¹ᵁ W) (s : Γ(Y, U)) :
    val p W (φ.appLE U W hW s) = val q U s := by
  have hqU : ⊤ ≤ q ⁻¹ᵁ U := by
    rw [← hq, Scheme.Hom.comp_preimage]
    exact hp.trans (Scheme.Hom.preimage_mono _ hW)
  rw [val_of_le _ _ _ hp, val_of_le _ _ _ hqU,
    ← CommRingCat.comp_apply (φ.appLE U W hW) (p.appLE W ⊤ hp) s, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq hq]

theorem tendsto_iff_val {p : ℕ → (Spec (CommRingCat.of ℂ) ⟶ Z)} {q : Spec (CommRingCat.of ℂ) ⟶ Z}
    (U : Z.Opens) (n₀ : ℕ) (hp : ∀ n, n₀ ≤ n → ⊤ ≤ (p n) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(Z, U)) :
    Tendsto (fun n : ℕ => if h : n₀ ≤ n then
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((p n).appLE U ⊤ (hp n h)) s) else 0)
      atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((q.appLE U ⊤ hq) s))) ↔
    Tendsto (fun n => val (p n) U s) atTop (𝓝 (val q U s)) := by
  rw [val_of_le _ _ _ hq]
  refine Filter.tendsto_congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  beta_reduce
  rw [dif_pos hn, val_of_le]

end SVProd

open SVProd in
theorem solution
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)} {g : Y ⟶ Spec (CommRingCat.of ℂ)}
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (hP : ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s))))
    (P' : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hP' : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q'.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P' n).1 ⁻¹ᵁ U,
          ∀ s : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P' n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q'.1.appLE U ⊤ hx) s)))) :
    ∀ (U : (pullback f g).Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ (⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1 ⁻¹ᵁ U,
          ∀ s : Γ((pullback f g), U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm), by rw [pullback.lift_fst_assoc]; exact (P n).2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((⟨pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm), by rw [pullback.lift_fst_assoc]; exact Q.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (pullback.fst f g ≫ f)).1.appLE U ⊤ hx) s))) := by
  classical

  let pr : ℕ → (Spec (CommRingCat.of ℂ) ⟶ pullback f g) := fun n =>
    pullback.lift (P n).1 (P' n).1 ((P n).2.trans (P' n).2.symm)
  let q : Spec (CommRingCat.of ℂ) ⟶ pullback f g := pullback.lift Q.1 Q'.1 (Q.2.trans Q'.2.symm)
  have hpr_fst : ∀ n, pr n ≫ pullback.fst f g = (P n).1 := fun n => pullback.lift_fst _ _ _
  have hpr_snd : ∀ n, pr n ≫ pullback.snd f g = (P' n).1 := fun n => pullback.lift_snd _ _ _
  have hq_fst : q ≫ pullback.fst f g = Q.1 := pullback.lift_fst _ _ _
  have hq_snd : q ≫ pullback.snd f g = Q'.1 := pullback.lift_snd _ _ _

  have hQpt : Q.1.base (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) := trivial
  obtain ⟨U, hU, hQU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hQpt
  have hQ'pt : Q'.1.base (IsLocalRing.closedPoint ℂ) ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hQ'V, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) hQ'pt
  have top_le_iff : ∀ {T : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ T) (O : T.Opens),
      ⊤ ≤ p ⁻¹ᵁ O ↔ p.base (IsLocalRing.closedPoint ℂ) ∈ O := by
    intro T p O
    constructor
    · intro h; exact h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
    · intro h x _
      have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      subst hx; exact h
  have hQU' : ⊤ ≤ Q.1 ⁻¹ᵁ U := (top_le_iff _ _).2 hQU
  have hQ'V' : ⊤ ≤ Q'.1 ⁻¹ᵁ V := (top_le_iff _ _).2 hQ'V
  obtain ⟨n₁, hP₁, hs₁⟩ := hP U hU hQU'
  obtain ⟨n₂, hP₂, hs₂⟩ := hP' V hV hQ'V'

  let W₀ : (pullback f g).Opens := pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom g V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst f g ≫ f)
    (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
  obtain ⟨hW₀, e, he⟩ :=
    AlgebraicGeometry.Scheme.Pullback.isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      f g U hU V hV

  have mem_W₀ : ∀ (p : Spec (CommRingCat.of ℂ) ⟶ pullback f g),
      ⊤ ≤ (p ≫ pullback.fst f g) ⁻¹ᵁ U → ⊤ ≤ (p ≫ pullback.snd f g) ⁻¹ᵁ V → ⊤ ≤ p ⁻¹ᵁ W₀ := by
    intro p h1 h2
    rw [Scheme.Hom.comp_preimage] at h1 h2
    show ⊤ ≤ p ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
    rw [Scheme.Hom.preimage_inf]
    exact le_inf h1 h2
  have hqW₀ : ⊤ ≤ q ⁻¹ᵁ W₀ := mem_W₀ q (by rw [hq_fst]; exact hQU') (by rw [hq_snd]; exact hQ'V')
  let n₀ := max n₁ n₂
  have hprW₀ : ∀ n, n₀ ≤ n → ⊤ ≤ (pr n) ⁻¹ᵁ W₀ := fun n hn =>
    mem_W₀ (pr n) (by rw [hpr_fst]; exact hP₁ n ((le_max_left _ _).trans hn))
      (by rw [hpr_snd]; exact hP₂ n ((le_max_right _ _).trans hn))

  have hv₁ : ∀ a : Γ(X, U), Tendsto (fun n => val (P n).1 U a) atTop (𝓝 (val Q.1 U a)) :=
    fun a => (tendsto_iff_val U n₁ hP₁ hQU' a).1 (hs₁ a)
  have hv₂ : ∀ b : Γ(Y, V), Tendsto (fun n => val (P' n).1 V b) atTop (𝓝 (val Q'.1 V b)) :=
    fun b => (tendsto_iff_val V n₂ hP₂ hQ'V' b).1 (hs₂ b)

  have hten : ∀ t : Γ(X, U) ⊗[ℂ] Γ(Y, V),
      Tendsto (fun n => val (pr n) W₀ (e t)) atTop (𝓝 (val q W₀ (e t))) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, val_zero]; exact tendsto_const_nhds
    | tmul a b =>
      rw [he a b, val_mul,
        val_appLE_of_comp_eq _ q Q.1 hq_fst U W₀ inf_le_left hqW₀,
        val_appLE_of_comp_eq _ q Q'.1 hq_snd V W₀ inf_le_right hqW₀]
      refine ((hv₁ a).mul (hv₂ b)).congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
      beta_reduce
      rw [val_mul,
        val_appLE_of_comp_eq _ (pr n) (P n).1 (hpr_fst n) U W₀ inf_le_left (hprW₀ n hn),
        val_appLE_of_comp_eq _ (pr n) (P' n).1 (hpr_snd n) V W₀ inf_le_right (hprW₀ n hn)]
    | add t₁ t₂ h₁ h₂ => simp only [map_add, val_add]; exact h₁.add h₂
  have hval₀ : ∀ s : Γ(pullback f g, W₀),
      Tendsto (fun n => val (pr n) W₀ s) atTop (𝓝 (val q W₀ s)) := by
    intro s
    obtain ⟨t, rfl⟩ := e.surjective s
    exact hten t

  have h₀ : ∀ s : Γ(pullback f g, W₀),
      Tendsto (fun n : ℕ => if h : n₀ ≤ n then
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((pr n).appLE W₀ ⊤ (hprW₀ n h)) s) else 0)
        atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((q.appLE W₀ ⊤ hqW₀) s))) :=
    fun s => (tendsto_iff_val W₀ n₀ hprW₀ hqW₀ s).2 (hval₀ s)
  exact AlgebraicGeometry.tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex
    (f := pullback.fst f g ≫ f)
    (fun n => ⟨pr n, by rw [pullback.lift_fst_assoc]; exact (P n).2⟩)
    ⟨q, by rw [pullback.lift_fst_assoc]; exact Q.2⟩ W₀ hW₀ hqW₀ n₀ hprW₀ h₀

end
end S_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex
end P2MW
export P2MW.S_AlgebraicGeometry_tendsto_appLE_pullbackLift_complex (solution)
