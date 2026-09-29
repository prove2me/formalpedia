-- Prove2me | solution 1 for AlgebraicGeometry.tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/dd8b7c10-239a-59d6-84bf-ad1af969aa2c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

namespace SVLocal

variable {Z : Scheme.{0}}

def val (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appLE U ⊤ h s) else 0

theorem val_of_le (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    val p U s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appLE U ⊤ h s) := by
  classical
  unfold val; rw [dif_pos h]

theorem val_mul (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s t : Γ(Z, U)) :
    val p U (s * t) = val p U s * val p U t := by
  classical
  unfold val; split_ifs <;> simp

theorem val_pow (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens) (s : Γ(Z, U)) (m : ℕ) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    val p U (s ^ m) = val p U s ^ m := by
  rw [val_of_le _ _ _ h, val_of_le _ _ _ h, map_pow, map_pow]

theorem val_res (p : Spec (CommRingCat.of ℂ) ⟶ Z) {V W : Z.Opens} (i : V ≤ W) (t : Γ(Z, W))
    (h : ⊤ ≤ p ⁻¹ᵁ V) :
    val p V (Z.presheaf.map (homOfLE i).op t) = val p W t := by
  have hW : ⊤ ≤ p ⁻¹ᵁ W := h.trans (Scheme.Hom.preimage_mono _ i)
  rw [val_of_le _ _ _ h, val_of_le _ _ _ hW,
    ← CommRingCat.comp_apply (Z.presheaf.map (homOfLE i).op) (p.appLE V ⊤ h) t, Scheme.Hom.map_appLE]

theorem top_le_iff (p : Spec (CommRingCat.of ℂ) ⟶ Z) (O : Z.Opens) :
    ⊤ ≤ p ⁻¹ᵁ O ↔ p.base (IsLocalRing.closedPoint ℂ) ∈ O := by
  constructor
  · intro h; exact h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro h x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hx; exact h

theorem top_le_opens_iff (O : (Spec (CommRingCat.of ℂ)).Opens) :
    ⊤ ≤ O ↔ IsLocalRing.closedPoint ℂ ∈ O := by
  constructor
  · intro hh; exact hh (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro hh x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hx; exact hh

theorem top_le_preimage_basicOpen_iff (p : Spec (CommRingCat.of ℂ) ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (r : Γ(Z, U)) :
    ⊤ ≤ p ⁻¹ᵁ Z.basicOpen r ↔ val p U r ≠ 0 := by
  rw [val_of_le _ _ _ h]
  have h1 : (Spec (CommRingCat.of ℂ)).basicOpen (p.appLE U ⊤ h r) = ⊤ ⊓ p ⁻¹ᵁ Z.basicOpen r :=
    Scheme.basicOpen_appLE p ⊤ U h r
  rw [top_inf_eq] at h1
  rw [← h1, top_le_opens_iff, AlgebraicGeometry.basicOpen_eq_of_affine']
  change (IsLocalRing.closedPoint ℂ ∈ PrimeSpectrum.basicOpen _) ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change _ ∉ IsLocalRing.maximalIdeal ℂ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]

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

end SVLocal

open SVLocal in
theorem solution
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)}
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (U₀ : X.Opens) (hU₀ : IsAffineOpen U₀) (hQ₀ : ⊤ ≤ Q.1 ⁻¹ᵁ U₀) (n₀ : ℕ) (hP₀ : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U₀)
    (h₀ : ∀ s : Γ(X, U₀),
      Tendsto (fun n : ℕ => if h : n₀ ≤ n then
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U₀ ⊤ (hP₀ n h)) s) else 0)
        atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U₀ ⊤ hQ₀) s)))) :
    ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s))) := by
  classical
  intro U hU hx
  let x₀ : X := Q.1.base (IsLocalRing.closedPoint ℂ)
  have hx₀U : x₀ ∈ U := (top_le_iff _ _).1 hx
  have hx₀U₀ : x₀ ∈ U₀ := (top_le_iff _ _).1 hQ₀
  obtain ⟨r, hrU, hx₀r⟩ := hU₀.exists_basicOpen_le ⟨x₀, hx₀U⟩ hx₀U₀

  have hv₀ : ∀ s : Γ(X, U₀), Tendsto (fun n => val (P n).1 U₀ s) atTop (𝓝 (val Q.1 U₀ s)) :=
    fun s => (tendsto_iff_val U₀ n₀ hP₀ hQ₀ s).1 (h₀ s)
  have hQD : ⊤ ≤ Q.1 ⁻¹ᵁ X.basicOpen r := (top_le_iff _ _).2 hx₀r
  have hrQ : val Q.1 U₀ r ≠ 0 := (top_le_preimage_basicOpen_iff Q.1 U₀ hQ₀ r).1 hQD

  obtain ⟨N, hN⟩ := eventually_atTop.1 (((hv₀ r).eventually_ne hrQ).and (eventually_ge_atTop n₀))
  have hPD : ∀ n, N ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ X.basicOpen r := fun n hn =>
    (top_le_preimage_basicOpen_iff (P n).1 U₀ (hP₀ n (hN n hn).2) r).2 (hN n hn).1
  have hPU : ∀ n, N ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U := fun n hn =>
    (hPD n hn).trans (Scheme.Hom.preimage_mono _ hrU)
  refine ⟨N, hPU, fun s => ?_⟩
  rw [tendsto_iff_val U N hPU hx s]

  haveI := hU₀.isLocalization_basicOpen r
  let s' : Γ(X, X.basicOpen r) := X.presheaf.map (homOfLE hrU).op s
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hsa⟩ := IsLocalization.surj (Submonoid.powers r) s'
  obtain ⟨m, rfl⟩ := hb

  have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ X), ⊤ ≤ q ⁻¹ᵁ X.basicOpen r → ⊤ ≤ q ⁻¹ᵁ U₀ →
      val q U s = val q U₀ a / val q U₀ r ^ m := by
    intro q hqD hqU₀
    have hr0 : val q U₀ r ≠ 0 := (top_le_preimage_basicOpen_iff q U₀ hqU₀ r).1 hqD
    have h1 : val q (X.basicOpen r) s' * val q (X.basicOpen r) (algebraMap Γ(X, U₀) Γ(X, X.basicOpen r) (r ^ m)) =
        val q (X.basicOpen r) (algebraMap Γ(X, U₀) Γ(X, X.basicOpen r) a) := by
      rw [← val_mul, hsa]
    have halg : ∀ b : Γ(X, U₀), algebraMap Γ(X, U₀) Γ(X, X.basicOpen r) b =
        X.presheaf.map (homOfLE (X.basicOpen_le r)).op b := fun b => rfl
    rw [halg, halg, val_res q (X.basicOpen_le r) _ hqD, val_res q (X.basicOpen_le r) _ hqD,
      val_pow _ _ _ _ hqU₀] at h1
    have h2 : val q (X.basicOpen r) s' = val q U s := val_res q hrU s hqD
    rw [h2] at h1
    rw [eq_div_iff (pow_ne_zero m hr0), h1]
  rw [key Q.1 hQD hQ₀]
  have lim := (hv₀ a).div ((hv₀ r).pow m) (pow_ne_zero m hrQ)
  refine lim.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  rw [Pi.div_apply]
  exact (key (P n).1 (hPD n hn) (hP₀ n (hN n hn).2)).symm

end
end S_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex
end P2MW
export P2MW.S_AlgebraicGeometry_tendsto_appLE_of_tendsto_appLE_of_isAffineOpen_complex (solution)
