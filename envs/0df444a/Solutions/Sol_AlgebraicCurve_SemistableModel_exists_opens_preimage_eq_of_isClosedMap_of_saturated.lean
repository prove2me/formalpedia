-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.exists_opens_preimage_eq_of_isClosedMap_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f94d4ce0-86d4-550e-be0e-2fd31a068aad

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (X₁ : Scheme.{u}) (π : M.X ⟶ X₁)
    (hcl : IsClosedMap π.base) (hsurj : Function.Surjective π.base)
    (hfib_sp : ∀ x x' : M.X, π.base x' = π.base x → M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x)
    (hfib_gen : ∀ x' : M.X, π.base x' = π.base (genericPoint M.X) → x' = genericPoint M.X)
    (hfib_pt : ∀ (P : Place L F) (x' : M.X), π.base x' = π.base (M.pt P) → ∃ P' : Place L F, x' = M.pt P')
    (G : Place L F → ℤ)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hU : (⨆ a, U a) = ⊤)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔ G P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨ (G P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨ (G P = 0 ∧ P.ord (h a) = 0))))
    (hGfib : ∀ P P' : Place L F, π.base (M.pt P) = π.base (M.pt P') → (G P = 0 ↔ G P' = 0))
    (hhfib : ∀ a (P P' : Place L F), π.base (M.pt P) = π.base (M.pt P') →
      (P.ord (h a) = 0 ↔ P'.ord (h a) = 0)) :
    ∃ U₁ : Fin r → X₁.Opens, (⨆ a, U₁ a) = ⊤ ∧ ∀ a (x : M.X), x ∈ U a ↔ π.base x ∈ U₁ a := by
  classical
  have hcont : Continuous π.base := π.continuous

  have hclosed_max : ∀ y : Spec (CommRingCat.of ↥A), IsLocalRing.closedPoint ↥A ⤳ y → y = IsLocalRing.closedPoint ↥A := by
    intro y hy
    have hle := (PrimeSpectrum.le_iff_specializes _ _).mpr hy
    apply PrimeSpectrum.ext
    exact ((IsLocalRing.maximalIdeal.isMaximal ↥A).eq_of_le y.2.ne_top hle).symm

  have hsp_of_gen_spec : ∀ (i : ιV) (x : M.X), M.gen i ⤳ x → M.toBase.base x = IsLocalRing.closedPoint ↥A := by
    intro i x hx
    have h1 : M.toBase.base (M.gen i) ⤳ M.toBase.base x := hx.map M.toBase.continuous
    rw [M.toBase_gen] at h1
    exact hclosed_max _ h1
  have hsp_sm : ∀ i Q, M.toBase.base (M.sm i Q) = IsLocalRing.closedPoint ↥A :=
    fun i Q => hsp_of_gen_spec i _ (M.gen_specializes_sm i Q)
  have hsp_nd : ∀ e, M.toBase.base (M.nd e) = IsLocalRing.closedPoint ↥A :=
    fun e => hsp_of_gen_spec (src e) _ (M.gen_specializes_nd e).1

  have hinj := M.classify_bijective.1
  have hsm_ne_pt : ∀ i Q (P : Place L F), M.sm i Q ≠ M.pt P := by
    intro i Q P h
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, Q⟩)))) (Sum.inr (Sum.inl P)) (by simpa using h)
    simp at this
  have hnd_ne_pt : ∀ e (P : Place L F), M.nd e ≠ M.pt P := by
    intro e P h
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inr (Sum.inl P)) (by simpa using h)
    simp at this
  have hsm_ne_nd : ∀ i Q e, M.sm i Q ≠ M.nd e := by
    intro i Q e h
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, Q⟩)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (by simpa using h)
    simp at this
  have hsm_inj : ∀ i Q i' Q', M.sm i Q = M.sm i' Q' →
      (⟨i, Q⟩ : Σ j, {q : Place (IsLocalRing.ResidueField ↥A) (Fbar j) // q ∉ (C j).nodes}) = ⟨i', Q'⟩ := by
    intro i Q i' Q' h
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, Q⟩)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i', Q'⟩)))) (by simpa using h)
    simpa using this
  have hnd_inj : ∀ e e', M.nd e = M.nd e' → e = e' := by
    intro e e' h
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e')))) (by simpa using h)
    simpa using this

  have hlift : ∀ (P' : Place L F) (z : M.X), M.toBase.base z = IsLocalRing.closedPoint ↥A →
      π.base (M.pt P') ⤳ π.base z → M.pt P' ⤳ z := by
    intro P' z hz hspec
    rw [specializes_iff_mem_closure] at hspec
    have h1 : π.base z ∈ closure (π.base '' {M.pt P'}) := by rwa [Set.image_singleton]
    obtain ⟨z', hz', hzz'⟩ := hcl.closure_image_subset _ h1
    have : z' = z := hfib_sp z z' hzz' hz
    rw [← this, specializes_iff_mem_closure]; exact hz'

  have hclass_sm : ∀ (i : ιV) (q : Place (IsLocalRing.ResidueField ↥A) (Fbar i)) (P P' : Place L F),
      π.base (M.pt P) = π.base (M.pt P') → P ∈ (C i).dom → (C i).placeMap P = q →
      P' ∈ (C i).dom ∧ (C i).placeMap P' = q := by
    intro i q P P' hππ hP hq
    have hspec : M.pt P ⤳ M.sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩ := M.pt_specializes_sm i P hP
    have h1 : π.base (M.pt P') ⤳ π.base (M.sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩) := by
      rw [← hππ]; exact hspec.map hcont
    have h2 := hlift P' _ (hsp_sm i _) h1
    rcases M.eq_of_pt_specializes P' _ h2 with h | ⟨i', hP', h⟩ | ⟨e, -, h⟩
    · exact absurd h (hsm_ne_pt _ _ _)
    · have h3 := hsm_inj _ _ _ _ h
      obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.mp h3
      refine ⟨hP', ?_⟩
      have h5 := Subtype.ext_iff.mp (eq_of_heq h4)
      rw [← hq]; exact h5.symm
    · exact absurd h (hsm_ne_nd _ _ _)
  have hclass_nd : ∀ (e₀ : ιE) (P P' : Place L F),
      π.base (M.pt P) = π.base (M.pt P') → P ∈ (An e₀).dom → P' ∈ (An e₀).dom := by
    intro e₀ P P' hππ hP
    have hspec : M.pt P ⤳ M.nd e₀ := M.pt_specializes_nd e₀ P hP
    have h1 : π.base (M.pt P') ⤳ π.base (M.nd e₀) := by rw [← hππ]; exact hspec.map hcont
    have h2 := hlift P' _ (hsp_nd e₀) h1
    rcases M.eq_of_pt_specializes P' _ h2 with h | ⟨i', hP', h⟩ | ⟨e, hPe, h⟩
    · exact absurd h (hnd_ne_pt _ _)
    · exact absurd h.symm (hsm_ne_nd _ _ _)
    · rw [hnd_inj _ _ h]; exact hPe

  have hsat : ∀ a (x x' : M.X), π.base x' = π.base x → x ∈ U a → x' ∈ U a := by
    intro a x x' hππ hx

    obtain ⟨s, hs⟩ := M.classify_bijective.2 x
    rcases s with _ | P | i | iQ | e
    ·
      simp only [Sum.elim_inl] at hs
      rw [← hs] at hππ hx
      rw [hfib_gen x' hππ]; exact hx
    ·
      simp only [Sum.elim_inr, Sum.elim_inl] at hs
      rw [← hs] at hππ hx
      obtain ⟨P', rfl⟩ := hfib_pt P x' hππ
      have hππ' : π.base (M.pt P) = π.base (M.pt P') := hππ.symm
      rcases hv2 a with hA | ⟨i, q, hB⟩ | ⟨e₀, hC⟩
      · rw [hA] at hx ⊢; exact (hGfib P P' hππ').mp hx
      · rw [hB] at hx ⊢
        rcases hx with ⟨hP, hq⟩ | ⟨hG, ho⟩
        · exact Or.inl (hclass_sm i q P P' hππ' hP hq)
        · exact Or.inr ⟨(hGfib P P' hππ').mp hG, (hhfib a P P' hππ').mp ho⟩
      · rw [hC] at hx ⊢
        rcases hx with hP | ⟨hG, ho⟩
        · exact Or.inl (hclass_nd e₀ P P' hππ' hP)
        · exact Or.inr ⟨(hGfib P P' hππ').mp hG, (hhfib a P P' hππ').mp ho⟩
    ·
      simp only [Sum.elim_inr, Sum.elim_inl] at hs
      rw [← hs] at hππ hx
      rw [hfib_sp _ x' hππ (M.toBase_gen i)]; exact hx
    ·
      simp only [Sum.elim_inr, Sum.elim_inl] at hs
      rw [← hs] at hππ hx
      rw [hfib_sp _ x' hππ (hsp_sm iQ.1 iQ.2)]; exact hx
    ·
      simp only [Sum.elim_inr] at hs
      rw [← hs] at hππ hx
      rw [hfib_sp _ x' hππ (hsp_nd e)]; exact hx

  let U₁ : Fin r → X₁.Opens := fun a =>
    ⟨(π.base '' ((U a : Set M.X)ᶜ))ᶜ, (hcl _ (U a).isOpen.isClosed_compl).isOpen_compl⟩
  have hmem : ∀ a (x : M.X), x ∈ U a ↔ π.base x ∈ U₁ a := by
    intro a x
    constructor
    · intro hx
      show π.base x ∈ (π.base '' ((U a : Set M.X)ᶜ))ᶜ
      rintro ⟨x', hx', hππ⟩
      exact hx' (hsat a x x' hππ hx)
    · intro hx
      by_contra hxU
      exact hx ⟨x, hxU, rfl⟩
  refine ⟨U₁, ?_, hmem⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : x ∈ (⨆ a, U a) := by rw [hU]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, (hmem a x).mp ha⟩

end S_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated (solution)
