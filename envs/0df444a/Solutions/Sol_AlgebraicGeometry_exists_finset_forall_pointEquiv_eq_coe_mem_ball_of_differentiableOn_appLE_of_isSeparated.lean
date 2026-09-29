-- Prove2me | solution 1 for AlgebraicGeometry.exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e8b819e0-db6a-5509-8d0f-13620608910a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

open Filter

namespace TorusNbhd

noncomputable def val {G : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ G) (U : G.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (s : Γ(G, U)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((p.appLE U ⊤ h) s)

theorem val_map {G : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ G) {U U' : G.Opens} (hle : U ≤ U')
    (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ p ⁻¹ᵁ U') (s : Γ(G, U')) :
    val p U h (G.presheaf.map (homOfLE hle).op s) = val p U' h' s := by
  unfold val
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end TorusNbhd

namespace TorusNbhd

theorem top_le_preimage_iff {Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ q ⁻¹ᵁ U ↔ q.base (IsLocalRing.closedPoint ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ (IsLocalRing.closedPoint ℂ))
  · intro h p _
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact h

theorem val_zero {G : Scheme.{0}} (p : Spec (CommRingCat.of ℂ) ⟶ G) (U : G.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    val p U h 0 = 0 := by
  unfold val; rw [map_zero, map_zero]

end TorusNbhd

set_option maxHeartbeats 4000000 in
open TorusNbhd in
theorem solution
    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} [IsSeparated f] {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (hL1 : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀))
    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ))) :
    ∀ (v₀ : Fin g → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G.Opens) (fs : Finset (Γ(G, U))) (ε : ℝ) (h₀ : ⊤ ≤ (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e P = (w : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
  intro v₀ r hr
  classical

  set π : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f := fun v => e.symm (v : ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)) with hπ

  set 𝒮 : Set (Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)) :=
    {S | ∃ (U : G.Opens) (φ : Γ(G, U)) (c : ℂ) (ε : ℝ),
      S = {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ U, ‖val P.1 U h φ - c‖ < ε}} with h𝒮
  letI τ : TopologicalSpace (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) := TopologicalSpace.generateFrom 𝒮
  have hbasic : ∀ (U : G.Opens) (φ : Γ(G, U)) (c : ℂ) (ε : ℝ),
      IsOpen {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ U, ‖val P.1 U h φ - c‖ < ε} :=
    fun U φ c ε => TopologicalSpace.GenerateOpen.basic _ ⟨U, φ, c, ε, rfl⟩

  have hπc : Continuous π := by
    refine continuous_generateFrom_iff.2 ?_
    rintro S ⟨U, φ, c, ε, rfl⟩
    obtain ⟨hDopen, F, hFd, hFval⟩ := hAN U φ
    have hset : π ⁻¹' {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ U, ‖val P.1 U h φ - c‖ < ε} =
        {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∩ F ⁻¹' Metric.ball c ε := by
      ext v
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm, hπ]
      constructor
      · rintro ⟨h, hlt⟩
        refine ⟨h, ?_⟩
        rw [hFval v h]; exact hlt
      · rintro ⟨h, hlt⟩
        refine ⟨h, ?_⟩
        rw [hFval v h] at hlt; exact hlt
    rw [hset]
    exact hFd.continuousOn.isOpen_inter_preimage hDopen Metric.isOpen_ball

  have hē : Continuous (fun t : ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) => e.symm t) := by
    rw [(QuotientAddGroup.isQuotientMap_mk (Λ.toAddSubgroup)).continuous_iff]
    exact hπc

  obtain ⟨b₀, hb₀⟩ := hL1
  haveI : CompactSpace ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
    have hbdd : Bornology.IsBounded (ZSpan.fundamentalDomain b₀) := ZSpan.fundamentalDomain_isBounded b₀
    have hK : IsCompact (closure (ZSpan.fundamentalDomain b₀)) := hbdd.isCompact_closure
    have himg : IsCompact ((QuotientAddGroup.mk : (Fin g → ℂ) → ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)) '' closure (ZSpan.fundamentalDomain b₀)) :=
      hK.image continuous_quot_mk
    refine ⟨?_⟩
    refine himg.of_isClosed_subset isClosed_univ ?_
    intro t _
    induction t using QuotientAddGroup.induction_on with
    | H v =>
      refine ⟨ZSpan.fract b₀ v, subset_closure (ZSpan.fract_mem_fundamentalDomain b₀ v), ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have : ZSpan.fract b₀ v - v = -((ZSpan.floor b₀ v : Fin g → ℂ)) := by
        rw [ZSpan.fract_apply]; abel
      rw [this]
      refine neg_mem ?_
      show ((ZSpan.floor b₀ v : Submodule.span ℤ (Set.range b₀)) : Fin g → ℂ) ∈ Λ.toAddSubgroup
      rw [hb₀]
      exact (ZSpan.floor b₀ v).2

  haveI : T2Space (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) := by
    refine ⟨fun x y hxy => ?_⟩
    obtain ⟨U, V, hx, hy, fsU, fsV, ε, hε, hsep⟩ := AlgebraicGeometry.exists_finset_forall_norm_appLE_sub_lt_imp_false_of_ne_of_isSeparated x y hxy
    set Ox : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :=
      {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ U, ∀ φ ∈ fsU, ‖val P.1 U h φ - val x.1 U hx φ‖ < ε} with hOx
    set Oy : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :=
      {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ V, ∀ ψ ∈ fsV, ‖val P.1 V h ψ - val y.1 V hy ψ‖ < ε} with hOy
    have hopen : ∀ (W : G.Opens) (fs : Finset (Γ(G, W))) (cf : Γ(G, W) → ℂ),
        IsOpen {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ W, ∀ φ ∈ fs, ‖val P.1 W h φ - cf φ‖ < ε} := by
      intro W fs cf
      have : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ W, ∀ φ ∈ fs, ‖val P.1 W h φ - cf φ‖ < ε} =
          {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ W, ‖val P.1 W h 0 - 0‖ < 1} ∩
            ⋂ φ ∈ fs, {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ W, ‖val P.1 W h φ - cf φ‖ < ε} := by
        ext P
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · rintro ⟨h, hall⟩
          exact ⟨⟨h, by rw [val_zero, sub_zero, norm_zero]; exact one_pos⟩, fun φ hφ => ⟨h, hall φ hφ⟩⟩
        · rintro ⟨⟨h, -⟩, hall⟩
          exact ⟨h, fun φ hφ => by obtain ⟨h', hh'⟩ := hall φ hφ; exact hh'⟩
      rw [this]
      exact (hbasic W 0 0 1).inter (isOpen_biInter_finset fun φ _ => hbasic W φ (cf φ) ε)
    refine ⟨Ox, Oy, hopen U fsU (fun φ => val x.1 U hx φ), hopen V fsV (fun ψ => val y.1 V hy ψ), ?_, ?_, ?_⟩
    · exact ⟨hx, fun φ _ => by rw [sub_self, norm_zero]; exact hε⟩
    · exact ⟨hy, fun ψ _ => by rw [sub_self, norm_zero]; exact hε⟩
    · rw [Set.disjoint_left]
      rintro P ⟨hPU, hPU'⟩ ⟨hPV, hPV'⟩
      exact hsep P hPU hPV hPU' hPV'

  have hopenmap : IsOpenMap (fun t : ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) => e.symm t) :=
    (Continuous.homeoOfEquivCompactToT2 (f := e.symm) hē).isOpenMap

  set W : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) :=
    (fun t : ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) => e.symm t) '' ((QuotientAddGroup.mk : (Fin g → ℂ) → ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)) '' Metric.ball v₀ r) with hW
  have hWopen : IsOpen W := hopenmap _ (QuotientAddGroup.isOpenMap_coe _ Metric.isOpen_ball)
  have hx0W : π v₀ ∈ W := ⟨(v₀ : ((Fin g → ℂ) ⧸ Λ.toAddSubgroup)), ⟨v₀, Metric.mem_ball_self hr, rfl⟩, rfl⟩

  have hbasis := TopologicalSpace.isTopologicalBasis_of_subbasis (t := τ) (s := 𝒮) rfl
  obtain ⟨Wb, ⟨Fam, ⟨hFfin, hFsub⟩, rfl⟩, hx0, hWb⟩ := hbasis.exists_subset_of_mem_open hx0W hWopen
  haveI : Fintype ↑Fam := hFfin.fintype
  have hdata : ∀ S : ↑Fam, ∃ (U : G.Opens) (φ : Γ(G, U)) (c : ℂ) (ε : ℝ),
      (S.1 : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)) = {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f | ∃ h : ⊤ ≤ P.1 ⁻¹ᵁ U, ‖val P.1 U h φ - c‖ < ε} := fun S => hFsub S.2
  choose Uo φo co εo hSo using hdata

  have hx0S : ∀ S : ↑Fam, ∃ h : ⊤ ≤ (π v₀).1 ⁻¹ᵁ Uo S, ‖val (π v₀).1 (Uo S) h (φo S) - co S‖ < εo S := by
    intro S
    have : π v₀ ∈ (S.1 : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)) := hx0 S.1 S.2
    rw [hSo S] at this
    exact this

  set U : G.Opens := Finset.univ.inf Uo with hU
  have hUle : ∀ S : ↑Fam, U ≤ Uo S := fun S => Finset.inf_le (Finset.mem_univ S)
  have hmemU : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ G), (∀ S : ↑Fam, ⊤ ≤ q ⁻¹ᵁ Uo S) → ⊤ ≤ q ⁻¹ᵁ U := by
    intro q hq
    rw [top_le_preimage_iff]
    show q.base (IsLocalRing.closedPoint ℂ) ∈ ((Finset.univ.inf Uo : G.Opens) : Set G)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simp only [Set.mem_iInter, Function.comp_apply]
    intro S _
    exact (top_le_preimage_iff q (Uo S)).1 (hq S)
  have h₀ : ⊤ ≤ (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U := hmemU _ fun S => (hx0S S).1
  set res : (S : ↑Fam) → Γ(G, U) := fun S => G.presheaf.map (homOfLE (hUle S)).op (φo S) with hres
  set fs : Finset (Γ(G, U)) := Finset.univ.image res with hfs
  set δ : ↑Fam → ℝ := fun S => εo S - ‖val (π v₀).1 (Uo S) (hx0S S).1 (φo S) - co S‖ with hδ
  have hδpos : ∀ S, 0 < δ S := fun S => by have := (hx0S S).2; simp only [hδ]; linarith
  obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ S : ↑Fam, ε ≤ δ S := by
    by_cases hne : Nonempty ↑Fam
    · obtain ⟨S₀, hS₀⟩ := Finite.exists_min δ
      exact ⟨δ S₀, hδpos S₀, hS₀⟩
    · exact ⟨1, one_pos, fun S => (hne ⟨S⟩).elim⟩
  refine ⟨U, fs, ε, h₀, hεpos, ?_⟩
  intro P hP hclose

  have hPS : ∀ S : ↑Fam, P ∈ (S.1 : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)) := by
    intro S
    rw [hSo S]
    have hPU : ⊤ ≤ P.1 ⁻¹ᵁ Uo S := by
      rw [top_le_preimage_iff]; exact hUle S ((top_le_preimage_iff _ _).1 hP)
    refine ⟨hPU, ?_⟩
    have h1' := hclose (res S) (Finset.mem_image_of_mem _ (Finset.mem_univ S))
    have h1 : ‖val P.1 U hP (G.presheaf.map (homOfLE (hUle S)).op (φo S)) -
        val (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 U h₀ (G.presheaf.map (homOfLE (hUle S)).op (φo S))‖ < ε := h1'
    rw [val_map P.1 (hUle S) hP hPU, val_map _ (hUle S) h₀ (hx0S S).1] at h1
    have h2 := hεle S
    simp only [hδ] at h2
    calc ‖val P.1 (Uo S) hPU (φo S) - co S‖
        ≤ ‖val P.1 (Uo S) hPU (φo S) - val (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 (Uo S) (hx0S S).1 (φo S)‖ +
          ‖val (e.symm (v₀ : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 (Uo S) (hx0S S).1 (φo S) - co S‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < εo S := by linarith
  have hPW : P ∈ W := hWb (Set.mem_sInter.2 fun S hS => hPS ⟨S, hS⟩)
  obtain ⟨t, ⟨w, hw, rfl⟩, hPt⟩ := hPW
  exact ⟨w, hw, by rw [← hPt, Equiv.apply_symm_apply]⟩

end S_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_exists_finset_forall_pointEquiv_eq_coe_mem_ball_of_differentiableOn_appLE_of_isSeparated (solution)
