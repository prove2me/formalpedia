-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ad369367-d47f-5968-acf6-4c399206f161

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (hconn : _root_.IsPreconnected (M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A}))
    (k : ℕ) (g : F) (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (c : ιV → L) (hc0 : ∀ i, c i ≠ 0)
    (hcunit : ∀ i a, M.gen i ∈ U a →
      c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (hcslope : ∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e'))) :
    ∃ c₀ : L, c₀ ≠ 0 ∧ (c₀ = 1 ∨ ∃ i₀, c₀ = c i₀) ∧ ∀ i a, M.gen i ∈ U a →
      c₀ • (g / h a ^ k) ∈ (C i).integers ∧ (c₀ • (g / h a ^ k))⁻¹ ∈ (C i).integers := by
  classical

  by_cases hne : Nonempty ιV
  swap
  · refine ⟨1, one_ne_zero, Or.inl rfl, fun i => (hne ⟨i⟩).elim⟩
  obtain ⟨i₀⟩ := hne

  have hcontB : Continuous M.toBase.base := M.toBase.continuous
  set Z : Set M.X := M.toBase.base ⁻¹' {IsLocalRing.closedPoint ↥A} with hZ
  have hinj := M.classify_bijective.1

  have hgen_inj : ∀ i j, M.gen i = M.gen j → i = j := by
    intro i j hij
    have := @hinj (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inl j))) (by simpa using hij)
    simpa using this
  have hgen_ne_sm : ∀ i j Q, M.gen i ≠ M.sm j Q := by
    intro i j Q hh
    have := @hinj (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, Q⟩)))) (by simpa using hh)
    simp at this
  have hgen_ne_nd : ∀ i e, M.gen i ≠ M.nd e := by
    intro i e hh
    have := @hinj (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (by simpa using hh)
    simp at this
  have hsm_ne_nd : ∀ i Q e, M.sm i Q ≠ M.nd e := by
    intro i Q e hh
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, Q⟩)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (by simpa using hh)
    simp at this
  have hsm_inj : ∀ i Q i' Q', M.sm i Q = M.sm i' Q' → i = i' := by
    intro i Q i' Q' hh
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, Q⟩)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i', Q'⟩)))) (by simpa using hh)
    have h2 : (⟨i, Q⟩ : Σ j, {q : Place (IsLocalRing.ResidueField ↥A) (Fbar j) // q ∉ (C j).nodes}) = ⟨i', Q'⟩ := by
      simpa using this
    exact congrArg Sigma.fst h2
  have hnd_inj : ∀ e e', M.nd e = M.nd e' → e = e' := by
    intro e e' hh
    have := @hinj (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))) (Sum.inr (Sum.inr (Sum.inr (Sum.inr e')))) (by simpa using hh)
    simpa using this

  have hkey : ∀ i j (x : M.X), M.gen i ⤳ x → M.gen j ⤳ x → A.valuation (c i) = A.valuation (c j) := by
    intro i j x hi hj
    rcases M.eq_of_gen_specializes i x hi with hx | ⟨Q, hx⟩ | ⟨e, hei, hx⟩
    · rcases M.eq_of_gen_specializes j x hj with hx' | ⟨Q', hx'⟩ | ⟨e', hej, hx'⟩
      · rw [hgen_inj i j (hx.symm.trans hx')]
      · exact absurd (hx.symm.trans hx') (hgen_ne_sm i j Q')
      · exact absurd (hx.symm.trans hx') (hgen_ne_nd i e')
    · rcases M.eq_of_gen_specializes j x hj with hx' | ⟨Q', hx'⟩ | ⟨e', hej, hx'⟩
      · exact absurd (hx'.symm.trans hx) (hgen_ne_sm j i Q)
      · rw [hsm_inj i Q j Q' (hx.symm.trans hx')]
      · exact absurd (hx.symm.trans hx') (hsm_ne_nd i Q e')
    · rcases M.eq_of_gen_specializes j x hj with hx' | ⟨Q', hx'⟩ | ⟨e', hej, hx'⟩
      · exact absurd (hx'.symm.trans hx) (hgen_ne_nd j e)
      · exact absurd (hx'.symm.trans hx) (hsm_ne_nd j Q' e)
      · have hee : e = e' := hnd_inj e e' (hx.symm.trans hx')
        subst hee
        have hs := hcslope e
        rcases hei with rfl | rfl <;> rcases hej with rfl | rfl
        · rfl
        · exact hs
        · exact hs.symm
        · rfl

  have hall : ∀ j, A.valuation (c j) = A.valuation (c i₀) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨j₀, hj₀⟩ := hnot

    have hAtop : A ≠ ⊤ := by
      intro htop
      apply hj₀
      have h1 : ∀ x : L, x ≠ 0 → A.valuation x = 1 := by
        intro x hx
        apply le_antisymm ((A.valuation_le_one_iff x).mpr (htop.symm ▸ ValuationSubring.mem_top x))
        have h2 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr (htop.symm ▸ ValuationSubring.mem_top _)
        rw [map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hx).symm)] at h2
        exact h2
      rw [h1 _ (hc0 j₀), h1 _ (hc0 i₀)]
    have hmax_ne_bot : IsLocalRing.maximalIdeal ↥A ≠ ⊥ := by
      intro hbot
      apply hAtop

      by_contra hne'
      exact (ValuationSubring.not_isField_of_ne_top L hne') (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)

    have hZspecial : ∀ x ∈ Z, ∃ i, M.gen i ⤳ x := by
      intro x hx
      have hx' : M.toBase.base x = IsLocalRing.closedPoint ↥A := hx
      obtain ⟨s, hs⟩ := M.classify_bijective.2 x
      rcases s with _ | P | i | iQ | e
      ·
        exfalso
        simp only [Sum.elim_inl] at hs
        have hgm : GeneralizingMap M.toBase.base := AlgebraicGeometry.Flat.generalizingMap M.toBase
        let η : Spec (CommRingCat.of ↥A) := ⟨⊥, Ideal.bot_prime⟩
        have hη : η ⤳ M.toBase.base x :=
          (PrimeSpectrum.le_iff_specializes _ _).mp (fun z hz => by
            have : z = 0 := hz
            rw [this]; exact Ideal.zero_mem _)
        obtain ⟨x', hx'x, hfx'⟩ := hgm hη
        have hxgen : x' = x := by
          rw [← hs] at hx'x ⊢
          exact (hx'x.antisymm (genericPoint_specializes x')).eq
        rw [hxgen, hx'] at hfx'
        apply hmax_ne_bot
        have h5 : (IsLocalRing.closedPoint ↥A).asIdeal = η.asIdeal := congrArg PrimeSpectrum.asIdeal hfx'
        exact h5
      · exfalso
        simp only [Sum.elim_inr, Sum.elim_inl] at hs
        have h3 : (M.toBase.base x).asIdeal = ⊥ := by rw [← hs]; exact M.toBase_pt P
        rw [hx'] at h3
        exact hmax_ne_bot h3
      · exact ⟨i, by simp only [Sum.elim_inr, Sum.elim_inl] at hs; rw [← hs]⟩
      · exact ⟨iQ.1, by simp only [Sum.elim_inr, Sum.elim_inl] at hs; rw [← hs]; exact M.gen_specializes_sm iQ.1 iQ.2⟩
      · exact ⟨src e, by simp only [Sum.elim_inr] at hs; rw [← hs]; exact (M.gen_specializes_nd e).1⟩

    set S : Set M.X := ⋃ i ∈ ({i | A.valuation (c i) = A.valuation (c i₀)} : Set ιV), closure {M.gen i} with hS
    set T : Set M.X := ⋃ i ∈ ({i | A.valuation (c i) ≠ A.valuation (c i₀)} : Set ιV), closure {M.gen i} with hT
    have hSc : IsClosed S := (Set.toFinite _).isClosed_biUnion fun i _ => isClosed_closure
    have hTc : IsClosed T := (Set.toFinite _).isClosed_biUnion fun i _ => isClosed_closure
    have hcov : Z ⊆ S ∪ T := by
      intro x hx
      obtain ⟨i, hi⟩ := hZspecial x hx
      by_cases hgi : A.valuation (c i) = A.valuation (c i₀)
      · left; rw [hS]; exact Set.mem_biUnion (show i ∈ {i | _} from hgi) (specializes_iff_mem_closure.mp hi)
      · right; rw [hT]; exact Set.mem_biUnion (show i ∈ {i | _} from hgi) (specializes_iff_mem_closure.mp hi)
    have hgenZ : ∀ i, M.gen i ∈ Z := fun i => M.toBase_gen i
    have hZS : (Z ∩ S).Nonempty := ⟨M.gen i₀, hgenZ i₀, by
      rw [hS]; exact Set.mem_biUnion (show i₀ ∈ {i | A.valuation (c i) = A.valuation (c i₀)} from rfl) (subset_closure rfl)⟩
    have hZT : (Z ∩ T).Nonempty := ⟨M.gen j₀, hgenZ j₀, by
      rw [hT]; exact Set.mem_biUnion (show j₀ ∈ {i | A.valuation (c i) ≠ A.valuation (c i₀)} from hj₀) (subset_closure rfl)⟩
    obtain ⟨x, hxZ, hxS, hxT⟩ := isPreconnected_closed_iff.mp hconn S T hSc hTc hcov hZS hZT
    rw [hS] at hxS; rw [hT] at hxT
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxS
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxT
    apply hj
    rw [← hkey i j x (specializes_iff_mem_closure.mpr hxi) (specializes_iff_mem_closure.mpr hxj)]
    exact hi

  refine ⟨c i₀, hc0 i₀, Or.inr ⟨i₀, rfl⟩, fun i a ha => ?_⟩
  obtain ⟨hu, hu'⟩ := hcunit i a ha

  have hval : A.valuation (c i₀ / c i) = 1 := by
    rw [map_div₀, hall i, div_self ((map_ne_zero A.valuation).mpr (hc0 i₀))]
  have hval' : A.valuation (c i / c i₀) = 1 := by
    rw [map_div₀, hall i, div_self ((map_ne_zero A.valuation).mpr (hc0 i₀))]
  have huA : algebraMap L F (c i₀ / c i) ∈ (C i).integers :=
    ((C i).algebraMap_mem_iff _).mpr ((A.valuation_le_one_iff _).mp hval.le)
  have huA' : algebraMap L F (c i / c i₀) ∈ (C i).integers :=
    ((C i).algebraMap_mem_iff _).mpr ((A.valuation_le_one_iff _).mp hval'.le)
  have hci : algebraMap L F (c i) ≠ 0 := (map_ne_zero _).mpr (hc0 i)
  have hci₀ : algebraMap L F (c i₀) ≠ 0 := (map_ne_zero _).mpr (hc0 i₀)
  constructor
  · have : c i₀ • (g / h a ^ k) = algebraMap L F (c i₀ / c i) * (c i • (g / h a ^ k)) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_div₀]
      field_simp
    rw [this]; exact mul_mem huA hu
  · have : (c i₀ • (g / h a ^ k))⁻¹ = algebraMap L F (c i / c i₀) * (c i • (g / h a ^ k))⁻¹ := by
      rw [Algebra.smul_def, Algebra.smul_def, map_div₀, mul_inv, mul_inv]
      field_simp
    rw [this]; exact mul_mem huA' hu'

end S_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_exists_smul_div_pow_mem_integers_of_isPreconnected_of_fintype_mem_range (solution)
