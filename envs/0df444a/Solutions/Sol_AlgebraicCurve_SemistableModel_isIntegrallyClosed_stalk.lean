-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e66f2615-a9e2-5a5f-8cdd-c76cb38b351b

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem NormX.mem_of_isIntegral_of_le {F : Type u'} [Field F] (R : Subring F) (V : ValuationSubring F)
    (hRV : R ≤ V.toSubring) (y : F) (hy : IsIntegral R y) : y ∈ V := by
  have hV : V.valuation.Integers V :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => V.valuation_le_one a
      exists_of_le_one := fun r hr => ⟨⟨r, (V.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  rw [← V.valuation_le_one_iff, ← hV.isIntegral_iff_v_le_one]
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (Subring.inclusion hRV), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  convert hpy using 2
  rfl

theorem solution
    {L : Type u} [Field L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (x : M.X) :
    IsIntegrallyClosed (M.X.presheaf.stalk x) := by
  classical

  by_cases hgen : x = genericPoint M.X
  · subst hgen
    exact Field.instIsIntegrallyClosed _

  let K := M.X.functionField
  let θ : M.X.presheaf.stalk x →+* F := (M.ffEquiv.symm : K ≃+* F).toRingHom.comp (algebraMap _ K)
  have hθ : SemistableModel.localRing M.X M.ffEquiv x = θ.range := rfl

  suffices H : ∀ y : F, IsIntegral θ.range y → y ∈ θ.range by
    rw [isIntegrallyClosed_iff K]
    intro k hk
    have hk' : IsIntegral θ.range ((M.ffEquiv.symm : K ≃+* F) k) := by
      obtain ⟨p, hp, hpk⟩ := hk
      refine ⟨p.map θ.rangeRestrict, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hc : (algebraMap θ.range F).comp θ.rangeRestrict =
          (M.ffEquiv.symm : K ≃+* F).toRingHom.comp (algebraMap _ K) := by
        ext; rfl
      rw [hc]
      change Polynomial.eval₂ _ ((M.ffEquiv.symm : K ≃+* F).toRingHom k) p = 0
      rw [← Polynomial.hom_eval₂, hpk, map_zero]
    obtain ⟨o, ho⟩ := (RingHom.mem_range).mp (H _ hk')
    refine ⟨o, ?_⟩
    apply (M.ffEquiv.symm : K ≃+* F).injective
    exact ho.symm ▸ rfl

  obtain ⟨c, hc⟩ := M.classify_bijective.surjective x
  rcases c with u | P | i | iQ | e
  · exact absurd hc.symm hgen
  ·
    simp only [Sum.elim_inr, Sum.elim_inl] at hc
    subst hc
    have hR : θ.range = P.toValuationSubring.toSubring := hθ ▸ M.localRing_pt P
    intro y hy
    rw [hR]
    exact NormX.mem_of_isIntegral_of_le _ _ hR.le y hy
  ·
    simp only [Sum.elim_inr, Sum.elim_inl] at hc
    subst hc
    have hR : θ.range = (C i).integers.toSubring := hθ ▸ M.localRing_gen i
    intro y hy
    rw [hR]
    exact NormX.mem_of_isIntegral_of_le _ _ hR.le y hy
  ·
    obtain ⟨i, Q⟩ := iQ
    simp only [Sum.elim_inr, Sum.elim_inl] at hc
    subst hc
    intro y hy
    show y ∈ SemistableModel.localRing M.X M.ffEquiv (M.sm i Q)
    rw [M.localRing_sm]
    refine ⟨NormX.mem_of_isIntegral_of_le _ _ (fun f hf => ((M.localRing_sm i Q f).mp (hθ ▸ hf)).1) y hy, ?_⟩
    intro P hP hPQ
    exact NormX.mem_of_isIntegral_of_le _ _ (fun f hf => ((M.localRing_sm i Q f).mp (hθ ▸ hf)).2 P hP hPQ) y hy
  ·
    simp only [Sum.elim_inr] at hc
    subst hc
    intro y hy
    show y ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd e)
    rw [M.localRing_nd]
    refine ⟨NormX.mem_of_isIntegral_of_le _ _ (fun f hf => ((M.localRing_nd e f).mp (hθ ▸ hf)).1) y hy,
      NormX.mem_of_isIntegral_of_le _ _ (fun f hf => ((M.localRing_nd e f).mp (hθ ▸ hf)).2.1) y hy, ?_⟩
    intro P hP
    exact NormX.mem_of_isIntegral_of_le _ _ (fun f hf => ((M.localRing_nd e f).mp (hθ ▸ hf)).2.2 P hP) y hy

end S_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk (solution)
