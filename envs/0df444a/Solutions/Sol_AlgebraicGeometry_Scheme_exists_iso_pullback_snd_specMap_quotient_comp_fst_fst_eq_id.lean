-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/2aa31c34-9859-59b4-afd9-f337b4c588cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (B : Type u) [CommRing B] [Algebra k B] (i : Spec (CommRingCat.of B) ⟶ A)
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (𝔪 : Ideal B) [𝔪.IsMaximal] (χ : B →ₐ[k] k) (hχ : ∀ b : B, b ∈ 𝔪 ↔ χ b = 0) :
    ∃ (Φ : A ⟶ pullback (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪))),
      IsIso Φ ∧
      Φ ≫ pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.fst f (i ≫ f) = 𝟙 A ∧
      Φ ≫ pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) ≫ pullback.snd f (i ≫ f) =
        f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ∧
      Φ ≫ pullback.snd (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)) =
        f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift 𝔪 χ.toRingHom (fun b hb => (hχ b).mp hb))) ∧
      ∀ N : (pullback f f).Modules,
        Nonempty ((Scheme.Modules.pullback Φ).obj
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (i ≫ f)) (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj
            ((Scheme.Modules.pullback
              (pullback.lift (pullback.fst f (i ≫ f)) (pullback.snd f (i ≫ f) ≫ i)
                (by rw [Category.assoc]; exact pullback.condition))).obj N)) ≅
          (Scheme.Modules.pullback
            (pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ i)
              (by rw [Category.id_comp, Category.assoc, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    show χ.toRingHom.comp (algebraMap k B) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
                    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]))).obj N) := by
  classical

  let P := pullback f (i ≫ f)
  let ϖ := pullback.snd f (i ≫ f)
  let σ := Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)
  let χ' : B ⧸ 𝔪 →+* k := Ideal.Quotient.lift 𝔪 χ.toRingHom (fun b hb => (hχ b).mp hb)

  have key : (algebraMap k (B ⧸ 𝔪)).comp χ.toRingHom = Ideal.Quotient.mk 𝔪 := by
    ext b
    change algebraMap k (B ⧸ 𝔪) (χ b) = Ideal.Quotient.mk 𝔪 b
    rw [IsScalarTower.algebraMap_apply k B (B ⧸ 𝔪), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hχ,
      map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hχ'mk : χ'.comp (Ideal.Quotient.mk 𝔪) = χ.toRingHom :=
    RingHom.ext fun b => Ideal.Quotient.lift_mk 𝔪 χ.toRingHom (fun b hb => (hχ b).mp hb)
  have hχ'alg : χ'.comp (algebraMap k (B ⧸ 𝔪)) = RingHom.id k := by
    ext x
    change χ' (algebraMap k (B ⧸ 𝔪) x) = x
    rw [IsScalarTower.algebraMap_apply k B (B ⧸ 𝔪), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk]
    exact χ.commutes x
  have halgχ' : (algebraMap k (B ⧸ 𝔪)).comp χ' = RingHom.id (B ⧸ 𝔪) := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, hχ'mk, key, RingHom.id_comp]

  have hσk : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (B ⧸ 𝔪))) := by
    show Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ 𝔪))) ≫ _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq k B (B ⧸ 𝔪)]
  have hstr : pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f) ≫ f =
      pullback.snd ϖ σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (B ⧸ 𝔪))) := by
    calc pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f) ≫ f
        = pullback.fst ϖ σ ≫ pullback.snd f (i ≫ f) ≫ (i ≫ f) := by rw [pullback.condition]
      _ = pullback.fst ϖ σ ≫ pullback.snd f (i ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) :=
          congrArg (fun t => pullback.fst ϖ σ ≫ (pullback.snd f (i ≫ f) ≫ t)) hi
      _ = (pullback.fst ϖ σ ≫ ϖ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := (Category.assoc _ _ _).symm
      _ = (pullback.snd ϖ σ ≫ σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by rw [pullback.condition]
      _ = pullback.snd ϖ σ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (B ⧸ 𝔪))) := by rw [Category.assoc, hσk]

  have h1 : 𝟙 A ≫ f = (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom)) ≫ (i ≫ f) := by
    rw [Category.id_comp, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show χ.toRingHom.comp (algebraMap k B) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
      CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let Φ₁ : A ⟶ P := pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom)) h1
  have h2 : Φ₁ ≫ ϖ = (f ≫ Spec.map (CommRingCat.ofHom χ')) ≫ σ := by
    rw [pullback.lift_snd, Category.assoc]
    congr 1
    change Spec.map _ = Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⧸ 𝔪)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.algebraMap_eq 𝔪, hχ'mk]
  let Φ : A ⟶ pullback ϖ σ := pullback.lift Φ₁ (f ≫ Spec.map (CommRingCat.ofHom χ')) h2
  have e1 : Φ ≫ pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f) = 𝟙 A := by
    rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
  have e2 : Φ ≫ pullback.fst ϖ σ ≫ pullback.snd f (i ≫ f) = f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) := by
    rw [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
  have e3 : Φ ≫ pullback.snd ϖ σ = f ≫ Spec.map (CommRingCat.ofHom χ') := pullback.lift_snd _ _ _

  let Ψ : pullback ϖ σ ⟶ A := pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f)
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.id_comp]
        show Ψ ≫ Φ ≫ pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f) = _
        rw [e1, Category.comp_id]
      · rw [Category.assoc, Category.assoc, Category.id_comp]
        show Ψ ≫ Φ ≫ pullback.fst ϖ σ ≫ pullback.snd f (i ≫ f) = _
        rw [e2]
        show (pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f)) ≫ f ≫ Spec.map _ = _
        rw [Category.assoc, ← Category.assoc (pullback.fst f (i ≫ f)), ← Category.assoc, hstr, Category.assoc,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]
        exact pullback.condition.symm
    · rw [Category.assoc, Category.id_comp, e3]
      show (pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f)) ≫ f ≫ Spec.map _ = _
      rw [Category.assoc, ← Category.assoc (pullback.fst f (i ≫ f)), ← Category.assoc, hstr, Category.assoc,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, halgχ', CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  haveI : IsIso Φ := ⟨⟨Ψ, by rw [show Φ ≫ Ψ = Φ ≫ pullback.fst ϖ σ ≫ pullback.fst f (i ≫ f) from rfl, e1], hΨΦ⟩⟩
  refine ⟨Φ, inferInstance, e1, e2, e3, fun N => ?_⟩

  have hs : (Φ ≫ pullback.fst ϖ σ) ≫ pullback.lift (pullback.fst f (i ≫ f)) (pullback.snd f (i ≫ f) ≫ i)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (𝟙 A) (f ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ i)
        (by rw [Category.id_comp, Category.assoc, Category.assoc, hi, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              show χ.toRingHom.comp (algebraMap k B) = RingHom.id k from RingHom.ext fun x => χ.commutes x,
              CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) := by
    apply pullback.hom_ext
    · simp only [Φ, Φ₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
    · simp only [Φ, Φ₁, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  exact ⟨(Scheme.Modules.pullbackComp Φ (pullback.fst ϖ σ)).app _ ≪≫
    (Scheme.Modules.pullbackComp (Φ ≫ pullback.fst ϖ σ) _).app N ≪≫ (Scheme.Modules.pullbackCongr hs).app N⟩

end S_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_iso_pullback_snd_specMap_quotient_comp_fst_fst_eq_id (solution)
