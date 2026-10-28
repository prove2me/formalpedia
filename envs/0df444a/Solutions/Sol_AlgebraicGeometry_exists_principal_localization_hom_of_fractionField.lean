-- Prove2me | solution 1 for AlgebraicGeometry.exists_principal_localization_hom_of_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T15:02:39.649926+00:00
-- url     : https://prove2.me/submissions/23407402-fe15-45e5-bf82-66db1cfa0c82

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PhilipponGenericMorphismCoefficients


/-- A finitely generated base subalgebra of a fraction field is defined on
one principal open of any given affine model. The factorization uses the
actual field, not an abstractly isomorphic field. -/
lemma factor_fg_base_subalgebra
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (A : Subalgebra B E) (hA : A.FG) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (φ : A →ₐ[B] Localization.Away s),
          γ.comp φ = A.val := by
  classical
  obtain ⟨T, hT⟩ := hA
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors B) T
  have hs0 : (s : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  let γ : Localization.Away (s : B) →ₐ[B] E :=
    IsLocalization.Away.liftAlgHom (s : B)
      (f := Algebra.ofId B E)
      (isUnit_iff_ne_zero.mpr (by
        change algebraMap B E (s : B) ≠ 0
        simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0))
  have hγbase (b : B) : γ (algebraMap B (Localization.Away (s : B)) b) =
      algebraMap B E b := γ.commutes b
  have hM : Submonoid.powers (s : B) ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := by simpa only [Algebra.smul_def] using hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs0)
  have hγ : Function.Injective γ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (s : B)) γ.toRingHom).mpr
    intro x y
    change algebraMap B (Localization.Away (s : B)) x = _ ↔
      γ (algebraMap B (Localization.Away (s : B)) x) =
        γ (algebraMap B (Localization.Away (s : B)) y)
    rw [hγbase, hγbase]
    exact (IsLocalization.injective _ hM).eq_iff.trans
      (IsFractionRing.injective B E).eq_iff.symm
  have hTA : A ≤ γ.range := by
    rw [← hT]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨b, hb⟩ := hs x hx
    have hb' : algebraMap B E b = algebraMap B E s * x := by simpa only [Algebra.smul_def] using hb
    refine ⟨algebraMap B (Localization.Away (s : B)) b *
      IsLocalization.Away.invSelf (s : B), ?_⟩
    change γ (_ * _) = x
    apply mul_left_cancel₀ (show algebraMap B E s ≠ 0 by
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0)
    rw [map_mul, hγbase, hb']
    calc
      algebraMap B E s * (algebraMap B E s * x * γ (IsLocalization.Away.invSelf (s : B))) =
          (algebraMap B E s * x) * γ (algebraMap B (Localization.Away (s : B)) s *
            IsLocalization.Away.invSelf (s : B)) := by rw [map_mul, hγbase]; ring
      _ = algebraMap B E s * x := by
        rw [IsLocalization.Away.mul_invSelf, map_one]
        simp
  let e := AlgEquiv.ofInjective γ hγ
  let φ : A →ₐ[B] Localization.Away (s : B) :=
    e.symm.toAlgHom.comp (Subalgebra.inclusion hTA)
  refine ⟨s, hs0, γ, hγ, φ, ?_⟩
  ext x
  change γ (e.symm (Subalgebra.inclusion hTA x)) = (x : E)
  have he := congrArg (fun z : γ.range => (z : E))
    (e.apply_symm_apply (Subalgebra.inclusion hTA x))
  exact (AlgEquiv.ofInjective_apply γ hγ _).symm.trans he


end PhilipponGenericMorphismCoefficients


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PhilipponGenericMorphismSpread

/-- Canonical comparison of two pullbacks with compatible base maps. -/
def changeBase {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    pullback f a ⟶ pullback f b :=
  pullback.lift (pullback.fst f a) (pullback.snd f a ≫ c)
    (by rw [Category.assoc, hc]; exact pullback.condition)

@[reassoc (attr := simp)] lemma changeBase_fst {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.fst f b = pullback.fst f a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] lemma changeBase_snd {X S T U : Scheme.{u}} (f : X ⟶ S)
    (a : T ⟶ S) (b : U ⟶ S) (c : T ⟶ U) (hc : c ≫ b = a) :
    changeBase f a b c hc ≫ pullback.snd f b = pullback.snd f a ≫ c :=
  pullback.lift_snd _ _ _

/-- A morphism of generic fibres spreads over a principal localization of
the prescribed affine base, with exact recovery over the actual field. -/
theorem exists_hom_of_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by
  classical
  obtain ⟨T, hT, _hcontains, gT, hgT, hrec⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      f₁ f₂ g hg ∅
  obtain ⟨s, hs, γ, hγ, φ, hφ⟩ :=
    PhilipponGenericMorphismCoefficients.factor_fg_base_subalgebra B E T hT
  let A := Localization.Away s
  let bE := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let bT := Spec.map (CommRingCat.ofHom (algebraMap B T))
  let bA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let c : Spec (.of A) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let d : Spec (.of E) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom γ.toRingHom)
  let e : Spec (.of E) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom T.val.toRingHom)
  have hc : c ≫ bT = bA := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    exact φ.comp_algebraMap
  have hd : d ≫ c = e := by
    dsimp only [d, c, e]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h))
      (congrArg AlgHom.toRingHom hφ)
  let t₁ := changeBase f₁ bA bT c hc
  let t₂ := changeBase f₂ bA bT c hc
  let u := t₁ ≫ gT
  have hu : (u ≫ pullback.fst f₂ bT) ≫ f₂ = pullback.snd f₁ bA ≫ bA := by
    dsimp only [u]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc gT,
      hgT, changeBase_snd_assoc, hc]
  let gA : pullback f₁ bA ⟶ pullback f₂ bA :=
    pullback.lift (u ≫ pullback.fst f₂ bT) (pullback.snd f₁ bA) hu
  have hgA : gA ≫ pullback.snd f₂ bA = pullback.snd f₁ bA :=
    pullback.lift_snd _ _ _
  refine ⟨s, hs, γ, hγ, gA, hgA, ?_⟩
  intro q₁ q₂ hq₁f hq₁s hq₂f hq₂s
  have H := hrec (q₁ ≫ t₁) (q₂ ≫ t₂)
    (by rw [Category.assoc, changeBase_fst]; exact hq₁f)
    (by rw [Category.assoc, changeBase_snd, ← Category.assoc, hq₁s, Category.assoc, hd])
    (by rw [Category.assoc, changeBase_fst]; exact hq₂f)
    (by rw [Category.assoc, changeBase_snd, ← Category.assoc, hq₂s, Category.assoc, hd])
  apply pullback.hom_ext
  · dsimp only [gA]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
    have H' := congrArg (fun h => h ≫ pullback.fst f₂ bT) H
    have hq₂f' : q₂ ≫ pullback.fst f₂ bA = pullback.fst f₂ bE := hq₂f
    simpa only [Category.assoc, t₂, changeBase_fst, hq₂f', hq₂f, u, t₁] using H'
  · rw [Category.assoc, hgA, Category.assoc, hq₂s, ← Category.assoc, hg]
    exact hq₁s

end PhilipponGenericMorphismSpread

theorem solution
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by
  exact PhilipponGenericMorphismSpread.exists_hom_of_fractionField B E f₁ f₂ g hg
