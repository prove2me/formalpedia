-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2533b94b-ee81-5cfb-8040-1b174fed103e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul
import Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

noncomputable section

namespace TgTpow

variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

abbrev H (M₁ M₂ : A.Modules) : Subgroup (thetaGroup f L hc M₁ × thetaGroup f L hc M₂) :=
  MonoidHom.eqLocus
    ((thetaGroup.pt f L hc M₁).comp (MonoidHom.fst (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))
    ((thetaGroup.pt f L hc M₂).comp (MonoidHom.snd (thetaGroup f L hc M₁) (thetaGroup f L hc M₂)))

def Over {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ : C → k) : Prop :=
  ∃ α : G →* thetaGroup f L hc M, (∀ g, thetaGroup.pt f L hc M (α g) = π g) ∧
    (∀ g c, S g c → thetaGroup.IsScalarElt f L hc M (α g) (φ c))

def pairHom {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) :
    G →* H f L hc M₁ M₂ :=
  (α.prod β).codRestrict _ (fun g => show thetaGroup.pt f L hc M₁ (α g) = thetaGroup.pt f L hc M₂ (β g) by
    rw [hα, hβ])

theorem pairHom_fst {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) (g : G) :
    (pairHom f L hc M₁ M₂ π α β hα hβ g).1.1 = α g := rfl

theorem pairHom_snd {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    (α : G →* thetaGroup f L hc M₁) (β : G →* thetaGroup f L hc M₂)
    (hα : ∀ g, thetaGroup.pt f L hc M₁ (α g) = π g) (hβ : ∀ g, thetaGroup.pt f L hc M₂ (β g) = π g) (g : G) :
    (pairHom f L hc M₁ M₂ π α β hα hβ g).1.2 = β g := rfl

theorem tensor_of {G : Type} [Group G] (M₁ M₂ : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ₁ φ₂ : C → k)
    (h₁ : Over f L hc M₁ π S φ₁) (h₂ : Over f L hc M₂ π S φ₂) :
    Over f L hc (M₁ ⊗ M₂) π S (fun c => φ₁ c * φ₂ c) := by
  obtain ⟨α, hα, hαs⟩ := h₁
  obtain ⟨β, hβ, hβs⟩ := h₂
  obtain ⟨τ, τpt, τsc⟩ := thetaGroup.exists_monoidHom_tensor_pt_eq_and_isScalarElt_mul k f L hc M₁ M₂
  refine ⟨τ.comp (pairHom f L hc M₁ M₂ π α β hα hβ), fun g => ?_, fun g c hg => ?_⟩
  · rw [MonoidHom.comp_apply, τpt, pairHom_fst, hα]
  · rw [MonoidHom.comp_apply]
    exact τsc _ _ _ (hαs g c hg) (hβs g c hg)

theorem transport_of {G : Type} [Group G] (M₁ M₂ : A.Modules) (ι : M₁ ≅ M₂)
    (π : G →* Multiplicative (L.AlgPoints hc k)) {C : Type} (S : G → C → Prop) (φ : C → k)
    (h₁ : Over f L hc M₁ π S φ) : Over f L hc M₂ π S φ := by
  obtain ⟨α, hα, hαs⟩ := h₁
  obtain ⟨τ, τpt, τsc⟩ := thetaGroup.exists_mulEquiv_pt_eq_and_isScalarElt_iff_of_iso k f L hc M₁ M₂ ι
  refine ⟨τ.toMonoidHom.comp α, fun g => ?_, fun g c hg => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, τpt, hα]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (τsc _ _).1 (hαs g c hg)

theorem over_congr {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) {φ ψ : C → k} (e : ∀ c, φ c = ψ c) (h : Over f L hc M π S φ) :
    Over f L hc M π S ψ := by
  obtain ⟨α, hα, hαs⟩ := h
  exact ⟨α, hα, fun g c hg => (e c) ▸ hαs g c hg⟩

theorem tpow_succ_of {G : Type} [Group G] (M : A.Modules) (π : G →* Multiplicative (L.AlgPoints hc k))
    {C : Type} (S : G → C → Prop) (φ : C → k) (h : Over f L hc M π S φ) : ∀ n : ℕ,
    Over f L hc (Scheme.Modules.tpow M (n + 1)) π S (fun c => φ c ^ (n + 1))
  | 0 => by
      have h' : Over f L hc (𝟙_ _ ⊗ M) π S φ := transport_of f L hc M (𝟙_ _ ⊗ M) (λ_ M).symm π S φ h
      exact over_congr f L hc _ π S (fun c => (pow_one (φ c)).symm) h'
  | n + 1 => by
      have h' := tensor_of f L hc (Scheme.Modules.tpow M (n + 1)) M π S (fun c => φ c ^ (n + 1)) φ
        (tpow_succ_of M π S φ h n) h
      exact over_congr f L hc _ π S (fun c => (pow_succ (φ c) (n + 1)).symm) h'

theorem tpow_hom (M : A.Modules) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : thetaGroup f L hc M →* thetaGroup f L hc (Scheme.Modules.tpow M n),
      (∀ g, thetaGroup.pt f L hc (Scheme.Modules.tpow M n) (ρ g) = thetaGroup.pt f L hc M g) ∧
      (∀ g c, thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow M n) (ρ g) (c ^ n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact tpow_succ_of f L hc M (thetaGroup.pt f L hc M) (fun g c => thetaGroup.IsScalarElt f L hc M g c) (fun c => c)
    ⟨MonoidHom.id _, fun _ => rfl, fun _ _ hg => hg⟩ m

theorem tpow_tensor_hom (𝓜 𝓝 : A.Modules) (a b : ℕ) (hab : 1 ≤ a + b) :
    ∃ ρ : H f L hc 𝓜 𝓝 →* thetaGroup f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b),
      (∀ p, thetaGroup.pt f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) (ρ p) =
        thetaGroup.pt f L hc 𝓜 p.1.1) ∧
      (∀ p (c₁ c₂ : k), thetaGroup.IsScalarElt f L hc 𝓜 p.1.1 c₁ → thetaGroup.IsScalarElt f L hc 𝓝 p.1.2 c₂ →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) (ρ p) (c₁ ^ a * c₂ ^ b)) := by
  let π : H f L hc 𝓜 𝓝 →* Multiplicative (L.AlgPoints hc k) :=
    (thetaGroup.pt f L hc 𝓜).comp ((MonoidHom.fst _ _).comp (H f L hc 𝓜 𝓝).subtype)
  let S : H f L hc 𝓜 𝓝 → k × k → Prop := fun p c =>
    thetaGroup.IsScalarElt f L hc 𝓜 p.1.1 c.1 ∧ thetaGroup.IsScalarElt f L hc 𝓝 p.1.2 c.2
  have h𝓜 : Over f L hc 𝓜 π S (fun c => c.1) :=
    ⟨(MonoidHom.fst _ _).comp (H f L hc 𝓜 𝓝).subtype, fun _ => rfl, fun _ _ hg => hg.1⟩
  have h𝓝 : Over f L hc 𝓝 π S (fun c => c.2) :=
    ⟨(MonoidHom.snd _ _).comp (H f L hc 𝓜 𝓝).subtype, fun p => p.2.symm, fun _ _ hg => hg.2⟩

  suffices hO : Over f L hc (Scheme.Modules.tpow 𝓜 a ⊗ Scheme.Modules.tpow 𝓝 b) π S (fun c => c.1 ^ a * c.2 ^ b) by
    obtain ⟨ρ, hρ, hρs⟩ := hO
    exact ⟨ρ, hρ, fun p c₁ c₂ h₁ h₂ => hρs p (c₁, c₂) ⟨h₁, h₂⟩⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  ·
    subst ha
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hB := tpow_succ_of f L hc 𝓝 π S (fun c => c.2) h𝓝 b'
    have hT := transport_of f L hc _ (𝟙_ _ ⊗ Scheme.Modules.tpow 𝓝 (b' + 1)) (λ_ _).symm π S _ hB
    exact over_congr f L hc _ π S (fun c => by simp only [pow_zero, one_mul]) hT
  rcases Nat.eq_zero_or_pos b with hb | hb
  ·
    subst hb
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hA := tpow_succ_of f L hc 𝓜 π S (fun c => c.1) h𝓜 a'
    have hT := transport_of f L hc _ (Scheme.Modules.tpow 𝓜 (a' + 1) ⊗ 𝟙_ _) (ρ_ _).symm π S _ hA
    exact over_congr f L hc _ π S (fun c => by simp only [pow_zero, mul_one]) hT
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    exact tensor_of f L hc _ _ π S _ _ (tpow_succ_of f L hc 𝓜 π S (fun c => c.1) h𝓜 a')
      (tpow_succ_of f L hc 𝓝 π S (fun c => c.2) h𝓝 b')

end TgTpow

end

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ρ : thetaGroup f L hc M →* thetaGroup f L hc (Scheme.Modules.tpow M n),
      (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc (Scheme.Modules.tpow M n) (ρ g) = thetaGroup.pt f L hc M g) ∧
      (∀ (g : thetaGroup f L hc M) (c : k), thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (Scheme.Modules.tpow M n) (ρ g) (c ^ n)) :=
  TgTpow.tpow_hom f L hc M n hn

end S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tpow_pt_eq_and_isScalarElt_pow (solution)
