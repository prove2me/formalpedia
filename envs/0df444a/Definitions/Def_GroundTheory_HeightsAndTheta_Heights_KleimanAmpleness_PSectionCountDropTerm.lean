-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:34:27.079015+00:00
-- url     : https://prove2.me/theorems/976ff59a-2cf1-5150-88ce-a44a5c0a800e
-- title:
--   PSection Count Drop Term
-- statement:
--   Definitions and structural lemmas for PSection Count Drop Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace SectionCount.Drop.Term
section Cancel
variable {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω]
end Cancel
section Ideal
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}
end Ideal
section CechMap
variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G G' : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}
def cechZeroCocycleMap (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) :
    LinearMap.ker (Cech.d G ρ 0) →ₗ[R] LinearMap.ker (Cech.d G' ρ' 0) :=
  (Cech.mapC φ 0).restrict fun s hs => by
    rw [LinearMap.mem_ker] at hs ⊢
    rw [← Cech.mapC_d φ hφ, hs, map_zero]
def cechH0Map (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) :
    Cech.H G ρ 0 →ₗ[R] Cech.H G' ρ' 0 :=
  Submodule.mapQ _ _ (cechZeroCocycleMap φ hφ)
    (by
      intro s hs
      change (s : Cech.Cochain G 0) ∈ (⊥ : Submodule R _) at hs
      rw [Submodule.mem_bot] at hs
      change (Cech.mapC φ 0 s : Cech.Cochain G' 0) ∈ (⊥ : Submodule R _)
      rw [hs, map_zero]; exact Submodule.zero_mem _)
end CechMap
section QuotMul
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
def quotMul (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω) (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ G₁ I) →ₗ[k] (F₂.sub I ⧸ SubSystem.quotSub F₂ G₂ I) :=
  (SubSystem.quotSub F₁ G₁ I).mapQ (SubSystem.quotSub F₂ G₂ I)
    { toFun := fun y => ⟨s * y, hF I y y.2⟩
      map_add' := fun a b => Subtype.ext (mul_add s a b)
      map_smul' := fun c a => Subtype.ext (mul_smul_comm c s (a : Ω)) }
    (fun y hy => hG I y y.2 hy)
end QuotMul
section Main
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
def ampleDataOfVeryAmple (H : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hH : IsVeryAmpleBy H.toSubSystem h) : AmpleData k x H where
  m := 1
  m_pos := one_pos
  r := r
  h := h
  mem_secs j := by
    rw [show H.toSubSystem.pow 1 = H.toSubSystem from twistSys_zero_twist _]
    exact hH.mem_secs j
  generates I := by
    rw [show H.toSubSystem.pow 1 = H.toSubSystem from twistSys_zero_twist _]
    exact hH.generates I
  finite j hj := ⟨{1}, fun a ha => by
    have hb := hH.closed j hj ha
    rw [Finset.coe_singleton]
    exact Submodule.mem_span_singleton.mpr ⟨⟨a, hb⟩, by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_one]⟩⟩
  affine j hj := hH.affine j hj
end Main
end SectionCount.Drop.Term
end
end GroundTheory.Heights₂.Heights.Kleiman


