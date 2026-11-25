-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:38:49.019244+00:00
-- url     : https://prove2.me/theorems/3d2fb21d-56ce-428a-9961-b3accc0cb0d9
-- title:
--   PSnapper Devissage
-- statement:
--   Definitions and structural lemmas for PSnapper Devissage, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDevissage.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
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
universe u v w u₁ v₁ w₁
namespace Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}
def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)
def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))
end Cech
section Zero
variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne
end Zero
section Lemmas
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
end Lemmas
end
end GroundTheory.Heights₂.Heights.Kleiman


