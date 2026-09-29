-- Prove2me | solution 1 for Algebra.exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b4bc6638-442d-597e-8f63-a1b235b98b4c

import Mathlib
import Theorems.Thm_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem solution
    {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] [Algebra.Smooth k B]
    {B' : Type u} [CommRing B'] [Algebra k B'] (ψ : B →ₐ[k] B') (hψ : Function.Surjective ψ)
    (v' : Ideal B') [v'.IsPrime] (v : Ideal B) [v.IsPrime] (hv' : v'.comap ψ.toRingHom = v)
    (hsm : Algebra.IsSmoothAt k v')
    (hrank : Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) ≤
      Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k])) :
    ∃ t : B, t ∉ v ∧ (RingHom.ker ψ.toRingHom).map (algebraMap B (Localization.Away t)) = ⊥ := by
  classical
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  letI algBB' : Algebra B B' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower k B B' := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm

  set P := Localization.AtPrime v with hP
  set S := Localization.AtPrime v' with hS
  haveI : v'.LiesOver v := ⟨by rw [Ideal.under_def, ← hv']; rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver v v'
  haveI : Algebra.FormallySmooth k S := hsm
  have halgPS : ∀ x : B, algebraMap P S (algebraMap B P x) = algebraMap B' S (ψ x) := fun x => by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq (p := v) (P := v'), Localization.localRingHom_to_map]
    rfl
  have hPS : Function.Surjective (algebraMap P S) := by
    intro y
    obtain ⟨⟨xb, sb⟩, rfl⟩ := IsLocalization.mk'_surjective v'.primeCompl y
    obtain ⟨x, hx⟩ := hψ xb
    obtain ⟨s, hs⟩ := hψ (sb : B')
    have hsv : s ∉ v := by
      intro h; apply sb.2; rw [← hs]; rw [← hv'] at h; exact h
    refine ⟨IsLocalization.mk' P x (⟨s, hsv⟩ : v.primeCompl), ?_⟩
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq (p := v) (P := v'), Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs

  set κ := IsLocalRing.ResidueField S with hκ
  haveI : IsScalarTower P S κ := inferInstance
  haveI : IsScalarTower B P κ := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B S κ, IsScalarTower.algebraMap_apply P S κ, ← IsScalarTower.algebraMap_apply B P S]
  haveI : IsScalarTower B v.ResidueField κ := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B P v.ResidueField, IsScalarTower.algebraMap_apply B P κ,
      ← IsScalarTower.algebraMap_apply P v.ResidueField κ]

  haveI : Algebra.FormallyEtale B P := Algebra.FormallyEtale.of_isLocalization (Rₘ := P) v.primeCompl
  haveI : Algebra.FormallyEtale B' S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) v'.primeCompl
  let eP : P ⊗[B] Ω[B⁄k] ≃ₗ[P] Ω[P⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B P
  let eS : S ⊗[B'] Ω[B'⁄k] ≃ₗ[S] Ω[S⁄k] := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k B' S
  have hL : Module.finrank κ (κ ⊗[S] (S ⊗[P] Ω[P⁄k])) = Module.finrank v.ResidueField (v.ResidueField ⊗[B] Ω[B⁄k]) := by
    have e1 : κ ⊗[S] (S ⊗[P] Ω[P⁄k]) ≃ₗ[κ] κ ⊗[P] Ω[P⁄k] := TensorProduct.AlgebraTensorModule.cancelBaseChange P S κ κ Ω[P⁄k]
    have e2 : κ ⊗[P] Ω[P⁄k] ≃ₗ[κ] κ ⊗[P] (P ⊗[B] Ω[B⁄k]) := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) eP.symm
    have e3 : κ ⊗[P] (P ⊗[B] Ω[B⁄k]) ≃ₗ[κ] κ ⊗[B] Ω[B⁄k] := TensorProduct.AlgebraTensorModule.cancelBaseChange B P κ κ Ω[B⁄k]
    have e4 : κ ⊗[v.ResidueField] (v.ResidueField ⊗[B] Ω[B⁄k]) ≃ₗ[κ] κ ⊗[B] Ω[B⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange B v.ResidueField κ κ Ω[B⁄k]
    rw [(e1.trans (e2.trans (e3.trans e4.symm))).finrank_eq, Module.finrank_baseChange]
  have hR : Module.finrank κ (κ ⊗[S] Ω[S⁄k]) = Module.finrank v'.ResidueField (v'.ResidueField ⊗[B'] Ω[B'⁄k]) := by
    have e1 : κ ⊗[S] Ω[S⁄k] ≃ₗ[κ] κ ⊗[S] (S ⊗[B'] Ω[B'⁄k]) := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ) eS.symm
    have e2 : κ ⊗[S] (S ⊗[B'] Ω[B'⁄k]) ≃ₗ[κ] κ ⊗[B'] Ω[B'⁄k] :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange B' S κ κ Ω[B'⁄k]
    exact (e1.trans e2).finrank_eq
  have hker := Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le (k := k) (P := P) (S := S) hPS
    (by rw [hL, hR]; exact hrank)

  have hIP : ∀ g ∈ RingHom.ker ψ.toRingHom, algebraMap B P g = 0 := by
    intro g hg
    have : algebraMap B P g ∈ RingHom.ker (algebraMap P S) := by
      rw [RingHom.mem_ker, halgPS, show ψ g = 0 from hg, map_zero]
    rwa [hker, Ideal.mem_bot] at this

  obtain ⟨G, hG⟩ := (isNoetherian_def.mp (inferInstance : IsNoetherian B B)) (RingHom.ker ψ.toRingHom)
  have hann : ∀ g ∈ (G : Set B), ∃ m : v.primeCompl, (m : B) * g = 0 := fun g hg =>
    (IsLocalization.map_eq_zero_iff v.primeCompl P g).mp (hIP g (hG ▸ Submodule.subset_span hg))
  choose m hm using hann
  let tM : v.primeCompl := ∏ g ∈ G.attach, m g.1 g.2
  let t : B := tM
  have ht : t = ∏ g ∈ G.attach, (m g.1 g.2 : B) := Submonoid.coe_finsetProd _ _ _
  have htv : t ∉ v := tM.2
  refine ⟨t, htv, ?_⟩
  rw [Ideal.map_eq_bot_iff_le_ker, ← hG, Ideal.span_le]
  intro g hg
  rw [SetLike.mem_coe, RingHom.mem_ker, IsLocalization.map_eq_zero_iff (Submonoid.powers t)]
  refine ⟨⟨t, Submonoid.mem_powers t⟩, ?_⟩
  show t * g = 0
  obtain ⟨u, hu⟩ : (m g hg : B) ∣ t := by
    rw [ht]; exact Finset.dvd_prod_of_mem (fun g' : {x // x ∈ G} => (m g'.1 g'.2 : B)) (Finset.mem_attach G ⟨g, hg⟩)
  rw [hu]
  linear_combination u * hm g hg

end S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le
end P2MW
export P2MW.S_Algebra_exists_notMem_map_ker_eq_bot_of_surjective_of_isSmoothAt_of_finrank_le (solution)
