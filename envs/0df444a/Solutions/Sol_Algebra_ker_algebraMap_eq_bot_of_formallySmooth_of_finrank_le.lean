-- Prove2me | solution 1 for Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/daf49ee1-013c-5ace-9a06-bd1491bf881f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {k P S : Type u} [Field k] [CommRing P] [CommRing S] [IsLocalRing P] [IsLocalRing S] [IsNoetherianRing P]
    [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [Algebra.FormallySmooth k P] [Algebra.FormallySmooth k S] [Module.Finite P Ω[P⁄k]]
    (hPS : Function.Surjective (algebraMap P S))
    (hrank : Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P] Ω[P⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k])) :
    RingHom.ker (algebraMap P S) = ⊥ := by
  classical
  letI _acg : AddCommGroup (S ⊗[P] Ω[P⁄k]) := inferInstance
  set ι := KaehlerDifferential.kerCotangentToTensor k P S with hι
  set g := KaehlerDifferential.mapBaseChange k P S with hg
  have hex : Function.Exact ι g := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k P S hPS
  have hgs : Function.Surjective g := KaehlerDifferential.mapBaseChange_surjective k P S hPS
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hPS).mp ‹Algebra.FormallySmooth k S›
  have hlι : ∀ c, l (ι c) = c := fun c => by
    have := congrArg (fun f => f c) hl; simpa using this
  have hιinj : Function.Injective ι := fun a b h => by rw [← hlι a, ← hlι b, h]

  set N : Submodule S (S ⊗[P] Ω[P⁄k]) := LinearMap.ker g with hN
  have hmemN : ∀ x, x ∈ N ↔ ∃ c, ι c = x := fun x => by rw [hN, LinearMap.mem_ker]; exact hex x

  have hsmul : ∀ (p : P) (x : S ⊗[P] Ω[P⁄k]), algebraMap P S p • x = p • x := fun p x => algebraMap_smul S p x
  let r : (S ⊗[P] Ω[P⁄k]) →ₗ[S] N :=
    { toFun := fun x => ⟨ι (l x), (hmemN _).mpr ⟨_, rfl⟩⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun s x => by
        obtain ⟨p, rfl⟩ := hPS s
        apply Subtype.ext
        show ι (l (algebraMap P S p • x)) = algebraMap P S p • ι (l x)
        rw [hsmul, map_smul, map_smul, hsmul] }
  have hr : ∀ n : N, r n = n := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmemN x).mp hx
    ext
    show ι (l (ι c)) = ι c
    rw [hlι]
  have hrincl : r ∘ₗ N.subtype = LinearMap.id := by ext n; exact congrArg Subtype.val (hr n) ▸ rfl

  haveI : IsNoetherianRing S := isNoetherianRing_of_surjective P S (algebraMap P S) hPS
  haveI : Module.Finite S (S ⊗[P] Ω[P⁄k]) := inferInstance
  haveI : Module.Finite (IsLocalRing.ResidueField S) ((IsLocalRing.ResidueField S) ⊗[S] (S ⊗[P] Ω[P⁄k])) := inferInstance

  set gK := g.baseChange (IsLocalRing.ResidueField S) with hgK
  set iK := N.subtype.baseChange (IsLocalRing.ResidueField S) with hiK
  have hgKs : Function.Surjective gK := by
    have := LinearMap.lTensor_surjective (IsLocalRing.ResidueField S) hgs
    intro y; obtain ⟨x, hx⟩ := this y; exact ⟨x, hx⟩
  have hexK : Function.Exact iK gK := by
    have := lTensor_exact (IsLocalRing.ResidueField S) (f := N.subtype) (g := g) (LinearMap.exact_subtype_ker_map g) hgs
    intro y; exact this y
  have hiKinj : Function.Injective iK := by
    intro a b hab
    have := congrArg (r.baseChange (IsLocalRing.ResidueField S)) hab
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hrincl,
      LinearMap.baseChange_id, LinearMap.id_apply, LinearMap.id_apply] at this
    exact this

  have hdim := LinearMap.finrank_range_add_finrank_ker gK
  rw [LinearMap.range_eq_top.mpr hgKs, finrank_top, LinearMap.exact_iff.mp hexK] at hdim
  have hrange0 : Module.finrank (IsLocalRing.ResidueField S) (LinearMap.range iK) = 0 := by omega
  have hrange : LinearMap.range iK = ⊥ := Submodule.finrank_eq_zero.mp hrange0
  have hKN : ∀ x : (IsLocalRing.ResidueField S) ⊗[S] N, x = 0 := by
    intro x
    apply hiKinj
    rw [map_zero]
    have : iK x ∈ LinearMap.range iK := ⟨x, rfl⟩
    rwa [hrange, Submodule.mem_bot] at this

  have hNfg : N.FG := IsNoetherian.noetherian N
  have hNbot : N = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal S) N hNfg
    ·
      have htop : (IsLocalRing.maximalIdeal S • ⊤ : Submodule S N) = ⊤ := by
        rw [eq_top_iff]
        intro n _
        have e := TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal S)
        have h0 : e.symm (Submodule.Quotient.mk n) = 0 := hKN _
        have h1 : (Submodule.Quotient.mk n : N ⧸ (IsLocalRing.maximalIdeal S • ⊤ : Submodule S N)) = 0 := by
          simpa using congrArg e h0
        exact (Submodule.Quotient.mk_eq_zero _).mp h1
      intro x hx
      have : (⟨x, hx⟩ : N) ∈ (IsLocalRing.maximalIdeal S • ⊤ : Submodule S N) := by rw [htop]; exact Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := N.subtype) this
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

  have hcot : ∀ c : (RingHom.ker (algebraMap P S)).Cotangent, c = 0 := by
    intro c
    apply hιinj
    rw [map_zero]
    have : ι c ∈ N := (hmemN _).mpr ⟨c, rfl⟩
    rwa [hNbot, Submodule.mem_bot] at this
  set K : Ideal P := RingHom.ker (algebraMap P S) with hK
  have hKsq : K ≤ K • K := by
    intro x hx
    have := (Ideal.toCotangent_eq_zero K ⟨x, hx⟩).mp (hcot _)
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  have hKtop : K ≠ ⊤ := by
    intro h
    have : (1 : P) ∈ K := h ▸ Submodule.mem_top
    rw [hK, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot K K (IsNoetherian.noetherian K) hKsq
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact IsLocalRing.le_maximalIdeal hKtop)

end S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
end P2MW
export P2MW.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le (solution)
