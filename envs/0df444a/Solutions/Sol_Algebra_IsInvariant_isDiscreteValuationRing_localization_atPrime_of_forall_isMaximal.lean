-- Prove2me | solution 1 for Algebra.IsInvariant.isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/94cf5cf9-62a0-5079-a97c-90c875d7e8b3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal

set_option autoImplicit false

open scoped Pointwise

namespace LNI21

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
variable {G : Type*} [Group G] [MulSemiringAction G A] [SMulCommClass G S A]

theorem exists_mem_forall_smul_notMem [Finite G] (P : Ideal A) [hP : P.IsPrime] (J : Ideal A)
    (hJ : ∀ (g : G) (x : A), x ∈ J → g • x ∈ J) (hJP : ¬ J ≤ P) :
    ∃ u ∈ J, ∀ g : G, g • u ∉ P := by
  classical
  cases nonempty_fintype G
  by_contra h
  push_neg at h
  have hsub : (J : Set A) ⊆ ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G), ((g⁻¹ • P : Ideal A) : Set A) := by
    intro x hx
    obtain ⟨g, hg⟩ := h x hx
    exact Set.mem_biUnion (Finset.mem_univ g) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
  rw [Ideal.subset_union_prime (1 : G) 1 (fun g _ _ _ => hP.smul g⁻¹)] at hsub
  obtain ⟨g, -, hg⟩ := hsub
  apply hJP
  intro x hx
  have h1 : g⁻¹ • x ∈ g⁻¹ • P := hg (hJ g⁻¹ x hx)
  have h2 := Ideal.mem_inv_pointwise_smul_iff.mp h1
  rwa [smul_inv_smul] at h2

theorem smul_prod_smul [Fintype G] (u : A) (g : G) : g • (∏ h : G, h • u) = ∏ h : G, h • u :=
  Finset.smul_prod_perm u g

theorem prod_smul_notMem [Fintype G] (P : Ideal A) [hP : P.IsPrime] (u : A) (hu : ∀ g : G, g • u ∉ P) :
    (∏ h : G, h • u) ∉ P := by
  intro h
  obtain ⟨g, -, hg⟩ := hP.prod_mem_iff.mp h
  exact hu g hg

theorem prod_smul_eq_mul [Fintype G] [DecidableEq G] (u : A) :
    (∏ h : G, h • u) = u * ∏ h ∈ (Finset.univ : Finset G).erase 1, h • u := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset G) (fun h : G => h • u) (Finset.mem_univ 1), one_smul]

theorem exists_algebraMap_eq_prod_smul [Fintype G] [Algebra.IsInvariant S A G]
    (q : Ideal S) (P : Ideal A) [hP : P.IsPrime] (hPq : P.under S = q) (u : A) (hu : ∀ g : G, g • u ∉ P) :
    ∃ σ : S, σ ∉ q ∧ algebraMap S A σ = ∏ h : G, h • u := by
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.isInvariant (A := S) (B := A) (G := G) (∏ h : G, h • u)
    (fun g => smul_prod_smul u g)
  refine ⟨σ, fun hσq => ?_, hσ⟩
  apply prod_smul_notMem P u hu
  rw [← hσ]
  rw [← hPq] at hσq
  exact Ideal.mem_comap.mp hσq

theorem exists_notMem_mul_eq_zero [Finite G] [Algebra.IsInvariant S A G] [FaithfulSMul S A]
    (q : Ideal S) (P : Ideal A) [hP : P.IsPrime] (hPq : P.under S = q)
    (s : S) (hs : ∃ t ∉ P, t * algebraMap S A s = 0) :
    ∃ σ ∉ q, σ * s = 0 := by
  classical
  cases nonempty_fintype G
  obtain ⟨t, htP, ht⟩ := hs
  let J : Ideal A := LinearMap.ker (LinearMap.mulLeft A (algebraMap S A s))
  have memJ : ∀ x : A, x ∈ J ↔ algebraMap S A s * x = 0 := fun x => Iff.rfl
  have hJ : ∀ (g : G) (x : A), x ∈ J → g • x ∈ J := by
    intro g x hx
    rw [memJ] at hx ⊢
    calc algebraMap S A s * g • x = g • algebraMap S A s * g • x := by rw [smul_algebraMap]
      _ = g • (algebraMap S A s * x) := (smul_mul' g _ _).symm
      _ = 0 := by rw [hx, smul_zero]
  have hJP : ¬ J ≤ P := fun hle => htP (hle ((memJ t).2 (by rw [mul_comm]; exact ht)))
  obtain ⟨u, huJ, hu⟩ := exists_mem_forall_smul_notMem (G := G) P J hJ hJP
  obtain ⟨σ, hσq, hσ⟩ := exists_algebraMap_eq_prod_smul (G := G) q P hPq u hu
  refine ⟨σ, hσq, ?_⟩
  apply FaithfulSMul.algebraMap_injective S A
  rw [map_mul, map_zero, hσ, prod_smul_eq_mul u, mul_right_comm, mul_comm u, (memJ u).1 huJ, zero_mul]

theorem exists_notMem_mul_eq_mul [Finite G] [Algebra.IsInvariant S A G] [FaithfulSMul S A] [IsNoetherianRing A]
    (q : Ideal S) (P : Ideal A) [hP : P.IsPrime] (hPq : P.under S = q)
    (a b : S) (ha : ∀ x : A, algebraMap S A a * x = 0 → ∃ t ∉ P, t * x = 0)
    (hdiv : ∃ t ∉ P, ∃ z : A, t * algebraMap S A b = algebraMap S A a * z) :
    ∃ σ ∉ q, ∃ c : S, σ * b = a * c := by
  classical
  cases nonempty_fintype G
  have hqprime : q.IsPrime := by rw [← hPq]; exact Ideal.IsPrime.under S P
  set a' := algebraMap S A a with ha'
  set b' := algebraMap S A b with hb'
  have ha'fix : ∀ g : G, g • a' = a' := fun g => smul_algebraMap g a
  have hb'fix : ∀ g : G, g • b' = b' := fun g => smul_algebraMap g b
  obtain ⟨t, htP, z, htz⟩ := hdiv

  let J : Ideal A := Submodule.comap (LinearMap.mulLeft A b') (Ideal.span {a'})
  have memJ : ∀ x : A, x ∈ J ↔ ∃ w : A, b' * x = a' * w := by
    intro x
    simp only [J, Submodule.mem_comap, LinearMap.mulLeft_apply, Ideal.mem_span_singleton']
    exact ⟨fun ⟨w, hw⟩ => ⟨w, by rw [← hw, mul_comm]⟩, fun ⟨w, hw⟩ => ⟨w, by rw [hw, mul_comm]⟩⟩
  have hJ : ∀ (g : G) (x : A), x ∈ J → g • x ∈ J := by
    intro g x hx
    obtain ⟨w, hw⟩ := (memJ x).1 hx
    refine (memJ _).2 ⟨g • w, ?_⟩
    calc b' * g • x = g • b' * g • x := by rw [hb'fix]
      _ = g • (b' * x) := (smul_mul' g _ _).symm
      _ = g • (a' * w) := by rw [hw]
      _ = g • a' * g • w := smul_mul' g _ _
      _ = a' * g • w := by rw [ha'fix]
  have hJP : ¬ J ≤ P := fun hle => htP (hle ((memJ t).2 ⟨z, by rw [mul_comm]; exact htz⟩))
  obtain ⟨u, huJ, hu⟩ := exists_mem_forall_smul_notMem (G := G) P J hJ hJP
  obtain ⟨z₁, hz₁⟩ := (memJ u).1 huJ
  obtain ⟨σ₁, hσ₁q, hσ₁⟩ := exists_algebraMap_eq_prod_smul (G := G) q P hPq u hu
  set R₁ : A := ∏ h ∈ (Finset.univ : Finset G).erase 1, h • u with hR₁
  set z' : A := z₁ * R₁ with hz'
  have hNu : (∏ h : G, h • u) = u * R₁ := prod_smul_eq_mul u
  have hbz' : b' * (∏ h : G, h • u) = a' * z' := by
    rw [hNu, ← mul_assoc, hz₁, mul_assoc]

  let 𝔞 : Ideal A := LinearMap.ker (LinearMap.mulLeft A a')
  have mem𝔞 : ∀ x : A, x ∈ 𝔞 ↔ a' * x = 0 := fun x => Iff.rfl
  have h𝔞stab : ∀ (g : G) (x : A), x ∈ 𝔞 → g • x ∈ 𝔞 := by
    intro g x hx
    rw [mem𝔞] at hx ⊢
    calc a' * g • x = g • a' * g • x := by rw [ha'fix]
      _ = g • (a' * x) := (smul_mul' g _ _).symm
      _ = 0 := by rw [hx, smul_zero]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian 𝔞 : 𝔞.FG)
  have hgen : ∀ x : ↥T, ∃ t : A, t ∉ P ∧ t * (x : A) = 0 := by
    intro x
    obtain ⟨t, ht, htx⟩ := ha x ((mem𝔞 x).1 (hT ▸ Submodule.subset_span x.2))
    exact ⟨t, ht, htx⟩
  choose tf htf using hgen
  let tt : A := ∏ x : ↥T, tf x
  have httP : tt ∉ P := by
    intro h
    obtain ⟨x, -, hx⟩ := hP.prod_mem_iff.mp h
    exact (htf x).1 hx
  have htt : ∀ x ∈ 𝔞, tt * x = 0 := by
    intro x hx
    rw [← hT] at hx
    refine Submodule.span_induction (p := fun y _ => tt * y = 0) ?_ ?_ ?_ ?_ hx
    · intro y hy
      have hsplit : tt = (∏ x' ∈ (Finset.univ : Finset ↥T).erase ⟨y, hy⟩, tf x') * tf ⟨y, hy⟩ := by
        rw [mul_comm, Finset.mul_prod_erase (Finset.univ : Finset ↥T) tf (Finset.mem_univ _)]
      rw [hsplit, mul_assoc, (htf ⟨y, hy⟩).2, mul_zero]
    · exact mul_zero _
    · intro y w _ _ hy hw; rw [mul_add, hy, hw, add_zero]
    · intro r y _ hy; rw [smul_eq_mul, mul_left_comm, hy, mul_zero]
  let 𝔟 : Ideal A := 𝔞.annihilator
  have mem𝔟 : ∀ v : A, v ∈ 𝔟 ↔ ∀ x ∈ 𝔞, v * x = 0 := by
    intro v; rw [Submodule.mem_annihilator]; rfl
  have h𝔟stab : ∀ (g : G) (v : A), v ∈ 𝔟 → g • v ∈ 𝔟 := by
    intro g v hv
    rw [mem𝔟] at hv ⊢
    intro x hx
    have h1 : v * g⁻¹ • x = 0 := hv _ (h𝔞stab g⁻¹ x hx)
    calc g • v * x = g • v * g • (g⁻¹ • x) := by rw [smul_inv_smul]
      _ = g • (v * g⁻¹ • x) := (smul_mul' g _ _).symm
      _ = 0 := by rw [h1, smul_zero]
  have h𝔟P : ¬ 𝔟 ≤ P := fun hle => httP (hle ((mem𝔟 tt).2 htt))
  obtain ⟨v, hv𝔟, hv⟩ := exists_mem_forall_smul_notMem (G := G) P 𝔟 h𝔟stab h𝔟P
  obtain ⟨τ, hτq, hτ⟩ := exists_algebraMap_eq_prod_smul (G := G) q P hPq v hv
  have hNv : (∏ h : G, h • v) = v * ∏ h ∈ (Finset.univ : Finset G).erase 1, h • v := prod_smul_eq_mul v
  set c' : A := (∏ h : G, h • v) * z' with hc'
  have hc'fix : ∀ g : G, g • c' = c' := by
    intro g
    rw [hc', smul_mul', smul_prod_smul]
    have h1 : a' * (g • z') = a' * z' := by
      calc a' * g • z' = g • a' * g • z' := by rw [ha'fix]
        _ = g • (a' * z') := (smul_mul' g _ _).symm
        _ = g • (b' * ∏ h : G, h • u) := by rw [hbz']
        _ = g • b' * g • (∏ h : G, h • u) := smul_mul' g _ _
        _ = b' * ∏ h : G, h • u := by rw [hb'fix, smul_prod_smul]
        _ = a' * z' := hbz'
    have h2 : g • z' - z' ∈ 𝔞 := (mem𝔞 _).2 (by rw [mul_sub, h1, sub_self])
    have h3 : v * (g • z' - z') = 0 := ((mem𝔟 v).1 hv𝔟) _ h2
    have h4 : (∏ h : G, h • v) * (g • z' - z') = 0 := by
      rw [hNv, mul_right_comm, h3, zero_mul]
    rw [mul_sub, sub_eq_zero] at h4
    exact h4
  obtain ⟨c, hc⟩ := Algebra.IsInvariant.isInvariant (A := S) (B := A) (G := G) c' hc'fix
  refine ⟨τ * σ₁, fun h => ?_, c, ?_⟩
  · rcases hqprime.mem_or_mem h with h' | h'
    · exact hτq h'
    · exact hσ₁q h'
  · apply FaithfulSMul.algebraMap_injective S A
    rw [map_mul, map_mul, map_mul, hτ, hσ₁, hc, hc']
    calc (∏ h : G, h • v) * (∏ h : G, h • u) * b' = (∏ h : G, h • v) * (b' * ∏ h : G, h • u) := by ring
      _ = (∏ h : G, h • v) * (a' * z') := by rw [hbz']
      _ = a' * ((∏ h : G, h • v) * z') := by ring

end LNI21

open LNI21 in
theorem solution
    {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] [FaithfulSMul S A]
    [IsNoetherianRing S] [IsNoetherianRing A]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G S A] [Algebra.IsInvariant S A G]
    (hA : ∀ (P : Ideal A) (_ : P.IsMaximal),
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P))
    (q : Ideal S) [q.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime q), IsDiscreteValuationRing (Localization.AtPrime q) := by
  classical
  cases nonempty_fintype G
  haveI : Algebra.IsIntegral S A := Algebra.IsInvariant.isIntegral S A G
  have hinjSA : Function.Injective (algebraMap S A) := FaithfulSMul.algebraMap_injective S A

  obtain ⟨P, hPmax, hPq⟩ : ∃ P : Ideal A, P.IsMaximal ∧ P.under S = q := by
    have hker : RingHom.ker (algebraMap S A) ≤ q := fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from hinjSA (by rw [hx, map_zero])]
      exact q.zero_mem
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) q hker
    exact ⟨P, hP, hPq⟩
  haveI := hPmax
  obtain ⟨hdomP, hdvrP⟩ := hA P hPmax
  haveI := hdomP; haveI := hdvrP
  let Sq := Localization.AtPrime q
  let AP := Localization.AtPrime P

  let φ : Sq →+* AP := Localization.localRingHom q P (algebraMap S A) (hPq.symm.trans (Ideal.under_def S P))
  have hφalg : ∀ s : S, φ (algebraMap S Sq s) = algebraMap A AP (algebraMap S A s) := fun s =>
    Localization.localRingHom_to_map q P (algebraMap S A) _ s
  have hφ0 : ∀ x : Sq, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    dsimp only at hx ⊢
    have h1 : φ (IsLocalization.mk' Sq s t) * φ (algebraMap S Sq (t : S)) = φ (algebraMap S Sq s) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [hx, zero_mul, hφalg] at h1
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl AP (algebraMap S A s)).1 h1.symm
    obtain ⟨σ, hσq, hσs⟩ := exists_notMem_mul_eq_zero (G := G) q P hPq s ⟨m, m.2, hm⟩
    exact (IsLocalization.mk'_eq_zero_iff s t).2 ⟨⟨σ, show σ ∈ q.primeCompl from hσq⟩, hσs⟩
  have hφ : Function.Injective φ := fun x y h =>
    sub_eq_zero.1 (hφ0 _ (by rw [map_sub, h, sub_self]))
  haveI : IsDomain Sq := Function.Injective.isDomain φ hφ

  have hne : ∀ a : S, algebraMap S Sq a ≠ 0 → ∀ x : A, algebraMap S A a * x = 0 → ∃ t ∉ P, t * x = 0 := by
    intro a ha0 x hax
    have h1 : algebraMap A AP (algebraMap S A a) ≠ 0 := by
      rw [← hφalg]; exact fun h => ha0 (hφ (by rw [h, map_zero]))
    have h2 : algebraMap A AP (algebraMap S A a) * algebraMap A AP x = 0 := by rw [← map_mul, hax, map_zero]
    have h3 : algebraMap A AP x = 0 := (mul_eq_zero.1 h2).resolve_left h1
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl AP x).1 h3
    exact ⟨m, m.2, hm⟩

  have hnfP : ¬ IsField AP := IsDiscreteValuationRing.not_isField AP
  haveI : ValuationRing AP := ((IsDiscreteValuationRing.TFAE AP hnfP).out 0 1).mp hdvrP
  have key : ∀ a b : S, algebraMap S Sq a ≠ 0 →
      algebraMap A AP (algebraMap S A a) ∣ algebraMap A AP (algebraMap S A b) →
      algebraMap S Sq a ∣ algebraMap S Sq b := by
    intro a b ha0 hdvd
    obtain ⟨w, hw⟩ := hdvd
    obtain ⟨⟨z, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl w
    have h1 : algebraMap A AP (algebraMap S A b) * algebraMap A AP (t : A) =
        algebraMap A AP (algebraMap S A a) * algebraMap A AP z := by
      rw [hw, mul_assoc, IsLocalization.mk'_spec]
    rw [← map_mul, ← map_mul] at h1
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl AP).1 h1
    have hdiv : ∃ t' ∉ P, ∃ z' : A, t' * algebraMap S A b = algebraMap S A a * z' := by
      refine ⟨(c : A) * t, fun h => ?_, (c : A) * z, ?_⟩
      · rcases hPmax.isPrime.mem_or_mem h with h' | h'
        · exact c.2 h'
        · exact t.2 h'
      · calc ((c : A) * t) * algebraMap S A b = (c : A) * (algebraMap S A b * t) := by ring
          _ = (c : A) * (algebraMap S A a * z) := hc
          _ = algebraMap S A a * ((c : A) * z) := by ring
    obtain ⟨σ, hσq, c₁, hσ⟩ := exists_notMem_mul_eq_mul (G := G) q P hPq a b (hne a ha0) hdiv
    have hu : IsUnit (algebraMap S Sq σ) := IsLocalization.map_units Sq (⟨σ, show σ ∈ q.primeCompl from hσq⟩ : q.primeCompl)
    have h2 : algebraMap S Sq b * algebraMap S Sq σ = algebraMap S Sq a * algebraMap S Sq c₁ := by
      rw [← map_mul, ← map_mul, mul_comm b, hσ]
    exact (hu.dvd_mul_right).1 ⟨_, h2⟩

  have hred : ∀ a b : S, algebraMap S Sq a ∣ algebraMap S Sq b ∨ algebraMap S Sq b ∣ algebraMap S Sq a := by
    intro a b
    by_cases ha0 : algebraMap S Sq a = 0
    · exact Or.inr (by rw [ha0]; exact dvd_zero _)
    by_cases hb0 : algebraMap S Sq b = 0
    · exact Or.inl (by rw [hb0]; exact dvd_zero _)
    rcases ValuationRing.dvd_total (algebraMap A AP (algebraMap S A a)) (algebraMap A AP (algebraMap S A b)) with h | h
    · exact Or.inl (key a b ha0 h)
    · exact Or.inr (key b a hb0 h)
  have htot : ∀ x y : Sq, x ∣ y ∨ y ∣ x := by
    intro x y
    obtain ⟨⟨a, sa⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    obtain ⟨⟨b, sb⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one a sa, IsLocalization.mk'_eq_mul_mk'_one b sb]
    have hua : IsUnit (IsLocalization.mk' Sq (1 : S) sa) :=
      isUnit_iff_exists_inv.2 ⟨algebraMap S Sq (sa : S), by rw [IsLocalization.mk'_spec, map_one]⟩
    have hub : IsUnit (IsLocalization.mk' Sq (1 : S) sb) :=
      isUnit_iff_exists_inv.2 ⟨algebraMap S Sq (sb : S), by rw [IsLocalization.mk'_spec, map_one]⟩
    rcases hred a b with h | h
    · exact Or.inl ((hua.mul_right_dvd).2 ((hub.dvd_mul_right).2 h))
    · exact Or.inr ((hub.mul_right_dvd).2 ((hua.dvd_mul_right).2 h))
  haveI : IsTotal Sq (· ∣ ·) := ⟨htot⟩
  haveI : ValuationRing Sq := ValuationRing.iff_dvd_total.mpr inferInstance

  have hnf : ¬ IsField Sq := by
    intro hF

    let η : Ideal A := (⊥ : Ideal AP).comap (algebraMap A AP)
    haveI : η.IsPrime := Ideal.IsPrime.comap _
    have hηP : η ≤ P := by
      intro x hx
      rw [← Localization.AtPrime.comap_maximalIdeal (I := P)]
      exact Ideal.comap_mono bot_le hx
    have hηne : η ≠ P := by
      intro h
      apply hnfP
      rw [IsLocalRing.isField_iff_maximalIdeal_eq]
      apply le_bot_iff.1
      rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P), Ideal.map_le_iff_le_comap]
      exact le_of_eq h.symm
    obtain ⟨x, hxP, hxη⟩ : ∃ x ∈ P, x ∉ η := by
      by_contra h; push_neg at h; exact hηne (le_antisymm hηP h)
    have hlt : η.comap (algebraMap S A) < P.comap (algebraMap S A) :=
      Ideal.comap_lt_comap_of_integral_mem_sdiff hηP ⟨hxP, hxη⟩ (Algebra.IsIntegral.isIntegral x)
    rw [← Ideal.under_def S P, hPq] at hlt
    obtain ⟨s, hsq, hsη⟩ := SetLike.exists_of_lt hlt

    have hs0 : algebraMap S Sq s ≠ 0 := by
      intro h0
      obtain ⟨τ, hτ⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl Sq s).1 h0
      have : (τ : S) * s ∈ η.comap (algebraMap S A) := by rw [hτ]; exact Ideal.zero_mem _
      rcases (Ideal.IsPrime.comap (algebraMap S A) : (η.comap (algebraMap S A)).IsPrime).mem_or_mem this with h' | h'
      · exact τ.2 (hlt.le h')
      · exact hsη h'
    have hsu : ¬ IsUnit (algebraMap S Sq s) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff Sq q s]
      exact fun h => h hsq
    letI := hF.toField
    exact hsu (isUnit_iff_ne_zero.2 hs0)
  have hVR : ValuationRing Sq := inferInstance
  have hdvr : IsDiscreteValuationRing Sq := ((IsDiscreteValuationRing.TFAE Sq hnf).out 0 1).mpr hVR
  exact ⟨‹IsDomain Sq›, hdvr⟩

end S_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal
end P2MW
export P2MW.S_Algebra_IsInvariant_isDiscreteValuationRing_localization_atPrime_of_forall_isMaximal (solution)
