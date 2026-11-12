-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03b_Lemma33
-- name    : OddOrder_BG_Ch1_Preliminary_S03b_Lemma33
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:51.682028+00:00
-- url     : https://prove2.me/theorems/3c2dcb10-6c50-4051-951c-c5ea1fc49914
-- title:
--   BG §3B: Lemma 3.3 (Wielandt's fixed-point lemma for Frobenius groups)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter I §3B, Lemma 3.3 (Wielandt): let $G=KR$ be a Frobenius group with kernel $K$ and complement $R$, and $V$ a representation of $G$ over a field $F$ with $\mathrm{char}\,F\nmid|K|$. If $K$ acts nontrivially on $V$, then $C_V(R)\ne0$. It is used for BG Theorem 3.7 (nilpotency of the Frobenius kernel).
--
--   The main definition is `groupSumMap`, the averaging endomorphism $\sum_{h\in H}\rho(h)$ of a finite subgroup $H$.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03b_Lemma33.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03b_Lemma33.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Mathlib.RepresentationTheory.Basic

namespace OddOrder.BG.Ch1.S03b

open OddOrder.Isaacs.Ch06

open scoped Pointwise

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The averaging endomorphism `∑_{h ∈ H} ρ h` of a finite subgroup `H` under a representation. -/
noncomputable def groupSumMap (ρ : Representation F G V) (H : Subgroup G) [Fintype H] :
    V →ₗ[F] V :=
  ∑ h : H, ρ (h : G)

/-- **Averaging into fixed points**: `(∑_{h∈H} ρ h) v` is fixed by every `h₀ ∈ H`, because
left multiplication by `h₀` permutes `H`. -/
theorem fixed_apply_groupSumMap (ρ : Representation F G V) (H : Subgroup G) [Fintype H]
    {h₀ : G} (hh₀ : h₀ ∈ H) (v : V) :
    ρ h₀ (groupSumMap ρ H v) = groupSumMap ρ H v := by
  simp only [groupSumMap, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  -- `ρ h₀ (ρ ↑h v) = ρ (↑(⟨h₀,hh₀⟩ * h)) v`; reindex by `Equiv.mulLeft ⟨h₀,hh₀⟩`.
  have hreindex : ∀ h : H, ρ h₀ (ρ (h : G) v)
      = ρ ((⟨h₀, hh₀⟩ * h : H) : G) v := by
    intro h
    rw [Subgroup.coe_mul, map_mul]
    rfl
  rw [Finset.sum_congr rfl (fun h _ => hreindex h)]
  exact Equiv.sum_comp (Equiv.mulLeft (⟨h₀, hh₀⟩ : H)) (fun h => ρ ((h : H) : G) v)

/-- **Endgame of Wielandt**: if the `K`-averaging map equals `|K| • id`, then `K` acts
trivially. (`|K| • v` is `K`-fixed by `fixed_apply_groupSumMap`, so `|K| • ρ k v = |K| • v`;
cancel the nonzero scalar `|K|`.) -/
theorem trivial_of_groupSumMap_eq_card_smul (ρ : Representation F G V) (K : Subgroup G)
    [Fintype K] (hchar : (Nat.card K : F) ≠ 0)
    (h : groupSumMap ρ K = (Nat.card K : F) • LinearMap.id) :
    ∀ k : K, ρ (k : G) = 1 := by
  intro k
  ext v
  have hfix : ρ (k : G) (groupSumMap ρ K v) = groupSumMap ρ K v :=
    fixed_apply_groupSumMap ρ K k.2 v
  rw [h] at hfix
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul] at hfix
  have := smul_right_injective V hchar hfix
  simpa using this

/-- `φ • H = H.map φ`: the pointwise `MulAut`-action on a subgroup is its image. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-- Composition of representation maps: `ρ a (ρ b w) = ρ (a * b) w`. -/
private theorem rep_apply_apply (ρ : Representation F G V) (a b : G) (w : V) :
    ρ a (ρ b w) = ρ (a * b) w := by
  rw [map_mul]; rfl

/-- **Conjugate has trivial centralizer too**: if `C_V(R) = 0`, then the averaging map over a
conjugate `R^x = conj x • R` kills every `v` (`groupSumMap ρ (conj x • R) v = 0`), since
`ρ x⁻¹ (groupSumMap ρ (conj x • R) v)` is `R`-fixed hence zero. -/
theorem groupSumMap_conjugate_eq_zero (ρ : Representation F G V)
    {R : Subgroup G} (x : G) [Fintype (MulAut.conj x • R : Subgroup G)]
    (hCR : ∀ w : V, (∀ r : R, ρ (r : G) w = w) → w = 0) (v : V) :
    groupSumMap ρ (MulAut.conj x • R) v = 0 := by
  set w := groupSumMap ρ (MulAut.conj x • R) v with hw
  -- `ρ x⁻¹ w` is `R`-fixed.
  have hRfix : ∀ r : R, ρ (r : G) (ρ x⁻¹ w) = ρ x⁻¹ w := by
    intro r
    have hmem : (x * (r : G) * x⁻¹) ∈ (MulAut.conj x • R : Subgroup G) := by
      rw [mulAut_smul_eq_map]
      exact ⟨(r : G), r.2, by simp [MulAut.conj_apply]⟩
    have hfix : ρ (x * (r : G) * x⁻¹) w = w := fixed_apply_groupSumMap ρ _ hmem v
    have e1 : ρ (r : G) (ρ x⁻¹ w) = ρ ((r : G) * x⁻¹) w := rep_apply_apply ρ _ _ w
    have e2 : ρ x⁻¹ w = ρ ((r : G) * x⁻¹) w := by
      have hcalc : ρ ((r : G) * x⁻¹) w = ρ x⁻¹ (ρ (x * (r : G) * x⁻¹) w) := by
        rw [rep_apply_apply]; congr 1; group
      rw [hcalc, hfix]
    rw [e1, ← e2]
  -- `R`-fixed ⟹ zero; hence `w = ρ x (ρ x⁻¹ w) = 0`.
  have hzero : ρ x⁻¹ w = 0 := hCR _ hRfix
  have hxx : ρ x (ρ x⁻¹ w) = w := by rw [rep_apply_apply]; simp
  rw [hzero, map_zero] at hxx
  exact hxx.symm

/-- **BG Lemma 3.3** (Wielandt, mmd L845): if `G = KR` is a Frobenius group and `K` acts
nontrivially on a representation `V` over a field `F` of characteristic not dividing `|K|`,
then `C_V(R) ≠ 0` (some nonzero vector is fixed by all of `R`). -/
theorem centralizer_ne_bot_of_nontrivial_kernel [Finite G] {K R : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (ρ : Representation F G V)
    (hchar : (Nat.card K : F) ≠ 0)
    (hKnt : ∃ k : K, ρ (k : G) ≠ 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ r : R, ρ (r : G) v = v := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hCon
  push Not at hCon
  have hCR : ∀ w : V, (∀ r : R, ρ (r : G) w = w) → w = 0 := fun w hw => by
    by_contra hw0; obtain ⟨r, hr⟩ := hCon w hw0; exact hr (hw r)
  -- The nonidentity part of `groupSumMap ρ H w` over a finite subgroup `H`.
  have hsplit : ∀ (H : Subgroup G) (w : V),
      (∑ x : {x : H // x ≠ 1}, ρ ((x : H) : G) w) = groupSumMap ρ H w - w := by
    intro H w
    have h1 : groupSumMap ρ H w = ∑ h : H, ρ (h : G) w := by
      rw [groupSumMap, LinearMap.sum_apply]
    rw [h1, ← Finset.add_sum_erase Finset.univ (fun h : H => ρ (h : G) w) (Finset.mem_univ 1)]
    simp only [Subgroup.coe_one, map_one, Module.End.one_apply, add_sub_cancel_left]
    exact (Finset.sum_subtype (Finset.univ.erase 1) (p := fun h : H => h ≠ 1)
      (fun h => by simp [Finset.mem_erase]) (fun h : H => ρ (h : G) w)).symm
  have hKtriv : ∀ k : K, ρ (k : G) = 1 := by
    apply trivial_of_groupSumMap_eq_card_smul ρ K hchar
    ext v
    rw [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    -- the full-group sum is `0` (it lands in `C_V(G) ⊆ C_V(R) = 0`)
    have hS0 : (∑ g : G, ρ g v) = 0 := by
      refine hCR _ (fun r => ?_)
      rw [map_sum, Finset.sum_congr rfl (fun g _ => rep_apply_apply ρ (r : G) g v)]
      exact Equiv.sum_comp (Equiv.mulLeft (r : G)) (fun g => ρ g v)
    set partn := SubgroupPartition.frobeniusGroup hFrob with hpartn
    have hbij : Function.Bijective partn.nonidentitySigmaTo :=
      ⟨partn.nonidentitySigmaTo_injective, partn.nonidentitySigmaTo_surjective⟩
    -- reindex the nonidentity sum across the partition parts
    have hreindex :
        (∑ y : {g : G // g ≠ 1}, ρ (y : G) v)
          = ∑ X : {X : Subgroup G // X ∈ partn.parts},
              ∑ x : {x : X.1 // x ≠ 1}, ρ ((x : X.1) : G) v := by
      rw [← Fintype.sum_bijective partn.nonidentitySigmaTo hbij
            (fun p => ρ ((p.2.1 : p.1.1) : G) v) (fun y => ρ (y : G) v) (fun _ => rfl)]
      rw [Fintype.sum_sigma]
    -- the full-group sum splits as identity + nonidentity
    have hGsum : (∑ g : G, ρ g v) = v + ∑ y : {g : G // g ≠ 1}, ρ (y : G) v := by
      rw [← Finset.add_sum_erase Finset.univ (fun g : G => ρ g v) (Finset.mem_univ 1)]
      congr 1
      · simp
      · exact Finset.sum_subtype (Finset.univ.erase 1) (p := fun g : G => g ≠ 1)
          (fun g => by simp [Finset.mem_erase]) (fun g : G => ρ g v)
    -- the partition sum collapses: kernel gives `groupSumMap ρ K v - v`, conjugates give `-v`
    have hmem_parts : ∀ X : Subgroup G,
        X ∈ partn.parts ↔ X = K ∨ ∃ g : G, X = MulAut.conj g • R := by
      rw [hpartn]; exact fun X => SubgroupPartition.mem_frobeniusGroup_parts hFrob
    have hKmem : K ∈ partn.parts := (hmem_parts K).mpr (Or.inl rfl)
    have hcard : partn.parts.card = Nat.card K + 1 := by
      rw [hpartn]; exact SubgroupPartition.frobeniusGroup_parts_card hFrob
    -- non-kernel parts are conjugates of `R`, on which the average vanishes.
    have hconj_term : ∀ X ∈ partn.parts.erase K, groupSumMap ρ X v - v = -v := by
      intro X hX
      rw [Finset.mem_erase] at hX
      obtain ⟨hXne, hXp⟩ := hX
      obtain hXK | ⟨g, rfl⟩ := (hmem_parts X).mp hXp
      · exact absurd hXK hXne
      · rw [groupSumMap_conjugate_eq_zero ρ g hCR v, zero_sub]
    have hpart_sum :
        (∑ X : {X : Subgroup G // X ∈ partn.parts},
            ∑ x : {x : X.1 // x ≠ 1}, ρ ((x : X.1) : G) v)
          = groupSumMap ρ K v - v - (Nat.card K) • v :=
      calc (∑ X : {X : Subgroup G // X ∈ partn.parts},
              ∑ x : {x : X.1 // x ≠ 1}, ρ ((x : X.1) : G) v)
          = ∑ X : {X : Subgroup G // X ∈ partn.parts}, (groupSumMap ρ X.1 v - v) :=
            Finset.sum_congr rfl (fun X _ => hsplit X.1 v)
        _ = ∑ X ∈ partn.parts, (groupSumMap ρ X v - v) :=
            Finset.sum_coe_sort partn.parts (fun X => groupSumMap ρ X v - v)
        _ = (groupSumMap ρ K v - v) + ∑ X ∈ partn.parts.erase K, (groupSumMap ρ X v - v) :=
            (Finset.add_sum_erase partn.parts (fun X => groupSumMap ρ X v - v) hKmem).symm
        _ = (groupSumMap ρ K v - v) + ∑ _X ∈ partn.parts.erase K, (-v) := by
            rw [Finset.sum_congr rfl hconj_term]
        _ = (groupSumMap ρ K v - v) + (partn.parts.erase K).card • (-v) := by
            rw [Finset.sum_const]
        _ = (groupSumMap ρ K v - v) + (Nat.card K) • (-v) := by
            rw [Finset.card_erase_of_mem hKmem, hcard, Nat.add_sub_cancel]
        _ = groupSumMap ρ K v - v - (Nat.card K) • v := by rw [smul_neg]; abel
    have hcombine : groupSumMap ρ K v - (Nat.card K) • v = 0 := by
      rw [← hS0, hGsum, hreindex, hpart_sum]; abel
    rw [sub_eq_zero] at hcombine
    rw [hcombine, Nat.cast_smul_eq_nsmul]
  obtain ⟨k, hk⟩ := hKnt
  exact hk (hKtriv k)

/-- **Contrapositive of BG Lemma 3.3**, the form used in the coprime chief-factor case of
Theorem 3.7: if `G = KR` is a Frobenius group and the complement `R` has no nonzero fixed vector
on a representation `V` over a field `F` with `char F ∤ |K|` (i.e. `C_V(R) = 0`), then the kernel
`K` acts trivially on `V`. -/
theorem kernel_acts_trivially_of_centralizer_eq_bot [Finite G] {K R : Subgroup G}
    (hFrob : IsFrobeniusGroup G K R) (ρ : Representation F G V)
    (hchar : (Nat.card K : F) ≠ 0)
    (hCR : ∀ v : V, (∀ r : R, ρ (r : G) v = v) → v = 0) :
    ∀ k : K, ρ (k : G) = 1 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv0, hvfix⟩ := centralizer_ne_bot_of_nontrivial_kernel hFrob ρ hchar h
  exact hv0 (hCR v hvfix)

end OddOrder.BG.Ch1.S03b


