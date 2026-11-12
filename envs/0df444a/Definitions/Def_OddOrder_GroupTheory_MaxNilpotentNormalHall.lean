-- Prove2me | Definitions.Def_OddOrder_GroupTheory_MaxNilpotentNormalHall
-- name    : OddOrder_GroupTheory_MaxNilpotentNormalHall
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:54.914262+00:00
-- url     : https://prove2.me/theorems/34fa9e89-802e-4624-8aa6-32720cb29ef0
-- title:
--   Maximal nilpotent normal Hall subgroups
-- statement:
--   The shared subgroup used by BG Section 15 and Peterfalvi Section 10: $M_F$, the maximal nilpotent normal Hall subgroup of a finite subgroup $M$. At the scaffold stage it is defined as a supremum of the subgroups with Peterfalvi's defining property.
--
--   Main definition: `maxNilpotentNormalHall` (Peterfalvi's $M_F$), with `maxNilpotentNormalHall_pointwise_smul` showing it is automorphism-equivariant. The bundle consists of this definition and supporting lemmas.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/MaxNilpotentNormalHall.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaxNilpotentNormalHall.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_GroupTheory_OpResidual

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- Peterfalvi's `M_F`: the maximal nilpotent normal Hall subgroup of `M`,
realized in the ambient group.  The Hall set is the set of prime divisors of the
candidate subgroup. -/
noncomputable def maxNilpotentNormalHall (M : Subgroup G) : Subgroup G :=
  sSup {N : Subgroup G |
    N ≤ M ∧
      (N.subgroupOf M).Normal ∧
      Group.IsNilpotent ↥(N.subgroupOf M) ∧
      OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)}

open scoped Pointwise in
/-- The automorphism action sends a subgroup to its image: `ψ • N = N.map ψ`. -/
theorem pointwise_mulAut_smul_eq_map (ψ : MulAut G) (N : Subgroup G) :
    (ψ • N : Subgroup G) = N.map (ψ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]; rfl

open scoped Pointwise in
/-- The image of `N.subgroupOf M'` under the restriction isomorphism
`ψ.subgroupMap M' : ↥M' ≃* ↥(M'.map ψ)` is `(ψ • N).subgroupOf (ψ • M')`. -/
theorem map_subgroupMap_subgroupOf (ψ : MulAut G) (N M' : Subgroup G) :
    (N.subgroupOf M').map (ψ.subgroupMap M' : ↥M' →* ↥(M'.map (ψ : G →* G))) =
      (N.map (ψ : G →* G)).subgroupOf (M'.map (ψ : G →* G)) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe]
  constructor
  · rintro ⟨y, hyN, rfl⟩
    exact ⟨↑y, hyN, rfl⟩
  · rintro ⟨n, hnN, hn⟩
    obtain ⟨m, hmM', hmx⟩ := Subgroup.mem_map.mp x.2
    have hnm : n = m := ψ.injective (hn.trans hmx.symm)
    exact ⟨⟨n, hnm ▸ hmM'⟩, hnN, Subtype.ext hn⟩

open scoped Pointwise in
/-- **`M_F` is automorphism-equivariant.**  The maximal nilpotent normal Hall
subgroup is natural under any automorphism `φ` of `G`:
`φ • maxNilpotentNormalHall M = maxNilpotentNormalHall (φ • M)`.

Both the candidate set defining `M_F` (the nilpotent normal Hall subgroups of `M`,
phrased entirely in terms of the abstract group structure) and the `sSup` are
preserved by the order-isomorphism `φ • ·`. -/
theorem maxNilpotentNormalHall_pointwise_smul [Finite G] (φ : MulAut G) (M : Subgroup G) :
    φ • maxNilpotentNormalHall M = maxNilpotentNormalHall (φ • M) := by
  -- Membership in the defining candidate set transports along any automorphism `ψ`.
  have transport : ∀ (ψ : MulAut G) (N M' : Subgroup G),
      N ≤ M' → (N.subgroupOf M').Normal → Group.IsNilpotent ↥(N.subgroupOf M') →
        OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M') →
      (ψ • N) ≤ (ψ • M') ∧ ((ψ • N).subgroupOf (ψ • M')).Normal ∧
        Group.IsNilpotent ↥((ψ • N).subgroupOf (ψ • M')) ∧
        OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥(ψ • N)).primeFactors
          ((ψ • N).subgroupOf (ψ • M')) := by
    intro ψ N M' hle hnorm hnilp hhall
    have hψN : (ψ • N : Subgroup G) = N.map (ψ : G →* G) := pointwise_mulAut_smul_eq_map ψ N
    have hψM : (ψ • M' : Subgroup G) = M'.map (ψ : G →* G) := pointwise_mulAut_smul_eq_map ψ M'
    have hcardN : Nat.card ↥(ψ • N) = Nat.card ↥N := by
      rw [hψN]; exact Subgroup.card_map_of_injective ψ.injective
    set e : ↥M' ≃* ↥(M'.map (ψ : G →* G)) := ψ.subgroupMap M' with he
    have eInj : Function.Injective (e : ↥M' →* ↥(M'.map (ψ : G →* G))) := e.injective
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hψN, hψM]; exact Subgroup.map_mono hle
    · rw [hψN, hψM, ← map_subgroupMap_subgroupOf]
      exact hnorm.map (e : ↥M' →* ↥(M'.map (ψ : G →* G))) e.surjective
    · rw [hψN, hψM, ← map_subgroupMap_subgroupOf]
      have := hnilp
      exact Group.nilpotent_of_mulEquiv (e.subgroupMap (N.subgroupOf M'))
    · rw [hcardN, hψN, hψM, ← map_subgroupMap_subgroupOf]
      have hidx : ((N.subgroupOf M').map (e : ↥M' →* ↥(M'.map (ψ : G →* G)))).index =
          (N.subgroupOf M').index := by
        have h1 := Subgroup.card_mul_index (N.subgroupOf M')
        have h2 := Subgroup.card_mul_index
          ((N.subgroupOf M').map (e : ↥M' →* ↥(M'.map (ψ : G →* G))))
        rw [Subgroup.card_map_of_injective eInj, ← Nat.card_congr e.toEquiv] at h2
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
      refine ⟨fun p hp => hhall.1 p ?_, fun p hp => hhall.2 p ?_⟩
      · rwa [Subgroup.card_map_of_injective eInj] at hp
      · rwa [hidx] at hp
  refine le_antisymm ?_ ?_
  · rw [pointwise_mulAut_smul_eq_map φ (maxNilpotentNormalHall M),
        Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro N hN
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨h1, h2, h3, h4⟩ := hN
    have hT := transport φ N M h1 h2 h3 h4
    rw [pointwise_mulAut_smul_eq_map φ N] at hT
    exact le_sSup hT
  · apply sSup_le
    intro N' hN'
    obtain ⟨h1, h2, h3, h4⟩ := hN'
    have hT := transport φ⁻¹ N' (φ • M) h1 h2 h3 h4
    rw [inv_smul_smul] at hT
    have hle : φ⁻¹ • N' ≤ maxNilpotentNormalHall M := le_sSup hT
    have hmono : φ • (φ⁻¹ • N') ≤ φ • maxNilpotentNormalHall M :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hle
    rwa [smul_inv_smul] at hmono

end OddOrder.GroupTheory


