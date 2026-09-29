-- Prove2me | Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup
-- name    : Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e62fdf0a-6468-5316-b243-b6ac911407a4
-- title:
--   Lower ramification groups under subgroups and compatible homomorphisms
-- statement:
--   Throughout, $R$ is a commutative local ring with maximal ideal $\mathfrak m$, acted on by a group $G$ through ring automorphisms, and $\mathrm{lowerRamificationGroup}\ R\ G\ i$ is the subgroup of those $\sigma \in G$ with $\sigma x - x \in \mathfrak m^{i+1}$ for every $x \in R$ (the inertia subgroup of the ideal $\mathfrak m^{i+1}$). The module records how this filtration behaves under change of acting group. The basic functoriality statement is [`IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.html#L15): if $H$ also acts on $R$ and $f : H \to G$ is a group homomorphism with $f(h) \cdot x = h \cdot x$ for all $h \in H$, $x \in R$, then for every $i$ the $i$-th lower ramification group of $H$ is the preimage under $f$ of that of $G$. For a subgroup $H \le G$, acting by restriction, the consequences are: membership of $\sigma \in H$ in the $i$-th group of $H$ is membership of its image in the $i$-th group of $G$; the $i$-th group of $H$ is exactly $G_i$ viewed inside $H$ (`subgroupOf`); its image under the inclusion $H \hookrightarrow G$ is $G_i \cap H$, in both orders of the intersection; the $i$-th group of $H$ is all of $H$ precisely when $H \le G_i$; for $H \le K \le G$ the filtration of $H$ is the preimage of that of $K$ along the inclusion, and the images in $G$ are monotone in the subgroup. In the second half, $L/K$ is an extension of fields, $A$ a valuation subring of $L$, and $H$ a subgroup of the decomposition subgroup $D = A.\mathrm{decompositionSubgroup}\ K$; the same statements are given for $A.\mathrm{lowerRamificationGroup}\ K\ i \le D$, together with the case $i = 0$, where the image in $D$ of the zeroth group of $H$ is the intersection of the inertia subgroup of $A$ over $K$ with $H$.
--
--   **Relation to Mathlib.** The lower ramification filtration used here is the project's own ([`IsLocalRing.lowerRamificationGroup`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58), defined as the inertia subgroup of $\mathfrak m^{i+1}$ in the sense of Mathlib's `Ideal.inertia`, and its valuation-subring version relative to Mathlib's `decompositionSubgroup` and `inertiaSubgroup`); this module supplies the subgroup- and homomorphism-compatibility lemmas for it.
--
--   **Where it is used.** These lemmas let the lower ramification filtration be transported along inclusions of groups acting on the same local ring, for instance when restricting from a decomposition subgroup to the subgroup attached to a subextension, which is how the filtration is used in local ramification computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

section CompatibleHom

variable {H : Type*} [Group H] [MulSemiringAction H R]

theorem lowerRamificationGroup_comap_of_forall_smul_eq (f : H →* G)
    (hf : ∀ (h : H) (x : R), f h • x = h • x) (i : ℕ) :
    lowerRamificationGroup R H i = (lowerRamificationGroup R G i).comap f := by
  ext σ
  simp only [mem_lowerRamificationGroup, Subgroup.mem_comap, hf]

end CompatibleHom

section Subgroup

theorem mem_lowerRamificationGroup_subgroup {H : Subgroup G} {σ : H} {i : ℕ} :
    σ ∈ lowerRamificationGroup R H i ↔ (σ : G) ∈ lowerRamificationGroup R G i :=
  Iff.rfl

@[simp]
theorem lowerRamificationGroup_subgroupOf (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R G i).subgroupOf H = lowerRamificationGroup R H i :=
  rfl

@[simp]
theorem lowerRamificationGroup_map_subtype (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype = lowerRamificationGroup R G i ⊓ H := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_map_subtype]

theorem lowerRamificationGroup_map_subtype' (H : Subgroup G) (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype = H ⊓ lowerRamificationGroup R G i := by
  rw [lowerRamificationGroup_map_subtype, inf_comm]

theorem lowerRamificationGroup_subgroup_eq_top_iff (H : Subgroup G) (i : ℕ) :
    lowerRamificationGroup R H i = ⊤ ↔ H ≤ lowerRamificationGroup R G i := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_eq_top]

theorem lowerRamificationGroup_comap_inclusion {H K : Subgroup G} (hHK : H ≤ K) (i : ℕ) :
    lowerRamificationGroup R H i =
      (lowerRamificationGroup R K i).comap (Subgroup.inclusion hHK) :=
  lowerRamificationGroup_comap_of_forall_smul_eq (Subgroup.inclusion hHK) (fun _ _ => rfl) i

theorem lowerRamificationGroup_map_subtype_le_map_subtype {H K : Subgroup G} (hHK : H ≤ K)
    (i : ℕ) :
    (lowerRamificationGroup R H i).map H.subtype ≤
      (lowerRamificationGroup R K i).map K.subtype := by
  rw [lowerRamificationGroup_map_subtype, lowerRamificationGroup_map_subtype]
  exact inf_le_inf_left _ hHK

end Subgroup

end IsLocalRing

namespace ValuationSubring

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L}

@[simp]
theorem lowerRamificationGroup_subgroupOf (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (A.lowerRamificationGroup K i).subgroupOf H = IsLocalRing.lowerRamificationGroup A H i :=
  rfl

theorem mem_lowerRamificationGroup_subgroup {H : Subgroup (A.decompositionSubgroup K)} {σ : H}
    {i : ℕ} :
    σ ∈ IsLocalRing.lowerRamificationGroup A H i ↔
      (σ : A.decompositionSubgroup K) ∈ A.lowerRamificationGroup K i :=
  Iff.rfl

@[simp]
theorem lowerRamificationGroup_map_subtype (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A H i).map H.subtype =
      A.lowerRamificationGroup K i ⊓ H := by
  rw [← lowerRamificationGroup_subgroupOf H i, Subgroup.subgroupOf_map_subtype]

theorem lowerRamificationGroup_zero_map_subtype (H : Subgroup (A.decompositionSubgroup K)) :
    (IsLocalRing.lowerRamificationGroup A H 0).map H.subtype =
      A.inertiaSubgroup K ⊓ H := by
  rw [lowerRamificationGroup_map_subtype, lowerRamificationGroup_zero]

end ValuationSubring

section Gates

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

example (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup R (⊤ : Subgroup G) i).map (⊤ : Subgroup G).subtype =
      IsLocalRing.lowerRamificationGroup R G i := by
  rw [IsLocalRing.lowerRamificationGroup_map_subtype, inf_top_eq]

example (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R (⊥ : Subgroup G) i = ⊤ :=
  (IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff ⊥ i).mpr bot_le

example [Subsingleton G] (H : Subgroup G) (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R H i = ⊤ := by
  refine (IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff H i).mpr fun σ _ => ?_
  rw [IsLocalRing.mem_lowerRamificationGroup]
  intro x
  rw [Subsingleton.elim σ 1, one_smul, sub_self]
  exact zero_mem _

example (H : Subgroup G) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup R H (i + 1)).map H.subtype ≤
      (IsLocalRing.lowerRamificationGroup R H i).map H.subtype := by
  rw [IsLocalRing.lowerRamificationGroup_map_subtype,
    IsLocalRing.lowerRamificationGroup_map_subtype]
  exact inf_le_inf_right _ (IsLocalRing.lowerRamificationGroup_antitone (by omega))

example {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A (⊤ : Subgroup (A.decompositionSubgroup K)) i).map
        (⊤ : Subgroup (A.decompositionSubgroup K)).subtype =
      A.lowerRamificationGroup K i := by
  rw [ValuationSubring.lowerRamificationGroup_map_subtype, inf_top_eq]

example {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (H : Subgroup (A.decompositionSubgroup K)) (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup A H i).map H.subtype ≤ A.inertiaSubgroup K := by
  rw [ValuationSubring.lowerRamificationGroup_map_subtype]
  exact le_trans inf_le_left (ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup i)

end Gates

/--
info: 'IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_comap_of_forall_smul_eq

/--
info: 'IsLocalRing.lowerRamificationGroup_subgroupOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_subgroupOf

/--
info: 'IsLocalRing.lowerRamificationGroup_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_map_subtype

/--
info: 'IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_subgroup_eq_top_iff

/--
info: 'IsLocalRing.lowerRamificationGroup_comap_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_comap_inclusion

/--
info: 'ValuationSubring.lowerRamificationGroup_subgroupOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_subgroupOf

/--
info: 'ValuationSubring.lowerRamificationGroup_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_map_subtype

/--
info: 'ValuationSubring.lowerRamificationGroup_zero_map_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_zero_map_subtype


