-- Prove2me | Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
-- name    : OddOrder_GroupTheory_MaximalSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:29.712194+00:00
-- url     : https://prove2.me/theorems/46e688d5-e3a7-433d-a39d-81ef8c33dca9
-- title:
--   Maximal subgroup families $\mathcal{M}$, $\mathcal{M}(H)$ and the uniqueness predicate $\mathcal{U}$
-- statement:
--   The shared Bender–Glauberman notation for the family of maximal subgroups and the uniqueness subgroups of a group $G$, introduced in BG §7 and used throughout §8-§16.
--
--   Main definitions: `maximalSubgroups` (BG $\mathcal{M}$, the coatoms of the subgroup lattice), `maximalSubgroupsContaining` ($\mathcal{M}(H)$, the maximal subgroups containing $H$), `IsUniquelyMaximal` (BG $H\in\mathcal{U}$, $H$ is uniquely maximal) and `uniqueMaximalSubgroup`.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/MaximalSubgroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Max
import Mathlib.Order.Atoms

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℳ`** (§7): the family of *maximal subgroups* of `G` — the coatoms of the subgroup
lattice (proper subgroups `M < ⊤` maximal under inclusion). -/
def maximalSubgroups (G : Type*) [Group G] : Set (Subgroup G) :=
  {M | IsCoatom M}

/-- **BG `ℳ(H)`** (§7): the maximal subgroups of `G` containing `H`. -/
def maximalSubgroupsContaining (H : Subgroup G) : Set (Subgroup G) :=
  {M | IsCoatom M ∧ H ≤ M}

/-- **BG `H ∈ 𝒰`** (§9, Uniqueness): `H` is *uniquely maximal* — a proper subgroup contained
in exactly one maximal subgroup of `G`. The BG Uniqueness Theorem (Thm 9.6) concludes
`K ∈ 𝒰` for various `K`, and §10–§16 use `𝒰`-membership to pin down the maximal subgroup
attached to a local structure. -/
def IsUniquelyMaximal (H : Subgroup G) : Prop :=
  H < ⊤ ∧ ∃! M : Subgroup G, IsCoatom M ∧ H ≤ M

@[simp]
theorem mem_maximalSubgroups {M : Subgroup G} : M ∈ maximalSubgroups G ↔ IsCoatom M :=
  Iff.rfl

@[simp]
theorem mem_maximalSubgroupsContaining {H M : Subgroup G} :
    M ∈ maximalSubgroupsContaining H ↔ IsCoatom M ∧ H ≤ M :=
  Iff.rfl

/-- In a finite group, if there is a maximal subgroup over `H` different from `M`, then
one can choose such a counterexample maximizing any natural-valued measure `w`.

This is the Lean form of the BG phrase "choose `K ∈ ℳ(H)` maximal subject to ...".
The measure is kept abstract so later arguments can instantiate it with a cardinal, a
Sylow-order, or a `p`-part without changing the choice API. -/
theorem exists_maximal_counterexample_image [Finite (Subgroup G)] {H M : Subgroup G}
    (w : Subgroup G → ℕ)
    (hne : ∃ K : Subgroup G, K ∈ maximalSubgroups G ∧ H ≤ K ∧ K ≠ M) :
    ∃ K : Subgroup G,
      K ∈ maximalSubgroups G ∧ H ≤ K ∧ K ≠ M ∧
        ∀ L : Subgroup G, L ∈ maximalSubgroups G → H ≤ L → L ≠ M → w L ≤ w K := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  let family : Finset (Subgroup G) :=
    Finset.univ.filter (fun K => K ∈ maximalSubgroups G ∧ H ≤ K ∧ K ≠ M)
  have hfamily_ne : family.Nonempty := by
    rcases hne with ⟨K, hK, hHK, hKM⟩
    exact ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ K, hK, hHK, hKM⟩⟩
  obtain ⟨K, hK_mem, hK_max⟩ := family.exists_max_image w hfamily_ne
  obtain ⟨_, hK, hHK, hKM⟩ := Finset.mem_filter.mp hK_mem
  refine ⟨K, hK, hHK, hKM, ?_⟩
  intro L hL hHL hLM
  exact hK_max L (Finset.mem_filter.mpr ⟨Finset.mem_univ L, hL, hHL, hLM⟩)

namespace IsUniquelyMaximal

/-- A uniquely maximal subgroup is proper. -/
theorem lt_top {H : Subgroup G} (h : IsUniquelyMaximal H) : H < ⊤ :=
  h.1

/-- The unique maximal subgroup containing a uniquely maximal `H` (its `ℳ(H)`-singleton). -/
theorem existsUnique {H : Subgroup G} (h : IsUniquelyMaximal H) :
    ∃! M : Subgroup G, IsCoatom M ∧ H ≤ M :=
  h.2

/-- The maximal subgroup attached to a uniquely maximal `H`. -/
noncomputable def uniqueMaximalSubgroup {H : Subgroup G} (h : IsUniquelyMaximal H) :
    Subgroup G :=
  Classical.choose h.existsUnique

/-- To prove `H ∈ 𝒰`, it suffices to exhibit one maximal subgroup over `H` and prove
that every maximal subgroup over `H` is that one. -/
theorem of_unique_maximal {H M : Subgroup G}
    (hH : H < ⊤) (hM : M ∈ maximalSubgroups G) (hHM : H ≤ M)
    (huniq : ∀ N : Subgroup G, N ∈ maximalSubgroups G → H ≤ N → N = M) :
    IsUniquelyMaximal H := by
  refine ⟨hH, ⟨M, ⟨hM, hHM⟩, ?_⟩⟩
  intro N hN
  exact huniq N hN.1 hN.2

/-- The chosen maximal subgroup over `H` is maximal and contains `H`. -/
theorem uniqueMaximalSubgroup_spec {H : Subgroup G} (h : IsUniquelyMaximal H) :
    IsCoatom (h.uniqueMaximalSubgroup) ∧ H ≤ h.uniqueMaximalSubgroup :=
  (Classical.choose_spec h.existsUnique).1

/-- The chosen maximal subgroup over `H` is a member of `ℳ(H)`. -/
theorem uniqueMaximalSubgroup_mem {H : Subgroup G} (h : IsUniquelyMaximal H) :
    h.uniqueMaximalSubgroup ∈ maximalSubgroupsContaining H :=
  h.uniqueMaximalSubgroup_spec

/-- The chosen maximal subgroup over `H` is maximal. -/
theorem uniqueMaximalSubgroup_isCoatom {H : Subgroup G} (h : IsUniquelyMaximal H) :
    IsCoatom h.uniqueMaximalSubgroup :=
  h.uniqueMaximalSubgroup_spec.1

/-- The uniquely maximal subgroup `H` lies in its chosen maximal subgroup. -/
theorem le_uniqueMaximalSubgroup {H : Subgroup G} (h : IsUniquelyMaximal H) :
    H ≤ h.uniqueMaximalSubgroup :=
  h.uniqueMaximalSubgroup_spec.2

/-- Any maximal subgroup containing `H` is the chosen one. -/
theorem eq_uniqueMaximalSubgroup_of_isCoatom_of_le {H M : Subgroup G}
    (h : IsUniquelyMaximal H) (hM : IsCoatom M) (hHM : H ≤ M) :
    M = h.uniqueMaximalSubgroup :=
  (Classical.choose_spec h.existsUnique).2 M ⟨hM, hHM⟩

/-- Two maximal subgroups containing a uniquely maximal `H` are equal. -/
theorem eq_of_isCoatom_of_le {H M N : Subgroup G} (h : IsUniquelyMaximal H)
    (hM : IsCoatom M) (hHM : H ≤ M) (hN : IsCoatom N) (hHN : H ≤ N) :
    M = N :=
  (h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hM hHM).trans
    (h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hN hHN).symm

/-- If a uniquely maximal subgroup lies in a proper overgroup, that overgroup is also
uniquely maximal. -/
theorem of_le_of_lt_top [Finite (Subgroup G)] {H K : Subgroup G} (h : IsUniquelyMaximal H)
    (hHK : H ≤ K) (hK : K < ⊤) : IsUniquelyMaximal K := by
  classical
  obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK.ne
  refine IsUniquelyMaximal.of_unique_maximal hK hM hKM ?_
  intro N hN hKN
  exact h.eq_of_isCoatom_of_le hN (hHK.trans hKN) hM (hHK.trans hKM)

/-- Transport unique maximality across a group isomorphism. -/
theorem map_equiv {G' : Type*} [Group G'] {H : Subgroup G} (φ : G ≃* G')
    (h : IsUniquelyMaximal H) : IsUniquelyMaximal (H.map (φ : G →* G')) := by
  classical
  obtain ⟨M, hM, huniq⟩ := h.existsUnique
  refine ⟨?_, ⟨M.map φ, ⟨?_, Subgroup.map_mono hM.2⟩, ?_⟩⟩
  · simpa using (Subgroup.map_lt_map_iff_of_injective (f := (φ : G →* G')) φ.injective).mpr
      h.lt_top
  · exact (OrderIso.isCoatom_iff (φ.mapSubgroup) M).mpr hM.1
  · intro N hN
    have hNco : IsCoatom (N.comap (φ : G →* G')) :=
      (OrderIso.isCoatom_iff (φ.comapSubgroup) N).mpr hN.1
    have hHN : H ≤ N.comap (φ : G →* G') :=
      (Subgroup.map_le_iff_le_comap).mp hN.2
    have hcomap_eq : N.comap (φ : G →* G') = M :=
      huniq (N.comap (φ : G →* G')) ⟨hNco, hHN⟩
    calc
      N = (N.comap (φ : G →* G')).map (φ : G →* G') :=
        (Subgroup.map_comap_eq_self_of_surjective φ.surjective N).symm
      _ = M.map φ := by rw [hcomap_eq]

/-- Pull unique maximality back across a group isomorphism. -/
theorem comap_equiv {G' : Type*} [Group G'] {H : Subgroup G'} (φ : G ≃* G')
    (h : IsUniquelyMaximal H) : IsUniquelyMaximal (H.comap (φ : G →* G')) := by
  simpa [Subgroup.comap_equiv_eq_map_symm] using h.map_equiv φ.symm

/-- Membership in `ℳ(H)` is equality with the chosen maximal subgroup. -/
theorem mem_maximalSubgroupsContaining_iff_eq_uniqueMaximalSubgroup {H M : Subgroup G}
    (h : IsUniquelyMaximal H) :
    M ∈ maximalSubgroupsContaining H ↔ M = h.uniqueMaximalSubgroup := by
  constructor
  · intro hM
    exact h.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hM.1 hM.2
  · intro hM
    rw [hM]
    exact h.uniqueMaximalSubgroup_mem

/-- `ℳ(H)` is the singleton consisting of the chosen maximal subgroup. -/
theorem maximalSubgroupsContaining_eq_singleton {H : Subgroup G} (h : IsUniquelyMaximal H) :
    maximalSubgroupsContaining H = {h.uniqueMaximalSubgroup} := by
  ext M
  rw [h.mem_maximalSubgroupsContaining_iff_eq_uniqueMaximalSubgroup, Set.mem_singleton_iff]

end IsUniquelyMaximal

/-- If a proper subgroup `H` lies in a known maximal subgroup `M` but is not uniquely maximal,
then there is another maximal subgroup over `H` different from `M`. -/
theorem exists_maximal_counterexample_of_not_isUniquelyMaximal {H M : Subgroup G}
    (hHproper : H < ⊤) (hM : M ∈ maximalSubgroups G) (hHM : H ≤ M)
    (hnot : ¬ IsUniquelyMaximal H) :
    ∃ K : Subgroup G, K ∈ maximalSubgroups G ∧ H ≤ K ∧ K ≠ M := by
  by_contra hnone
  apply hnot
  refine IsUniquelyMaximal.of_unique_maximal hHproper hM hHM ?_
  intro K hK hHK
  by_contra hKM
  exact hnone ⟨K, hK, hHK, hKM⟩

/-- If a proper subgroup `H` lies in a known maximal subgroup `M` but is not uniquely maximal,
choose a different maximal subgroup over `H` maximizing a natural-valued measure `w`. -/
theorem exists_maximal_counterexample_image_of_not_isUniquelyMaximal
    [Finite (Subgroup G)] {H M : Subgroup G} (w : Subgroup G → ℕ)
    (hHproper : H < ⊤) (hM : M ∈ maximalSubgroups G) (hHM : H ≤ M)
    (hnot : ¬ IsUniquelyMaximal H) :
    ∃ K : Subgroup G,
      K ∈ maximalSubgroups G ∧ H ≤ K ∧ K ≠ M ∧
        ∀ L : Subgroup G, L ∈ maximalSubgroups G → H ≤ L → L ≠ M → w L ≤ w K :=
  exists_maximal_counterexample_image w
    (exists_maximal_counterexample_of_not_isUniquelyMaximal hHproper hM hHM hnot)

end OddOrder.GroupTheory


