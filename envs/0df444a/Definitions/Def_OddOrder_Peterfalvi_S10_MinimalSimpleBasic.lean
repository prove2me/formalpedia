-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleBasic
-- name    : OddOrder_Peterfalvi_S10_MinimalSimpleBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:14:25.238201+00:00
-- url     : https://prove2.me/theorems/6d9c9b4c-8461-4e07-940d-ba74557ffe64
-- title:
--   Peterfalvi §10: minimal simple groups, basic layer (continuation)
-- statement:
--   A continuation of the basic layer of the minimal-simple-groups development of Peterfalvi, *Character Theory for the Odd Order Theorem*, §10. It consists of lemmas only, including normalizer support, Dade support hypothesis data, and conjugation statements for the sets $A_1$, type IA and type $\mathcal{P}A$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 21 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_MinimalSimpleBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_MinimalSimpleBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup
import Definitions.Def_OddOrder_Peterfalvi_S10_ConjugationTransport

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Conjugation transports the centralizer of a singleton:
`g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)` (local copy of the S12/S14 helper; pure group theory). -/
theorem conj_smul_centralizer_singleton' (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group

/-- **(8.15) normalizer identification**: for a nonempty `M`-invariant `X ⊆ M ∖ {1}`,
`N_G(X) = M`.  Peterfalvi: `X ⊆ M ⊆ N_G(X)`; if `N_G(X) = G` then `⟨X⟩` would be a nontrivial
normal subgroup inside the proper `M`, contradicting simplicity; maximality forces equality. -/
theorem normalizer_support_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Set G}
    (hXM : X ⊆ (M : Set G)) (hX1 : ∀ x ∈ X, x ≠ (1 : G)) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Subgroup.normalizer X = M := by
  have hMle : M ≤ Subgroup.normalizer X := by
    intro m hm
    rw [Subgroup.mem_set_normalizer_iff]
    exact fun n => (hXiff hm).symm
  rcases eq_or_lt_of_le hMle with h | h
  · exact h.symm
  · exfalso
    have hcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
    have htop : Subgroup.normalizer X = ⊤ := hcoatom.2 _ h
    have hGinv : ∀ g x : G, x ∈ X → g * x * g⁻¹ ∈ X := by
      intro g x hx
      have hg : g ∈ Subgroup.normalizer X := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx
    have hnormal : (Subgroup.closure X).Normal := by
      constructor
      intro n hn g
      induction hn using Subgroup.closure_induction with
      | mem x hx => exact Subgroup.subset_closure (hGinv g x hx)
      | one => simp
      | mul x y _ _ hx hy =>
          have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          rw [hxy]; exact mul_mem hx hy
      | inv x _ hx =>
          have hxi : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
          rw [hxi]; exact inv_mem hx
    obtain ⟨x0, hx0⟩ := hXne
    have hle : Subgroup.closure X ≤ M := (Subgroup.closure_le M).mpr hXM
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnormal with hb | ht
    · exact hX1 x0 hx0 (Subgroup.mem_bot.mp (hb ▸ Subgroup.subset_closure hx0))
    · exact hcoatom.1 (top_le_iff.mp (ht ▸ hle))

/-- **Faithful (8.15) datum for an `M`-invariant sub-support of `A(M)`** (assembly): the (2.2)
kernel at `a` is `ftSupportKernel M X a`; escaping points get the (8.13.c1/c2) semidirect
structure from `escaping_typeIA_signalizer_structure`, non-escaping points are the trivial
`C_G(a) = C_M(a)` case.  Instantiated at `X = A(M)` and `X = A₁(M)` below. -/
theorem dadeSupportHypothesisData_of_subset [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {X : Set G} (hXA : X ⊆ typeIA M data) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hXsharp : ∀ x ∈ X, x ≠ (1 : G) := fun x hx =>
    (OddOrder.Peterfalvi.S04.mem_sharp.mp (typeIA_subset_sharp M data (hXA hx))).2
  have hXM : X ⊆ (M : Set G) := fun x hx => typeIA_subset M data (hXA hx)
  -- the escaping-point structure, converted from the `A(M)`-level pin to `X`-level points
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ typeIA M data,
          Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) :=
    fun {a} ha => escaping_typeIA_signalizer_structure hG hM data ⟨hXA ha.1, ha.2⟩
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ :=
                    typeIA_isConj_conj_in_M hG hM data (hXA ha) (hXA hb) hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 (hXA b.2)
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simp }
            H_eq_ftSupportKernel := fun _ => rfl
            }⟩

/-- `A₁(M) = (M_F)^# ⊆ A(M)` for type I (`M_s = M_F = H`, and `x ∈ H^#` centralizes itself). -/
theorem A1_subset_typeIA (M : Subgroup G) (data : TypeIData M) :
    A1 M PeterfalviType.I ⊆ typeIA M data := by
  intro x hx
  obtain ⟨hxH, hx1⟩ := (Set.mem_sdiff x).mp hx
  have hx1' : x ≠ 1 := fun h => hx1 (Set.mem_singleton_iff.mpr h)
  have hxH' : x ∈ data.typeF.H := data.typeF.H_eq ▸ SetLike.mem_coe.mp hxH
  exact ⟨data.typeF.H_le hxH', hx1',
    x, (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr hxH', hx1⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-- **`M`-conjugation invariance of `A₁(M) = M_s#`** for every Peterfalvi type: `M_s` is `M_F`
(types I, II, V) or `M'` (types III, IV), both `⊴ M`. -/
theorem A1_conj_mem (M : Subgroup G) (tau : OddOrder.GroupTheory.PeterfalviType) {m : G}
    (hm : m ∈ M) {a : G} (ha : a ∈ A1 M tau) : m * a * m⁻¹ ∈ A1 M tau := by
  refine sharpSubgroup_conj_mem (H := OddOrder.GroupTheory.mainSubgroup M tau) ?_ ha
  cases tau with
  | I => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | II => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | V => exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
  | III => exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm
  | IV => exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm

/-- **`M`-conjugation invariance of the type-`P` support `A(M) = (M')#`** (`M' ⊴ M`). -/
theorem typePA_conj_mem (M : Subgroup G) (data : TypePData M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ typePA M data) : m * a * m⁻¹ ∈ typePA M data := by
  rw [typePA_eq_sharpSubgroup_derivedInG] at ha ⊢
  exact sharpSubgroup_conj_mem (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm) ha

/-- **Type-`P₁` support is `M_σ#`** (`A(M) = (M')# = M_σ#`).  For a type-`P₁` maximal subgroup
`M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`, from `mainSubgroup_eq_Msigma`/BG Prop 16.1), so the
Peterfalvi Dade support `typePA = (M')#` coincides with the BG σ-sharp set `sigmaSharp = M_σ#`.

This is the structural bridge that makes the type-`P` Dade-support escaping structure a **direct**
application of the σ-sharp signalizer machinery (`signalizer_structure_of_mem_sigmaSharp`), with no
`ASet` detour: every escaping point of `A(M)` is already `σ`-sharp.  (For type `P₂`, `M_σ ⊊ M'`, so
`typePA ⊋ M_σ#`; the escaping points still land in `A_1 = M_σ#` by Peterfalvi (8.13.b) +
`A1_eq_sigmaSharp`, but that reduction is the deeper type-`P₂` obligation.) -/
theorem typePA_eq_sigmaSharp_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    typePA M data = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  rw [typePA_eq_sharpSubgroup_derivedInG,
    OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hM hP1]
  rfl

/-- **Peterfalvi (4.6.b) / (4.3.a), ambient version**: for a type-`P` maximal subgroup, the
exceptional set `V = W − (W₁ ∪ W₂)` is a TI-subset of `G` with normalizer-bound `W`.

Given `g` conjugating some `a ∈ V` into `V`, the singleton normalizer fact `N_G({a}) = W`
(`TypePData.normalizer_V`) forces `g` to normalize `W` — both `h ∈ W` and `g h g⁻¹ ∈ W` reduce to
`h a h⁻¹ = a`.  Since `W = W₁ × W₂` is cyclic with coprime factors, `W₁` and `W₂` are the *unique*
subgroups of their orders (`cyclic_subgroup_eq_of_card_eq`), hence characteristic, so `g` also
normalizes `W₁` and `W₂` and therefore `V`; finally `N_G(V) = W` (`normalizer_V` with `X = V`) gives
`g ∈ W`.  This is the `V`-conjugacy control behind the type-`P` `A_0(M)` support (`(8.13.a)` for the
exceptional part) and the §10 → §5 ω-grid bridge (S12). -/
theorem typePData_V_ti [Finite G] {M : Subgroup G} (data : TypePData M) :
    IsTISubset (typePV M data) data.W := by
  classical
  have : IsCyclic ↥data.W := data.W_cyclic
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have mem_norm_sing : ∀ c z : G,
      z ∈ Subgroup.normalizer ({c} : Set G) ↔ z * c * z⁻¹ = c := by
    intro c z
    rw [Subgroup.mem_set_normalizer_iff]
    constructor
    · intro hz
      have := (hz c).mp rfl
      simpa using this
    · intro hz h
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro rfl; exact hz
      · intro hh
        have hcc : z * h * z⁻¹ = z * c * z⁻¹ := by rw [hh, hz]
        exact mul_left_cancel (mul_right_cancel hcc)
  intro g hg
  obtain ⟨a, haV, hbV⟩ := hg
  have hNa : Subgroup.normalizer ({a} : Set G) = data.W :=
    data.normalizer_V {a} (Set.singleton_nonempty a) (Set.singleton_subset_iff.mpr haV)
  have hNb : Subgroup.normalizer ({g * a * g⁻¹} : Set G) = data.W :=
    data.normalizer_V {g * a * g⁻¹} (Set.singleton_nonempty _) (Set.singleton_subset_iff.mpr hbV)
  have hgW : ∀ h, h ∈ data.W ↔ g * h * g⁻¹ ∈ data.W := by
    intro h
    have e1 : (h ∈ data.W) ↔ h * a * h⁻¹ = a := by rw [← hNa, mem_norm_sing]
    have e2 : (g * h * g⁻¹ ∈ data.W) ↔ h * a * h⁻¹ = a := by
      rw [← hNb, mem_norm_sing]
      have hexp : g * h * g⁻¹ * (g * a * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ := by
        group
      rw [hexp]
      constructor
      · intro hh; exact mul_left_cancel (mul_right_cancel hh)
      · intro hh; rw [hh]
    rw [e1, e2]
  have hstab : ∀ (A : Subgroup G), A ≤ data.W → ∀ x : G, g * x * g⁻¹ ∈ A ↔ x ∈ A := by
    intro A hAW
    have hmap_le : A.map (MulAut.conj g).toMonoidHom ≤ data.W := by
      rintro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hzA, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (hgW z).mp (hAW hzA)
    have hcard : Nat.card ↥(A.map (MulAut.conj g).toMonoidHom) = Nat.card ↥A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
    have hsubeq : (A.map (MulAut.conj g).toMonoidHom).subgroupOf data.W
        = A.subgroupOf data.W := by
      apply OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq (C := ↥data.W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmap_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv, hcard]
    have hmapeq : A.map (MulAut.conj g).toMonoidHom = A := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hmap_le, hsubeq,
        Subgroup.map_subgroupOf_eq_of_le hAW]
    intro x
    constructor
    · intro hx
      have hmem : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := by rw [hmapeq]; exact hx
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hzA, hz⟩ := hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hz
      have hzx : z = x := mul_left_cancel (mul_right_cancel hz)
      rwa [hzx] at hzA
    · intro hx
      have hmem : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hmapeq] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [← data.normalizer_V (typePV M data) ⟨a, haV⟩ Set.Subset.rfl,
    Subgroup.mem_set_normalizer_iff]
  intro h
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe]
  rw [hgW h, hstab data.W1 hW1le h, hstab data.W2 hW2le h]

/-- An element of the exceptional set `V = W − (W₁ ∪ W₂)` of a type-`P` maximal subgroup lies
outside the derived subgroup `M' = [M,M]`.  Decompose `v ∈ W = W₁ ⊔ W₂` (cyclic, abelian) as
`v = x·y` (`x ∈ W₁`, `y ∈ W₂`); `W₂ ≤ M'`, so `v ∈ M'` forces `x = v·y⁻¹ ∈ W₁ ⊓ M' = ⊥`
(`M_complement`), i.e. `x = 1` and `v = y ∈ W₂`, contradicting `v ∉ W₂`.  (Upstreamed here for the
type-`P` `A_0(M)` support geometry; also used in S12's §10 Dade-image analysis.) -/
theorem typePData_typePV_not_mem_derived {M : Subgroup G} (data : TypePData M)
    {v : G} (hv : v ∈ typePV M data) : v ∉ derivedInG M := by
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at hv
  obtain ⟨hvW, _hvnW1, hvnW2⟩ := hv
  intro hvM'
  have hcyc : IsCyclic ↥data.W := data.W_cyclic
  let : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hsup : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hvmem : (⟨v, hvW⟩ : ↥data.W) ∈
      data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W := by
    rw [hsup]; exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hvmem
  obtain ⟨a, ha, b, hb, hab⟩ := hvmem
  have haW1 : ((a : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp ha
  have hbW2 : ((b : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hb
  have habG : ((a : ↥data.W) : G) * ((b : ↥data.W) : G) = v := by
    have := congrArg (Subtype.val) hab
    simpa using this
  have hW2D : data.W2 ≤ derivedInG M := data.W2_le.trans (inf_le_left.trans data.H_le)
  have haM' : ((a : ↥data.W) : G) ∈ derivedInG M := by
    have heq : ((a : ↥data.W) : G) = v * ((b : ↥data.W) : G)⁻¹ := by rw [← habG]; group
    rw [heq]; exact mul_mem hvM' (inv_mem (hW2D hbW2))
  have haM : ((a : ↥data.W) : G) ∈ M := data.W1_le haW1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hm1 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haM'
  have hm2 : (⟨(a : ↥data.W), haM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr haW1
  have ha1 : ((a : ↥data.W) : G) = 1 := Subtype.ext_iff.mp (hdisj hm1 hm2)
  exact hvnW2 (by rw [← habG, ha1, one_mul]; exact hbW2)

/-- **Type-`P` exceptional points are non-escaping**: for `v ∈ V = W ∖ (W₁ ∪ W₂)`, the singleton
normalizer `N_G(⟨v⟩) = W` (`TypePData.normalizer_V`) equals `C_G(v)` (singleton: centralizing ⟺
normalizing), and `W = W₁ ⊔ W₂ ≤ M`.  So `C_G(v) ≤ M`: the exceptional `V^M`-support of `A_0(M)`
carries the *trivial* (non-escaping) Dade structure `H(v) = ⊥`, `C_G(v) = C_M(v)` — the only part of
`A_0(M)` outside `M_σ^#`, and it needs no signalizer. -/
theorem centralizer_typePV_le_M {M : Subgroup G} (data : TypePData M) {v : G}
    (hv : v ∈ typePV M data) : Subgroup.centralizer ({v} : Set G) ≤ M := by
  have hNV : Subgroup.normalizer ({v} : Set G) = data.W :=
    data.normalizer_V {v} (Set.singleton_nonempty v) (Set.singleton_subset_iff.mpr hv)
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    refine sup_le data.W1_le ?_
    exact data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _)))
  refine le_trans ?_ (hNV.le.trans hWM)
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  have hgv : g * v * g⁻¹ = v := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  intro n
  rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
  constructor
  · intro h; rw [h]; exact hgv
  · intro h
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = g⁻¹ * v * g := by rw [h]
      _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
      _ = v := by group

/-- **Peterfalvi (8.13.b) for the type-`P₁` `A_0`-support**: an escaping point of
`A_0(M) = A(M) ∪ V^M` is `σ`-sharp.  The exceptional `V^M`-points are non-escaping
(`centralizer_typePV_le_M`: `C_G(m·v·m⁻¹) = m·C_G(v)·m⁻¹ ≤ M`), so an escaping point of `A_0` lies
in
`A(M) = M_σ^#` (`typePA_eq_sigmaSharp_of_isTypeP1`).  This is the `(8.13.b)` reduction the `σ`-sharp
Dade engine needs to cover the full `A_0(M)` support (not just `A_1 = M_σ^#`) for type `P₁`. -/
theorem escaping_typePA0_mem_sigmaSharp_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {a : G}
    (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typePA0 M data)) :
    a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
  obtain ⟨haA0, hesc⟩ := ha
  rcases haA0 with hpa | hpv
  · rw [← typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1]
    exact hpa
  · exfalso
    obtain ⟨v, hv, m, hmM, hmva⟩ := hpv
    apply hesc
    rw [← hmva, ← conj_smul_centralizer_singleton']
    calc MulAut.conj m • Subgroup.centralizer ({v} : Set G)
        ≤ MulAut.conj m • M :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (centralizer_typePV_le_M data hv)
      _ = M := conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hmM)

/-- **Peterfalvi (8.13.a) for the exceptional `V^M`-support**: two `G`-conjugate elements of
`V^M = conjClassSetIn M V` are already `M`-conjugate.  Since `V` is a TI-subset with normalizer `W`
(`typePData_V_ti`), writing `a = m₁v₁m₁⁻¹`, `b = m₂v₂m₂⁻¹` and `b = gag⁻¹`, the element
`h = m₂⁻¹gm₁` conjugates `v₁ ∈ V` to `v₂ ∈ V`, so `h ∈ W ≤ M`; then `g = m₂·h·m₁⁻¹ ∈ M` is itself
the `M`-conjugator.  This is the `V^M`-half of the type-`P` `A_0(M)` `isConj` obligation (the
`M_σ^#`-half is `sigmaSharp_isConj_conj_in_M`). -/
theorem conjClassSetIn_typePV_isConj_conj_in_M {M : Subgroup G} (data : TypePData M)
    [Finite G] {a b : G} (ha : a ∈ conjClassSetIn M (typePV M data))
    (hb : b ∈ conjClassSetIn M (typePV M data)) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  obtain ⟨v1, hv1, m1, hm1, hm1a⟩ := ha
  obtain ⟨v2, hv2, m2, hm2, hm2b⟩ := hb
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    refine sup_le data.W1_le ?_
    exact data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _)))
  have hv2eq : (m2⁻¹ * g * m1) * v1 * (m2⁻¹ * g * m1)⁻¹ = v2 := by
    calc (m2⁻¹ * g * m1) * v1 * (m2⁻¹ * g * m1)⁻¹
        = m2⁻¹ * g * (m1 * v1 * m1⁻¹) * g⁻¹ * m2 := by group
      _ = m2⁻¹ * (g * a * g⁻¹) * m2 := by rw [hm1a]; group
      _ = m2⁻¹ * b * m2 := by rw [hg]
      _ = m2⁻¹ * (m2 * v2 * m2⁻¹) * m2 := by rw [hm2b]
      _ = v2 := by group
  have hhW : (m2⁻¹ * g * m1) ∈ data.W :=
    typePData_V_ti data (m2⁻¹ * g * m1) ⟨v1, hv1, by rw [hv2eq]; exact hv2⟩
  have hgM : g ∈ M := by
    have hgeq : g = m2 * (m2⁻¹ * g * m1) * m1⁻¹ := by group
    rw [hgeq]
    exact mul_mem (mul_mem hm2 (hWM hhW)) (inv_mem hm1)
  exact ⟨g, hgM, hg⟩

/-- **Peterfalvi (8.13.a) for the `σ`-sharp support**: two `G`-conjugate elements of `M_σ^#`
are already `M`-conjugate.  This is the `σ`-sharp analogue of `typeIA_isConj_conj_in_M`, but proved
*natively* from the `σ`-decomposition (BG Theorem 14.4,
`exists_conj_centralizer_of_mem_maximalSigma`) rather than through the BG §16 tame embedding.  Since
`A₁(M) = M_σ^#` for every Peterfalvi type (`A1_eq_sigmaSharp`) and `A(M) = (M')^# = M_σ^#` for type
`P₁` (`typePA_eq_sigmaSharp_of_isTypeP1`), this one lemma discharges the Dade-engine `conj_in_L`
obligation on `A₁` uniformly and on the type-`P₁` `A(M)`.

Both `M` and `g^{-1}Mg` are `σ`-maximals of `a` — the latter is a conjugate of `M` containing
`a = g^{-1}bg` (`b ∈ M`), so `maximalConjugatesContaining_eq_maximalSigma` places it in `𝓜_σ(a)`.
Theorem 14.4 gives `c ∈ C_G(a)` with `cMc^{-1} = g^{-1}Mg`, whence `gc ∈ N_G(M) = M`
(`normalizer_eq_self_of_mem_maximalSubgroups`) is the `M`-conjugator:
`(gc)a(gc)^{-1} = gag^{-1} = b`. -/
theorem sigmaSharp_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {a b : G} (ha : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hb : b ∈ OddOrder.BG.Ch4.S14.sigmaSharp M) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  classical
  have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := ha.1
  have ha1 : a ≠ 1 := ha.2
  have hbMσ : b ∈ OddOrder.BG.Ch3.S10.Msigma M := hb.1
  have hbM : b ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hbMσ
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  -- `g⁻¹Mg` is a conjugate of `M` containing `a = g⁻¹bg`, hence a `σ`-maximal of `a`.
  have hNconj : (MulAut.conj g⁻¹ • M) ∈
      OddOrder.BG.Ch4.S16.maximalConjugatesContaining M a := by
    refine ⟨g⁻¹, rfl, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g⁻¹)⁻¹ • a = g * a * g⁻¹ := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rw [hinv, hg]; exact hbM
  rw [OddOrder.BG.Ch4.S16.maximalConjugatesContaining_eq_maximalSigma hG hM haMσ ha1] at hNconj
  -- Theorem 14.4: `M` and `g⁻¹Mg` are `C_G(a)`-conjugate.
  obtain ⟨c, hcC, hc⟩ := OddOrder.BG.Ch4.S14.exists_conj_centralizer_of_mem_maximalSigma hG
    (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
    (OddOrder.BG.Ch4.S14.Msigma_ell1 hG hM haMσ ha1) ⟨hM, haMσ⟩ hNconj
  -- `conj c • M = conj g⁻¹ • M` ⟹ `conj (g*c) • M = M` ⟹ `g*c ∈ N_G(M) = M`.
  have hgc_norm : g * c ∈ Subgroup.normalizer M := by
    apply mem_normalizer_of_conj_smul_eq_self
    rw [map_mul, mul_smul, hc, ← mul_smul, ← map_mul]
    simp
  have hgc_M : g * c ∈ M := by
    rwa [OddOrder.BG.Ch4.S14.normalizer_eq_self_of_mem_maximalSubgroups hG hM] at hgc_norm
  refine ⟨g * c, hgc_M, ?_⟩
  have hca : c * a * c⁻¹ = a := by
    have h := Subgroup.mem_centralizer_iff.mp hcC a (Set.mem_singleton a)
    rw [← h]; group
  calc g * c * a * (g * c)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
    _ = g * a * g⁻¹ := by rw [hca]
    _ = b := hg

/-- **Mixed-case vacuity for the type-`P₁` `A_0`-support**: an `M_σ^#`-point (`= A(M)` for `P₁`) and
a `V^M`-point are never `G`-conjugate.  An `M_σ^#`-point is a `σ(M)`-element, conjugation preserves
this, and a `σ(M)`-element `v ∈ M` lies in the normal `σ`-Hall `M_σ = M'` (type `P₁`), contradicting
`v ∉ M'` (`typePData_typePV_not_mem_derived`). -/
theorem not_isConj_typePA_typePV_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {x y : G}
    (hx : x ∈ typePA M data) (hy : y ∈ conjClassSetIn M (typePV M data))
    (hxy : IsConj x y) : False := by
  classical
  rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hx
  have hxpi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hx.1
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hypi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) y :=
    hg ▸ OddOrder.BG.Ch4.S14.isPiElement_conj g hxpi
  obtain ⟨v, hv, m, hmM, hmv⟩ := hy
  have hvpi : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) v := by
    have h1 : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) (m⁻¹ * y * m⁻¹⁻¹) :=
      OddOrder.BG.Ch4.S14.isPiElement_conj m⁻¹ hypi
    rwa [show m⁻¹ * y * m⁻¹⁻¹ = v from by rw [← hmv]; group] at h1
  have hvW : v ∈ data.W := by
    have hv' := hv
    simp only [typePV, Set.mem_sdiff] at hv'
    exact hv'.1
  have hvM : v ∈ M := by
    have hWM : (data.W : Subgroup G) ≤ M := by
      rw [data.W_eq]
      exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
        (data.H_le.trans (Subgroup.map_subtype_le _))))
    exact hWM hvW
  have hvpiG : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M)
      (Subgroup.zpowers v) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hvpi p hp
  have hvMσ : v ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (Subgroup.zpowers_le.mpr hvM)
      hvpiG (Subgroup.mem_zpowers v)
  rw [← OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hM hP1] at hvMσ
  exact typePData_typePV_not_mem_derived data hv hvMσ

/-- **Peterfalvi (8.13.a) for the type-`P₁` `A_0`-support**: two `G`-conjugate elements of
`A_0(M) = A(M) ∪ V^M` are `M`-conjugate.  Three cases: both in `A(M) = M_σ^#`
(`sigmaSharp_isConj_conj_in_M`), both in `V^M` (`conjClassSetIn_typePV_isConj_conj_in_M`), or one of
each — the *mixed* case is vacuous (`not_isConj_typePA_typePV_of_isTypeP1`).  This is the
`conj_in_L` obligation for the type-`P₁` `A_0(M)` Dade support. -/
theorem typePA0_isConj_conj_in_M_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) {a b : G}
    (ha : a ∈ typePA0 M data) (hb : b ∈ typePA0 M data) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  simp only [typePA0, Set.mem_union] at ha hb
  rcases ha with hpa | hva
  · rcases hb with hpb | hvb
    · rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hpa hpb
      exact sigmaSharp_isConj_conj_in_M hG hM hpa hpb hab
    · exact (not_isConj_typePA_typePV_of_isTypeP1 hG hM data hP1 hpa hvb hab).elim
  · rcases hb with hpb | hvb
    · exact (not_isConj_typePA_typePV_of_isTypeP1 hG hM data hP1 hpb hva hab.symm).elim
    · exact conjClassSetIn_typePV_isConj_conj_in_M data hva hvb hab

/-- **(8.13.c2) coprimality for the exceptional `V^M`-support** (type `P₁`): for escaping
`a ∈ M_σ^#` and a `V^M`-point `b`, `|R(a)|` is coprime to `|C_M(b)|`.  `C_M(b)` is `M`-conjugate to
`C_M(v) = W` (`v ∈ V`: `C_G(v) = N_G(⟨v⟩) = W` by `normalizer_V`, using `W` abelian for `⊇`);
picking
a nonidentity `w ∈ W₂ ⊆ M_σ^#`, `W ≤ C_M(w)` (abelian), so the `σ`-sharp coprimality
(`escaping_sigmaSharp_disjoint_centralizer`) at `w` kills every common prime.  This reduces the
exceptional-support coprimality to the σ-sharp one — the `V^M` half of the engine's
`centralizer_coprime`. -/
theorem coprime_FT_signalizer_centralizerIn_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {b : G} (hb : b ∈ conjClassSetIn M (typePV M data)) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨v, hv, m, hmM, hmv⟩ := hb
  have hvW : v ∈ data.W := by
    have hv' := hv; simp only [typePV, Set.mem_sdiff] at hv'; exact hv'.1
  have hWM : (data.W : Subgroup G) ≤ M := by
    rw [data.W_eq]
    exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
      (data.H_le.trans (Subgroup.map_subtype_le _))))
  have hcyc : IsCyclic ↥data.W := data.W_cyclic
  let : CommGroup ↥data.W := hcyc.commGroup
  -- `C_G(v) = W` (`≤`: `normalizer_V`; `⊇`: `W` abelian).
  have hCGv : Subgroup.centralizer ({v} : Set G) = data.W := by
    refine le_antisymm ?_ ?_
    · rw [← data.normalizer_V {v} (Set.singleton_nonempty v) (Set.singleton_subset_iff.mpr hv)]
      intro g hg
      have hgv : g * v * g⁻¹ = v := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hg
        rw [mul_inv_eq_iff_eq_mul]; exact h
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
      constructor
      · intro h; rw [h]; exact hgv
      · intro h
        calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
          _ = g⁻¹ * v * g := by rw [h]
          _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hgv]
          _ = v := by group
    · intro x hxW
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc : (⟨x, hxW⟩ : ↥data.W) * ⟨v, hvW⟩ = ⟨v, hvW⟩ * ⟨x, hxW⟩ := mul_comm _ _
      have := congrArg Subtype.val hc
      simpa using this
  have hcard_b : Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b) = Nat.card data.W := by
    rw [← hmv, OddOrder.Peterfalvi.S04.card_centralizerIn_conj hmM v,
      OddOrder.Peterfalvi.S04.centralizerIn, hCGv, inf_eq_right.mpr hWM]
  rw [hcard_b]
  -- coprime `|R(a)| |W|`: pick `w ∈ W₂^#`, `W ≤ C_M(w)`, and the σ-sharp coprimality.
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.W2_nontrivial
  have hwW : (w : G) ∈ data.W := (data.W_eq ▸ le_sup_right : data.W2 ≤ data.W) w.2
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwMσ : (w : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    have hHMσ : data.H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
    exact hHMσ (Subgroup.mem_inf.mp (data.W2_le w.2)).1
  have hW_le_CMw : data.W ≤ OddOrder.Peterfalvi.S04.centralizerIn M (w : G) := by
    intro x hxW
    rw [OddOrder.Peterfalvi.S04.mem_centralizerIn]
    refine ⟨hWM hxW, ?_⟩
    have hc : (⟨x, hxW⟩ : ↥data.W) * ⟨(w : G), hwW⟩ = ⟨(w : G), hwW⟩ * ⟨x, hxW⟩ := mul_comm _ _
    have := congrArg Subtype.val hc
    simpa using this
  by_contra hnc
  obtain ⟨p, hpp, hpR, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
      (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    refine hpR.trans (Subgroup.card_dvd_of_le ?_)
    rw [OddOrder.BG.Ch4.S16.FT_signalizer]
    exact inf_le_left
  have hpCw : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M (w : G)) :=
    hpW.trans (Subgroup.card_dvd_of_le hW_le_CMw)
  exact escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hwMσ hw1' hpp hpσ hpCw

/-- **Peterfalvi (8.15)** for type I: the Dade (2.2) support hypotheses hold for `A(M) = A_0(M)`
and `A₁(M)`, with `L = M` and the faithful `H(a) = R(a)` of (8.14).  Assembly is genuine
(`dadeSupportHypothesisData_of_subset`); the deep (8.13.a/c1/c2) obligations are the pins above. -/
theorem dadeSupportHypotheses_typeI [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    Nonempty (DadeSupportHypothesisData M (typeIA M data)) ∧
      Nonempty (DadeSupportHypothesisData M (A1 M PeterfalviType.I)) := by
  have hiffA : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ typeIA M data ↔ x ∈ typeIA M data) := by
    intro m x hm
    refine ⟨fun h => ?_, typeIA_conj_mem M data hm⟩
    have h2 := typeIA_conj_mem M data (inv_mem hm) h
    have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    rwa [h3] at h2
  have hiffA1 : ∀ {m x : G}, m ∈ M →
      (m * x * m⁻¹ ∈ A1 M PeterfalviType.I ↔ x ∈ A1 M PeterfalviType.I) := by
    intro m x hm
    refine ⟨fun h => ?_, A1_conj_mem M OddOrder.GroupTheory.PeterfalviType.I hm⟩
    have h2 := A1_conj_mem M OddOrder.GroupTheory.PeterfalviType.I (inv_mem hm) h
    have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
    rwa [h3] at h2
  constructor
  · exact dadeSupportHypothesisData_of_subset hG hM data (fun _ h => h)
      (typeIA_nonempty M data) @hiffA
  · refine dadeSupportHypothesisData_of_subset hG hM data (A1_subset_typeIA M data) ?_ @hiffA1
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.typeF.H_nontrivial
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haH : a.1 ∈ mainSubgroup M PeterfalviType.I := by
      change a.1 ∈ maxNilpotentNormalHall M
      rw [← data.typeF.H_eq]
      exact a.2
    exact ⟨a.1, (Set.mem_sdiff _).mpr
      ⟨SetLike.mem_coe.mpr haH, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩⟩

/-- **Faithful (8.15) datum for an `M`-invariant sub-support of `M_σ^#`** (`σ`-generic engine): the
same assembly as `dadeSupportHypothesisData_of_subset`, but driven by the three `σ`-decomposition-
generic pins (`sigmaSharp_isConj_conj_in_M`, `escaping_sigmaSharp_signalizer_structure`,
`escaping_sigmaSharp_disjoint_centralizer`) instead of the type-I lemmas.  Any `X ⊆ M_σ^#` that is
`M`-conjugation-invariant and nonempty carries the Dade (2.2) support data.  Instantiated at
`X = A₁(M) = M_σ^#` (all types) and the type-`P₁` `A(M) = M_σ^#`. -/
theorem dadeSupportHypothesisData_of_subset_sigmaSharp [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXσ : X ⊆ OddOrder.BG.Ch4.S14.sigmaSharp M) (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hXsharp : ∀ x ∈ X, x ≠ (1 : G) := fun x hx => (hXσ hx).2
  have hXM : X ⊆ (M : Set G) := fun x hx => OddOrder.BG.Ch3.S10.Msigma_le M (hXσ hx).1
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ OddOrder.BG.Ch4.S14.sigmaSharp M,
          Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
    intro a ha
    have hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := hXσ ha.1
    obtain ⟨hjoin, hdisj, hnormc⟩ :=
      escaping_sigmaSharp_signalizer_structure hG hM hσa ha.2
    refine ⟨hjoin, hdisj, hnormc, ?_⟩
    intro b hb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
        (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [OddOrder.BG.Ch4.S16.FT_signalizer]
      exact inf_le_left
    exact escaping_sigmaSharp_disjoint_centralizer hG hM hσa ha.2 hb.1 hb.2 hpp hpσ hpC
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ :=
                    sigmaSharp_isConj_conj_in_M hG hM (hXσ ha) (hXσ hb) hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 (hXσ b.2)
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simp }
            H_eq_ftSupportKernel := fun _ => rfl
            }⟩

/-- **Faithful (8.15) datum for an `M`-invariant `X ⊆ M` whose escaping points are `σ`-sharp**
(the general `σ`-decomposition engine).  Generalises
`dadeSupportHypothesisData_of_subset_sigmaSharp` from `X ⊆ M_σ^#` to `X ⊆ M` with escaping points in
`M_σ^#`, taking the `(8.13.a)` `conj_in_L` and the
`(8.13.c2)` coprimality as inputs (the escaping structure `(8.13.c1)` is still the `σ`-generic
`escaping_sigmaSharp_signalizer_structure`).  Instantiated at `X = A_0(M)` for type `P₁`. -/
theorem dadeSupportHypothesisData_of_subset_escaping_sigmaSharp [Fintype G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X : Set G} (hXM : X ⊆ (M : Set G)) (hXsharp : ∀ x ∈ X, x ≠ (1 : G))
    (hXesc : ∀ a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X,
      a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hXconj : ∀ a ∈ X, ∀ b ∈ X, IsConj a b → ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b)
    (hXcop : ∀ a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X, ∀ b ∈ X,
      Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
        (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)))
    (hXne : X.Nonempty)
    (hXiff : ∀ {m x : G}, m ∈ M → (m * x * m⁻¹ ∈ X ↔ x ∈ X)) :
    Nonempty (DadeSupportHypothesisData M X) := by
  classical
  have hstruct : ∀ {a : G}, a ∈ OddOrder.GroupTheory.escapingCentralizerSet M X →
      Subgroup.centralizer ({a} : Set G)
          = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
        Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
          (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
        (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
          c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
        (∀ b ∈ X, Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
            (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
    intro a ha
    obtain ⟨hjoin, hdisj, hnormc⟩ :=
      escaping_sigmaSharp_signalizer_structure hG hM (hXesc a ha) ha.2
    exact ⟨hjoin, hdisj, hnormc, fun b hb => hXcop a ha b hb⟩
  refine ⟨{ normalizer_eq := normalizer_support_eq hG hM hXM hXsharp hXne @hXiff
            dade :=
              { subset_sharp := fun x hx =>
                  OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ x, hXsharp x hx⟩
                subset_L := fun x hx => hXM hx
                L_normalizes_A := fun l a ha => (hXiff l.2).mpr ha
                H := fun a => ftSupportKernel M X a.1
                conj_in_L := by
                  intro a b ha hb hab
                  obtain ⟨m, hmM, hmab⟩ := hXconj a ha b hb hab
                  exact ⟨⟨m, hmM⟩, hmab⟩
                centralizer_eq_sup := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).1
                  · have hle : Subgroup.centralizer ({a.1} : Set G) ≤ M := by
                      by_contra hnle
                      exact hesc ⟨a.2, hnle⟩
                    rw [ftSupportKernel_eq_bot_of_not_escaping hesc, bot_sup_eq]
                    exact (inf_eq_right.mpr hle).symm
                centralizer_disjoint := by
                  intro a
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.1
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    exact disjoint_bot_left
                H_normalized := by
                  intro a c hc x hx
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc] at hx ⊢
                    exact (hstruct hesc).2.2.1 c hc x hx
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc] at hx ⊢
                    rw [Subgroup.mem_bot] at hx ⊢
                    rw [hx]
                    group
                centralizer_coprime := by
                  intro a b
                  by_cases hesc : a.1 ∈ OddOrder.GroupTheory.escapingCentralizerSet M X
                  · rw [ftSupportKernel_eq_of_escaping hesc]
                    exact (hstruct hesc).2.2.2 b.1 b.2
                  · rw [ftSupportKernel_eq_bot_of_not_escaping hesc]
                    simp }
            H_eq_ftSupportKernel := fun _ => rfl
            }⟩

/-- **(8.13.c2) coprimality for the full type-`P₁` `A_0`-support**: for escaping `a ∈ M_σ^#` and any
`b ∈ A_0(M)`, `|R(a)|` is coprime to `|C_M(b)|`.  Splits `A_0 = A(M) ∪ V^M`: for `b ∈ A(M) = M_σ^#`
it is the σ-sharp coprimality (`escaping_sigmaSharp_disjoint_centralizer`); for `b ∈ V^M` it is
`coprime_FT_signalizer_centralizerIn_typePV`. -/
theorem coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M)
    {a : G} (haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {b : G} (hb : b ∈ typePA0 M data) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)) := by
  have : Fintype G := Fintype.ofFinite G
  simp only [typePA0, Set.mem_union] at hb
  rcases hb with hpb | hvb
  · rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1] at hpb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup (OddOrder.BG.Ch4.S16.FT_signalizerBase a) p
        (Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [OddOrder.BG.Ch4.S16.FT_signalizer]
      exact inf_le_left
    exact escaping_sigmaSharp_disjoint_centralizer hG hM haσ haesc hpb.1 hpb.2 hpp hpσ hpC
  · exact coprime_FT_signalizer_centralizerIn_typePV hG hM data haσ haesc hvb

/-- **Peterfalvi (8.15) type-`P₁` `A_0(M)` datum**: the Dade (2.2) support hypotheses hold for the
full type-`P₁` support `A_0(M) = A(M) ∪ V^M`.  Assembles the `σ`-decomposition-generic engine
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`) with the type-`P₁` pins: escaping points
are `σ`-sharp (`escaping_typePA0_mem_sigmaSharp_of_isTypeP1`, `(8.13.b)`), the `conj_in_L`
(`typePA0_isConj_conj_in_M_of_isTypeP1`, `(8.13.a)`), and the coprimality
(`coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1`, `(8.13.c2)`), plus the union set-facts
(`A_0 ⊆ M`, non-identity, nonempty, `M`-conjugation-invariant). -/
theorem dadeSupportHypothesisData_typePA0_of_isTypeP1 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M) :
    Nonempty (DadeSupportHypothesisData M (typePA0 M data)) := by
  classical
  have hVM : typePV M data ⊆ (M : Set G) := by
    intro v hv
    have hvW : v ∈ data.W := by simp only [typePV, Set.mem_sdiff] at hv; exact hv.1
    exact (show (data.W : Subgroup G) ≤ M by
      rw [data.W_eq]; exact sup_le data.W1_le (data.W2_le.trans (inf_le_left.trans
        (data.H_le.trans (Subgroup.map_subtype_le _))))) hvW
  refine dadeSupportHypothesisData_of_subset_escaping_sigmaSharp hG hM ?_ ?_
    (fun a ha => escaping_typePA0_mem_sigmaSharp_of_isTypeP1 hG hM data hP1 ha)
    (fun a ha b hb hab => typePA0_isConj_conj_in_M_of_isTypeP1 hG hM data hP1 ha hb hab)
    (fun a ha b hb => coprime_FT_signalizer_centralizerIn_typePA0_of_isTypeP1 hG hM data hP1
      (escaping_typePA0_mem_sigmaSharp_of_isTypeP1 hG hM data hP1 ha) ha.2 hb)
    ?_ ?_
  · -- `A_0(M) ⊆ M`
    intro x hx
    rcases hx with hpa | hva
    · rw [typePA_eq_sharpSubgroup_derivedInG] at hpa
      exact (Subgroup.map_subtype_le _) ((Set.mem_sdiff _).mp hpa).1
    · exact conjClassSetIn_subset hVM hva
  · -- `x ≠ 1`
    intro x hx
    rcases hx with hpa | hva
    · rw [typePA_eq_sharpSubgroup_derivedInG] at hpa
      exact fun h => ((Set.mem_sdiff _).mp hpa).2 (Set.mem_singleton_iff.mpr h)
    · obtain ⟨v, hv, m, hmM, hmv⟩ := hva
      have hv1 : v ≠ 1 := by
        rintro rfl
        have h1 := hv
        simp only [typePV, Set.mem_sdiff, Set.mem_union] at h1
        exact h1.2 (Or.inl (Subgroup.one_mem data.W1))
      intro hx1
      apply hv1
      calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
        _ = m⁻¹ * x * m := by rw [hmv]
        _ = m⁻¹ * 1 * m := by rw [hx1]
        _ = 1 := by group
  · -- `A_0(M)` nonempty
    obtain ⟨a, ha1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    refine ⟨a.1, Or.inl ?_⟩
    rw [typePA_eq_sigmaSharp_of_isTypeP1 hG hM data hP1]
    exact (Set.mem_sdiff _).mpr
      ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩
  · -- `M`-conjugation invariance
    intro m x hm
    simp only [typePA0, Set.mem_union]
    constructor
    · rintro (hpa | hva)
      · exact Or.inl (by
          have := typePA_conj_mem M data (inv_mem hm) hpa
          rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at this)
      · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mp hva)
    · rintro (hpa | hva)
      · exact Or.inl (typePA_conj_mem M data hm hpa)
      · exact Or.inr ((mem_conjClassSetIn_conj_iff hm x).mpr hva)

end OddOrder.Peterfalvi.S10


