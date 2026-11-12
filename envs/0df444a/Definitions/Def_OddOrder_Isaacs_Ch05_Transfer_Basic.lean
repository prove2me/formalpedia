-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
-- name    : OddOrder_Isaacs_Ch05_Transfer_Basic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:05.089206+00:00
-- url     : https://prove2.me/theorems/65a1d3ec-8382-425b-a21e-dccea514baea
-- title:
--   Isaacs Ch. 5: normal $p$-complements, fusion control, $O^p$ and $A^p$
-- statement:
--   The basic part of the Chapter 5 (Transfer) formalization of Isaacs, *Finite Group Theory*. It defines normal $p$-complements, control of fusion, and the subgroups $O^p(G)$ and $A^p(G)$.
--
--   Main definitions: `HasNormalPComplement` ($G$ has a normal $p$-complement), `Subgroup.ControlsFusionIn` ($K$ controls $G$-fusion in $H$: elements of $H$ conjugate in $G$ are conjugate in $K$), `OPrime` ($O^p(G)$, the smallest normal subgroup of $p$-power index) and `APrime` (the smallest normal subgroup $K$ with $G/K$ abelian of $p$-power index), together with normality instances.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Basic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- "G has a normal p-complement" — there exists a normal subgroup `N : Subgroup G` such
that for every Sylow `p`-subgroup `P`, `(N, P)` form a complement pair (`IsComplement'`).

For finite `G`, this is equivalent to existence of normal `N` with `|N|` coprime to `p`
and `|G:N|` a `p`-power. mathlib 未収載のため新規定義. -/
def HasNormalPComplement (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧
    ∀ P : Sylow p G, Subgroup.IsComplement' N (P : Subgroup G)

section

/-- **Isaacs Thm 4.34 (Fitting)** — Ch.5 subgroup-conjugation adapter.

`A` (= subgroup `K` of `G` with `K ≤ N_G(P)`) が abelian subgroup `P` に conjugation 経由で
作用. `(|P|, |K|) = 1` (coprime) ⇒ `P = C_P(K) × ⁅P, K⁆` (internal direct product, element form).

**証明戦略** (Isaacs p.142, θ trick):
* θ : ↥P → ↥P, θ(p) = ∏_{k ∈ K} k • p. P abelian なので well-def + homomorphism.
* θ(p) ∈ C_P(K) (θ は K 作用と可換).
* `p ∈ C_P(K)` で θ(p) = p^|K|; (|P|, |K|) = 1 ⇒ θ(p) = 1 ⇒ p = 1.
* ⁅P, K⁆ ⊆ ker θ (各 [p, k] が ker に入る).
* ⇒ C_P(K) ⊓ ⁅P, K⁆ = ⊥.
* p^|K| = θ(p) · h with h ∈ ⁅P, K⁆ (元素計算). Bezout で p ∈ C_P(K) · ⁅P, K⁆.

This is the form needed by Isaacs Thm 5.17: a subgroup `K ≤ N_G(P)` acts on the
abelian subgroup `P` by conjugation. Ch.4 gives the same result for an abstract
automorphism action on the group `↥P`; this theorem translates fixed points to
`C_G(K) ∩ P` and action-commutators to `⁅P, K⁆`. -/
theorem fitting_coprime_abelian_decomp
    {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} [IsMulCommutative ↥P]
    {K : Subgroup G} (hK_norm : K ≤ Subgroup.normalizer P)
    (h_coprime : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K)) :
    (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ ∧
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let KN : Subgroup N := K.subgroupOf N
  let φ : KN →* MulAut P := MulDistribMulAction.toMulAut KN P
  have hKN_card : Nat.card KN = Nat.card K :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := N)
        (by simpa [N] using hK_norm)).toEquiv
  have hCop : Nat.Coprime (Nat.card KN) (Nat.card P) := by
    rw [hKN_card]
    exact h_coprime.symm
  have hSolv : Group.IsSolvable KN ∨ Group.IsSolvable P := by
    right
    infer_instance
  have h_inf_P :
      Subgroup.fixedPointsOfMulAut φ ⊓
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian
      φ hCop
  have h_sup_P :
      Subgroup.fixedPointsOfMulAut φ ⊔
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ = ⊤ :=
    _root_.OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
      (φ := φ) hCop hSolv
  have h_fixed_map_le : (Subgroup.fixedPointsOfMulAut φ).map P.subtype ≤
      Subgroup.centralizer (K : Set G) ⊓ P := by
    intro x hx
    rw [Subgroup.mem_inf]
    rcases hx with ⟨xp, hxp_fixed, rfl⟩
    constructor
    · rw [Subgroup.mem_centralizer_iff]
      intro y hyK
      let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
      let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
      have hfix : (φ yKN) xp = xp := hxp_fixed yKN
      have hconj : y * (xp : G) * y⁻¹ = (xp : G) := by
        exact congrArg Subtype.val hfix
      calc y * (xp : G) = (y * (xp : G) * y⁻¹) * y := by group
        _ = (xp : G) * y := by rw [hconj]
    · exact xp.property
  have h_ac_map_le :
      (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype ≤
        (⁅P, K⁆ : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap,
      _root_.OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a x
    rw [Subgroup.mem_comap]
    change ((a : N).val * (x : G) * (a : N).val⁻¹) * (x : G)⁻¹ ∈
      (⁅P, K⁆ : Subgroup G)
    have haK : ((a : N).val : G) ∈ K := by
      have ha := a.property
      rwa [Subgroup.mem_subgroupOf] at ha
    have hxP : (x : G) ∈ P := x.property
    have hcomm : (⁅(x : G), ((a : N).val : G)⁆ : G) ∈ (⁅P, K⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hxP haK
    convert (Subgroup.inv_mem _ hcomm) using 1
    group
  have h_comm_le_ac_map :
      (⁅P, K⁆ : Subgroup G) ≤
        (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype := by
    rw [Subgroup.commutator_le]
    intro x hxP y hyK
    let yN : N := ⟨y, by simpa [N] using hK_norm hyK⟩
    let yKN : KN := ⟨yN, by rw [Subgroup.mem_subgroupOf]; exact hyK⟩
    let xP : P := ⟨x, hxP⟩
    have hgen : xP * (φ yKN) xP⁻¹ ∈
        _root_.OddOrder.Isaacs.Ch04.actionCommutator φ :=
      Subgroup.subset_closure ⟨xP, yKN, rfl⟩
    refine ⟨xP * (φ yKN) xP⁻¹, hgen, ?_⟩
    dsimp [φ, xP, yKN, yN]
    change x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹
    group
  have h_inf_bot :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊓ (⁅P, K⁆ : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases Subgroup.mem_inf.mp hx with ⟨hx_centP, hx_comm⟩
    rcases Subgroup.mem_inf.mp hx_centP with ⟨hx_cent, hxP⟩
    let xP : P := ⟨x, hxP⟩
    have hx_fixed : xP ∈ Subgroup.fixedPointsOfMulAut φ := by
      intro a
      apply Subtype.ext
      rcases a with ⟨⟨y, _hyN⟩, hyK⟩
      have hcomm : y * x = x * y := by
        rw [Subgroup.mem_centralizer_iff] at hx_cent
        exact hx_cent y hyK
      change y * x * y⁻¹ = x
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hx_ac : xP ∈ _root_.OddOrder.Isaacs.Ch04.actionCommutator φ := by
      have hx_map :
          x ∈ (_root_.OddOrder.Isaacs.Ch04.actionCommutator φ).map P.subtype :=
        h_comm_le_ac_map hx_comm
      rcases hx_map with ⟨z, hz_ac, hz_val⟩
      have hz_eq : z = xP := Subtype.ext hz_val
      rwa [hz_eq] at hz_ac
    have hxP_bot : xP ∈ (⊥ : Subgroup P) := by
      rw [← h_inf_P]
      exact ⟨hx_fixed, hx_ac⟩
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxP_bot)
  have h_sup_eq :
      (Subgroup.centralizer (K : Set G) ⊓ P) ⊔ (⁅P, K⁆ : Subgroup G) = P := by
    apply le_antisymm
    · exact sup_le inf_le_right (by
        rw [Subgroup.commutator_le]
        intro x hxP y hyK
        have hyN : y ∈ N := by simpa [N] using hK_norm hyK
        have hyxiy : y * x⁻¹ * y⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp (P.inv_mem hxP)
        have h_eq : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [show (⁅x, y⁆ : G) = x * y * x⁻¹ * y⁻¹ from rfl, h_eq]
        exact P.mul_mem hxP hyxiy)
    · intro x hxP
      have hx_map_top : x ∈ ((⊤ : Subgroup P).map P.subtype) := by
        exact ⟨⟨x, hxP⟩, Subgroup.mem_top _, rfl⟩
      rw [← h_sup_P, Subgroup.map_sup] at hx_map_top
      exact (sup_le_sup h_fixed_map_le h_ac_map_le) hx_map_top
  exact ⟨h_inf_bot, h_sup_eq⟩

/-- **Isaacs Thm 5.13 (Burnside normal p-complement)**:
if a Sylow `p`-subgroup centralizes its normalizer, then `G` has a normal
`p`-complement.

This adapts mathlib's `MonoidHom.ker_transferSylow_isComplement'`, which gives a
complement for the chosen Sylow subgroup, to this file's `HasNormalPComplement`
predicate requiring the same normal complement for every Sylow subgroup. -/
theorem hasNormalPComplement_of_sylow_normalizer_le_centralizer
    [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    HasNormalPComplement p G := by
  classical
  let N : Subgroup G := (MonoidHom.transferSylow P hP).ker
  have hNP : Subgroup.IsComplement' N (P : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨N, inferInstance, ?_⟩
  intro Q
  have hdisj : Disjoint N (Q : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_disjoint P hP
      (Q : Subgroup G) Q.isPGroup'
  have hcardQ : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by
    exact Nat.card_congr (Sylow.equiv Q P).toEquiv
  have hcard : Nat.card N * Nat.card (Q : Subgroup G) = Nat.card G := by
    rw [hcardQ]
    exact hNP.card_mul_card
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

end

section

/-- "`K` controls `G`-fusion in `H`": any two elements of `H` conjugate in the
ambient group `G` are already conjugate by an element of `K`.

Isaacs §5C-§5D で使う fusion-control 条件. -/
def _root_.Subgroup.ControlsFusionIn {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  ∀ ⦃x y : G⦄, x ∈ H → y ∈ H →
    (∃ g : G, g * x * g⁻¹ = y) →
    (∃ u : G, u ∈ K ∧ u * x * u⁻¹ = y)

/-- **Isaacs Cor 5.22 (focal-subgroup core)**:
if `H` controls `G`-fusion in `P`, then the focal subgroup of `P` computed inside
`H` maps to the focal subgroup of `P` computed inside `G`.

This is the substantive focal-subgroup step in the proof that `H` controls
`p`-transfer in `G`; the remaining book argument is an index/kernel comparison
via the focal subgroup theorem. -/
theorem _root_.Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn
    {G : Type*} [Group G] {P H : Subgroup G} (hP_le_H : P ≤ H)
    (hFusion : H.ControlsFusionIn P) :
    (P.subgroupOf H).focalSubgroup.map H.subtype = P.focalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.focalSubgroup_def, MonoidHom.map_closure, Subgroup.focalSubgroup_def]
    apply Subgroup.closure_mono
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨hzPH, x, hxPH, u, rfl⟩
    exact ⟨hzPH, (x : G), hxPH, (u : G), rfl⟩
  · rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hyP : u * x * u⁻¹ ∈ P := by
      have hy_eq : u * x * u⁻¹ = (⁅x, u⁆)⁻¹ * x := by
        rw [commutatorElement_def]
        group
      rw [hy_eq]
      exact P.mul_mem (P.inv_mem hgP) hxP
    obtain ⟨v, hvH, hv⟩ := hFusion hxP hyP ⟨u, rfl⟩
    have hcomm_eq : ⁅x, u⁆ = ⁅x, v⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc
        x * u * x⁻¹ * u⁻¹ = x * (u * x * u⁻¹)⁻¹ := by group
        _ = x * (v * x * v⁻¹)⁻¹ := by rw [hv]
        _ = x * v * x⁻¹ * v⁻¹ := by group
    let xH : H := ⟨x, hP_le_H hxP⟩
    let vH : H := ⟨v, hvH⟩
    let gH : H := ⟨⁅x, u⁆, hP_le_H hgP⟩
    have hgH_focal : gH ∈ (P.subgroupOf H).focalSubgroup := by
      rw [Subgroup.focalSubgroup_def]
      apply Subgroup.subset_closure
      refine ⟨hgP, xH, hxP, vH, ?_⟩
      apply Subtype.ext
      exact hcomm_eq
    exact Subgroup.mem_map_of_mem H.subtype hgH_focal

/-- `OPrime p G` — the smallest normal subgroup of `G` with `p`-power index.
For finite `G`, this is the intersection of all such normal subgroups (Isaacs §5D 冒頭, 'O^p(G)').

mathlib 未収載のため新規定義. 5.25 (⇐), 5.20 等で使用. -/
def OPrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}, N.val

/-- `OPrime p G` is normal. -/
instance OPrime_normal (p : ℕ) (G : Type*) [Group G] : (OPrime p G).Normal := by
  unfold OPrime
  exact Subgroup.normal_iInf_normal (fun N => N.property.1)

/-- Per-element Normal instance for the `OPrime` indexing subtype. Needed so that
`G ⧸ N.val` (over `N` in the subtype) has a group structure during type elaboration. -/
instance OPrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (N : {N : Subgroup G // N.Normal ∧ ∃ k : ℕ, N.index = p ^ k}) :
    (N.val : Subgroup G).Normal := N.property.1

/-- `APrime p G` — the smallest normal subgroup `K ⊴ G` with `G/K` abelian and p-power index.
Equivalently, the smallest member of the family `{K ⊴ G : commutator G ≤ K ∧ [G:K] is p-power}`.

For finite `G`, this corresponds to Isaacs' `A^p(G)`. mathlib 未収載のため新規定義. -/
def APrime (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}, K.val

/-- Per-element Normal instance for the `APrime` indexing subtype. -/
instance APrime_index_subtype_normal {p : ℕ} {G : Type*} [Group G]
    (K : {K : Subgroup G // K.Normal ∧ commutator G ≤ K ∧ ∃ k : ℕ, K.index = p ^ k}) :
    (K.val : Subgroup G).Normal := K.property.1

/-- `APrime p G` is normal. -/
instance APrime_normal (p : ℕ) (G : Type*) [Group G] : (APrime p G).Normal := by
  unfold APrime
  exact Subgroup.normal_iInf_normal (fun K => K.property.1)

end

end OddOrder.Isaacs.Ch05


