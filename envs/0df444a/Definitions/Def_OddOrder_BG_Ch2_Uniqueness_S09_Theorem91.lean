-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Theorem91
-- name    : OddOrder_BG_Ch2_Uniqueness_S09_Theorem91
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:30:54.501311+00:00
-- url     : https://prove2.me/theorems/b64dadd3-a2f9-4485-b35f-756b32cf3709
-- title:
--   BG §9: Theorem 9.1 (noncyclic uniqueness via Hall–Higman)
-- statement:
--   Formalizes Theorem 9.1 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §9: a criterion for a noncyclic $p$-elementary subgroup $B\le M$ to lie in $\mathcal{U}$, either by a centralizer condition (a) or by the condition (b) $\langle\mathcal{H}_G(B;p')\rangle\subseteq M$. The proof uses §8 Theorem 8.1, §7 Theorems 7.4/7.6 and the general Hall–Higman result from §1, and includes helpers for the intermediate steps and equations. It is the start of the §9 chain 9.1 → 9.2 → … → 9.6.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 26 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S09_Theorem91.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S09_Theorem91.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowPGroups
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_GroupTheory_NarrowPGroup

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `C_G(x) < ⊤` for `x ≠ 1` in a minimal simple group (`Z(G) = 1`). -/
theorem centralizer_singleton_lt_top [Finite G] (hG : IsMinimalSimpleOdd G) {x : G}
    (hx : x ≠ (1 : G)) : Subgroup.centralizer ({x} : Set G) < ⊤ := by
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  rw [lt_top_iff_ne_top]
  intro htop
  refine hx (Subgroup.mem_bot.mp (hZbot ▸ ?_))
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) x (Set.mem_singleton x)).symm

/-- If `L` has a unique containing maximal subgroup and `x` centralizes `L`, then the
centralizer of any nontrivial such `x` lies in that unique maximal subgroup. -/
theorem centralizer_singleton_le_uniqueMaximalSubgroup_of_mem_centralizer [Finite G]
    (hG : IsMinimalSimpleOdd G) {L : Subgroup G} (hL : IsUniquelyMaximal L)
    {x : G} (hxL : x ∈ Subgroup.centralizer (L : Set G)) (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ hL.uniqueMaximalSubgroup := by
  classical
  have hCGlt : Subgroup.centralizer ({x} : Set G) < ⊤ :=
    centralizer_singleton_lt_top hG hx
  have hLleCG : L ≤ Subgroup.centralizer ({x} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hxL l hl).symm
  obtain ⟨N, hNco, hCGleN⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer ({x} : Set G))).resolve_left hCGlt.ne
  have hLleN : L ≤ N := hLleCG.trans hCGleN
  have hN_eq : N = hL.uniqueMaximalSubgroup :=
    hL.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hNco hLleN
  exact hCGleN.trans (le_of_eq hN_eq)

/-- **BG Theorem 9.1, STEP 0** ((a)⇒(b), mmd L2496-2499): if every nonidentity `b ∈ B`
has `C_G(b) ≤ M`, then every `B`-invariant `p'`-subgroup `K ≤ ⊤` lies in `M`, hence
`sSup (ℋ_G(B;p')) ≤ M`. Proof: `B` is a noncyclic abelian `p`-group, so it acts coprimely by
conjugation on the `p'`-group `K`; BG Prop 1.16(1) / Isaacs 6.21
(`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) gives
`K = ⟨ C_K(b) ∣ b ∈ B^# ⟩`, and each `C_K(b) ≤ C_G(b) ≤ M`. -/
private theorem sSup_hInvariant_le_of_centralizer_le [Finite G]
    {p : ℕ} [Fact p.Prime] {M B : Subgroup G} (hBea : B.IsElementaryAbelian p)
    (hBnc : ¬ IsCyclic ↥B)
    (hcent : ∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M) :
    sSup (hInvariant ⊤ B ({p} : Set ℕ)ᶜ) ≤ M := by
  classical
  have hBcomm : IsMulCommutative ↥B := IsMulCommutative.of_comm hBea.comm
  have hBpi : Subgroup.IsPiSubgroup ({p} : Set ℕ) B :=
    isPiSubgroup_singleton_of_isPGroup hBea.isPGroup
  -- Reduce to: every member `K` of `ℋ_G(B;p')` lies in `M`.
  rw [sSup_le_iff]
  intro K hK
  have hBK : B ≤ Subgroup.normalizer K := hInvariant_le_normalizer hK
  have hKpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := hInvariant_isPiSubgroup hK
  -- `B` acts coprimely on the `p'`-group `K`.
  have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥K) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hBpi hKpi
  -- Conjugation action of `B` on `K`.
  have hK_inv : Ch03.IsAInvariant (S07.conjAction B) K :=
    S07.isAInvariant_conjAction_iff.mpr hBK
  -- Prop 1.16(1): the centralizers generate all of `K`.
  have htop := OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
    hK_inv.restrict hcop hBnc
  -- Each `C_K(b) ≤ M`, so the generated subgroup `K` is contained in `M.subgroupOf K`.
  have hle : OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure hK_inv.restrict
      ≤ M.subgroupOf K := by
    rw [OddOrder.Isaacs.Ch06.nontrivialActionFixedByClosure_le_iff]
    intro b hb_ne z hz
    rw [Subgroup.mem_subgroupOf]
    have hb_ne' : (b : G) ≠ 1 := fun h => hb_ne (Subtype.ext h)
    -- `z` is fixed by `b`, i.e. `z` centralizes `b`.
    have hzfix : (hK_inv.restrict b) z = z := OddOrder.Isaacs.Ch06.mem_actionFixedBy.mp hz
    have hval : ((hK_inv.restrict b) z : G) = (z : G) := congrArg Subtype.val hzfix
    rw [Ch03.IsAInvariant.restrict_apply_val] at hval
    simp only [S07.conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulAut.conj_apply] at hval
    have hzC : (z : G) ∈ Subgroup.centralizer ({(b : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact (mul_inv_eq_iff_eq_mul.mp hval)
    exact hcent (b : G) b.2 hb_ne' hzC
  rw [htop, top_le_iff, Subgroup.subgroupOf_eq_top] at hle
  exact hle

/-- **BG Theorem 9.1, Eq (9.1) core** (mmd L2503-2506), abstract form: in a finite solvable
group `G'`, a `P`-invariant `p'`-subgroup `Y` (where `P` is a Sylow `p`-subgroup) lies in
`O_{p'}(G')`. Proof (in `X̄ = G'/O_{p'}(G')`): `Ō_p(X̄) = O_p(X̄) ≤ P̄` (image of a Sylow `p` is
Sylow `p`, and `O_p ≤` every Sylow), and `P̄` normalizes `Ȳ`, so `[Ȳ, O_p(X̄)] ≤ Ȳ ⊓ O_p(X̄) = 1`
(`p'` ∩ `p`); thus `Ȳ` centralizes `O_p(X̄)`. Since `O_{p'}(X̄) = 1`, Hall–Higman 1.2.3
(`hall_higman_1_2_3`) gives `C_{X̄}(O_p(X̄)) ≤ O_p(X̄)`, so `Ȳ ≤ O_p(X̄)`; being a `p'`-group it is
trivial, i.e. `Y ≤ O_{p'}(G')`. -/
private theorem le_oPiCore_compl_of_sylow_normalizes
    {p : ℕ} [Fact p.Prime] {G' : Type*} [Group G'] [Finite G'] [Group.IsSolvable G']
        (P : Sylow p G')
    {Y : Subgroup G'} (hPY : (P : Subgroup G') ≤ Subgroup.normalizer Y)
    (hYpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Y) :
    Y ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ G' := by
  classical
  set N : Subgroup G' := Ch03.oPiCore ({p} : Set ℕ)ᶜ G' with hN
  set mk := QuotientGroup.mk' N with hmkdef
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective N
  have hker : mk.ker = N := QuotientGroup.ker_mk' N
  set Q : Subgroup (G' ⧸ N) := Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ N) with hQ
  have hQnorm : Q.Normal := by rw [hQ]; infer_instance
  set Ybar : Subgroup (G' ⧸ N) := Y.map mk with hYbar
  -- `Q = O_p(X̄)` is a `p`-group; `Ȳ` is a `p'`-group; hence `Q ⊓ Ȳ = ⊥`.
  have hQ_pg : IsPGroup p ↥Q := by
    rw [hQ, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup p _
  have hYbar_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ Ybar := by
    intro q hq
    have hdvd : Nat.card ↥Ybar ∣ Nat.card ↥Y := by rw [hYbar]; exact Subgroup.card_map_dvd _ _
    exact hYpi q (Nat.primeFactors_mono hdvd Nat.card_pos.ne' hq)
  have hYbar_cop : Nat.Coprime (Nat.card ↥Ybar) p := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := ({p} : Set ℕ)ᶜ) Nat.card_pos.ne' (Fact.out : p.Prime).pos.ne' ?_ ?_
    · intro q hq
      exact hYbar_pi q hq
    · intro q hq
      rw [Nat.Prime.primeFactors (Fact.out : p.Prime), Finset.mem_singleton] at hq
      simp [hq]
  have hQYbot : Q ⊓ Ybar = ⊥ := OddOrder.BG.Ch1.S01.inf_eq_bot_of_pGroup_coprime hQ_pg hYbar_cop
  -- `O_p(X̄) ⊆ mk(P)`: the image of the Sylow `P` is Sylow, and `O_p ≤` every Sylow.
  have hQ_le_Pbar : Q ≤ (P : Subgroup G').map mk := by
    have hle := OddOrder.Isaacs.Ch01.opCore_le (P.mapSurjective hsurj)
    rw [Sylow.coe_mapSurjective, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore] at hle
    exact hle
  -- `P̄` normalizes `Ȳ` (since `P` normalizes `Y`); hence so does `O_p(X̄) ≤ P̄`.
  have hPbar_norm : (P : Subgroup G').map mk ≤ Subgroup.normalizer Ybar := by
    rw [hYbar]
    exact (Subgroup.map_mono hPY).trans (Subgroup.le_normalizer_map mk)
  have hQ_norm_Ybar : Q ≤ Subgroup.normalizer Ybar := hQ_le_Pbar.trans hPbar_norm
  -- `[Ȳ, O_p(X̄)] ≤ Ȳ ⊓ O_p(X̄) = 1`, so `Ȳ` centralizes `O_p(X̄)`.
  have hYbar_cent_Q : Ybar ≤ Subgroup.centralizer (Q : Set (G' ⧸ N)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    -- `[y, c] = y c y⁻¹ c⁻¹`; show it is `1`.
    have hin_Q : y * c * y⁻¹ * c⁻¹ ∈ Q := by
      -- `Q` is normal in `X̄`, so `y c y⁻¹ ∈ Q`.
      have hconj : y * c * y⁻¹ ∈ Q := hQnorm.conj_mem c hc y
      simpa [mul_assoc] using Q.mul_mem hconj (Q.inv_mem hc)
    have hin_Y : y * c * y⁻¹ * c⁻¹ ∈ Ybar := by
      -- `c ∈ Q ≤ N_{X̄}(Ȳ)`, so `c y⁻¹ c⁻¹ ∈ Ȳ`.
      have hconj : c * y⁻¹ * c⁻¹ ∈ Ybar :=
        (Subgroup.mem_normalizer_iff.mp (hQ_norm_Ybar hc) y⁻¹).mp (Ybar.inv_mem hy)
      have heq : y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) := by group
      rw [heq]; exact Ybar.mul_mem hy hconj
    have h1 : y * c * y⁻¹ * c⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hQYbot ▸ Subgroup.mem_inf.mpr ⟨hin_Q, hin_Y⟩)
    have h2 : y * c * y⁻¹ = c := mul_inv_eq_one.mp h1
    have h3 : y * c = c * y := by
      have h4 := congrArg (· * y) h2
      simpa [mul_assoc] using h4
    exact h3.symm
  -- Hall–Higman 1.2.3 in `X̄` (where `O_{p'}(X̄) = ⊥`): `C_{X̄}(O_p(X̄)) ≤ O_p(X̄)`.
  have hbot : Ch03.oPiCore ({p} : Set ℕ)ᶜ (G' ⧸ N) = ⊥ := by
    have := OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot (G := G') ({p} : Set ℕ)ᶜ
    simpa [hN] using this
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) (G' ⧸ N) := inferInstance
  have hHH : Subgroup.centralizer (Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ N) : Set (G' ⧸ N))
      ≤ Ch03.oPiCore ({p} : Set ℕ) (G' ⧸ N) :=
    -- `({p} : Set ℕ)ᶜ` and `{q | ¬q = p}` are definitionally equal, so `hbot` applies directly.
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G' ⧸ N) ({p} : Set ℕ) hbot
  have hYbar_le_Q : Ybar ≤ Q := hYbar_cent_Q.trans hHH
  -- `Ȳ ≤ O_p(X̄)` is both `p'` and `p`, hence trivial; so `Y ≤ ker mk = O_{p'}(G')`.
  have hYbar_bot : Ybar = ⊥ := by
    have : Ybar ⊓ Q = Ybar := inf_eq_left.mpr hYbar_le_Q
    rw [inf_comm] at this
    rw [← this, hQYbot]
  rw [hYbar, Subgroup.map_eq_bot_iff, hker] at hYbar_bot
  rw [hN]; exact hYbar_bot

/-- A nontrivial singleton core of a maximal subgroup has normalizer contained in that
maximal subgroup. -/
theorem normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) :
    Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M := by
  have : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMleN : M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) :=
    le_normalizer_opiCoreInG ({q} : Set ℕ) M
  have hNne : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≠ ⊤ := by
    intro hNtop
    have hOq_normal : (opiCoreInG ({q} : Set ℕ) M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (opiCoreInG ({q} : Set ℕ) M)
        inferInstance with hOqbot | hOqtop
    · exact hOqne hOqbot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hOqtop]
        exact opiCoreInG_le ({q} : Set ℕ) M
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  exact (isCoatom_iff_ge_of_le.mp hMco).2 _ hNne hMleN

/-- A nontrivial `π`-core of a maximal subgroup has normalizer contained in that maximal
subgroup. General `π` version of `normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot`,
used for `π = {p}ᶜ` in BG Eq (9.3). -/
private theorem normalizer_opiCoreInG_le_maximal_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {π : Set ℕ} {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hOne : opiCoreInG π M ≠ ⊥) :
    Subgroup.normalizer (opiCoreInG π M : Set G) ≤ M := by
  have : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMleN : M ≤ Subgroup.normalizer (opiCoreInG π M : Set G) :=
    le_normalizer_opiCoreInG π M
  have hNne : Subgroup.normalizer (opiCoreInG π M : Set G) ≠ ⊤ := by
    intro hNtop
    have hO_normal : (opiCoreInG π M).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hG.simple.eq_bot_or_eq_top_of_normal (opiCoreInG π M)
        inferInstance with hObot | hOtop
    · exact hOne hObot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hOtop]
        exact opiCoreInG_le π M
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  exact (isCoatom_iff_ge_of_le.mp hMco).2 _ hNne hMleN

/-- **BG Theorem 9.1, Eq (9.1)** (mmd L2503-2506): for a Sylow `p`-subgroup `P` of a solvable
maximal `M` (here `P` a Sylow of `↥M`, `Pamb` its ambient image), if every `Pamb`-invariant
`p'`-subgroup lies in `M`, then `⟨ℋ_G(Pamb;p')⟩ = O_{p'}(M)`.

`≤`: each `K ∈ ℋ_G(Pamb;p')` lies in `M` (hypothesis) and is `Pamb`-invariant, so
`le_oPiCore_compl_of_sylow_normalizes` (in `↥M`, with the Sylow `P`) puts `K ≤ O_{p'}(M)`.
`≥`: `O_{p'}(M)` is itself a `Pamb`-invariant `p'`-subgroup (normal in `M`, `Pamb ≤ M`). -/
private theorem sSup_hInvariant_eq_opiCoreInG_singleton_compl [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Group.IsSolvable ↥M] (P : Sylow p ↥M)
    (hPle : ∀ K : Subgroup G, K ∈ hInvariant ⊤ ((P : Subgroup ↥M).map M.subtype) ({p} : Set ℕ)ᶜ →
      K ≤ M) :
    sSup (hInvariant ⊤ ((P : Subgroup ↥M).map M.subtype) ({p} : Set ℕ)ᶜ)
      = opiCoreInG ({p} : Set ℕ)ᶜ M := by
  classical
  set Pamb : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPamb
  have hPamb_le_M : Pamb ≤ M := Subgroup.map_subtype_le _
  refine le_antisymm ?_ ?_
  · -- `≤`: each member lies in `O_{p'}(M)`.
    rw [sSup_le_iff]
    intro K hK
    have hKM : K ≤ M := hPle K hK
    have hKnorm : Pamb ≤ Subgroup.normalizer K := hInvariant_le_normalizer hK
    have hKpi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := hInvariant_isPiSubgroup hK
    -- transport to `↥M` and apply the Sylow-normalizer core lemma.
    have hPsub : (P : Subgroup ↥M) ≤ Subgroup.normalizer (K.subgroupOf M) := by
      intro x hx
      have hxamb : (x : G) ∈ Pamb := ⟨x, hx, rfl⟩
      have hxn : (x : G) ∈ Subgroup.normalizer K := hKnorm hxamb
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hxn (z : G)
    have hKpi_sub : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (K.subgroupOf M) := by
      intro r hr
      refine hKpi r ?_
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr
    have hcore : K.subgroupOf M ≤ Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥M :=
      le_oPiCore_compl_of_sylow_normalizes P hPsub hKpi_sub
    calc K = (K.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hKM).symm
      _ ≤ (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥M).map M.subtype := Subgroup.map_mono hcore
      _ = opiCoreInG ({p} : Set ℕ)ᶜ M := rfl
  · -- `≥`: `O_{p'}(M)` is itself a `Pamb`-invariant `p'`-subgroup.
    refine le_sSup ?_
    refine ⟨le_top, ?_, ?_⟩
    · -- `Pamb` normalizes `O_{p'}(M)` (normal in `M`, `Pamb ≤ M`).
      refine hPamb_le_M.trans ?_
      exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M
    · exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ M

/-- The normalizer of `A` normalizes `sSup ℋ_G(A;π)`: conjugation by `g ∈ N_G(A)` permutes the
family `ℋ_⊤(A;π)` (`conj_smul_mem_hInvariant_top_of_normalizer`), hence fixes its supremum.
Used in BG Eq (9.3): `N_G(P) ≤ N_G(⟨ℋ_G(P;p')⟩) = N_G(O_{p'}(M))`. -/
private theorem normalizer_le_normalizer_sSup_hInvariant_top {A : Subgroup G} {π : Set ℕ} :
    Subgroup.normalizer (A : Set G)
      ≤ Subgroup.normalizer ((sSup (hInvariant ⊤ A π) : Subgroup G) : Set G) := by
  intro g hg
  have hgA : MulAut.conj g • A = A := conj_smul_eq_self_of_mem_normalizer hg
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    have hg' : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hg
    exact conj_smul_eq_self_of_mem_normalizer hg'
  apply mem_normalizer_of_conj_smul_eq_self
  have key : ∀ {h : G}, MulAut.conj h • A = A →
      MulAut.conj h • (sSup (hInvariant ⊤ A π) : Subgroup G) ≤ sSup (hInvariant ⊤ A π) := by
    intro h hhA
    rw [Subgroup.pointwise_smul_subset_iff]
    refine sSup_le ?_
    intro Q hQ
    have hmem : MulAut.conj h • Q ∈ hInvariant ⊤ A π :=
      conj_smul_mem_hInvariant_top_of_normalizer hQ hhA
    have hle : MulAut.conj h • Q ≤ sSup (hInvariant ⊤ A π) := le_sSup hmem
    rwa [Subgroup.pointwise_smul_subset_iff] at hle
  refine le_antisymm (key hgA) ?_
  have h2 := key hgA'
  rw [Subgroup.pointwise_smul_subset_iff, ← map_inv, inv_inv] at h2
  exact h2

/-- **BG Theorem 9.1, Eq (9.3)** (mmd L2510-2514): `N_G(P) ≤ M` for a Sylow `p`-subgroup `P` of
`M` (`P` a Sylow of `↥M`, `Pamb` its ambient image), where each `Pamb`-invariant `p'`-subgroup
lies in `M`. Two cases on `O_{p'}(M)`:

* `O_{p'}(M) = ⊥`: by Theorem 6.2, `Z(L(P)) ⊴ M`, so
  `N_G(Pamb) ≤ N_G(Z(L(P))) = M` (`normalizer_le_normalizer_zCenterLOdd_map`,
  `normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot`).
* `O_{p'}(M) ≠ ⊥`: by Eq (9.1), `N_G(Pamb)` normalizes `⟨ℋ_G(Pamb;p')⟩ = O_{p'}(M)`, so
  `N_G(Pamb) ≤ N_G(O_{p'}(M)) = M` (`normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot`). -/
private theorem normalizer_sylow_map_le_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (P : Sylow p ↥M) (hp_dvd_G : p ∣ Nat.card G)
    (hPamb_ne_bot : (P : Subgroup ↥M).map M.subtype ≠ ⊥)
    (hPle : ∀ K : Subgroup G, K ∈ hInvariant ⊤ ((P : Subgroup ↥M).map M.subtype) ({p} : Set ℕ)ᶜ →
      K ≤ M) :
    Subgroup.normalizer (((P : Subgroup ↥M).map M.subtype) : Set G) ≤ M := by
  classical
  set Pamb : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPamb
  have hM_solvable : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  by_cases hOp : opiCoreInG ({p} : Set ℕ)ᶜ M = ⊥
  · -- `O_{p'}(M) = ⊥`: route through `Z(L(P))`.
    have hZnorm :
        (((OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype).subgroupOf M).Normal :=
      S08.zCenterLOdd_sylow_map_subgroupOf_normal_of_opiCoreInG_singleton_compl_eq_bot
        hG hp_dvd_G P hM_solvable hOp
    have hZne : (OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype ≠ ⊥ := by
      have hZ_ne : OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M) ≠ ⊥ :=
        S08.zCenterLOdd_ne_bot_of_isPGroup P.isPGroup'
          (by
            intro hPbot
            exact hPamb_ne_bot (by rw [hPamb, hPbot, Subgroup.map_bot]))
      intro hmap
      exact hZ_ne ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp hmap)
    have hNZ_eq_M : Subgroup.normalizer
        (((OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype) : Set G) = M :=
      S08.normalizer_zCenterLOdd_map_eq_of_normal_of_ne_bot hG hM hZnorm hZne
    calc Subgroup.normalizer (Pamb : Set G)
        ≤ Subgroup.normalizer
            (((OddOrder.BG.AppB.zCenterLOdd (P : Subgroup ↥M)).map M.subtype) : Set G) :=
          S08.normalizer_map_le_normalizer_zCenterLOdd_map (P : Subgroup ↥M)
      _ = M := hNZ_eq_M
  · -- `O_{p'}(M) ≠ ⊥`: route through `O_{p'}(M)` via Eq (9.1).
    have hEq91 : sSup (hInvariant ⊤ Pamb ({p} : Set ℕ)ᶜ) = opiCoreInG ({p} : Set ℕ)ᶜ M :=
      sSup_hInvariant_eq_opiCoreInG_singleton_compl P hPle
    calc Subgroup.normalizer (Pamb : Set G)
        ≤ Subgroup.normalizer
            ((sSup (hInvariant ⊤ Pamb ({p} : Set ℕ)ᶜ) : Subgroup G) : Set G) :=
          normalizer_le_normalizer_sSup_hInvariant_top
      _ = Subgroup.normalizer ((opiCoreInG ({p} : Set ℕ)ᶜ M : Subgroup G) : Set G) := by
          rw [hEq91]
      _ ≤ M := normalizer_opiCoreInG_le_maximal_of_ne_bot hG hM hOp

/-- If a subgroup lies in two distinct maximal subgroups, it cannot be uniquely
maximal. This is the formal core of the BG Lemma 9.5 line `L ≠ M`, hence no
subgroup of `M ∩ L` lies in `𝒰`. -/
theorem not_isUniquelyMaximal_of_le_inf_distinct_maximals
    {K M L : Subgroup G} (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G)
    (hKML : K ≤ M ⊓ L) (hLM : L ≠ M) :
    ¬ IsUniquelyMaximal K := by
  intro hK
  have hKM : K ≤ M := hKML.trans inf_le_left
  have hKL : K ≤ L := hKML.trans inf_le_right
  exact hLM (hK.eq_of_isCoatom_of_le hL hKL hM hKM)

/-- **BG Theorem 9.1, Eq (9.5) split** (mmd L2527-2529): `F(H) ⊆ R · O_{p'}(H) ⊆ M`. The Fitting
subgroup of `H` decomposes as `⨆_q O_q(H)`; `O_p(H) ⊆ R` (Sylow) and `O_q(H) ⊆ O_{p'}(H)` for
`q ≠ p`, so `F(H) ⊆ R ⊔ O_{p'}(H)`. Given the ambient images `R ⊆ M` and `O_{p'}(H) ⊆ M`, this
yields `F(H) ⊆ M`. -/
private theorem fittingInG_le_of_sylow_of_opiCore_le [Finite G]
    {p : ℕ} [Fact p.Prime] {H M : Subgroup G} (R : Sylow p ↥H)
    (hRM : (R : Subgroup ↥H).map H.subtype ≤ M)
    (hOpM : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M) :
    S08.fittingInG H ≤ M := by
  classical
  have hfitN : Ch01.fitting ↥H ≤ (R : Subgroup ↥H) ⊔ Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥H := by
    rw [Ch01.fitting_eq_iSup_primeFactors]
    refine iSup_le (fun q => ?_)
    have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    by_cases hq : (q : ℕ) = p
    · subst hq; exact le_sup_of_le_left (Ch01.opCore_le R)
    · refine le_sup_of_le_right (Ch03.Subgroup.IsPiGroup.le_oPiCore ?_)
      intro r hr
      have hrq : r = (q : ℕ) := by
        obtain ⟨n, hn⟩ := (Ch01.opCore_isPGroup (q : ℕ) ↥H).exists_card_eq
        rw [hn] at hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        exact (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
          (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      simp [hrq, hq]
  rw [S08.fittingInG]
  calc (Ch01.fitting ↥H).map H.subtype
      ≤ ((R : Subgroup ↥H) ⊔ Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥H).map H.subtype :=
        Subgroup.map_mono hfitN
    _ = (R : Subgroup ↥H).map H.subtype ⊔ opiCoreInG ({p} : Set ℕ)ᶜ H := by
        rw [Subgroup.map_sup]; rfl
    _ ≤ M := sup_le hRM hOpM

/-- **BG Theorem 9.1, Eq (9.5)+STEP5-7** (mmd L2527-2539), abstract form: let `H` be a finite
solvable group of odd order, `R` a Sylow `p`-subgroup, with `r(F(H)) ≤ 2`. If the ambient images
satisfy `R ⊆ M`, `O_{p'}(H) ⊆ M` (b), and `N_G(R) ⊆ M` (Eq 9.4), then `H ⊆ M`.

Proof: by Theorem 5.7 (`derived_le_fitting_of_centralizer_rank_le_two` with `E = ⊥`, using
`r(F(H)) ≤ 2`), `H' ⊆ F(H)`. The nilpotent `F(H)` splits as `⨆_q O_q(H) ⊆ R ⊔ O_{p'}(H) =: N`
(`fitting_eq_iSup_primeFactors`; `O_p ⊆ R`, `O_q ⊆ O_{p'}` for `q ≠ p`). Hence `H' ⊆ N`, so
`N ⊴ H`, and Frattini (`Sylow.normalizer_sup_eq_top'`) gives `H = N_H(R)·N`. Mapping back to `G`,
`N_H(R) ⊆ N_G(R) ⊆ M`, `R ⊆ M`, `O_{p'}(H) ⊆ M`, so `H ⊆ M`. -/
private theorem le_maximal_of_rank_fitting_le_two_of_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] {H M : Subgroup G} [Group.IsSolvable ↥H]
    (hoddH : Odd (Nat.card ↥H)) (R : Sylow p ↥H)
    (hrank : rank ↥(Ch01.fitting ↥H) ≤ 2)
    (hRM : (R : Subgroup ↥H).map H.subtype ≤ M)
    (hOpM : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M)
    (hNRM : Subgroup.normalizer (((R : Subgroup ↥H).map H.subtype) : Set G) ≤ M) :
    H ≤ M := by
  classical
  set N : Subgroup ↥H := (R : Subgroup ↥H) ⊔ Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥H with hN
  -- Theorem 5.7: `H' ⊆ F(H)` (via `E = ⊥`, `C(⊥) ⊓ F = F`, `r(F) ≤ 2`).
  have hderiv : commutator ↥H ≤ Ch01.fitting ↥H := by
    have hcentbot : Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) = ⊤ := by
      rw [Subgroup.coe_bot]; ext x; simp [Subgroup.mem_centralizer_iff]
    have hrank' : rank
        ↥(Subgroup.centralizer ((⊥ : Subgroup ↥H) : Set ↥H) ⊓ Ch01.fitting ↥H) ≤ 2 := by
      rw [hcentbot, top_inf_eq]; exact hrank
    exact OddOrder.BG.Ch1.S05.derived_le_fitting_of_centralizer_rank_le_two hoddH
      (⊥ : Subgroup ↥H) (bot_isElementaryAbelian (p := p)) bot_le hrank'
  -- `F(H) ⊆ R ⊔ O_{p'}(H)` via the nilpotent decomposition.
  have hfitN : Ch01.fitting ↥H ≤ N := by
    rw [Ch01.fitting_eq_iSup_primeFactors]
    refine iSup_le (fun q => ?_)
    have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    by_cases hq : (q : ℕ) = p
    · subst hq; exact le_sup_of_le_left (Ch01.opCore_le R)
    · refine le_sup_of_le_right (Ch03.Subgroup.IsPiGroup.le_oPiCore ?_)
      intro r hr
      have hrq : r = (q : ℕ) := by
        obtain ⟨n, hn⟩ := (Ch01.opCore_isPGroup (q : ℕ) ↥H).exists_card_eq
        rw [hn] at hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        exact (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
          (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      simp [hrq, hq]
  -- `N ⊴ H` (it contains `H'`), then Frattini's argument.
  have hNnorm : N.Normal := Subgroup.Normal.of_commutator_le _ (hderiv.trans hfitN)
  have := hNnorm
  have hRN : (R : Subgroup ↥H) ≤ N := le_sup_left
  have hfrattini : Subgroup.normalizer (R : Subgroup ↥H) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top' R hRN
  -- map `⊤ = N_H(R) ⊔ N` back to `G`.
  have hmaptop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, H.range_subtype]
  calc H = (⊤ : Subgroup ↥H).map H.subtype := hmaptop.symm
    _ = (Subgroup.normalizer (R : Subgroup ↥H) ⊔ N).map H.subtype := by rw [hfrattini]
    _ ≤ M := by
        rw [Subgroup.map_sup]
        refine sup_le (le_trans (Subgroup.le_normalizer_map H.subtype) hNRM) ?_
        rw [hN, Subgroup.map_sup]
        refine sup_le hRM ?_
        have hrfl : (Ch03.oPiCore ({p} : Set ℕ)ᶜ ↥H).map H.subtype
            = opiCoreInG ({p} : Set ℕ)ᶜ H := rfl
        rw [hrfl]; exact hOpM

/-- A noncyclic `p`-subgroup of a minimal odd simple group has rank at least two.

This is the small rank bridge used at the end of BG Corollary 9.3: once the
intermediate rank-three elementary abelian subgroup has been put in `𝒰`, Corollary 9.2
can be applied to the original noncyclic `p`-subgroup. -/
theorem two_le_rank_of_noncyclic_pSubgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {B : Subgroup G} (hBp : IsPGroup p B)
    (hBnc : ¬ IsCyclic ↥B) :
    2 ≤ rank ↥B := by
  classical
  have hp_dvd_B : p ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      have hBcard_one : Nat.card B = 1 := by simpa [hn_zero] using hn
      have : Subsingleton ↥B := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact hBnc isCyclic_of_subsingleton
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B))
  obtain ⟨E, hEea, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hBp hp_odd hBnc
  have hElog : 2 ≤ Nat.log p (Nat.card E) := by
    rw [hEcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
  have h2pRank : 2 ≤ pRank ↥B p := hElog.trans (le_pRank E hEea)
  exact h2pRank.trans (pRank_le_rank (G := ↥B) p)

/-- In a finite `p`-group, elementary abelian subgroups for a different prime have
zero logarithmic size. This is the local arithmetic bridge behind turning BG rank
of a `p`-group back into the same-prime `pRank`. -/
private theorem pRank_eq_zero_of_isPGroup_of_ne_prime {H : Type*} [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (hH : IsPGroup p H) :
    pRank H q = 0 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  apply le_antisymm ?_ (Nat.zero_le _)
  rw [pRank_le_iff]
  intro E hE
  have hE_p : IsPGroup p E := hH.to_subgroup E
  have hE_q : IsPGroup q E := hE.isPGroup
  obtain ⟨a, ha⟩ := hE_p.exists_card_eq
  obtain ⟨b, hb⟩ := hE_q.exists_card_eq
  have hcard_one : Nat.card E = 1 := by
    by_contra hne
    have hbpos : 0 < b := by
      by_contra hb0
      have hb_zero : b = 0 := by omega
      have hEcard_one : Nat.card E = 1 := by
        simpa [hb_zero] using hb
      exact hne hEcard_one
    have hq_dvd_card : q ∣ Nat.card E := by
      rw [hb]
      exact dvd_pow_self q hbpos.ne'
    have hq_dvd_powa : q ∣ p ^ a := by
      rwa [ha] at hq_dvd_card
    have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hq_dvd_powa
    have hqeqp : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp hq_dvd_p
    exact hqp hqeqp
  simp [hcard_one]

/-- A finite `p`-group has no rank contribution from primes other than `p`. -/
private theorem rank_le_pRank_of_isPGroup {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) :
    rank H ≤ pRank H p := by
  rw [rank_le_iff]
  intro q hq
  by_cases hqp : q = p
  · subst q
    exact le_rfl
  · rw [pRank_eq_zero_of_isPGroup_of_ne_prime (H := H) (p := p) (q := q) hq hqp hH]
    exact Nat.zero_le _

/-- In a finite `p`-group, a rank-three lower bound is witnessed at the same prime `p`. -/
theorem three_le_pRank_of_isPGroup_of_three_le_rank {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hr : 3 ≤ rank H) :
    3 ≤ pRank H p :=
  hr.trans (rank_le_pRank_of_isPGroup hH)

/-- A positive `pRank` lower bound forces `p` to divide the group order. -/
theorem mem_primeFactors_card_of_pos_pRank {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hpos : 0 < pRank H p) :
    p ∈ (Nat.card H).primeFactors := by
  obtain ⟨E, hEea, hElog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := H) (p := p) (n := 1) (by norm_num) hpos
  have hEp : IsPGroup p E := hEea.isPGroup
  have hp_dvd_E : p ∣ Nat.card E := by
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hElog
      norm_num at hElog
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  exact Nat.mem_primeFactors.mpr
    ⟨Fact.out, hp_dvd_E.trans (Subgroup.card_subgroup_dvd_card E), Nat.card_pos.ne'⟩

/-- Extend an elementary abelian subgroup contained in `H` to one maximal inside `H`. -/
private theorem exists_isMaxElemAbelianIn_ge_of_le [Finite G] {p : ℕ}
    {E H : Subgroup G} (hE : E.IsElementaryAbelian p) (hEH : E ≤ H) :
    ∃ A₀ : Subgroup G, E ≤ A₀ ∧ S08.isMaxElemAbelianIn p A₀ H := by
  obtain ⟨A₀, hEA₀, hA₀max⟩ :=
    Finite.exists_le_maximal
      (p := fun A₀ : Subgroup G => A₀.IsElementaryAbelian p ∧ A₀ ≤ H) ⟨hE, hEH⟩
  refine ⟨A₀, hEA₀, hA₀max.1.1, hA₀max.1.2, ?_⟩
  intro B hB hBH hA₀B
  exact le_antisymm (hA₀max.2 ⟨hB, hBH⟩ hA₀B) hA₀B

/-- A `pRank ≥ 3` subgroup has a rank-three maximal elementary abelian subgroup inside it. -/
theorem exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (h3 : 3 ≤ pRank ↥H p) :
    ∃ A₀ : Subgroup G, S08.isMaxElemAbelianIn p A₀ H ∧ 3 ≤ rank ↥A₀ := by
  obtain ⟨E, hEea, hElog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥H) (p := p) (n := 3) (by norm_num) h3
  let EG : Subgroup G := E.map H.subtype
  have hEG_ea : EG.IsElementaryAbelian p := by
    change (E.map H.subtype).IsElementaryAbelian p
    exact Subgroup.IsElementaryAbelian.map H.subtype_injective hEea
  have hEGH : EG ≤ H := by
    change E.map H.subtype ≤ H
    exact Subgroup.map_subtype_le E
  obtain ⟨A₀, hEGA₀, hA₀max⟩ := exists_isMaxElemAbelianIn_ge_of_le hEG_ea hEGH
  have hEGlog : 3 ≤ Nat.log p (Nat.card EG) := by
    change 3 ≤ Nat.log p (Nat.card (E.map H.subtype))
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hElog
  have h3EG : 3 ≤ pRank ↥EG p := hEGlog.trans hEG_ea.log_card_le_pRank
  have h3A₀p : 3 ≤ pRank ↥A₀ p :=
    h3EG.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hEGA₀)
        (Subgroup.inclusion_injective hEGA₀))
  exact ⟨A₀, hA₀max, h3A₀p.trans (pRank_le_rank (G := ↥A₀) p)⟩

/-- **BG Theorem 8.1 witness form** (mmd L2533, the input to BG Eq (9.5)→r(F(H))≤2): if some
prime `q` has `r_q(F(M)) ≥ 3`, then `F(M)` contains a subgroup in `𝒰`. This is the `9.1`-free
extraction of `abelian_rank_three_isUniquelyMaximal_of_fitting`'s witness: case `F(M)` not a
`q`-group uses Theorem 8.1(a) (`cFitting_isUniquelyMaximal_of_not_pGroup`, giving
`C_{F(M)}(A₀) ∈ 𝒰`), case `F(M)` a `q`-group uses Theorem 8.1(b)
(`sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup`) with an `SCN₃` subgroup from BG Lem 5.1
(`scn3_nonempty_of_three_le_pRank`). Both witnesses lie in `F(M)`, so this avoids the
`Corollary 9.2 ↦ Theorem 9.1` cycle that `abelian_rank_three_isUniquelyMaximal_of_fitting` incurs.
-/
private theorem exists_isUniquelyMaximal_le_fittingInG_of_three_le_pRank [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hr : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    ∃ U : Subgroup G, U ≤ S08.fittingInG M ∧ IsUniquelyMaximal U := by
  classical
  have hpF : q ∈ (Nat.card ↥(S08.fittingInG M)).primeFactors :=
    mem_primeFactors_card_of_pos_pRank (H := ↥(S08.fittingInG M)) (p := q) (by omega)
  obtain ⟨A₀, hA₀max, hA₀rank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank (H := S08.fittingInG M) hr
  by_cases hFp : IsPGroup q ↥(S08.fittingInG M)
  · -- `F(M)` a `q`-group: Theorem 8.1(b) gives an `SCN₃` witness inside `F(M)`.
    have hFpM : IsPGroup q ((S08.fittingInG M).subgroupOf M) :=
      hFp.of_equiv (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm
    obtain ⟨P, hFP⟩ := hFpM.exists_le_sylow
    have h3Fsub : 3 ≤ pRank ↥((S08.fittingInG M).subgroupOf M) q :=
      hr.trans
        (pRank_le_of_injective
          (f := (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe (S08.fittingInG_le M)).symm.injective)
    have h3P : 3 ≤ pRank ↥(P : Subgroup ↥M) q :=
      h3Fsub.trans
        (pRank_le_of_injective (f := Subgroup.inclusion hFP)
          (Subgroup.inclusion_injective hFP))
    have hp_dvd_G : q ∣ Nat.card G :=
      (Nat.mem_primeFactors.mp hpF).2.1.trans
        (Subgroup.card_subgroup_dvd_card (S08.fittingInG M))
    have hp_odd : Odd q := hG.odd.of_dvd_nat hp_dvd_G
    obtain ⟨Asc, hAsc_scn⟩ :=
      OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank hp_odd P.isPGroup' h3P
    let A_M : Subgroup ↥M := Asc.map (P : Subgroup ↥M).subtype
    have hA_MP : A_M ≤ (P : Subgroup ↥M) := Subgroup.map_subtype_le Asc
    have hA_M_scn : IsSCN₃ q (A_M.subgroupOf (P : Subgroup ↥M)) := by
      have htarget : A_M.subgroupOf (P : Subgroup ↥M) = Asc := by
        apply (Subgroup.map_subtype_inj (H := (P : Subgroup ↥M))).mp
        rw [Subgroup.map_subgroupOf_eq_of_le hA_MP]
      rwa [htarget]
    have h8 :=
      (S08.sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup
        hG hM hpF hA₀max hA₀rank P hFp).2 A_M hA_MP hA_M_scn
    exact ⟨A_M.map M.subtype, h8.1, h8.2⟩
  · -- `F(M)` not a `q`-group: Theorem 8.1(a) gives `C_{F(M)}(A₀) ∈ 𝒰`, contained in `F(M)`.
    refine ⟨S08.cFittingInG M A₀, inf_le_right, ?_⟩
    exact S08.cFitting_isUniquelyMaximal_of_not_pGroup hG hM hpF hA₀max hA₀rank hFp

/-- **BG Theorem 8.1, rank-squeeze form** (mmd L2533): if `H ∈ ℳ` and no subgroup of `F(H)` lies
in `𝒰`, then `r(F(H)) ≤ 2`. Contrapositive of
`exists_isUniquelyMaximal_le_fittingInG_of_three_le_pRank` (which is `9.1`-free, so this is safe to
use inside the proof of Theorem 9.1). -/
private theorem rank_fittingInG_le_two_of_no_uniqueMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hno : ∀ U : Subgroup G, U ≤ S08.fittingInG M → ¬ IsUniquelyMaximal U) :
    rank ↥(S08.fittingInG M) ≤ 2 := by
  classical
  by_contra hnot
  have h3 : 3 ≤ rank ↥(S08.fittingInG M) := by omega
  obtain ⟨q, hq, h3q⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥(S08.fittingInG M)) (n := 3) (by norm_num) h3
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨U, hUF, hUU⟩ :=
    exists_isUniquelyMaximal_le_fittingInG_of_three_le_pRank hG hM h3q
  exact hno U hUF hUU

/-- **BG Theorem 9.1, Eq (9.4)** (mmd L2520-2526), the Sylow-promotion step: pick a Sylow
`p`-subgroup `Rinf` of `H ⊓ M` containing the `p`-group `B`. Once the Eq (9.3)/(9.4) normalizer
condition `N_G(R) ≤ M` is supplied (`hNloc`, discharged in the body from `|H ⊓ M|_p` maximality
and Eq (9.3)), `R := Rinf` is automatically a Sylow `p`-subgroup of `H` (anything strictly above
`R` inside `H` would, via its `R`-normalizer, exceed the Sylow `Rinf` of `H ⊓ M`,
`forall_card_le_of_normalizer_sylow_inf_map_le`). Mirrors the BG Theorem 8.1(b) endgame in `S08`. -/
private theorem exists_sylow_normalizer_le_maximal_of_selection [Finite G]
    {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    {B : Subgroup G} (hBp : IsPGroup p B) (hBH : B ≤ H) (hBM : B ≤ M)
    (hNloc : ∀ Rinf : Sylow p ↥(H ⊓ M),
      (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Subgroup G) ≤ M →
      B ≤ ((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) →
      Subgroup.normalizer (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M) :
    ∃ R : Sylow p ↥H,
      ((R : Subgroup ↥H).map H.subtype ≤ M) ∧
      Subgroup.normalizer (((R : Subgroup ↥H).map H.subtype) : Set G) ≤ M := by
  classical
  -- `Rinf` : Sylow `p` of `H ⊓ M` containing `B`.
  have hBinf : B ≤ H ⊓ M := le_inf hBH hBM
  obtain ⟨Rinf, hB_Rinf⟩ := (hBp.comap_subtype (K := H ⊓ M)).exists_le_sylow
  set Ramb : Subgroup G := (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype with hRamb
  have hRamb_le_H : Ramb ≤ H := by
    rw [hRamb]; rintro x ⟨xi, -, rfl⟩; exact xi.2.1
  have hRamb_le_M : Ramb ≤ M := by
    rw [hRamb]; rintro x ⟨xi, -, rfl⟩; exact xi.2.2
  have hRamb_p : IsPGroup p Ramb := Rinf.isPGroup'.map (H ⊓ M).subtype
  have hB_Ramb : B ≤ Ramb := by
    rw [hRamb]
    calc B = (B.subgroupOf (H ⊓ M)).map (H ⊓ M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hBinf).symm
      _ ≤ (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype := Subgroup.map_mono hB_Rinf
  -- `N_G(Ramb) ≤ M` from the Eq (9.3) hypothesis.
  have hNRamb_le_M : Subgroup.normalizer (Ramb : Set G) ≤ M :=
    hNloc Rinf hRamb_le_M hB_Ramb
  -- card-maximality of `Ramb` among `p`-subgroups of `H` (since `N_G(Ramb) ≤ M`).
  have hforall :
      ∀ L : Subgroup G, IsPGroup p L → Ramb ≤ L → L ≤ H → Nat.card ↥L ≤ Nat.card ↥Ramb := by
    have := S08.forall_card_le_of_normalizer_sylow_inf_map_le Rinf hNRamb_le_M
    simpa [hRamb] using this
  -- promote `Ramb` to a Sylow `p`-subgroup of `H`.
  obtain ⟨R, hR_map⟩ :=
    S08.exists_sylow_subgroupOf_map_eq_of_not_dvd_index hRamb_p hRamb_le_H
      (S08.not_dvd_subgroupOf_index_of_forall_card_le hRamb_p hRamb_le_H hforall)
  refine ⟨R, ?_, ?_⟩
  · rw [hR_map]; exact hRamb_le_M
  · rw [hR_map]; exact hNRamb_le_M

/-- **BG Theorem 9.1** (mmd L2492): `p` prime, `M ∈ ℳ`, `B ∈ ℰ_p(M)` noncyclic で、
(a) 任意の `b ∈ B^#` で `C_G(b) ⊆ M`、または (b) `⟨ℋ_G(B;p')⟩ ⊆ M`、のいずれかなら `B ∈ 𝒰`。

Proof gate: mmd L2533 invokes BG Thm 8.1 and BG Thm 4.20 after Eq. (9.5). Do not add
BG Lem 4.13, BG Thm 4.16, or §5 narrow hypotheses to this theorem. -/
theorem noncyclic_isUniquelyMaximal_of_centralizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {B : Subgroup G} (hBea : B.IsElementaryAbelian p) (hBle : B ≤ M) (hBnc : ¬ IsCyclic ↥B)
    (hcase :
      (∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer {b} ≤ M) ∨
      sSup (hInvariant ⊤ B {p}ᶜ) ≤ M) :
    IsUniquelyMaximal B := by
  classical
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hBp : IsPGroup p B := hBea.isPGroup
  -- STEP 0: reduce (a) to (b): `sSup ℋ_G(B;p') ≤ M`.
  have hb : sSup (hInvariant ⊤ B ({p} : Set ℕ)ᶜ) ≤ M := by
    rcases hcase with hcent | hb
    · exact sSup_hInvariant_le_of_centralizer_le hBea hBnc hcent
    · exact hb
  -- `B` is proper (a maximal `M` is proper, `B ≤ M`).
  have hBproper : B < ⊤ := lt_of_le_of_lt hBle (mem_maximalSubgroups.mp hM).lt_top
  have hBne : B ≠ ⊥ := by
    intro hBbot
    exact hBnc (hBbot ▸ (by infer_instance : IsCyclic ↥(⊥ : Subgroup G)))
  -- `p ∣ |G|` (since `B ≠ ⊥` is a `p`-group).
  have hp_dvd_G : p ∣ Nat.card G := by
    have hBcard : p ∣ Nat.card ↥B := by
      obtain ⟨k, hk⟩ := hBp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk
        exact hBne (Subgroup.card_eq_one.mp hk)
      rw [hk]; exact dvd_pow_self p hk0
    exact hBcard.trans (Subgroup.card_subgroup_dvd_card B)
  by_contra hBnotU
  -- STEP 4 selection: choose `H ≠ M` maximal over `B`, maximizing `|H ⊓ M|_p`.
  obtain ⟨H, hH, hBH, hHM, hHmax⟩ :=
    exists_maximal_counterexample_image_of_not_isUniquelyMaximal
      (H := B) (M := M) (w := fun K : Subgroup G => S08.sylowInfCard p K M)
      hBproper hM hBle hBnotU
  have hHsolv : Group.IsSolvable ↥H := hG.isSolvable_of_mem_maximalSubgroups hH
  have hoddH : Odd (Nat.card ↥H) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  -- The Eq (9.4) normalizer condition `hNloc` (discharged via Eq (9.3) + maximality).
  have hNloc : ∀ Rinf : Sylow p ↥(H ⊓ M),
      (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Subgroup G) ≤ M →
      B ≤ ((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) →
      Subgroup.normalizer (((Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype) : Set G) ≤ M := by
    intro Rinf hRamb_le_M hB_Ramb
    set Ramb : Subgroup G := (Rinf : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype with hRamb
    have hRamb_p : IsPGroup p Ramb := Rinf.isPGroup'.map (H ⊓ M).subtype
    have hRamb_ne : Ramb ≠ ⊥ := fun hbot => hBne (le_bot_iff.mp (hB_Ramb.trans (le_of_eq hbot)))
    -- choose `P` Sylow of `M` containing `Ramb`.
    obtain ⟨P, hRamb_P⟩ :=
      (hRamb_p.comap_subtype (K := M)).exists_le_sylow
    set Pamb : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPamb
    have hPamb_le_M : Pamb ≤ M := Subgroup.map_subtype_le _
    have hRamb_Pamb : Ramb ≤ Pamb := by
      rw [hPamb]
      calc Ramb = (Ramb.subgroupOf M).map M.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hRamb_le_M).symm
        _ ≤ (P : Subgroup ↥M).map M.subtype := Subgroup.map_mono hRamb_P
    have hB_Pamb : B ≤ Pamb := hB_Ramb.trans hRamb_Pamb
    -- the Eq (9.1)/(9.3) hypothesis: each `Pamb`-invariant `p'`-subgroup `≤ M`.
    have hPle : ∀ K : Subgroup G,
        K ∈ hInvariant ⊤ Pamb ({p} : Set ℕ)ᶜ → K ≤ M := by
      intro K hK
      refine (le_sSup ?_).trans hb
      exact ⟨le_top, hB_Pamb.trans (hInvariant_le_normalizer hK), hInvariant_isPiSubgroup hK⟩
    -- Eq (9.3): `N_G(Pamb) ≤ M`.
    have hNPamb_le_M : Subgroup.normalizer (Pamb : Set G) ≤ M :=
      normalizer_sylow_map_le_maximal hG hM P hp_dvd_G
        (by rw [← hPamb]; intro hbot; exact hRamb_ne (le_bot_iff.mp (hRamb_Pamb.trans (le_of_eq
            hbot))))
        (by rw [← hPamb]; exact hPle)
    -- Case `Ramb = Pamb`: `N_G(Ramb) = N_G(Pamb) ≤ M`.
    by_cases hRP : Ramb = Pamb
    · rw [hRP]; exact hNPamb_le_M
    · -- Case `Ramb < Pamb`: route `N_G(Ramb)` into a maximal `L`; `L = M` by maximality.
      have hRamb_lt_Pamb : Ramb < Pamb := lt_of_le_of_ne hRamb_Pamb hRP
      obtain ⟨L, hL, hNG_le_L⟩ :=
        S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
          hG hM hRamb_ne hRamb_le_M
      by_cases hLM : L = M
      · rw [← hLM]; exact hNG_le_L
      · exfalso
        -- `N_{Pamb}(Ramb) > Ramb`, lies in `L ⊓ M`, bigger than `sylowInfCard p H M`.
        have hPamb_p : IsPGroup p Pamb := P.isPGroup'.map M.subtype
        have hRamb_lt_N : Ramb < Pamb ⊓ Subgroup.normalizer (Ramb : Set G) :=
          S08.lt_inf_normalizer_of_isPGroup_lt hPamb_p hRamb_lt_Pamb
        set N : Subgroup G := Pamb ⊓ Subgroup.normalizer (Ramb : Set G) with hNdef
        have hN_p : IsPGroup p N := hPamb_p.to_inf_left
        have hN_le_M : N ≤ M := inf_le_left.trans hPamb_le_M
        have hN_le_L : N ≤ L := inf_le_right.trans hNG_le_L
        -- `|N| ≤ sylowInfCard p L M ≤ sylowInfCard p H M = |Ramb| < |N|`.
        have hN_card_le_L : Nat.card ↥N ≤ S08.sylowInfCard p L M :=
          S08.card_le_sylowInfCard_of_isPGroup_le hN_p hN_le_L hN_le_M
        -- `B ≤ Ramb ≤ N_G(Ramb) ≤ L`, so the maximality of `H` applies to `L`.
        have hB_L : B ≤ L := hB_Ramb.trans (Subgroup.le_normalizer.trans hNG_le_L)
        have hL_le_H : S08.sylowInfCard p L M ≤ S08.sylowInfCard p H M :=
          hHmax L hL hB_L hLM
        -- `sylowInfCard p H M = |Ramb|`.
        have hHcard : S08.sylowInfCard p H M = Nat.card ↥Ramb := by
          rw [S08.sylowInfCard_eq_card p H M Rinf, hRamb,
            Subgroup.card_map_of_injective (H ⊓ M).subtype_injective]
        have hRamb_lt_card : Nat.card ↥Ramb < Nat.card ↥N :=
          Set.Finite.card_lt_card (Set.toFinite (N : Set G))
            (SetLike.coe_ssubset_coe.mpr hRamb_lt_N)
        have : Nat.card ↥N ≤ Nat.card ↥Ramb := by
          calc Nat.card ↥N ≤ S08.sylowInfCard p L M := hN_card_le_L
            _ ≤ S08.sylowInfCard p H M := hL_le_H
            _ = Nat.card ↥Ramb := hHcard
        exact (not_lt_of_ge this) hRamb_lt_card
  -- STEP 4 (Eq 9.4): a Sylow `R` of `H` with `R ⊆ M`, `O_{p'}(H) ⊆ M`, `N_G(R) ⊆ M`.
  obtain ⟨R, hRamb_le_M, hNRamb_le_M⟩ :=
    exists_sylow_normalizer_le_maximal_of_selection hBp hBH hBle hNloc
  -- `O_{p'}(H) ⊆ M`: `O_{p'}(H)` is a `B`-invariant `p'`-subgroup (`B ≤ H`, `O_{p'}(H) ⊴ H`).
  have hOpH_le_M : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M := by
    refine (le_sSup ?_).trans hb
    refine ⟨le_top, ?_, isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H⟩
    exact hBH.trans (le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H)
  -- Eq (9.5): `F(H) ⊆ M`.
  have hFHM : S08.fittingInG H ≤ M := fittingInG_le_of_sylow_of_opiCore_le R hRamb_le_M hOpH_le_M
  -- STEP 6 (Eq 9.5 → Thm 8.1): `r(F(H)) ≤ 2` since no subgroup of `F(H)` is in `𝒰`.
  have hrankFInG : rank ↥(S08.fittingInG H) ≤ 2 := by
    refine rank_fittingInG_le_two_of_no_uniqueMaximal hG hH ?_
    intro U hUF
    -- `U ≤ F(H) ⊆ M ⊓ H` and `M ≠ H` ⟹ `U ∉ 𝒰`.
    have hUMH : U ≤ M ⊓ H := le_inf (hUF.trans hFHM) (hUF.trans (S08.fittingInG_le H))
    exact not_isUniquelyMaximal_of_le_inf_distinct_maximals hM hH hUMH hHM
  -- `rank (fittingInG H) = rank (Ch01.fitting ↥H)` (image by injective subtype).
  have hrank : rank ↥(Ch01.fitting ↥H) ≤ 2 := by
    have heq : rank ↥(Ch01.fitting ↥H) = rank ↥(S08.fittingInG H) := by
      rw [S08.fittingInG]
      exact le_antisymm
        (rank_le_of_injective
          (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥H) H.subtype
            H.subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective (Ch01.fitting ↥H) H.subtype
            H.subtype_injective).injective)
        (rank_le_of_injective
          (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥H) H.subtype
            H.subtype_injective).symm.toMonoidHom)
          (Subgroup.equivMapOfInjective (Ch01.fitting ↥H) H.subtype
            H.subtype_injective).symm.injective)
    rw [heq]; exact hrankFInG
  -- STEP 5-7: `H ⊆ M`, contradicting `H ≠ M` (both maximal/coatoms).
  have hHleM : H ≤ M :=
    le_maximal_of_rank_fitting_le_two_of_sylow hoddH R hrank hRamb_le_M hOpH_le_M hNRamb_le_M
  have hHeqM : H = M := by
    rcases eq_or_lt_of_le hHleM with heq | hlt
    · exact heq
    · exact absurd ((mem_maximalSubgroups.mp hH).2 M hlt) (mem_maximalSubgroups.mp hM).1
  exact hHM hHeqM

/-- Contrapositive form of BG Theorem 9.1 used in Lemma 9.5: if the noncyclic
`p`-elementary subgroup `B ≤ M` is not in `𝒰`, then some nonidentity element of
`B` has centralizer not contained in `M`. -/
theorem exists_nontrivial_centralizer_not_le_of_not_isUniquelyMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hBea : B.IsElementaryAbelian p) (hBM : B ≤ M)
    (hBnc : ¬ IsCyclic ↥B) (hBnot : ¬ IsUniquelyMaximal B) :
    ∃ y : G, y ∈ B ∧ y ≠ 1 ∧ ¬ Subgroup.centralizer ({y} : Set G) ≤ M := by
  by_contra hnone
  have hcent : ∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M := by
    intro b hb hb1
    by_contra hnot_le
    exact hnone ⟨b, hb, hb1, hnot_le⟩
  exact hBnot (noncyclic_isUniquelyMaximal_of_centralizer_le hG hM hBea hBM hBnc
    (Or.inl hcent))

/-- Lemma 9.5 witness selection after BG Theorem 9.1: choose `y ∈ B#` and a
maximal subgroup `L` over `C_G(y)` with `L ≠ M`. -/
theorem exists_nontrivial_centralizer_maximal_ne_of_not_isUniquelyMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hBea : B.IsElementaryAbelian p) (hBM : B ≤ M)
    (hBnc : ¬ IsCyclic ↥B) (hBnot : ¬ IsUniquelyMaximal B) :
    ∃ y : G, ∃ L : Subgroup G,
      y ∈ B ∧ y ≠ 1 ∧
      ¬ Subgroup.centralizer ({y} : Set G) ≤ M ∧
      L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) ∧
      L ≠ M := by
  obtain ⟨y, hyB, hy1, hCGnotM⟩ :=
    exists_nontrivial_centralizer_not_le_of_not_isUniquelyMaximal hG hM hBea hBM hBnc hBnot
  obtain ⟨L, hLco, hCGleL⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer ({y} : Set G))).resolve_left
      (centralizer_singleton_lt_top hG hy1).ne
  have hLneM : L ≠ M := by
    intro hLM
    exact hCGnotM (by simpa [hLM] using hCGleL)
  exact ⟨y, L, hyB, hy1, hCGnotM, ⟨hLco, hCGleL⟩, hLneM⟩

/-- If `y ∈ A`, then any maximal subgroup over `C_G(y)` is also a maximal
subgroup over `C_G(A)`. This is the formal `C_G(A) ≤ C_G(y) ≤ L` bridge used
when Lemma 9.5 reapplies (9.9) with `L` in place of `M`. -/
theorem maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton
    {A L : Subgroup G} {y : G} (hyA : y ∈ A)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G))) :
    L ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) := by
  exact ⟨hL.1,
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyA)).trans hL.2⟩

end OddOrder.BG.Ch2.S09


