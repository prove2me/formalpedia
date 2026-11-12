-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Basic
-- name    : OddOrder_Isaacs_Ch01_Sylow_Basic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:09.040191+00:00
-- url     : https://prove2.me/theorems/33c50668-20a5-4640-a910-a320df2dff6b
-- title:
--   Isaacs Ch. 1: $O_p(G)$, the Fitting subgroup, and basic Sylow facts
-- statement:
--   The basic part of the Chapter 1 (Sylow theory) formalization of Isaacs, *Finite Group Theory*. It defines $O_p(G)$ as the intersection of all Sylow $p$-subgroups (Isaacs Problem 1B.2) and the Fitting subgroup $F(G)$ as the join of the $O_p(G)$ over all primes, and proves they are normal and characteristic, and that $F(G)$ is nilpotent.
--
--   Main definitions: `opCore` ($O_p(G)$) with its normality and characteristic properties, and `fitting` ($F(G)$) with normality, characteristic and nilpotency results, plus `sup_isNilpotent_of_normal_nilpotent`. Lemmas include Cauchy's theorem and facts on $p$-groups, normalizers in nilpotent groups, and normal Sylow subgroups.
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch01_Sylow/Basic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch01_Sylow/Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ChermakDelgado
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Sylow

namespace OddOrder.Isaacs.Ch01

open scoped IsMulCommutative

section

variable {G : Type*} [Group G]

/-- **Isaacs Cor 1.9** (Cauchy).  有限群 `G` で素数 `p ∣ |G|` ⇒ `G` は位数 `p`
の元を持つ.

mathlib `exists_prime_orderOf_dvd_card'` の再述. -/
theorem cauchy [Finite G] {p : ℕ} [Fact p.Prime] (hdvd : p ∣ Nat.card G) :
    ∃ x : G, orderOf x = p :=
  exists_prime_orderOf_dvd_card' p hdvd

end

section

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Thm 1.19**.  `P` を有限 `p`-群, `N` をその非自明な正規部分群とすると,
`N ∩ Z(P)` は非自明.

証明骨子: `ConjAct P` の作用を `N` (正規部分群) に制限して考える
(`Subgroup.conjMulDistribMulAction`).  `IsPGroup p P` から `IsPGroup p (ConjAct P)`,
`IsPGroup.card_modEq_card_fixedPoints` で `|N| ≡ |fixedPoints| (mod p)`.
`N` 非自明 p-群より `p ∣ |N|`, ゆえ `p ∣ |fixedPoints|`. `1 ∈ fixedPoints` なので
`|fixedPoints| ≥ 1`, よって `≥ p ≥ 2`, 非自明. fixed point は `N ∩ Z(P)` の元. -/
theorem IsPGroup.normal_inf_center_nontrivial {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N : Subgroup P} [N.Normal] (hN : Nontrivial N) :
    Nontrivial ((N ⊓ Subgroup.center P : Subgroup P)) := by
  -- ConjAct P acts on N (since N is normal), IsPGroup p (ConjAct P).
  have hCA : IsPGroup p (ConjAct P) := hP.of_equiv ConjAct.toConjAct
  -- p divides |N| since N is a nontrivial p-group.
  have hpN : p ∣ Nat.card N := by
    obtain ⟨n, hn0, hn⟩ := (hP.to_subgroup N).nontrivial_iff_card.mp hN
    exact hn.symm ▸ dvd_pow_self _ hn0.ne'
  -- 1 is fixed under the ConjAct P action on N.
  have h1 : (1 : N) ∈ MulAction.fixedPoints (ConjAct P) N := by
    intro g
    apply Subtype.ext
    change (g : ConjAct P) • ((1 : N) : P) = ((1 : N) : P)
    rw [ConjAct.smul_def]
    simp
  -- p ∣ |N| and ∃ fixed point ⇒ ∃ another fixed point ≠ 1.
  obtain ⟨g, hgFix, hg1⟩ :=
    hCA.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := N) hpN h1
  -- (g : P) is central, and g ∈ N, hence ≠ 1 gives nontriviality of N ⊓ center P.
  have hg_center : (g : P) ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro h
    have heq : ConjAct.toConjAct h • g = g := hgFix _
    have hcoe : (((ConjAct.toConjAct h) • g : N) : P) = (g : P) := by rw [heq]
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul_eq_mulAut_conj,
      MulAut.conj_apply] at hcoe
    -- hcoe : h * (g : P) * h⁻¹ = (g : P)
    rw [mul_inv_eq_iff_eq_mul] at hcoe
    exact hcoe
  refine ⟨⟨1, ⟨((g : N) : P), Subgroup.mem_inf.mpr ⟨g.2, hg_center⟩⟩, ?_⟩⟩
  intro heq
  apply hg1
  -- heq : (1 : (N ⊓ center P)) = ⟨(g : P), ...⟩ at the inf level
  -- goal: 1 = g at the N level
  apply Subtype.ext  -- to P level
  have := congrArg (fun x : (N ⊓ Subgroup.center P : Subgroup P) => (x : P)) heq
  simpa using this

/-- **Isaacs Thm 1.22** (Normalizer Condition、p.22).  冪零群 `G` で真部分群 `H < G` ならば
`H < N_G(H)`.

⚠ 書籍は **"(not necessarily finite) nilpotent group"** と明記する。本 statement も
`[Finite G]` を取らないので書籍強度 — 以前の docstring が「有限冪零群」と書いていたのは
**statement より狭い記述**で、2026-08-08 の逐条監査 (issue 0176) で訂正した。

mathlib `Group.normalizerCondition_of_isNilpotent` の再述. -/
theorem lt_normalizer_of_isNilpotent_of_lt_top [Group.IsNilpotent G]
    {H : Subgroup G} (hH : H < ⊤) :
    H < Subgroup.normalizer H :=
  Group.normalizerCondition_of_isNilpotent H hH

/-- **Isaacs Lemma 1.23**.  `P` を有限 `p`-群, `N, M ⊴ P` で `N < M` ならば,
ある `L ⊴ P` が存在して `N < L`, `L ≤ M`, かつ `N.relIndex L = p`.

証明: `M.map (mk' N) ⊴ P/N` は非自明 (`N < M`).  `P/N` は finite p-群なので
Thm 1.19 で `M.map (mk' N) ⊓ Z(P/N)` も非自明. Cauchy で位数 `p` の元 `y` を取り,
`zpowers y ≤ Z(P/N)` ゆえ `P/N` で正規.  `L := (zpowers y).comap (mk' N)` が
条件 (`N < L ≤ M`, `relIndex = p`) を満たす. -/
theorem IsPGroup.exists_normal_index_eq_prime {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    {N M : Subgroup P} [N.Normal] [M.Normal] (hNM : N < M) :
    ∃ L : Subgroup P, L.Normal ∧ N < L ∧ L ≤ M ∧ N.relIndex L = p := by
  -- P/N も p-群
  have hQuot_pgroup : IsPGroup p (P ⧸ N) := hP.to_quotient N
  -- M.map (mk' N) ⊴ P/N
  let M' : Subgroup (P ⧸ N) := M.map (QuotientGroup.mk' N)
  have : M'.Normal := inferInstance
  -- M' は非自明 (N < M)
  have hM'_nontriv : Nontrivial M' := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    obtain ⟨m, hmM, hmN⟩ := SetLike.exists_of_lt hNM
    apply hmN
    have hm_in : QuotientGroup.mk' N m ∈ M' := Subgroup.mem_map.mpr ⟨m, hmM, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hm_in
    exact (QuotientGroup.eq_one_iff m).mp hm_in
  -- Thm 1.19 で M' ⊓ Z(P/N) も非自明.  Quotient is finite.
  have : Finite (P ⧸ N) := Quotient.finite _
  have hinf_nontriv : Nontrivial ((M' ⊓ Subgroup.center (P ⧸ N) : Subgroup (P ⧸ N))) :=
    IsPGroup.normal_inf_center_nontrivial hQuot_pgroup hM'_nontriv
  -- Cauchy: 位数 p の元を取る
  have h_subgroup_pgroup : IsPGroup p (↥(M' ⊓ Subgroup.center (P ⧸ N))) :=
    hQuot_pgroup.to_subgroup _
  obtain ⟨k, hk0, hk_card⟩ := h_subgroup_pgroup.nontrivial_iff_card.mp hinf_nontriv
  have hp_dvd_inf : p ∣ Nat.card (↥(M' ⊓ Subgroup.center (P ⧸ N))) := by
    rw [hk_card]; exact dvd_pow_self _ hk0.ne'
  obtain ⟨ysub, hy_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd_inf
  set y : P ⧸ N := (ysub : P ⧸ N)
  have hy_M : y ∈ M' := (Subgroup.mem_inf.mp ysub.2).1
  have hy_Z : y ∈ Subgroup.center (P ⧸ N) := (Subgroup.mem_inf.mp ysub.2).2
  have hy_order : orderOf y = p := by
    rw [show y = ((ysub : ↥(M' ⊓ Subgroup.center (P ⧸ N))) : P ⧸ N) from rfl]
    exact (orderOf_injective ((M' ⊓ Subgroup.center (P ⧸ N)).subtype)
      Subtype.coe_injective ysub).trans hy_ord
  -- ⟨y⟩ ≤ Z(P/N), 正規
  have hzpowers_le_center : Subgroup.zpowers y ≤ Subgroup.center (P ⧸ N) :=
    Subgroup.zpowers_le.mpr hy_Z
  have hzpowers_normal : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn_center := hzpowers_le_center hn
    rw [Subgroup.mem_center_iff] at hn_center
    have hgn : g * n = n * g := hn_center g
    have : g * n * g⁻¹ = n := by rw [hgn, mul_inv_cancel_right]
    rw [this]; exact hn
  have hzpowers_le_M' : Subgroup.zpowers y ≤ M' := Subgroup.zpowers_le.mpr hy_M
  set L : Subgroup P := (Subgroup.zpowers y).comap (QuotientGroup.mk' N) with hL_def
  refine ⟨L, inferInstance, ?_, ?_, ?_⟩
  · -- N < L
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      rw [hL_def, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx]
      exact (Subgroup.zpowers y).one_mem
    · intro heq
      have hy_eq_one : y = 1 := by
        obtain ⟨pbar, hpbar⟩ := QuotientGroup.mk'_surjective N y
        have hpbar_L : pbar ∈ L := by
          rw [hL_def, Subgroup.mem_comap, hpbar]; exact Subgroup.mem_zpowers y
        rw [← heq] at hpbar_L
        rw [← hpbar]; exact (QuotientGroup.eq_one_iff pbar).mpr hpbar_L
      have hOrder1 : orderOf (1 : P ⧸ N) = p := hy_eq_one ▸ hy_order
      rw [orderOf_one] at hOrder1
      exact (Fact.out (p := p.Prime)).one_lt.ne hOrder1
  · -- L ≤ M
    intro x hx
    simp only [hL_def, Subgroup.mem_comap, QuotientGroup.mk'_apply] at hx
    have hx_M' : QuotientGroup.mk x ∈ M' := hzpowers_le_M' hx
    obtain ⟨m, hmM, hmEq⟩ := Subgroup.mem_map.mp hx_M'
    have hmx : (QuotientGroup.mk m : P ⧸ N) = QuotientGroup.mk x := by
      have := hmEq; simp only [QuotientGroup.mk'_apply] at this; exact this
    have hinN : m⁻¹ * x ∈ N := QuotientGroup.eq.mp hmx
    have hmix_M : m⁻¹ * x ∈ M := hNM.le hinN
    have hxeq : x = m * (m⁻¹ * x) := by group
    rw [hxeq]; exact M.mul_mem hmM hmix_M
  · -- N.relIndex L = p
    have hN_le_L : N ≤ L := by
      intro x hx
      rw [hL_def, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff x).mpr hx]
      exact (Subgroup.zpowers y).one_mem
    have hLidx : L.index = (Subgroup.zpowers y).index :=
      Subgroup.index_comap_of_surjective (Subgroup.zpowers y) (QuotientGroup.mk'_surjective N)
    have hLag1 : Nat.card (Subgroup.zpowers y) * (Subgroup.zpowers y).index = Nat.card (P ⧸ N) :=
      (Subgroup.zpowers y).card_mul_index
    have hzy_card : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hy_order]
    have hLag2 : N.relIndex L * L.index = N.index := Subgroup.relIndex_mul_index hN_le_L
    have hN_index : N.index = Nat.card (P ⧸ N) := rfl
    have h_N_eq : N.index = p * L.index := by rw [hN_index, ← hLag1, hzy_card, hLidx]
    have h_eq : N.relIndex L * L.index = p * L.index := by rw [hLag2, h_N_eq]
    have : Finite (P ⧸ L) := Quotient.finite _
    have hL_index_ne_zero : L.index ≠ 0 := Nat.card_pos.ne'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hL_index_ne_zero) h_eq

/-- `O_p(G)`: `G` の全 Sylow `p`-部分群の共通部分.  Isaacs Problem 1B.2 で示される
ように, これは `G` の最大の正規 `p`-部分群と一致する.

mathlib 未収載のため新規定義 (将来 mathlib に `Subgroup.opCore` として PR したい形). -/
def opCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ P : Sylow p G, (P : Subgroup G)

@[simp]
theorem mem_opCore {p : ℕ} {x : G} :
    x ∈ opCore p G ↔ ∀ P : Sylow p G, x ∈ (P : Subgroup G) := by
  simp [opCore, Subgroup.mem_iInf]

theorem opCore_le {p : ℕ} (P : Sylow p G) : opCore p G ≤ (P : Subgroup G) :=
  iInf_le _ P

/-- `O_p(G)` は `p`-部分群 (Sylow に含まれるから).

`[Fact p.Prime]` 必須 (`Sylow.nonempty` から少なくとも 1 つの Sylow を取るため). -/
theorem opCore_isPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] :
    IsPGroup p (opCore p G) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact P.2.of_injective (Subgroup.inclusion (opCore_le P))
    (Subgroup.inclusion_injective _)

/-- `O_p(G)` は `G` で正規.
証明: `Subgroup.Normal.of_conjugate_fixed` を使い,
`∀ g : G, MulAut.conj g • opCore p G = opCore p G` を示す.
各 `g` について `MulAut.conj g` は Sylow 部分群を Sylow 部分群に写す (`g • P ∈ Sylow p G`)
ので, 全 Sylow の共通部分 `opCore p G` も共役不変. -/
instance opCore.normal (p : ℕ) (G : Type*) [Group G] : (opCore p G).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  ext x
  simp only [mem_opCore, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  -- After simp: ∀ P, (MulAut.conj g)⁻¹ x ∈ ↑P  ↔  ∀ P, x ∈ ↑P
  -- Here ↑P is the Subgroup G coercion via CoeOut (Sylow p G) (Subgroup G)
  constructor
  · intro h P
    -- Apply h to (g⁻¹ • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : (MulAut.conj g)⁻¹ x ∈ (↑(g⁻¹ • P) : Subgroup G) := h (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, ← map_inv,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    simp only [map_inv, inv_inv, MulAut.smul_def] at hQ
    rwa [MulAut.apply_inv_self] at hQ
  · intro h P
    -- Apply h to (g • P : Sylow p G); then unfold the smul at Subgroup level
    have hQ : x ∈ (↑(g • P) : Subgroup G) := h (g • P)
    rw [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    exact hQ

/-- `O_p(G)` は `G` で特性的 (任意の自己同型 `φ : G ≃* G` で不変).

証明: `characteristic_iff_le_comap` 経由. 任意の `φ` と `x ∈ opCore p G` について,
全 Sylow `Q` に対し `Q.comapOfInjective φ.toMonoidHom` も Sylow `p` で,
`x ∈ Q.comapOfInjective ...` ⇔ `φ x ∈ Q`. -/
instance opCore.characteristic (p : ℕ) (G : Type*) [Group G] :
    (opCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap, mem_opCore]
  rw [mem_opCore] at hx
  intro Q
  have hinj : Function.Injective (φ.toMonoidHom : G →* G) := φ.injective
  have hrange : (Q : Subgroup G) ≤ (φ.toMonoidHom : G →* G).range := by
    rw [MonoidHom.range_eq_top.mpr φ.surjective]; exact le_top
  -- `Q.comapOfInjective φ.toMonoidHom hinj hrange : Sylow p G` and its coercion is `Q.comap φ`.
  have hxQ' := hx (Q.comapOfInjective (φ.toMonoidHom : G →* G) hinj hrange)
  rwa [Sylow.coe_comapOfInjective, Subgroup.mem_comap] at hxQ'

/-- **Isaacs Problem 1B.2**. 任意の正規 `p`-部分群 `N` は `opCore p G` に含まれる.
これにより `opCore p G` は `G` の最大正規 `p`-部分群である.

証明: Sylow D (`IsPGroup.exists_le_sylow`) で `N ≤ Q` となる Sylow `Q` を取り,
任意の Sylow `P` に対して Sylow C (`[Finite (Sylow p G)]`) で `∃ g, P = g • Q` を取る.
`N` の正規性から `N = MulAut.conj g • N ≤ MulAut.conj g • Q = ↑(g • Q) = ↑P`. -/
theorem normal_pgroup_le_opCore {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite (Sylow p G)]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) :
    N ≤ opCore p G := by
  rw [opCore, le_iInf_iff]
  intro P
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-- A normal Sylow `p`-subgroup is the `p`-core. -/
theorem Sylow.eq_opCore_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (hP : (P : Subgroup G).Normal) :
    (P : Subgroup G) = opCore p G := by
  have : (P : Subgroup G).Normal := hP
  exact le_antisymm (normal_pgroup_le_opCore P.isPGroup') (opCore_le P)

/-- A characteristic subgroup with the order of a Sylow `p`-subgroup supplies a normal
Sylow `p`-subgroup. -/
theorem exists_normal_sylow_of_characteristic_card_eq [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G} (hKchar : K.Characteristic)
    (hKcard : Nat.card K = p ^ (Nat.card G).factorization p) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal := by
  classical
  have : K.Characteristic := hKchar
  let P : Sylow p G := Sylow.ofCard K hKcard
  refine ⟨P, ?_⟩
  have hP : (P : Subgroup G) = K := by
    simp [P]
  rw [hP]
  infer_instance

/-- A characteristic subgroup whose order matches a Sylow `p`-subgroup is itself a normal
Sylow `p`-subgroup. -/
theorem exists_normal_sylow_of_characteristic_card_eq_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G} (hKchar : K.Characteristic)
    (P₀ : Sylow p G) (hKcard : Nat.card K = Nat.card (P₀ : Subgroup G)) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal :=
  exists_normal_sylow_of_characteristic_card_eq hKchar
    (hKcard.trans P₀.card_eq_multiplicity)

/-- **Isaacs Thm 1.26 (1) ⇔ (4)**.  有限群 `G` について「`G` が冪零」と
「`G` の任意の Sylow 部分群が正規」は同値.

mathlib `Group.isNilpotent_of_finite_tfae` の (0) ⇔ (3) の抽出ラッパー.  Isaacs 流 5 条件
((1)冪零, (2)`H<G ⇒ N_G(H)>H`, (3) 全極大正規, (4) 全 Sylow 正規, (5) Sylow 内部直積)
は TFAE 全体 (`Group.isNilpotent_of_finite_tfae`) で確保される. -/
theorem isNilpotent_iff_forall_sylow_normal [Finite G] :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal :=
  Group.isNilpotent_of_finite_tfae.out 0 3

/-- **Isaacs Thm 1.26 (1) ⇒ (4)** (片向き取り出し).
冪零ならば任意の Sylow は正規. -/
theorem Sylow.normal_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  isNilpotent_iff_forall_sylow_normal.mp ‹_› p P

/-- **Isaacs Lemma 1.27**.  `H i : ι → Subgroup G` が有限族で各 `H i` が正規部分群,
かつ位数 (`Nat.card`) が対ごとに互いに素ならば, 族 `H` は `iSupIndep` (内部直積構造).

証明: 互いに素 ⇒ `Subgroup.disjoint_of_coprime_natCard` で `Disjoint`,
正規 + Disjoint ⇒ `commute_of_normal_of_disjoint` で `Pairwise Commute`,
最後に mathlib `Subgroup.independent_of_coprime_order` を適用. -/
theorem iSupIndep_of_coprime_card_of_normal {ι : Type*} [Finite ι]
    (H : ι → Subgroup G) [∀ i, (H i).Normal] [∀ i, Finite (H i)]
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    iSupIndep H := by
  -- Step 1: Disjoint from coprime cards.
  have hdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j) := fun i j hij =>
    Subgroup.disjoint_of_coprime_natCard (hcoprime hij)
  -- Step 2: Pairwise commute from disjoint + normal.
  have hcomm : Pairwise fun i j : ι =>
      ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact Subgroup.commute_of_normal_of_disjoint (H i) (H j)
      inferInstance inferInstance (hdisj i j hij) x y hx hy
  -- Step 3: Apply mathlib's independent_of_coprime_order.
  classical
  have : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite _
  have hcoprime' : Pairwise fun i j =>
      Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j)) := by
    intro i j hij
    have := hcoprime hij
    simpa [Nat.card_eq_fintype_card] using this
  exact Subgroup.independent_of_coprime_order hcomm hcoprime'

/-- **Fitting subgroup** `F(G)`: 全ての素数 `p` についての `opCore p G` (= `O_p(G)`)
の supremum.  これは `G` の最大の正規冪零部分群となる (Isaacs Cor 1.28).

mathlib 未収載のため新規定義. `Subgroup.fitting` として将来 mathlib に PR したい形.

Isaacs 流の定義「`|G|` の各素因子 `p` について `O_p(G)` の積」と等価. 非素数 `p` や
`|G|` に分割しない素数 `p` に対しては `opCore p G ⊆` 既存の sup なので, 範囲を
広げても結果は変わらない (実際 `opCore p G = ⊥` for primes p ∤ |G|, 有限 G で). -/
def fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : Nat.Primes, opCore (p : ℕ) G

theorem opCore_le_fitting (p : Nat.Primes) (G : Type*) [Group G] :
    opCore (p : ℕ) G ≤ fitting G :=
  le_iSup (fun q : Nat.Primes => opCore (q : ℕ) G) p

/-- `F(G)` は `G` で特性的. 各 `opCore p G` が特性的 (`opCore.characteristic`) で,
特性的部分群の sup は特性的 (`Subgroup.map_iSup` + `iSup_congr`). -/
instance fitting.characteristic (G : Type*) [Group G] : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change (⨆ p : Nat.Primes, opCore (p : ℕ) G).map φ.toMonoidHom
    = ⨆ p : Nat.Primes, opCore (p : ℕ) G
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp (opCore.characteristic _ _) φ

/-- `F(G)` は `G` の正規部分群. 各 `opCore p G` の正規性を `iSup_induction` で全体に持ち上げる. -/
instance fitting.normal (G : Type*) [Group G] : (fitting G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ fitting G) hn
    ?mem ?one ?mul
  case mem =>
    intro p x hx
    -- x ∈ opCore p G が正規だから g * x * g⁻¹ ∈ opCore p G ≤ fitting
    exact (opCore_le_fitting p G) ((opCore.normal (p : ℕ) G).conj_mem x hx g)
  case one =>
    simp
  case mul =>
    intro x y hx hy
    -- g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (fitting G).mul_mem hx hy

/-- 補助補題: 有限冪零群 `N` では, 各素因数 `p` に対する代表 Sylow 部分群
`default : Sylow p N` の supremum は `⊤_N` に等しい.

証明骨子: Thm 1.26 で全 Sylow が正規, よって `unique_of_normal` で各素因数につき
Sylow が 1 つ. `noncommPiCoprod` 経由で `(∀ p ∈ pf(|N|), Sylow p N) →* N` を作り,
互いに素な p-群より単射 (`independent_of_coprime_order`), 濃度比較で全射 ⇒ range = ⊤.
range = `⨆ p, ↑(default Sylow)` (by `noncommPiCoprod_range`). -/
theorem iSup_default_sylow_eq_top_of_nilpotent
    (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N] :
    ⨆ p : (Nat.card N).primeFactors,
        ((default : Sylow (p : ℕ) N) : Subgroup N) = ⊤ := by
  classical
  have hnormal : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), P.Normal := fun P =>
    Sylow.normal_of_isNilpotent P
  have _ := Fintype.ofFinite N
  set ps := (Nat.card N).primeFactors with hps
  let P : ∀ p, Sylow p N := default
  have hPfin : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : N, x ∈ (P p₁ : Subgroup N) → y ∈ (P p₂ : Subgroup N) → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hnormal (P p₁)) (hnormal (P p₂))
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- noncommPiCoprod : (∀ p : ps, P p) →* N
  set f := Subgroup.noncommPiCoprod (G := N) (H := fun p : ps => (P p : Subgroup N)) hcomm
    with hf
  -- f is injective by independent_of_coprime_order
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  -- |∀ p : ps, P p| = |N|
  have hcard : Fintype.card (∀ p : ps, P p) = Fintype.card N := by
    simp only [← Nat.card_eq_fintype_card]
    calc Nat.card (∀ p : ps, P p)
        = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card N).factorization p.1 := by
          refine Finset.prod_congr rfl ?_
          rintro ⟨p, hp⟩ _
          exact @Sylow.card_eq_multiplicity _ _ _ p
            ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card N).factorization p :=
          Finset.prod_finset_coe (fun p => p ^ (Nat.card N).factorization p) _
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'
  -- bijective
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  -- range = ⊤
  have hrange : f.range = (⊤ : Subgroup N) :=
    MonoidHom.range_eq_top.mpr hbij.surjective
  -- but noncommPiCoprod_range says range = ⨆ i, H i
  have hrange' : f.range = ⨆ p : ps, (P p : Subgroup N) :=
    Subgroup.noncommPiCoprod_range
  rw [hrange'] at hrange
  exact hrange

/-- In a finite nilpotent group, the center of any Sylow subgroup lies in the center of the
whole group. -/
theorem center_sylow_le_center_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (Subgroup.center ↥(P : Subgroup G)).map (P : Subgroup G).subtype ≤ Subgroup.center G := by
  classical
  intro z hz
  obtain ⟨zp, hzp_center, hzp_eq⟩ := hz
  have hzp_eqG : (zp : G) = z := hzp_eq
  have hzP : z ∈ (P : Subgroup G) := by
    rw [← hzp_eqG]
    exact zp.2
  rw [Subgroup.mem_center_iff]
  intro g
  have hg_sup :
      g ∈ ⨆ r : (Nat.card G).primeFactors,
          ((default : Sylow (r : ℕ) G) : Subgroup G) := by
    rw [iSup_default_sylow_eq_top_of_nilpotent G]
    exact trivial
  refine Subgroup.iSup_induction _ (C := fun x => x * z = z * x) hg_sup ?mem ?one ?mul
  · rintro ⟨r, hr⟩ x hx
    have hrprime : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    by_cases hrp : r = p
    · subst p
      have hP_normal : P.Normal := Sylow.normal_of_isNilpotent P
      have : Unique (Sylow r G) := Sylow.unique_of_normal P hP_normal
      have hxP : x ∈ (P : Subgroup G) := by
        simpa [Subsingleton.elim (default : Sylow r G) P] using hx
      have hcomm := congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzp_center ⟨x, hxP⟩)
      simpa [hzp_eqG] using hcomm
    · have hD_normal : ((default : Sylow r G) : Subgroup G).Normal :=
        Sylow.normal_of_isNilpotent _
      have hP_normal : (P : Subgroup G).Normal := Sylow.normal_of_isNilpotent P
      have hdisjoint : Disjoint ((default : Sylow r G) : Subgroup G) (P : Subgroup G) :=
        IsPGroup.disjoint_of_ne r p hrp _ _ (default : Sylow r G).isPGroup' P.isPGroup'
      exact (Subgroup.commute_of_normal_of_disjoint _ _ hD_normal hP_normal hdisjoint _ _
        hx hzP).eq
  · simp
  · intro x y hx hy
    calc
      (x * y) * z = x * (y * z) := by group
      _ = x * (z * y) := by rw [hy]
      _ = (x * z) * y := by group
      _ = (z * x) * y := by rw [hx]
      _ = z * (x * y) := by group

/-- In a finite nilpotent group, every prime divisor of the group order divides the center. -/
theorem mem_primeFactors_center_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (hp : p ∈ (Nat.card G).primeFactors) :
    p ∈ (Nat.card ↥(Subgroup.center G)).primeFactors := by
  let P : Sylow p G := default
  let ZP : Subgroup G := (Subgroup.center ↥(P : Subgroup G)).map (P : Subgroup G).subtype
  have hp_dvd : p ∣ Nat.card G := (Nat.mem_primeFactors.mp hp).2.1
  have hP_ne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd
  have hZP_ne : ZP ≠ ⊥ := by
    dsimp [ZP]
    intro hbot
    have hcenter_bot : Subgroup.center ↥(P : Subgroup G) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup G).subtype_injective).mp hbot
    have : Nontrivial ↥(P : Subgroup G) := (P : Subgroup G).nontrivial_iff_ne_bot.mpr hP_ne
    exact (Subgroup.center _).nontrivial_iff_ne_bot.mp P.isPGroup'.center_nontrivial hcenter_bot
  have hZP_le_center : ZP ≤ Subgroup.center G := by
    dsimp [ZP]
    exact center_sylow_le_center_of_isNilpotent P
  have hZP_pgroup : IsPGroup p ZP := by
    dsimp [ZP]
    exact (P.isPGroup'.to_subgroup (Subgroup.center ↥(P : Subgroup G))).map
      (P : Subgroup G).subtype
  have hp_dvd_ZP : p ∣ Nat.card ↥ZP := by
    obtain ⟨n, hn⟩ := hZP_pgroup.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hZP_ne
      apply Subgroup.card_eq_one.mp
      rw [hn, hn0, pow_zero]
    rw [hn]
    exact dvd_pow_self p hn0
  exact Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd_ZP.trans
    (Subgroup.card_dvd_of_le hZP_le_center), Nat.card_pos.ne'⟩

/-- **Isaacs Cor 1.28(b)** (Fitting subgroup の最大性).
任意の正規冪零部分群 `N` は `fitting G` に含まれる.

証明骨子: `N` が冪零 ⇒ `N` の各 Sylow `Q` は `N` で正規 (Thm 1.26) ⇒ `Q` は `N` で
特性的 (`Sylow.characteristic_of_normal`) ⇒ `N ◁ G` で `Q.map N.subtype ◁ G` (Lemma 1.10).
これが `p`-部分群なので Problem 1B.2 で `Q.map N.subtype ≤ opCore p G ≤ fitting G`.
`N` 全体が unique Sylow 達の sup に等しい (`iSup_default_sylow_eq_top_of_nilpotent`) ことから
`N ≤ fitting G`. -/
theorem nilpotent_normal_le_fitting [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsNilpotent N] : N ≤ fitting G := by
  -- N 全体 (= ⊤ within Subgroup N, mapped through N.subtype = N) ≤ fitting G
  have hsup : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hsup, ← iSup_default_sylow_eq_top_of_nilpotent N, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hp' : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- default : Sylow p N is normal in N
  have hPN : (default : Sylow p N).Normal := Sylow.normal_of_isNilpotent _
  -- default Sylow is characteristic in N (unique Sylow ⇒ characteristic)
  have : ((default : Sylow p N) : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal _ hPN
  -- so its image in G is normal (mathlib instance: characteristic in normal ⇒ normal)
  have : (((default : Sylow p N) : Subgroup N).map N.subtype).Normal :=
    inferInstance
  -- it's a p-subgroup of G
  have hpGroup : IsPGroup p (((default : Sylow p N) : Subgroup N).map N.subtype) :=
    (default : Sylow p N).2.map N.subtype
  -- Problem 1B.2 + opCore ≤ fitting
  calc ((default : Sylow p N) : Subgroup N).map N.subtype
      ≤ opCore p G := normal_pgroup_le_opCore hpGroup
    _ ≤ fitting G := opCore_le_fitting ⟨p, hp'.out⟩ G

/-- A nontrivial finite solvable group has nontrivial Fitting subgroup.

Take the last nontrivial derived-series term. It is abelian, hence nilpotent, and normal;
therefore it lies in the Fitting subgroup by maximality. -/
theorem fitting_ne_bot_of_isSolvable_nontrivial
    (M : Type*) [Group M] [Finite M] [Nontrivial M] [Group.IsSolvable M] :
    fitting M ≠ ⊥ := by
  classical
  obtain ⟨N, hN⟩ := (Group.isSolvable_def M).mp inferInstance
  have hex : ∃ n, derivedSeries M n = ⊥ := ⟨N, hN⟩
  set n := Nat.find hex with hn_def
  have hn_bot : derivedSeries M n = ⊥ := Nat.find_spec hex
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      have : derivedSeries M 0 = ⊥ := h0 ▸ hn_bot
      rw [derivedSeries_zero] at this
      exact (bot_ne_top (α := Subgroup M)) this.symm
    · exact hpos
  set m := n - 1 with hm_def
  have hm_succ : m + 1 = n := by omega
  set L := derivedSeries M m with hL_def
  have hL_ne_bot : L ≠ ⊥ := by
    rw [hL_def]
    exact Nat.find_min hex (by omega)
  have hLL_bot : ⁅L, L⁆ = ⊥ := by
    rw [hL_def, ← derivedSeries_succ, hm_succ, hn_bot]
  have hL_comm : IsMulCommutative L := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hLL_bot
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha_cent : (a : M) ∈ Subgroup.centralizer (L : Set M) := hLL_bot a.property
    rw [Subgroup.mem_centralizer_iff] at ha_cent
    apply Subtype.ext
    exact (ha_cent b.val b.property).symm
  have hL_normal : L.Normal := by
    rw [hL_def]
    exact derivedSeries_normal M m
  have hL_nilp : Group.IsNilpotent ↥L := inferInstance
  have hL_le_fitting : L ≤ fitting M := nilpotent_normal_le_fitting
  intro hF_bot
  rw [hF_bot, le_bot_iff] at hL_le_fitting
  exact hL_ne_bot hL_le_fitting

/-- 有限 `G` で `p ∤ |G|` (より一般に `p` が `|G|` の素因子でない) なら, 任意の
Sylow `p`-部分群は自明 `⊥`, 従って `opCore p G = ⊥`.

`Sylow.card_eq_multiplicity` で各 Sylow の濃度は `p ^ v_p(|G|)`. `p ∉ pf(|G|)` なら
`v_p(|G|) = 0` で濃度 1, ゆえ `⊥`. -/
theorem opCore_eq_bot_of_not_mem_primeFactors [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∉ (Nat.card G).primeFactors) :
    opCore p G = ⊥ := by
  -- Pick any Sylow P; it's ⊥ since its card is p^0 = 1.
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hcard : Nat.card (P : Subgroup G) = 1 := by
    rw [Sylow.card_eq_multiplicity P]
    have hfact : (Nat.card G).factorization p = 0 := by
      by_cases hdvd : p ∣ Nat.card G
      · -- p divides but is not in primeFactors → contradiction since Nat.card G ≠ 0
        exfalso
        exact hp (Nat.mem_primeFactors.mpr
          ⟨(Fact.out : p.Prime), hdvd, Nat.card_pos.ne'⟩)
      · exact Nat.factorization_eq_zero_of_not_dvd hdvd
    rw [hfact, pow_zero]
  have hPbot : (P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact le_bot_iff.mp (le_of_le_of_eq (opCore_le P) hPbot)

/-- 有限 `G` について `fitting G` は `|G|` の素因子だけに渡る `opCore` の sup と等しい.
非素因子 `p` に対しては `opCore p G = ⊥` で寄与しないため. -/
theorem fitting_eq_iSup_primeFactors [Finite G] :
    fitting G = ⨆ p : (Nat.card G).primeFactors, opCore (p : ℕ) G := by
  apply le_antisymm
  · -- fitting = ⨆ p : Primes ≤ ⨆ p : pf
    refine iSup_le (fun p => ?_)
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    by_cases hmem : (p : ℕ) ∈ (Nat.card G).primeFactors
    · -- p is in primeFactors, contribute via the indexed sup
      exact le_iSup (fun q : (Nat.card G).primeFactors => opCore (q : ℕ) G) ⟨p, hmem⟩
    · -- p not in primeFactors: opCore p G = ⊥
      rw [opCore_eq_bot_of_not_mem_primeFactors hmem]
      exact bot_le
  · -- ⨆ p : pf ≤ ⨆ p : Primes (= fitting)
    refine iSup_le (fun p => ?_)
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    exact opCore_le_fitting ⟨(p : ℕ), hp⟩ G

/-- **Isaacs Cor 1.28(a)** (Fitting subgroup の冪零性).
有限群 `G` について `fitting G` は冪零.

証明骨子: `(Nat.card G).primeFactors` 上の積 `∀ p, opCore p G` から `G` への
`noncommPiCoprod` を考える. (i) 異なる素数 `p ≠ q` で `opCore p G, opCore q G` は
互いに素な p-群 (`IsPGroup.disjoint_of_ne`) ゆえ可換 (`commute_of_normal_of_disjoint`,
両者は正規), (ii) `independent_of_coprime_order` で `iSupIndep`, よって
`noncommPiCoprod` は単射 (`injective_noncommPiCoprod_of_iSupIndep`).
range は `⨆ p, opCore p G = fitting G` (`fitting_eq_iSup_primeFactors`).
従って `(∀ p, opCore p G) ≃* fitting G` (`MulEquiv.ofInjective` + `subgroupCongr`).
各 `opCore p G` は有限 p-群ゆえ冪零 (`IsPGroup.isNilpotent`), 有限積も冪零
(`Group.isNilpotent_pi`), `MulEquiv` で `fitting G` も冪零.

`instance` 指定で `[Group.IsNilpotent (fitting G)]` が下流で自動推論される. -/
instance fitting.isNilpotent [Finite G] : Group.IsNilpotent (fitting G) := by
  classical
  have _ := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors with hps
  -- For each p ∈ pf, opCore p G is a p-group and normal in G
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : G, x ∈ opCore (p₁ : ℕ) G → y ∈ opCore (p₂ : ℕ) G → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    have hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (opCore.normal p₁ G)
      (opCore.normal p₂ G)
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  set f := Subgroup.noncommPiCoprod (G := G)
    (H := fun p : ps => opCore (p : ℕ) G) hcomm with hf
  -- f is injective by iSupIndep (coprime orders)
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    have hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  -- range f = ⨆ p, opCore p G = fitting G
  have hrange : f.range = fitting G := by
    rw [hf, Subgroup.noncommPiCoprod_range, ← fitting_eq_iSup_primeFactors]
  -- Build MulEquiv (∀ p, opCore p G) ≃* fitting G
  let e : (∀ p : ps, opCore (p : ℕ) G) ≃* fitting G :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  -- Each opCore p G (as a group) is finite + p-group ⇒ nilpotent
  have hnilp : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := by
    rintro ⟨p, hp⟩
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact (opCore_isPGroup p G).isNilpotent
  -- Finite product of nilpotent is nilpotent
  have : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := hnilp
  have : Group.IsNilpotent (∀ p : ps, opCore (p : ℕ) G) := Group.isNilpotent_pi
  -- Transport across the MulEquiv
  exact Group.nilpotent_of_mulEquiv e

/-- **Isaacs Cor 1.29** (冪零正規部分群の積も冪零).
`K, L` が `G` の正規冪零部分群ならば `K ⊔ L` (= `KL`) も冪零.

証明: Cor 1.28(b) で `K, L ≤ fitting G` ⇒ `K ⊔ L ≤ fitting G`.
`(K ⊔ L).subgroupOf (fitting G)` は冪零 (Cor 1.28(a) + `Subgroup.isNilpotent` instance),
`subgroupOfEquivOfLe` の同型で `K ⊔ L` も冪零. -/
instance sup_isNilpotent_of_normal_nilpotent [Finite G]
    (K L : Subgroup G) [K.Normal] [L.Normal]
    [Group.IsNilpotent K] [Group.IsNilpotent L] :
    Group.IsNilpotent (↥(K ⊔ L)) := by
  have hKLfit : K ⊔ L ≤ fitting G :=
    sup_le nilpotent_normal_le_fitting nilpotent_normal_le_fitting
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKLfit)

/-- **Isaacs Lucchini 2.20 prereq**: `M ⊴ G` ⇒ `F(M) ⊆ F(G)` (`F(M)` を `M.subtype`
で `G` 部分群として見て).

形式的には `(fitting ↥M).map M.subtype ≤ fitting G`. Lucchini Thm 2.20 (K=⊥ case)
の M non-abelian 場面で利用.

**証明**: `fitting ↥M` は `↥M` で characteristic (`fitting.characteristic`).
`M ⊴ G` ゆえ mathlib `Subgroup.normal_of_characteristic_of_normal` instance で
`(fitting ↥M).map M.subtype ⊴ G`. `fitting ↥M` は冪零 (`fitting.isNilpotent`),
`equivMapOfInjective` + `Group.nilpotent_of_mulEquiv` で image も冪零.
`nilpotent_normal_le_fitting` を適用して結論. -/
theorem fitting_map_subtype_le_fitting [Finite G] {M : Subgroup G} [M.Normal] :
    (fitting ↥M).map M.subtype ≤ fitting G := by
  have : Finite ↥M := inferInstance
  have : Group.IsNilpotent ↥(fitting (↥M : Type _)) := fitting.isNilpotent
  have hNilp : Group.IsNilpotent ↥((fitting ↥M).map M.subtype) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (fitting ↥M) M.subtype
      M.subtype_injective)
  exact nilpotent_normal_le_fitting

end

end OddOrder.Isaacs.Ch01


