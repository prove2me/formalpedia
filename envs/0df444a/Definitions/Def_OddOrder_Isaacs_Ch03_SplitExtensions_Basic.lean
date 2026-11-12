-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Basic
-- name    : OddOrder_Isaacs_Ch03_SplitExtensions_Basic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:57:31.050968+00:00
-- url     : https://prove2.me/theorems/34f584c5-88bf-4411-ab99-8296e4fc0b3f
-- title:
--   Isaacs Ch. 3: Hall subgroups and minimal normal subgroups of solvable groups
-- statement:
--   The basic part of the Chapter 3 (Split Extensions) formalization of Isaacs, *Finite Group Theory*. It contains the first half of Thm 3.11 (p. 80): a solvable minimal normal subgroup is abelian, and the definition of Hall subgroups.
--
--   Main definitions: `IsHallSubgroup` ($\pi$-Hall subgroups: the prime divisors of $|H|$ lie in $\pi$ and $|G:H|$ is coprime to $\pi$), `HallSubgroups` (the type of $\pi$-Hall subgroups), and the actions of ambient automorphisms (`mulAutAction`) and of $G$ by conjugation (`conjAction`) on it.
--
--   The bundle also proves 20 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch03_SplitExtensions/Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_SplitExtensionUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_SemidirectAut
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh02
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable

namespace OddOrder.Isaacs.Ch03

open SemidirectProduct

open scoped Pointwise

section

variable {G : Type*} [Group G]

open scoped commutatorElement in
/-- **Isaacs Thm 3.11 の前半** (書籍 p. 80): `M` が可解な minimal normal subgroup なら abelian.

⚠ 環境 `G` の可解性も有限性も**不要** — 書籍どおり `M` の可解性のみを仮定する
(書籍の infinite clause もこの形で入る). 環境が可解な場合は
mathlib の instance (部分群への可解性の遺伝) が `Group.IsSolvable ↥M` を供給するので,
`[Group.IsSolvable G]` 側の呼び出しはそのまま通る.

証明: `M ≠ ⊥` (minimal normal) と `M` 可解で `⁅M, M⁆ < M`
(`Ch04.commutator_lt_self_of_isSolvable_subtype`). `⁅M, M⁆ ⊴ G` (commutator of normals).
M の minimality で `⁅M, M⁆ = ⊥`, よって M abelian. -/
theorem minimal_normal_isAbelian_of_isSolvable {G : Type*} [Group G]
    {M : Subgroup G} [Group.IsSolvable ↥M] (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
  have hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  -- ⁅M, M⁆ < M (M solvable, M ≠ ⊥).
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hcomm_lt : ⁅M, M⁆ < M :=
    OddOrder.Isaacs.Ch04.commutator_lt_self_of_isSolvable_subtype M
  -- ⁅M, M⁆ ⊴ G (commutator of normals: mathlib auto-instance).
  have hCommNormal : (⁅M, M⁆ : Subgroup G).Normal := inferInstance
  -- By minimality of M, ⁅M, M⁆ = ⊥ or = M. Strict < rules out =.
  have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
    rcases hM.2.2 ⁅M, M⁆ hCommNormal hcomm_lt.le with h | h
    · exact h
    · exact absurd h hcomm_lt.ne
  -- M abelian: ⁅x, y⁆ ∈ ⁅M, M⁆ = ⊥ ⇒ x * y = y * x.
  intro x hx y hy
  have hcomm_xy : ⁅x, y⁆ ∈ ⁅M, M⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm_eq_bot, Subgroup.mem_bot] at hcomm_xy
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm_xy

/-- **Isaacs Thm 3.11** (書籍 p. 80): **可解な** minimal normal subgroup `M` は
ある素数 `p` について elementary abelian p-group.

⚠ **仮定は書籍と同一** — 環境 `G` には可解性も有限性も課さない. 書籍が
「`M` が**有限なら** elementary abelian」と述べるとおり, 有限性は **`M` にのみ**要る
(`[Finite ↥M]`; `G` は無限でよい). 書籍の infinite clause = abelian までは
`minimal_normal_isAbelian_of_isSolvable` が有限性なしで与える.
環境が可解な場合は mathlib の instance (部分群への可解性の遺伝) が
`Group.IsSolvable ↥M` を供給し, `[Finite G]` からは `Finite ↥M` が instance 解決で出るので,
`[Finite G] [Group.IsSolvable G]` 側の呼び出しはそのまま通る.

証明: M abelian (前補題). `p ∣ |M|` を取り, `T = {x ∈ M | x^p = 1}` を M の部分群とする
(M abelian で閉性 OK). T は M で characteristic (自己同型は p-冪を保つ).
Cauchy で T ≠ ⊥. T.map M.subtype は characteristic-in-normal で G 正規 + ≤ M.
M minimality で T.map M.subtype ∈ {⊥, M}. T ≠ ⊥ より T.map M.subtype = M, よって T = ⊤,
即ち全 x ∈ M で x^p = 1. -/
theorem minimal_normal_isElementaryAbelian_of_isSolvable
    {M : Subgroup G} [Finite ↥M] [Group.IsSolvable ↥M]
    (hM : OddOrder.Isaacs.Ch02.IsMinimalNormal M) :
    ∃ p : ℕ, p.Prime ∧ M.IsElementaryAbelian p := by
  have hMnormal : M.Normal := hM.1
  have hM_ne_bot : M ≠ ⊥ := hM.2.1
  have habel := minimal_normal_isAbelian_of_isSolvable hM
  have hMcomm : IsMulCommutative ↥M :=
    ⟨⟨fun a b => Subtype.ext (habel a a.2 b b.2)⟩⟩
  have hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
  have hM_card_pos : 1 < Nat.card ↥M := Finite.one_lt_card
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd hM_card_pos.ne'
  refine ⟨p, hp_prime, ?_⟩
  have hpFact : Fact p.Prime := ⟨hp_prime⟩
  -- T = {x : ↥M | x^p = 1} as a Subgroup of ↥M.
  let T : Subgroup ↥M :=
    { carrier := {x | x ^ p = 1}
      one_mem' := one_pow p
      mul_mem' := by
        intro a b ha hb
        change (a * b) ^ p = 1
        change a ^ p = 1 at ha
        change b ^ p = 1 at hb
        -- rc2: `mul_pow` needs `CommMonoid ↥M`; derive `Commute a b` from `habel`.
        have hcomm : Commute a b := Subtype.ext (habel a a.2 b b.2)
        rw [hcomm.mul_pow, ha, hb, one_mul]
      inv_mem' := by
        intro a ha
        change a⁻¹ ^ p = 1
        change a ^ p = 1 at ha
        rw [inv_pow, ha, inv_one] }
  -- T characteristic in ↥M.
  have hT_char : T.Characteristic := by
    rw [Subgroup.characteristic_iff_le_comap]
    intro φ x hx
    rw [Subgroup.mem_comap]
    change (φ x) ^ p = 1
    change x ^ p = 1 at hx
    rw [← map_pow, hx, map_one]
  -- T ≠ ⊥ via Cauchy.
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) p hp_dvd
  have hx_pow : x ^ p = 1 := by
    rw [← hx_ord]; exact pow_orderOf_eq_one x
  have hx_ne_one : x ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at hx_ord
    exact hp_prime.ne_one hx_ord.symm
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hx_T : x ∈ T := hx_pow
    rw [hbot, Subgroup.mem_bot] at hx_T
    exact hx_ne_one hx_T
  -- T.map M.subtype ⊴ G (characteristic-in-normal).
  have hTM_normal : (T.map M.subtype).Normal := inferInstance
  have hTM_le_M : T.map M.subtype ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  -- Minimality.
  rcases hM.2.2 (T.map M.subtype) hTM_normal hTM_le_M with hTM_bot | hTM_eq
  · exfalso
    have hT_eq_bot : T = ⊥ := by
      have : T.map M.subtype = (⊥ : Subgroup ↥M).map M.subtype := by
        rw [hTM_bot, Subgroup.map_bot]
      exact Subgroup.map_injective M.subtype_injective this
    exact hT_ne_bot hT_eq_bot
  · refine ⟨fun a b => Subtype.ext (habel a a.2 b b.2), fun y => ?_⟩
    have hy_TM : (y : G) ∈ T.map M.subtype := by
      rw [hTM_eq]; exact y.2
    obtain ⟨z, hz_T, hz_eq⟩ := hy_TM
    have hzy : z = y := Subtype.ext hz_eq
    exact hzy ▸ hz_T

end

section

variable {G : Type*} [Group G]

/-- **`π`-Hall 部分群** (Isaacs Def): 有限群 `G` の部分群 `H` で,
`|H|` の素因子が全て `π` に含まれ, `|G:H|` の素因子が `π` を避ける.

同値な条件: `Nat.Coprime (Nat.card H) H.index` (Hall property = 位数と指数 coprime).
mathlib 未収載の新規定義. -/
def IsHallSubgroup (π : Set ℕ) (H : Subgroup G) : Prop :=
  (∀ p ∈ (Nat.card H).primeFactors, p ∈ π) ∧
  (∀ p ∈ H.index.primeFactors, p ∉ π)

/-- π-Hall H ⇒ H's order has only π-prime factors (definition の片半分 = π-group 性質). -/
theorem IsHallSubgroup.primeFactors_card_subset {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : ∀ p ∈ (Nat.card H).primeFactors, p ∈ π := h.1

/-- π-Hall H ⇒ H.index is a π'-number (no π-prime divides it). -/
theorem IsHallSubgroup.index_no_pi {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : ∀ p ∈ H.index.primeFactors, p ∉ π := h.2

/-- `IsHallSubgroup` is order-determined: equal cardinality transfers the Hall property
(`H.index` is `|ambient| / |H|`, so equal `|H|` gives equal index, and both Hall conditions are
prime-factor conditions on `|H|` and `H.index`). -/
theorem isHallSubgroup_of_card_eq [Finite G] {π : Set ℕ} {A B : Subgroup G}
    (hB : IsHallSubgroup π B) (hc : Nat.card A = Nat.card B) :
    IsHallSubgroup π A := by
  have hidx : A.index = B.index := by
    have key : Nat.card A * A.index = Nat.card B * B.index := by
      rw [Subgroup.card_mul_index, Subgroup.card_mul_index]
    rw [hc] at key
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key
  exact ⟨fun p hp => hB.1 p (hc ▸ hp), fun p hp => hB.2 p (hidx ▸ hp)⟩

/-- π-Hall ⇒ Coprime `|H|` `|G:H|`. 標準的: 共通素因子は π と π' 両方に属し矛盾. -/
theorem IsHallSubgroup.coprime_index [Finite G] {π : Set ℕ} {H : Subgroup G}
    (h : IsHallSubgroup π H) : Nat.Coprime (Nat.card H) H.index := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
  rw [Nat.dvd_gcd_iff] at hp_dvd
  have hH_pos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hI_pos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hp_H_pf : p ∈ (Nat.card H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.1, hH_pos⟩
  have hp_idx_pf : p ∈ H.index.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.2, hI_pos⟩
  exact h.2 p hp_idx_pf (h.1 p hp_H_pf)

/-- The image of a π-Hall subgroup in a quotient is again π-Hall. -/
theorem IsHallSubgroup.map_quotient [Finite G] {π : Set ℕ} {N : Subgroup G}
    [N.Normal] {H : Subgroup G} (hH : IsHallSubgroup π H) :
    IsHallSubgroup π (H.map (QuotientGroup.mk' N)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    apply hH.1
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hp.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
  · intro p hp
    apply hH.2
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1,
      hp.2.1.trans (H.index_map_dvd (QuotientGroup.mk'_surjective N)),
      Subgroup.index_ne_zero_of_finite⟩

/-- A `π`-Hall subgroup stays `π`-Hall under any automorphism of the ambient group. -/
theorem IsHallSubgroup.mulAut_smul [Finite G] {π : Set ℕ} {H : Subgroup G}
    (hH : IsHallSubgroup π H) (φ : MulAut G) : IsHallSubgroup π (φ • H) := by
  rw [show (φ • H : Subgroup G) = H.map (φ : G →* G) by
    rw [Subgroup.pointwise_smul_def]
    rfl]
  refine ⟨?_, ?_⟩
  · have hcard : Nat.card ↥(H.map (φ : G →* G)) = Nat.card ↥H :=
      (Nat.card_congr (Subgroup.equivMapOfInjective H _ φ.injective).toEquiv).symm
    rw [hcard]
    exact hH.1
  · have hidx : (H.map (φ : G →* G)).index = H.index :=
      Subgroup.index_map_equiv H φ
    rw [hidx]
    exact hH.2

/-- The type of `π`-Hall subgroups of `G`. -/
abbrev HallSubgroups (π : Set ℕ) (G : Type*) [Group G] :=
  {H : Subgroup G // IsHallSubgroup π H}

/-- Ambient automorphisms act on the type of `π`-Hall subgroups. -/
instance HallSubgroups.mulAutAction [Finite G] (π : Set ℕ) :
    MulAction (MulAut G) (HallSubgroups π G) where
  smul φ H := ⟨φ • H.1, H.2.mulAut_smul φ⟩
  one_smul H := by
    apply Subtype.ext
    change (1 : MulAut G) • H.1 = H.1
    simp
  mul_smul φ ψ H := by
    apply Subtype.ext
    change (φ * ψ) • H.1 = φ • (ψ • H.1)
    simp [mul_smul]

/-- The conjugation action of `G` on its `π`-Hall subgroups. -/
instance HallSubgroups.conjAction [Finite G] (π : Set ℕ) :
    MulAction G (HallSubgroups π G) :=
  MulAction.compHom (HallSubgroups π G) (MulAut.conj : G →* MulAut G)

/-- `⊤` は π-Hall ⇔ `G` が π-group (`|G|` の全素因子が π に属す). -/
theorem IsHallSubgroup.top_iff (π : Set ℕ) :
    IsHallSubgroup π (⊤ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∈ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_top, Subgroup.card_top, Nat.primeFactors_one]
  simp

/-- `⊥` は π-Hall ⇔ `G` が π'-group (`|G|` の素因子が π を避ける). -/
theorem IsHallSubgroup.bot_iff (π : Set ℕ) :
    IsHallSubgroup π (⊥ : Subgroup G) ↔ ∀ p ∈ (Nat.card G).primeFactors, p ∉ π := by
  unfold IsHallSubgroup
  rw [Subgroup.index_bot, Subgroup.card_bot, Nat.primeFactors_one]
  simp

/-- `|G| = 1` ⇒ `⊥` は任意の π について π-Hall. -/
theorem IsHallSubgroup.bot_of_card_eq_one (π : Set ℕ) (h : Nat.card G = 1) :
    IsHallSubgroup π (⊥ : Subgroup G) := by
  rw [IsHallSubgroup.bot_iff]
  intro p hp
  rw [h, Nat.primeFactors_one] at hp
  exact absurd hp (Finset.notMem_empty p)

/-- **Isaacs Thm 3.13 Hall-E** の `|G|`-強誘導補助補題.

`n` パラメータは `Nat.card G ≤ n` を表し, induction by `n` で strong induction の
形を取れる. base case (`Nat.card G = 1`) は完全に閉じる. step case (~200 LOC):
1. M minimal normal 取り (G nontrivial で existence).
2. Thm 3.11 で M elementary abelian p-group.
3. `IH (G ⧸ M) (|G/M| ≤ n から |G/M| = |G|/|M| < |G|)` で `H̄` π-Hall in G/M を得る.
4. pullback `H = comap (mk' M) H̄`.
5. p ∈ π case: H は π-Hall (|H| = |H̄|·|M|, |M| は p-power, |G:H| = |G/M : H̄|).
6. p ∉ π case: H の subgroup M ⊴ H で `Coprime (Nat.card M) M.index` (in H).
   Schur-Zassenhaus で `H = M ⋊ K`. K が π-Hall in G.

**実装状態** ⭐ sorry-free (2026-05-23 完成). AxiomsCheck flagship 入り
(`OddOrder.Isaacs.Ch03.hall_E_exists`). -/
private theorem hall_E_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G ≤ n → ∀ (π : Set ℕ),
      ∃ H : Subgroup G, IsHallSubgroup π H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall π
    · by_cases hG_one : Nat.card G = 1
      · exact ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one⟩
      · -- |G| > 1. G nontrivial.
        have hG_nontrivial : Nontrivial G :=
          Finite.one_lt_card_iff_nontrivial.mp
            (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
        -- Get minimal normal M ≤ ⊤.
        obtain ⟨M, hM, _⟩ :=
          OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
        have hMnormal : M.Normal := hM.1
        have hM_ne_bot : M ≠ ⊥ := hM.2.1
        -- M elementary abelian p-group via Thm 3.11.
        obtain ⟨_p, _hp_prime, _hp_elem⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hM
        -- |M| ≥ 2 since M is nontrivial.
        have hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
        have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
        -- |G/M| · |M| = |G|. So |G/M| ≤ |G|/2 ≤ n (since |G| ≤ n+1).
        have hquot_card : Nat.card (G ⧸ M) ≤ n := by
          have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup M
          have hQ_pos : 0 < Nat.card (G ⧸ M) := Nat.card_pos
          -- |G/M| * 2 ≤ |G/M| * |M| = |G| ≤ n+1.
          have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
            rw [key]
            exact Nat.mul_le_mul_left _ hM_card_ge_two
          omega
        have hQuot_sol : Group.IsSolvable (G ⧸ M) := inferInstance
        -- IH on G/M.
        obtain ⟨Hbar, hHbar⟩ := ih (G ⧸ M) hquot_card π
        -- Pull back: H = comap (mk' M) Hbar.
        set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
        -- Key cardinality facts.
        have hH_index : H.index = Hbar.index :=
          Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
        have hHbar_idx_pos : 0 < Hbar.index := Nat.pos_of_ne_zero
          (Subgroup.index_ne_zero_of_finite)
        -- |H| = |Hbar| * |M|.
        have hH_card_eq : Nat.card H = Nat.card Hbar * Nat.card ↥M := by
          have eq1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
          have eq2 : Nat.card Hbar * Hbar.index = Nat.card (G ⧸ M) :=
            Subgroup.card_mul_index Hbar
          have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
            (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
          have h_eq : Nat.card H * Hbar.index = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by
            calc Nat.card H * Hbar.index
                = Nat.card H * H.index := by rw [hH_index]
              _ = Nat.card G := eq1
              _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
              _ = (Nat.card Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
              _ = (Nat.card Hbar * Nat.card ↥M) * Hbar.index := by ring
          exact Nat.mul_right_cancel hHbar_idx_pos h_eq
        -- |M| is a p-power (M is elementary abelian p-group ⇒ IsPGroup).
        have hM_pPower : ∃ k, Nat.card ↥M = _p ^ k := by
          have : Fact _p.Prime := ⟨_hp_prime⟩
          have hPG : IsPGroup _p ↥M := fun x => ⟨1, by
            rw [pow_one]
            exact _hp_elem.2 x⟩
          exact IsPGroup.iff_card.mp hPG
        -- Primes of |M| ⊆ {p}.
        have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = _p := by
          obtain ⟨k, hk⟩ := hM_pPower
          intro q hq
          rw [hk] at hq
          rw [Nat.mem_primeFactors] at hq
          obtain ⟨hq_prime, hq_dvd, _⟩ := hq
          exact (Nat.prime_dvd_prime_iff_eq hq_prime _hp_prime).mp
            (hq_prime.dvd_of_dvd_pow hq_dvd)
        by_cases hp_pi : _p ∈ π
        · -- Case 1: p ∈ π. H is π-Hall.
          refine ⟨H, ?_, ?_⟩
          · -- Primes of |H| ⊆ π.
            intro q hq_pf
            rw [hH_card_eq] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, hq_ne0⟩ := hq_pf
            -- q divides |Hbar| * |M|, so q divides |Hbar| or q divides |M|.
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
            · -- q ∈ primeFactors(|Hbar|) ⊆ π.
              refine hHbar.1 q ?_
              exact Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩
            · -- q ∈ primeFactors(|M|) ⊆ {p} ⊆ π.
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              rw [hM_primes q hq_in_M_pf]
              exact hp_pi
          · -- Primes of H.index ⊆ π'.
            rw [hH_index]
            exact hHbar.2
        · -- Case 2: p ∉ π. Apply Schur-Zassenhaus to M.subgroupOf H ≤ H.
          have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
          have h_card_MH : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
          -- Coprime |M| |Hbar|.
          have h_disjoint : Disjoint (Nat.card ↥M).primeFactors (Nat.card Hbar).primeFactors := by
            rw [Finset.disjoint_left]
            intro q hq_M hq_Hbar
            exact hp_pi (hM_primes q hq_M ▸ hHbar.1 q hq_Hbar)
          have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card Hbar) :=
            (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').mp h_disjoint
          -- (M.subgroupOf H).index = |Hbar|.
          have h_idx_MH : (M.subgroupOf H).index = Nat.card Hbar := by
            have hMH_lag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
              Subgroup.card_mul_index (M.subgroupOf H)
            rw [h_card_MH, hH_card_eq] at hMH_lag
            -- Nat.card ↥M * (M.subgroupOf H).index = Nat.card Hbar * Nat.card ↥M
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card Hbar := by
              rw [hMH_lag, mul_comm (Nat.card Hbar)]
            exact Nat.mul_left_cancel hM_pos this
          -- Schur-Zassenhaus.
          have h_coprime_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
            rw [h_card_MH, h_idx_MH]; exact h_coprime_M_Hbar
          have : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
          obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_coprime_MH
          -- K.index in H = |M.subgroupOf H|, |K| = |Hbar|.
          have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
          have hK_card : Nat.card ↥K = Nat.card Hbar := by
            have := hK.card_mul_card
            -- this : Nat.card (M.subgroupOf H) * Nat.card K = Nat.card H
            rw [h_card_MH, hH_card_eq] at this
            -- |M| * |K| = |Hbar| * |M|
            have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
            have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card Hbar := by
              rw [this, mul_comm]
            exact Nat.mul_left_cancel hM_pos h_eq
          -- |K.map H.subtype| = |K| = |Hbar|.
          have hKlift_card : Nat.card ↥(K.map H.subtype) = Nat.card Hbar := by
            rw [Subgroup.card_subtype, hK_card]
          -- (K.map H.subtype).index = K.index * H.index = |M| * Hbar.index.
          have hKlift_index : (K.map H.subtype).index = Nat.card ↥M * Hbar.index := by
            rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK_index, h_card_MH,
                Subgroup.range_subtype, hH_index]
          refine ⟨K.map H.subtype, ?_, ?_⟩
          · -- Primes of |K.map H.subtype| ⊆ π.
            intro q hq_pf
            rw [hKlift_card] at hq_pf
            exact hHbar.1 q hq_pf
          · -- Primes of (K.map H.subtype).index ⊆ π'.
            intro q hq_pf hq_pi
            rw [hKlift_index] at hq_pf
            rw [Nat.mem_primeFactors] at hq_pf
            obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
            rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
            · -- q divides |M| ⇒ q = p (M is p-power).
              have hq_in_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
              have hq_eq_p : q = _p := hM_primes q hq_in_M_pf
              rw [hq_eq_p] at hq_pi
              exact hp_pi hq_pi
            · -- q divides Hbar.index ⇒ q ∉ π (from IH).
              have hq_in_HbarIdx_pf : q ∈ Hbar.index.primeFactors :=
                Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩
              exact hHbar.2 q hq_in_HbarIdx_pf hq_pi

/-- **Isaacs Thm 3.13 Hall-E** ⭐ **FT クリティカル**: `G` 可解 ⇒ 任意の `π ⊆ Primes`
について `π`-Hall 部分群が存在.

証明骨子 (Isaacs p.84): `|G|`-induction.
* Base: `|G| = 1` ⇒ `⊥ = ⊤` が π-Hall.
* Step: minimal normal `M` を取る (G ≠ ⊥). Thm 3.11 で `M` は elem abelian p-group.
  - **Case 1** `p ∈ π`: IH を `G/M` に適用 (`G/M` solvable, `|G/M| < |G|`),
    π-Hall `H/M` を得る. 引き戻した `H` が `G` の π-Hall.
  - **Case 2** `p ∉ π`: IH を `G/M` に. π-Hall `L/M`. `M` 位数と `L/M` 位数 coprime
    (`p ∉ π` で `L/M` 内に `p` 因子なし). Schur-Zassenhaus で `L = M ⋊ H`, `H` が
    `G` の π-Hall. -/
theorem hall_E_exists [Finite G] [Group.IsSolvable G] (π : Set ℕ) :
    ∃ H : Subgroup G, IsHallSubgroup π H :=
  hall_E_strong_aux (Nat.card G) G le_rfl π

/-- **Isaacs Thm 3.14 Hall-C** の `|G|`-強誘導補助補題.

`Phase 2` (2026-05-23): Phase 1 `IsComplement'.exists_conj_of_coprime` 完成で実装可能化.

証明骨格 (Isaacs FGT p.85-86):
1. base case (`Nat.card G = 1`): trivial (H = K = ⊥).
2. step case:
   - `M` minimal normal ⊆ `G`, Thm 3.11 で elementary abelian `p`-group.
   - `H̄, K̄ : Subgroup (G/M)` ともに π-Hall (cardinality 議論).
   - IH on `G/M` で `∃ ḡ, H̄.map (conj ḡ) = K̄`. Lift to `g ∈ G`.
   - `H^g ⊔ M = K ⊔ M` (= `HM`) via `mk'_comp_conj_eq` + `map_eq_map_iff`.
   - **Case `p ∈ π`**: `M ⊆ H, M ⊆ K` (cardinality + π-Hall maximality). 故に
     `HM = H^g = K`.
   - **Case `p ∉ π`**: `H^g ∩ M = ⊥, K ∩ M = ⊥` (coprime orders). 両方 `M` の
     complement in `HM`. Phase 1 `IsComplement'.exists_conj_of_coprime`
     (M solvable since abelian p-group) で `∃ m ∈ M, H^g.map (conj m) = K`. -/
private theorem hall_C_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G ≤ n → ∀ {π : Set ℕ} {H K : Subgroup G},
      IsHallSubgroup π H → IsHallSubgroup π K →
      ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _ _ _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π H K hH hK
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall hH hK
    by_cases hG_one : Nat.card G = 1
    · -- |G| = 1 ⇒ G subsingleton ⇒ H = K = ⊥. Take g = 1.
      have : Subsingleton G := Nat.card_eq_one_iff_unique.mp hG_one |>.1
      refine ⟨1, ?_⟩
      apply Subgroup.ext
      intro x
      have hx : x = 1 := Subsingleton.elim x 1
      subst hx
      simp
    -- |G| > 1: G nontrivial.
    have hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    -- Minimal normal M ⊆ G.
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    have hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    -- M elementary abelian p-group via Thm 3.11.
    obtain ⟨p, hp_prime, hp_elem⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hM
    have hp_fact : Fact p.Prime := ⟨hp_prime⟩
    have hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    -- |G/M| ≤ n.
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]
        exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    -- M is a p-group (from elementary abelian structure).
    have hM_pPower : ∃ k, Nat.card ↥M = p ^ k := by
      have hPG : IsPGroup p ↥M := fun x => ⟨1, by rw [pow_one]; exact hp_elem.2 x⟩
      exact IsPGroup.iff_card.mp hPG
    -- |M| primes ⊆ {p}.
    have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = p := by
      obtain ⟨k, hk⟩ := hM_pPower
      intro q hq
      rw [hk, Nat.mem_primeFactors] at hq
      exact (Nat.prime_dvd_prime_iff_eq hq.1 hp_prime).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    -- Step 1: H̄ := H.map (mk' M), K̄ := K.map (mk' M) are π-Hall in G/M.
    have hbar_hall : ∀ {S : Subgroup G}, IsHallSubgroup π S →
        IsHallSubgroup π (S.map (QuotientGroup.mk' M)) := by
      intro S hS
      refine ⟨?_, ?_⟩
      · -- |S̄| divides |S|, so primeFactors ⊆ π.
        intro q hq
        apply hS.1
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1, hq.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
      · -- S̄.index divides S.index, so primeFactors ⊆ π'.
        intro q hq
        apply hS.2
        rw [Nat.mem_primeFactors] at hq ⊢
        exact ⟨hq.1,
          hq.2.1.trans (S.index_map_dvd (QuotientGroup.mk'_surjective M)),
          Subgroup.index_ne_zero_of_finite⟩
    have h_Hbar_hall := hbar_hall hH
    have h_Kbar_hall := hbar_hall hK
    -- Step 2: IH on G/M.
    have : Group.IsSolvable (G ⧸ M) := inferInstance
    obtain ⟨gbar, h_gbar⟩ := ih (G ⧸ M) hquot_card h_Hbar_hall h_Kbar_hall
    -- Step 3: Lift gbar to g.
    obtain ⟨g, hg_mk⟩ : ∃ g : G, (QuotientGroup.mk g : G ⧸ M) = gbar :=
      QuotientGroup.mk_surjective gbar
    -- Step 4: H^g ⊔ M = K ⊔ M via mk'-conj intertwining.
    have h_supeq : (H.map (MulAut.conj g).toMonoidHom) ⊔ M = K ⊔ M := by
      -- (mk' M).comp (conj g) = (conj (mk g)).comp (mk' M), so:
      -- (H.map (conj g)).map (mk' M) = H.map ((conj (mk g)).comp (mk' M))
      --   = (H.map (mk' M)).map (conj (mk g)) = H̄.map (conj gbar) = K̄
      have h_intertwine : (QuotientGroup.mk' M).comp (MulAut.conj g).toMonoidHom =
          ((MulAut.conj (QuotientGroup.mk g : G ⧸ M)).toMonoidHom).comp (QuotientGroup.mk' M) := by
        ext x
        change (QuotientGroup.mk (g * x * g⁻¹) : G ⧸ M) =
             (QuotientGroup.mk g) * (QuotientGroup.mk x) * (QuotientGroup.mk g)⁻¹
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h_quot_eq : (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' M) =
          K.map (QuotientGroup.mk' M) := by
        rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map, hg_mk]
        exact h_gbar
      have h_iff := (Subgroup.map_eq_map_iff (f := QuotientGroup.mk' M)).mp h_quot_eq
      rwa [QuotientGroup.ker_mk'] at h_iff
    -- Step 5: Case split on p ∈ π.
    by_cases hp_pi : p ∈ π
    · -- Case p ∈ π. M ⊆ H, M ⊆ K. So H^g · M = H^g, K · M = K. H^g = K.
      -- π-Hall maximality: |S| ∣ |T| for any π-subgroup S and π-Hall T.
      have π_hall_max : ∀ {T : Subgroup G}, IsHallSubgroup π T →
          ∀ {S : Subgroup G}, (∀ q ∈ (Nat.card ↥S).primeFactors, q ∈ π) →
          Nat.card ↥S ∣ Nat.card ↥T := by
        intro T hT S hS_pi
        have h_S_dvd_G : Nat.card ↥S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
        have h_cop : Nat.Coprime (Nat.card ↥S) T.index := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
          rw [Nat.dvd_gcd_iff] at hq_dvd
          have hq_S_pf : q ∈ (Nat.card ↥S).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
          have hq_idx_pf : q ∈ T.index.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩
          exact hT.2 q hq_idx_pf (hS_pi q hq_S_pf)
        have h_G_eq : Nat.card G = Nat.card ↥T * T.index := (Subgroup.card_mul_index T).symm
        rw [h_G_eq] at h_S_dvd_G
        exact h_cop.dvd_of_dvd_mul_right h_S_dvd_G
      have hM_pi : ∀ q ∈ (Nat.card ↥M).primeFactors, q ∈ π := fun q hq =>
        hM_primes q hq ▸ hp_pi
      -- |S ⊔ M| primes ⊆ π when S is π-Hall.
      have hSup_pi : ∀ {S : Subgroup G}, IsHallSubgroup π S →
          ∀ q ∈ (Nat.card ↥(S ⊔ M : Subgroup G)).primeFactors, q ∈ π := by
        intro S hS q hq
        rw [Nat.mem_primeFactors] at hq
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq
        have h_card_eq : Nat.card ↥(S ⊔ M : Subgroup G) * Nat.card ↥(S ⊓ M : Subgroup G)
            = Nat.card ↥S * Nat.card ↥M := by
          have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card S M
          rwa [show (↑S * ↑M : Set G) = ↑(S ⊔ M : Subgroup G) from
            (Subgroup.mul_normal S M).symm] at h_hk
        have h_dvd_prod : q ∣ Nat.card ↥S * Nat.card ↥M := by
          rw [← h_card_eq]; exact hq_dvd.mul_right _
        rcases (Nat.Prime.dvd_mul hq_prime).mp h_dvd_prod with hS_dvd | hM_dvd
        · exact hS.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hS_dvd, Nat.card_pos.ne'⟩)
        · exact hM_pi q (Nat.mem_primeFactors.mpr ⟨hq_prime, hM_dvd, Nat.card_pos.ne'⟩)
      -- M ⊆ S for any π-Hall S (since p ∈ π).
      have hM_le_hall : ∀ {S : Subgroup G}, IsHallSubgroup π S → M ≤ S := by
        intro S hS
        have h_HM_card_dvd : Nat.card ↥(S ⊔ M : Subgroup G) ∣ Nat.card ↥S :=
          π_hall_max hS (hSup_pi hS)
        have h_S_le_SM : S ≤ S ⊔ M := le_sup_left
        have h_S_le_card : Nat.card ↥S ≤ Nat.card ↥(S ⊔ M : Subgroup G) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h_S_le_SM)
        have h_card_eq : Nat.card ↥(S ⊔ M : Subgroup G) = Nat.card ↥S :=
          Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_HM_card_dvd) h_S_le_card
        have h_SM_eq : (S ⊔ M : Subgroup G) = S :=
          (Subgroup.eq_of_le_of_card_ge h_S_le_SM h_card_eq.le).symm
        intro x hxM
        have : x ∈ (S ⊔ M : Subgroup G) := Subgroup.mem_sup_right hxM
        rwa [h_SM_eq] at this
      have hM_le_H : M ≤ H := hM_le_hall hH
      have hM_le_K : M ≤ K := hM_le_hall hK
      -- M ⊴ G + M ≤ H ⇒ M ≤ H^g.
      have hM_le_Hg : M ≤ H.map (MulAut.conj g).toMonoidHom := by
        intro x hxM
        rw [Subgroup.mem_map]
        refine ⟨g⁻¹ * x * g, ?_, by
          change g * (g⁻¹ * x * g) * g⁻¹ = x
          group⟩
        apply hM_le_H
        have := hMnormal.conj_mem x hxM g⁻¹
        simpa using this
      -- H^g · M = H^g, K · M = K. Conclude H^g = K.
      have h_HMg_eq : (H.map (MulAut.conj g).toMonoidHom) ⊔ M =
          H.map (MulAut.conj g).toMonoidHom := sup_eq_left.mpr hM_le_Hg
      have h_KM_eq : K ⊔ M = K := sup_eq_left.mpr hM_le_K
      refine ⟨g, ?_⟩
      rw [← h_HMg_eq, h_supeq, h_KM_eq]
    · -- Case p ∉ π. H ∩ M = ⊥, K ∩ M = ⊥. Apply SZ conjugacy in HM.
      -- Helper: any π-Hall S has S ⊓ M = ⊥ (coprime orders).
      have h_inter_bot : ∀ {S : Subgroup G}, IsHallSubgroup π S →
          (S ⊓ M : Subgroup G) = ⊥ := by
        intro S hS
        apply Subgroup.eq_bot_of_card_eq
        have h_dvd_S : Nat.card ↥(S ⊓ M : Subgroup G) ∣ Nat.card ↥S :=
          Subgroup.card_dvd_of_le inf_le_left
        have h_dvd_M : Nat.card ↥(S ⊓ M : Subgroup G) ∣ Nat.card ↥M :=
          Subgroup.card_dvd_of_le inf_le_right
        have h_cop : Nat.Coprime (Nat.card ↥S) (Nat.card ↥M) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
          rw [Nat.dvd_gcd_iff] at hq_dvd
          have hq_S_pf : q ∈ (Nat.card ↥S).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
          have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
          exact hp_pi (hM_primes q hq_M_pf ▸ hS.1 q hq_S_pf)
        have h := Nat.dvd_gcd h_dvd_S h_dvd_M
        rw [h_cop] at h
        exact Nat.dvd_one.mp h
      -- Hg := H^g is also π-Hall (conjugation preserves cardinality and index).
      set Hg : Subgroup G := H.map (MulAut.conj g).toMonoidHom with hHg_def
      have h_Hg_card : Nat.card ↥Hg = Nat.card ↥H :=
        Nat.card_congr (Subgroup.equivMapOfInjective H _
          (MulEquiv.injective _)).toEquiv.symm
      have h_Hg_index : Hg.index = H.index := Subgroup.index_map_equiv H (MulAut.conj g)
      have hHg_hall : IsHallSubgroup π Hg := by
        refine ⟨?_, ?_⟩
        · intro q hq
          apply hH.1
          rwa [h_Hg_card] at hq
        · intro q hq
          apply hH.2
          rwa [h_Hg_index] at hq
      have h_Hg_inter_M : (Hg ⊓ M : Subgroup G) = ⊥ := h_inter_bot hHg_hall
      have h_K_inter_M : (K ⊓ M : Subgroup G) = ⊥ := h_inter_bot hK
      -- HM := Hg ⊔ M = K ⊔ M (from h_supeq).
      set HM : Subgroup G := Hg ⊔ M with hHM_def
      have hM_le_HM : M ≤ HM := le_sup_right
      have hHg_le_HM : Hg ≤ HM := le_sup_left
      have hK_le_HM : K ≤ HM := h_supeq.symm ▸ (le_sup_left : K ≤ K ⊔ M)
      -- Setup in ↥HM: N' := M.subgroupOf HM.
      have hHM_finite : Finite ↥HM := inferInstance
      have hM_subgroupOf_normal : (M.subgroupOf HM).Normal :=
        Subgroup.normal_subgroupOf
      -- N' ≃ M (since M ≤ HM).
      have h_M_card_eq : Nat.card ↥(M.subgroupOf HM) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_HM).toEquiv
      -- Construct IsComplement' (M.subgroupOf HM) (Hg.subgroupOf HM) in ↥HM.
      have h_compl_Hg : Subgroup.IsComplement' (M.subgroupOf HM) (Hg.subgroupOf HM) := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        · -- Disjoint via M ⊓ Hg = ⊥.
          rw [disjoint_iff]
          ext ⟨x, hx⟩
          simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                     Subtype.ext_iff, OneMemClass.coe_one]
          refine ⟨fun ⟨hxM, hxHg⟩ => ?_, fun h => by simp [h]⟩
          have : x ∈ (M ⊓ Hg : Subgroup G) := ⟨hxM, hxHg⟩
          rw [show (M ⊓ Hg : Subgroup G) = ⊥ by rw [inf_comm]; exact h_Hg_inter_M,
            Subgroup.mem_bot] at this
          exact this
        · -- Product covers ↥HM: ∀ x : HM, ∃ m ∈ M, h ∈ Hg, m * h = x.
          rw [Set.eq_univ_iff_forall]
          rintro ⟨x, hx_HM⟩
          -- x ∈ HM = Hg ⊔ M. Decompose: ∃ h ∈ Hg, m ∈ M, x = h * m (Hg.normalizes M or M ⊴ G).
          have hx_sup : x ∈ (Hg ⊔ M : Subgroup G) := hx_HM
          rw [Subgroup.mem_sup_of_normal_right] at hx_sup
          obtain ⟨h, hhHg, m, hmM, h_eq⟩ := hx_sup
          -- x = h * m. Use normality to rewrite it as m' * h,
          -- with m' := h * m * h⁻¹ ∈ M.
          refine ⟨⟨h * m * h⁻¹, ?_⟩,
            Subgroup.mem_subgroupOf.mpr (hMnormal.conj_mem m hmM h), ⟨h, ?_⟩,
            Subgroup.mem_subgroupOf.mpr hhHg, ?_⟩
          · exact hM_le_HM (hMnormal.conj_mem m hmM h)
          · exact hHg_le_HM hhHg
          · ext
            change h * m * h⁻¹ * h = x
            rw [← h_eq]
            group
      -- Similarly for K.
      have h_compl_K : Subgroup.IsComplement' (M.subgroupOf HM) (K.subgroupOf HM) := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
        · rw [disjoint_iff]
          ext ⟨x, hx⟩
          simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                     Subtype.ext_iff, OneMemClass.coe_one]
          refine ⟨fun ⟨hxM, hxK⟩ => ?_, fun h => by simp [h]⟩
          have : x ∈ (M ⊓ K : Subgroup G) := ⟨hxM, hxK⟩
          rw [show (M ⊓ K : Subgroup G) = ⊥ by rw [inf_comm]; exact h_K_inter_M,
            Subgroup.mem_bot] at this
          exact this
        · rw [Set.eq_univ_iff_forall]
          rintro ⟨x, hx_HM⟩
          have hx_sup : x ∈ (K ⊔ M : Subgroup G) := by rw [← h_supeq]; exact hx_HM
          rw [Subgroup.mem_sup_of_normal_right] at hx_sup
          obtain ⟨h, hhK, m, hmM, h_eq⟩ := hx_sup
          refine ⟨⟨h * m * h⁻¹, ?_⟩,
            Subgroup.mem_subgroupOf.mpr (hMnormal.conj_mem m hmM h), ⟨h, ?_⟩,
            Subgroup.mem_subgroupOf.mpr hhK, ?_⟩
          · exact hM_le_HM (hMnormal.conj_mem m hmM h)
          · exact hK_le_HM hhK
          · ext
            change h * m * h⁻¹ * h = x
            rw [← h_eq]
            group
      -- M.subgroupOf HM has solvable structure (M abelian / p-group).
      have hM_solv : Group.IsSolvable ↥(M.subgroupOf HM) := by
        have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_HM
        exact Group.isSolvable_of_isSolvable_injective (f := h_iso.toMonoidHom) h_iso.injective
      -- Coprime: |M.subgroupOf HM| coprime its index.
      have h_HM_card : Nat.card ↥HM = Nat.card ↥Hg * Nat.card ↥M := by
        have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Hg M
        rw [show Hg ⊓ M = (⊥ : Subgroup G) from h_Hg_inter_M, Subgroup.card_bot,
            mul_one] at h_hk
        have h_set : (↑Hg * ↑M : Set G) = (↑HM : Set G) := by
          rw [← Subgroup.mul_normal, ← hHM_def]
        rw [h_set] at h_hk
        omega
      have h_M_idx_HM : (M.subgroupOf HM).index = Nat.card ↥Hg := by
        have h1 : Nat.card ↥(M.subgroupOf HM) * (M.subgroupOf HM).index = Nat.card ↥HM :=
          (M.subgroupOf HM).card_mul_index
        rw [h_M_card_eq, h_HM_card] at h1
        -- h1 : |M| · idx = |Hg| · |M|.
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h2 : Nat.card ↥M * (M.subgroupOf HM).index = Nat.card ↥M * Nat.card ↥Hg := by
          rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left hM_pos h2
      have h_cop : Nat.Coprime (Nat.card ↥(M.subgroupOf HM)) (M.subgroupOf HM).index := by
        rw [h_M_card_eq, h_M_idx_HM]
        -- gcd(|M|, |Hg|) = gcd(p-power, π-Hall) = 1.
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hq_M_pf : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hq_Hg_pf : q ∈ (Nat.card ↥Hg).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hq_M_pf ▸ hHg_hall.1 q hq_Hg_pf)
      -- Apply SZ conjugacy (Phase 1).
      obtain ⟨n_HM, hn_HM_mem, hn_eq⟩ :=
        Subgroup.IsComplement'.exists_conj_of_coprime h_cop (Or.inl hM_solv)
          h_compl_Hg h_compl_K
      -- Lift n_HM ∈ M.subgroupOf HM to m ∈ M (via HM.subtype + subgroupOf membership).
      let m : G := n_HM.val
      have hm_M : m ∈ M := Subgroup.mem_subgroupOf.mp hn_HM_mem
      -- Push hn_eq via HM.subtype: Hg.map (conj m) = K.
      have h_Hg_conj_m : Hg.map (MulAut.conj m).toMonoidHom = K := by
        have h_intertwine : HM.subtype.comp ((MulAut.conj n_HM).toMonoidHom) =
            ((MulAut.conj (n_HM.val : G)).toMonoidHom).comp HM.subtype := by
          ext ⟨x, hx⟩; rfl
        have h_lhs : (((Hg.subgroupOf HM).map (MulAut.conj n_HM).toMonoidHom).map
            HM.subtype) = Hg.map (MulAut.conj m).toMonoidHom := by
          rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map]
          congr 1
          rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
              inf_of_le_right hHg_le_HM]
        have h_rhs : ((K.subgroupOf HM).map HM.subtype) = K := by
          rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
              inf_of_le_right hK_le_HM]
        have := congrArg (·.map HM.subtype) hn_eq
        rw [h_lhs, h_rhs] at this
        exact this
      -- K = H^(m * g) via composition.
      refine ⟨m * g, ?_⟩
      have hcomp : (MulAut.conj (m * g)).toMonoidHom =
            (MulAut.conj m).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
        ext x
        change m * g * x * (m * g)⁻¹ = m * (g * x * g⁻¹) * m⁻¹
        group
      rw [hcomp, ← Subgroup.map_map]
      exact h_Hg_conj_m

/-- **Isaacs Thm 3.14 Hall-C**: `G` 可解 ⇒ 任意の `π`-Hall 部分群対は共役.

Phase 2 (2026-05-23) で完成. Phase 1 (Isaacs Thm 3.12 SZ 共役性) を前提に
`hall_C_strong_aux` 経由で `|G|`-強誘導.

主結果: `∃ g : G, H.map (MulAut.conj g).toMonoidHom = K` (即ち `H^g = K`).
共役元 `g` は一般に `G` 全体 (`N` の部分集合とは限らない). -/
theorem hall_C [Finite G] [Group.IsSolvable G] {π : Set ℕ} {H K : Subgroup G}
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) :
    ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K :=
  hall_C_strong_aux (Nat.card G) G le_rfl hH hK

/-- **Schur-Zassenhaus D-part (抽象版)**: `M ⊴ G` が補群 `K` を持ち `M` か `U` の一方が可解なとき,
`|M|` と位数が互いに素な部分群 `U` は `K` の共役 `Kˣ` (`x ∈ M`) に含まれる.

Hall D-定理 (`hall_D`) のエンジン. 証明: `P := U ⊔ M` の中で `U` も `P ⊓ K` も
正規部分群 `M.subgroupOf P` (index は `|U|`, よって `|M|` と互いに素) の補群になる.
Schur-Zassenhaus 共役性 (`IsComplement'.exists_conj_of_coprime`) を `P` 内で適用すると,
`P ⊓ K` の (`M` の元による) 共役が `U` に一致するので, `U = (P ⊓ K)ᵐ ≤ Kᵐ`. -/
theorem exists_conj_le_of_isComplement'_of_coprime' [Finite G] {M K U : Subgroup G} [M.Normal]
    (hsolv : Group.IsSolvable ↥M ∨ Group.IsSolvable ↥U) (hK : M.IsComplement' K)
    (hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥M)) :
    ∃ x ∈ M, U ≤ K.map (MulAut.conj x).toMonoidHom := by
  set P : Subgroup G := U ⊔ M with hP_def
  have hM_le_P : M ≤ P := le_sup_right
  have hU_le_P : U ≤ P := le_sup_left
  have hMnorm : M.Normal := inferInstance
  have hMP_normal : (M.subgroupOf P).Normal := Subgroup.normal_subgroupOf
  have hU_inf_M : (U ⊓ M : Subgroup G) = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hM_inf_K : (M ⊓ K : Subgroup G) = ⊥ := hK.disjoint.eq_bot
  have h_card_MP : Nat.card ↥(M.subgroupOf P) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_P).toEquiv
  have h_card_UP : Nat.card ↥(U.subgroupOf P) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_P).toEquiv
  -- Complement 1: `U.subgroupOf P` complements `M.subgroupOf P` in `P`.
  have h_compl_U : Subgroup.IsComplement' (M.subgroupOf P) (U.subgroupOf P) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                 Subtype.ext_iff, OneMemClass.coe_one]
      refine ⟨fun ⟨hxM, hxU⟩ => ?_, fun h => by simp [h]⟩
      have : x ∈ (U ⊓ M : Subgroup G) := ⟨hxU, hxM⟩
      rwa [hU_inf_M, Subgroup.mem_bot] at this
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx_P⟩
      have hx_sup : x ∈ (U ⊔ M : Subgroup G) := hx_P
      rw [Subgroup.mem_sup_of_normal_right] at hx_sup
      obtain ⟨u, huU, m, hmM, h_eq⟩ := hx_sup
      refine ⟨⟨u * m * u⁻¹, hM_le_P (hMnorm.conj_mem m hmM u)⟩,
        Subgroup.mem_subgroupOf.mpr (hMnorm.conj_mem m hmM u), ⟨u, hU_le_P huU⟩,
        Subgroup.mem_subgroupOf.mpr huU, ?_⟩
      ext; change u * m * u⁻¹ * u = x; rw [← h_eq]; group
  -- Complement 2: `K.subgroupOf P` (= `(P ⊓ K).subgroupOf P`) complements `M.subgroupOf P`.
  have h_compl_K : Subgroup.IsComplement' (M.subgroupOf P) (K.subgroupOf P) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot,
                 Subtype.ext_iff, OneMemClass.coe_one]
      refine ⟨fun ⟨hxM, hxK⟩ => ?_, fun h => by simp [h]⟩
      have : x ∈ (M ⊓ K : Subgroup G) := ⟨hxM, hxK⟩
      rwa [hM_inf_K, Subgroup.mem_bot] at this
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx_P⟩
      have hx_top : x ∈ (M ⊔ K : Subgroup G) := by rw [hK.sup_eq_top]; trivial
      rw [Subgroup.mem_sup_of_normal_left] at hx_top
      obtain ⟨m, hmM, k, hkK, h_eq⟩ := hx_top
      have hk_P : k ∈ P := by
        have hkeq : k = m⁻¹ * x := by rw [← h_eq]; group
        rw [hkeq]; exact P.mul_mem (P.inv_mem (hM_le_P hmM)) hx_P
      refine ⟨⟨m, hM_le_P hmM⟩, Subgroup.mem_subgroupOf.mpr hmM, ⟨k, hk_P⟩,
        Subgroup.mem_subgroupOf.mpr hkK, ?_⟩
      ext; exact h_eq
  -- index of `M.subgroupOf P` in `P` is `|U|`, hence coprime to `|M|`.
  have h_idx_MP : (M.subgroupOf P).index = Nat.card ↥U := by
    rw [h_compl_U.symm.index_eq_card, h_card_UP]
  have h_cop_MP : Nat.Coprime (Nat.card ↥(M.subgroupOf P)) (M.subgroupOf P).index := by
    rw [h_card_MP, h_idx_MP]; exact hcop.symm
  -- Schur-Zassenhaus 共役性が要求する「`M` 側か商側のどちらかが可解」を供給する.
  -- `M` 可解ならそのまま; `U` 可解なら商 `P / M.subgroupOf P ≃* U.subgroupOf P` が可解.
  have hsolv_P : Group.IsSolvable ↥(M.subgroupOf P) ∨ Group.IsSolvable (↥P ⧸ M.subgroupOf P) := by
    rcases hsolv with hMsolv | hUsolv
    · left
      have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_P
      exact Group.isSolvable_of_isSolvable_injective (f := h_iso.toMonoidHom) h_iso.injective
    · right
      have : Group.IsSolvable ↥(U.subgroupOf P) := by
        have h_iso := Subgroup.subgroupOfEquivOfLe hU_le_P
        exact Group.isSolvable_of_isSolvable_injective (f := h_iso.toMonoidHom) h_iso.injective
      have h_iso := h_compl_U.symm.QuotientMulEquiv
      exact Group.isSolvable_of_isSolvable_injective (f := h_iso.toMonoidHom) h_iso.injective
  -- SZ conjugacy in `P`: conjugate `K.subgroupOf P` to `U.subgroupOf P` by `n ∈ M.subgroupOf P`.
  obtain ⟨n, hn_mem, hn_eq⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime h_cop_MP hsolv_P h_compl_K h_compl_U
  let m : G := n.val
  refine ⟨m, Subgroup.mem_subgroupOf.mp hn_mem, ?_⟩
  -- Push `hn_eq` through `P.subtype`: `(P ⊓ K)ᵐ = U`, hence `U ≤ Kᵐ`.
  have h_intertwine : P.subtype.comp (MulAut.conj n).toMonoidHom =
      ((MulAut.conj (n.val : G)).toMonoidHom).comp P.subtype := by
    ext ⟨x, hx⟩; rfl
  have h_lhs : (((K.subgroupOf P).map (MulAut.conj n).toMonoidHom).map P.subtype) =
      (P ⊓ K).map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_map, h_intertwine, ← Subgroup.map_map]
    congr 1
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have h_rhs : ((U.subgroupOf P).map P.subtype) = U := by
    rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hU_le_P]
  have h_eq_lifted := congrArg (·.map P.subtype) hn_eq
  rw [h_lhs, h_rhs] at h_eq_lifted
  rw [← h_eq_lifted]
  exact Subgroup.map_mono inf_le_right

/-- **Schur-Zassenhaus D-part (`M` 可解版)**: `exists_conj_le_of_isComplement'_of_coprime'` の
`M` 可解への特殊化. Hall D-定理や BG/Peterfalvi の呼び出し側はこの形を使う. -/
theorem exists_conj_le_of_isComplement'_of_coprime [Finite G] {M K : Subgroup G} [M.Normal]
    (hMsolv : Group.IsSolvable ↥M) (hK : M.IsComplement' K) {U : Subgroup G}
    (hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥M)) :
    ∃ x : G, U ≤ K.map (MulAut.conj x).toMonoidHom :=
  let ⟨x, _, hx⟩ := exists_conj_le_of_isComplement'_of_coprime' (Or.inl hMsolv) hK hcop
  ⟨x, hx⟩

/-- Hall D-定理の `|G|`-強誘導本体. `hall_E_strong_aux` と同じ骨格 (極小正規 `M`,
`G/M` への IH, `p ∈ π` / `p ∉ π` 場合分け) に, 「IH は `U` の像を含む π-Hall を返す」
+「`p ∉ π` では補群を `U` を含むものに取り替える (`exists_conj_le_of_isComplement'_of_coprime`)」
の 2 点を加えたもの. -/
private theorem hall_D_strong_aux : ∀ n : ℕ,
    ∀ (G : Type*) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G ≤ n → ∀ {π : Set ℕ} {U : Subgroup G},
      (∀ q ∈ (Nat.card ↥U).primeFactors, q ∈ π) →
      ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hcard _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ _ hcard π U hU
    by_cases hsmall : Nat.card G ≤ n
    · exact ih G hsmall hU
    by_cases hG_one : Nat.card G = 1
    · -- |G| = 1: G subsingleton, so U ≤ ⊥; take H = ⊥.
      have : Subsingleton G := Nat.card_eq_one_iff_unique.mp hG_one |>.1
      refine ⟨⊥, IsHallSubgroup.bot_of_card_eq_one π hG_one, ?_⟩
      intro x _
      rw [Subgroup.mem_bot]; exact Subsingleton.elim x 1
    have hG_nontrivial : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.card_pos.ne', hG_one⟩)
    obtain ⟨M, hM, _⟩ :=
      OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) top_ne_bot
    have hMnormal : M.Normal := hM.1
    have hM_ne_bot : M ≠ ⊥ := hM.2.1
    obtain ⟨p, hp_prime, hp_elem⟩ := minimal_normal_isElementaryAbelian_of_isSolvable hM
    have hM_nontrivial : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot
    have hM_card_ge_two : 2 ≤ Nat.card ↥M := Finite.one_lt_card
    have hquot_card : Nat.card (G ⧸ M) ≤ n := by
      have key : Nat.card G = Nat.card (G ⧸ M) * Nat.card ↥M :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup M
      have h1 : Nat.card (G ⧸ M) * 2 ≤ Nat.card G := by
        rw [key]; exact Nat.mul_le_mul_left _ hM_card_ge_two
      omega
    -- |M| is a p-power; its prime factors are {p}.
    have hM_pPower : ∃ k, Nat.card ↥M = p ^ k := by
      have : Fact p.Prime := ⟨hp_prime⟩
      have hPG : IsPGroup p ↥M := fun x => ⟨1, by rw [pow_one]; exact hp_elem.2 x⟩
      exact IsPGroup.iff_card.mp hPG
    have hM_primes : ∀ q ∈ (Nat.card ↥M).primeFactors, q = p := by
      obtain ⟨k, hk⟩ := hM_pPower
      intro q hq
      rw [hk, Nat.mem_primeFactors] at hq
      exact (Nat.prime_dvd_prime_iff_eq hq.1 hp_prime).mp (hq.1.dvd_of_dvd_pow hq.2.1)
    -- IH on G/M with the π-subgroup `U.map (mk' M)`: get a π-Hall ⊇ image of U.
    set Ubar : Subgroup (G ⧸ M) := U.map (QuotientGroup.mk' M) with hUbar_def
    have hUbar_pi : ∀ q ∈ (Nat.card ↥Ubar).primeFactors, q ∈ π := by
      intro q hq
      apply hU
      rw [Nat.mem_primeFactors] at hq ⊢
      exact ⟨hq.1, hq.2.1.trans (Subgroup.card_map_dvd _ _), Nat.card_pos.ne'⟩
    obtain ⟨Hbar, hHbar, hUbar_le⟩ := ih (G ⧸ M) hquot_card hUbar_pi
    -- Pull back: H = comap (mk' M) Hbar contains both M and U.
    set H : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) Hbar with hH_def
    have hM_le_H : M ≤ H := QuotientGroup.le_comap_mk' M Hbar
    have hU_le_H : U ≤ H := by
      intro u hu
      rw [hH_def, Subgroup.mem_comap]
      exact hUbar_le (Subgroup.mem_map_of_mem _ hu)
    have hH_index : H.index = Hbar.index :=
      Hbar.index_comap_of_surjective (QuotientGroup.mk'_surjective (N := M))
    have hHbar_idx_pos : 0 < Hbar.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hH_card_eq : Nat.card ↥H = Nat.card ↥Hbar * Nat.card ↥M := by
      have eq1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
      have eq2 : Nat.card ↥Hbar * Hbar.index = Nat.card (G ⧸ M) := Subgroup.card_mul_index Hbar
      have eq3 : Nat.card (G ⧸ M) * Nat.card ↥M = Nat.card G :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
      have h_eq : Nat.card ↥H * Hbar.index = (Nat.card ↥Hbar * Nat.card ↥M) * Hbar.index := by
        calc Nat.card ↥H * Hbar.index
            = Nat.card ↥H * H.index := by rw [hH_index]
          _ = Nat.card G := eq1
          _ = Nat.card (G ⧸ M) * Nat.card ↥M := eq3.symm
          _ = (Nat.card ↥Hbar * Hbar.index) * Nat.card ↥M := by rw [eq2]
          _ = (Nat.card ↥Hbar * Nat.card ↥M) * Hbar.index := by ring
      exact Nat.mul_right_cancel hHbar_idx_pos h_eq
    by_cases hp_pi : p ∈ π
    · -- Case p ∈ π: H is a Hall π-subgroup of G and U ≤ H.
      refine ⟨H, ⟨?_, ?_⟩, hU_le_H⟩
      · intro q hq_pf
        rw [hH_card_eq, Nat.mem_primeFactors] at hq_pf
        obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
        rcases hq_prime.dvd_mul.mp hq_dvd with h_in_Hbar | h_in_M
        · exact hHbar.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_Hbar, Nat.card_pos.ne'⟩)
        · have hqM : q ∈ (Nat.card ↥M).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
          rw [hM_primes q hqM]; exact hp_pi
      · rw [hH_index]; exact hHbar.2
    · -- Case p ∉ π: replace a complement of `M.subgroupOf H` by one containing `U`.
      have hMH_card : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_H).toEquiv
      have h_coprime_M_Hbar : Nat.Coprime (Nat.card ↥M) (Nat.card ↥Hbar) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hqM : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hqHbar : q ∈ (Nat.card ↥Hbar).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hqM ▸ hHbar.1 q hqHbar)
      have h_idx_MH : (M.subgroupOf H).index = Nat.card ↥Hbar := by
        have hlag : Nat.card ↥(M.subgroupOf H) * (M.subgroupOf H).index = Nat.card ↥H :=
          Subgroup.card_mul_index (M.subgroupOf H)
        rw [hMH_card, hH_card_eq] at hlag
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have : Nat.card ↥M * (M.subgroupOf H).index = Nat.card ↥M * Nat.card ↥Hbar := by
          rw [hlag, mul_comm (Nat.card ↥Hbar)]
        exact Nat.mul_left_cancel hM_pos this
      have h_cop_MH : Nat.Coprime (Nat.card ↥(M.subgroupOf H)) (M.subgroupOf H).index := by
        rw [hMH_card, h_idx_MH]; exact h_coprime_M_Hbar
      have hMH_normal : (M.subgroupOf H).Normal := hMnormal.subgroupOf H
      have hMH_solv : Group.IsSolvable ↥(M.subgroupOf H) := by
        have h_iso := Subgroup.subgroupOfEquivOfLe hM_le_H
        exact Group.isSolvable_of_isSolvable_injective (f := h_iso.toMonoidHom) h_iso.injective
      obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime h_cop_MH
      -- `U.subgroupOf H` is a π-subgroup with order coprime to `|M.subgroupOf H|`.
      have hUH_card : Nat.card ↥(U.subgroupOf H) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_H).toEquiv
      have h_cop_UH_MH :
          Nat.Coprime (Nat.card ↥(U.subgroupOf H)) (Nat.card ↥(M.subgroupOf H)) := by
        rw [hUH_card, hMH_card, Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
        rw [Nat.dvd_gcd_iff] at hq_dvd
        have hqU : q ∈ (Nat.card ↥U).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.1, Nat.card_pos.ne'⟩
        have hqM : q ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd.2, Nat.card_pos.ne'⟩
        exact hp_pi (hM_primes q hqM ▸ hU q hqU)
      -- SZ-D: `U.subgroupOf H` lies in a conjugate `K' = K.map (conj x)` of `K`.
      obtain ⟨x, hx⟩ := exists_conj_le_of_isComplement'_of_coprime hMH_solv hK h_cop_UH_MH
      set K' : Subgroup ↥H := K.map (MulAut.conj x).toMonoidHom with hK'_def
      have hK'_card : Nat.card ↥K' = Nat.card ↥K :=
        Nat.card_congr (Subgroup.equivMapOfInjective K _ (MulEquiv.injective _)).toEquiv.symm
      have hK'_index : K'.index = K.index := Subgroup.index_map_equiv K (MulAut.conj x)
      have hK_index : K.index = Nat.card ↥(M.subgroupOf H) := hK.index_eq_card
      have hK_card : Nat.card ↥K = Nat.card ↥Hbar := by
        have hcm := hK.card_mul_card
        rw [hMH_card, hH_card_eq] at hcm
        have hM_pos : 0 < Nat.card ↥M := Nat.card_pos
        have h_eq : Nat.card ↥M * Nat.card ↥K = Nat.card ↥M * Nat.card ↥Hbar := by
          rw [hcm, mul_comm]
        exact Nat.mul_left_cancel hM_pos h_eq
      -- `K'.map H.subtype` is the desired Hall π-subgroup of G, and contains U.
      refine ⟨K'.map H.subtype, ⟨?_, ?_⟩, ?_⟩
      · intro q hq_pf
        rw [Subgroup.card_subtype, hK'_card, hK_card] at hq_pf
        exact hHbar.1 q hq_pf
      · intro q hq_pf hq_pi
        rw [show (K'.map H.subtype).index = Nat.card ↥M * Hbar.index from ?_] at hq_pf
        · rw [Nat.mem_primeFactors] at hq_pf
          obtain ⟨hq_prime, hq_dvd, _⟩ := hq_pf
          rcases hq_prime.dvd_mul.mp hq_dvd with h_in_M | h_in_HbarIdx
          · have hqM : q ∈ (Nat.card ↥M).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hq_prime, h_in_M, Nat.card_pos.ne'⟩
            rw [hM_primes q hqM] at hq_pi; exact hp_pi hq_pi
          · exact hHbar.2 q (Nat.mem_primeFactors.mpr
              ⟨hq_prime, h_in_HbarIdx, Subgroup.index_ne_zero_of_finite⟩) hq_pi
        · rw [Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, hK'_index, hK_index,
              hMH_card, Subgroup.range_subtype, hH_index]
      · calc U = (U.subgroupOf H).map H.subtype := by
                rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
                    inf_of_le_right hU_le_H]
          _ ≤ K'.map H.subtype := Subgroup.map_mono hx

/-- **Isaacs 3C.1 (Hall D-定理, Wielandt)** ⭐: 有限可解群では, 任意の `π`-部分群は
ある Hall `π`-部分群に含まれる.

`U` を `π`-部分群 (`|U|` の全素因子が `π` に属す) とすると, `U ≤ H` なる `π`-Hall `H` が存在.
Hall E (`hall_E_exists`) / Hall C (`hall_C`) と合わせて Hall E-C-D を完備化する.
証明は `hall_E_strong_aux` と同型の `|G|`-強誘導 (`hall_D_strong_aux`). -/
theorem hall_D [Finite G] [Group.IsSolvable G] {π : Set ℕ} {U : Subgroup G}
    (hU : ∀ q ∈ (Nat.card ↥U).primeFactors, q ∈ π) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ U ≤ H :=
  hall_D_strong_aux (Nat.card G) G le_rfl hU

/-- `N ⊴ G` のとき, 任意の `H` について `[N : H ∩ N] = H.relIndex N` は `[G : H] = H.index`
を割る. (mathlib `relIndex_dvd_index_of_normal` は正規部分群側の relindex を扱うので, その
「右版」を指数の塔等式 + 第二同型から導く.)

`[G:H]·[H:H∩N] = [G:N]·[N:H∩N]` (どちらも `[G:H∩N]`), かつ `[H:H∩N] ∣ [G:N]` (正規) より
`[N:H∩N] ∣ [G:H]`. -/
theorem relIndex_dvd_index_of_normal_right [Finite G] (H : Subgroup G) {N : Subgroup G}
    [N.Normal] : H.relIndex N ∣ H.index := by
  -- (H⊓N).relIndex H * H.index = [G:H∩N] と (H⊓N).relIndex N * N.index = [G:H∩N].
  have hA : N.relIndex H * H.index = (H ⊓ N : Subgroup G).index := by
    rw [← Subgroup.inf_relIndex_left]; exact Subgroup.relIndex_mul_index inf_le_left
  have hB : H.relIndex N * N.index = (H ⊓ N : Subgroup G).index := by
    rw [← Subgroup.inf_relIndex_right]; exact Subgroup.relIndex_mul_index inf_le_right
  -- [H:H∩N] = N.relIndex H ∣ [G:N] = N.index (正規).
  obtain ⟨t, ht⟩ : N.relIndex H ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N H
  have hb_ne : N.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hA
    exact Subgroup.index_ne_zero_of_finite hA.symm
  -- N.relIndex H * H.index = N.relIndex H * (H.relIndex N * t).
  have key : N.relIndex H * H.index = N.relIndex H * (H.relIndex N * t) := by
    rw [hA, ← hB, ht]; ring
  exact ⟨t, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb_ne) key⟩

/-- **Hall ∩ normal**: `H` が `G` の `π`-Hall 部分群, `N ⊴ G` なら `H ∩ N` (= `N` 内で
`H.subgroupOf N`) は `N` の `π`-Hall 部分群.

`|H ∩ N| ∣ |H|` なので素因子は `π` に含まれ, `[N : H∩N] ∣ [G:H] = index H` (π'-number,
`relIndex_dvd_index_of_normal_right`) なので余指数の素因子は `π` の外. BG Cor 10.9 で
`W ∩ M'` / `W ∩ M_σ` が `M'` / `M_σ` の Hall になることに使う. -/
theorem isHallSubgroup_subgroupOf_of_normal [Finite G] {π : Set ℕ} {H N : Subgroup G}
    (hH : IsHallSubgroup π H) [N.Normal] :
    IsHallSubgroup π (H.subgroupOf N) := by
  have hcard : Nat.card ↥(H.subgroupOf N) = Nat.card ↥(H ⊓ N : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  refine ⟨?_, ?_⟩
  · -- |H.subgroupOf N| = |H ⊓ N| ∣ |H|, so prime factors ⊆ π.
    intro q hq
    rw [hcard] at hq
    apply hH.1
    rw [Nat.mem_primeFactors] at hq ⊢
    exact ⟨hq.1, hq.2.1.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩
  · -- index = H.relIndex N ∣ H.index, so prime factors ⊆ π'.
    intro q hq hqπ
    have hdvd : (H.subgroupOf N).index ∣ H.index := relIndex_dvd_index_of_normal_right H
    rw [Nat.mem_primeFactors] at hq
    exact hH.2 q (Nat.mem_primeFactors.mpr
      ⟨hq.1, hq.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩) hqπ

end

end OddOrder.Isaacs.Ch03


