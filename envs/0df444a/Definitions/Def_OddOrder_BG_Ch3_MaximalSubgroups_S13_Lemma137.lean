-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma137
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_Lemma137
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:54:23.645197+00:00
-- url     : https://prove2.me/theorems/7d039d26-0c2b-4f68-b207-844f96821789
-- title:
--   BG §13: Lemma 13.7 ($E_1E_3$ acts in a prime manner on $M_\sigma$) and helpers
-- statement:
--   Formalizes Lemma 13.7 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §13 (`E1E3_actsPrime`): if $E_1\ne 1$ and $E_1$ does not act regularly on $E_3$ then $E_1E_3$ acts in a prime manner on $M_\sigma$, together with supporting lemmas such as prime action implying trivial centralizer. It is downstream of the prime-action file and does not depend on Lemma 13.6.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_Lemma137.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_Lemma137.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction
import Definitions.Def_OddOrder_GroupTheory_CoprimeConjugacy
import Definitions.Def_OddOrder_Mathlib_Subgroup

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **prime-action ⟹ trivial centralizer** (BG §13 の (13.2) 適用パターン): `X` が `N` に
prime 作用し、`W ≤ N` を `X` が非中心化 (`⁅W, X⁆ ≠ ⊥`) するなら、`W` を中心化する `X` の元は
自明のみ — `C_X(W) = X ⊓ C_G(W) = 1`。

理由: `x ∈ X#` が `W` を中心化すると、`W ≤ N ⊓ C_G(x) = fixedByElement N x`、prime 作用で
これは `fixedBy N X = N ⊓ C_G(X)`、ゆえ `W ≤ C_G(X)` すなわち `⁅W, X⁆ = ⊥` で矛盾。
Lemma 13.7 step 5c (`C_{E₁}(M_σ∩M*)=1`) の核。 -/
theorem actsPrimeOn_inf_centralizer_eq_bot {N X W : Subgroup G}
    (h : ActsPrimeOn N X) (hW : W ≤ N) (hcomm : ⁅W, X⁆ ≠ ⊥) :
    X ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff] at hxC
  -- `W ≤ C_G(x)`: every `w ∈ W` commutes with `x`.
  have hWx : W ≤ Subgroup.centralizer ({x} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact (hxC w hw).symm
  -- `W ≤ fixedByElement N x = fixedBy N X` (prime action), hence `W ≤ C_G(X)`.
  have hWfix : W ≤ fixedByElement N x := by
    rw [fixedByElement_def]; exact le_inf hW hWx
  rw [h x hxX hxne, fixedBy_def] at hWfix
  exact hcomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hWfix.trans inf_le_right))

/-- **prime-order 十分条件 ⟹ prime action** (BG §13 intro の「`C_N(g)=C_N(X)` ⟺
`C_N(P)⊆C_N(X)` (∀`P∈ℰ¹(X)`)」の easy 方向): `X#` の全 **素数位数**元 `x` で
`C_N(x) ≤ C_N(X)` (`fixedByElement N x ≤ fixedBy N X`) なら、`X` は `N` に prime 作用する。

任意の `g∈X#` をその素数べき部分 `x = g^{ord g/p}` (`p ∣ ord g` 素数) に落とすと
`x ∈ X#` は素数位数で `C_N(g) ⊆ C_N(x)` (x は g のべき)。Lemma 13.7 step 4 (equal case) で
`E₁⊔E₃` の prime 作用を素数位数部分群ごとに検証する土台。 -/
theorem actsPrimeOn_of_prime_order_le [Finite G] {N X : Subgroup G}
    (hpr : ∀ x ∈ X, (orderOf x).Prime → fixedByElement N x ≤ fixedBy N X) :
    ActsPrimeOn N X := by
  intro g hg hg1
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hg)
  have hord1 : orderOf g ≠ 1 := fun hc => hg1 (orderOf_eq_one_iff.mp hc)
  have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨p, hp, hpdvd⟩ := (orderOf g).exists_prime_and_dvd hord1
  set d : ℕ := orderOf g / p with hd
  have hdvd : d ∣ orderOf g := ⟨p, (Nat.div_mul_cancel hpdvd).symm⟩
  have hd0 : d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hpdvd) hp.pos).ne'
  set x : G := g ^ d with hx
  have hxord : orderOf x = p := by
    rw [hx, orderOf_pow' g hd0, Nat.gcd_eq_right hdvd, hd, Nat.div_div_self hpdvd hord0]
  have hxX : x ∈ X := hx ▸ X.pow_mem hg d
  -- `C(g) ⊆ C(x)` because `x = g ^ d` is a power of `g`.
  have hgx : fixedByElement N g ≤ fixedByElement N x := by
    rw [fixedByElement_def, fixedByElement_def]
    refine inf_le_inf_left N ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    rintro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have hgy : Commute g y := hy g rfl
    rw [hx]
    exact (hgy.pow_left d).eq
  exact hgx.trans (hpr x hxX (by rw [hxord]; exact hp))

/-- `X` が `N` を正規化するなら、`X` は `C_N(X) = fixedBy N X = N ⊓ C(X)` も正規化する。
`X` は `N` も `X`(自分自身)も正規化するので、`C(X)` も保つ。Lemma 13.7 equal case で
`x'∈E₃` が `D = C_N(E₃)` を共役で保つために使う。 -/
theorem le_normalizer_fixedBy {N X : Subgroup G} (hXN : X ≤ Subgroup.normalizer N) :
    X ≤ Subgroup.normalizer (fixedBy N X) := by
  intro z hz
  have hzNX : z ∈ Subgroup.normalizer X := Subgroup.le_normalizer hz
  have hzN : z ∈ Subgroup.normalizer N := hXN hz
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [fixedBy_def, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  have hNpart : w ∈ N ↔ z * w * z⁻¹ ∈ N := Subgroup.mem_normalizer_iff.mp hzN w
  constructor
  · rintro ⟨hwN, hwC⟩
    refine ⟨hNpart.mp hwN, ?_⟩
    intro e he
    have hez : z⁻¹ * e * z ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hzNX) e).mp he
    have hcomm := hwC _ hez
    calc e * (z * w * z⁻¹) = z * ((z⁻¹ * e * z) * w) * z⁻¹ := by group
      _ = z * (w * (z⁻¹ * e * z)) * z⁻¹ := by rw [hcomm]
      _ = (z * w * z⁻¹) * e := by group
  · rintro ⟨hwN, hwC⟩
    refine ⟨hNpart.mpr hwN, ?_⟩
    intro e he
    have hez : z * e * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hzNX e).mp he
    have hcomm := hwC _ hez
    have hkey : z * (e * w) * z⁻¹ = z * (w * e) * z⁻¹ := by
      calc z * (e * w) * z⁻¹ = (z * e * z⁻¹) * (z * w * z⁻¹) := by group
        _ = (z * w * z⁻¹) * (z * e * z⁻¹) := hcomm
        _ = z * (w * e) * z⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel hkey)

/-- **prime action の join (equal case)**: `E₁`, `E₃` がともに `N` に prime 作用し、
互いに素な位数を持ち、`E₁` が `E₃` を正規化し、両者が `N` を正規化し、かつ
`C_N(E₁) = C_N(E₃)` (`= D`) なら、`E₁ ⊔ E₃` も `N` に prime 作用する。

BG Lemma 13.7 の equal case。素数位数 `x∈(E₁⊔E₃)#` を `x = b·a` (`b∈E₃`, `a∈E₁`) に分解。
`a=1` なら `x∈E₃` で済む。`a≠1` なら Peterfalvi (2.1) `exists_mem_centralizer_conj` で coset
`E₃·a` を `C_{E₃}(a)·a` に collapse — `x` は `c·a` (`c∈C_{E₃}(a)`) に `E₃`-共役。位数が素数ゆえ
`ord(x)=ord(c)·ord(a)` (commute+coprime) から `ord(c)=1`, すなわち `c=1`、つまり `x` は `a∈E₁#`
に共役。あとは `C_N(x)=D` を共役 (E₃ 元) で押し戻す (`le_normalizer_fixedBy` + `hD` で E₃ 経由)。 -/
theorem actsPrimeOn_sup_of_eq_centralizer [Finite G] {N E₁ E₃ : Subgroup G}
    (hE1 : ActsPrimeOn N E₁) (hE3 : ActsPrimeOn N E₃)
    (hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₃))
    (hnorm : E₁ ≤ Subgroup.normalizer E₃)
    (hN3 : E₃ ≤ Subgroup.normalizer N)
    (hD : fixedBy N E₁ = fixedBy N E₃) :
    ActsPrimeOn N (E₁ ⊔ E₃) := by
  have hHD : fixedBy N (E₁ ⊔ E₃) = fixedBy N E₁ := by
    have h1 : fixedBy N (E₁ ⊔ E₃) = fixedBy N E₁ ⊓ fixedBy N E₃ := by
      rw [fixedBy_def, fixedBy_def, fixedBy_def, Subgroup.centralizer_sup, inf_inf_distrib_left]
    rw [h1, ← hD, inf_idem]
  have hE3normD : E₃ ≤ Subgroup.normalizer (fixedBy N E₃) := le_normalizer_fixedBy hN3
  apply actsPrimeOn_of_prime_order_le
  intro x hxH hxprime
  rw [hHD]
  have hxne : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hxprime; exact hxprime.ne_one rfl
  -- decompose `x = b * a`, `b ∈ E₃`, `a ∈ E₁`
  have hxset : (x : G) ∈ (E₃ : Set G) * (E₁ : Set G) := by
    have hcoe : (↑(E₁ ⊔ E₃) : Set G) = (E₃ : Set G) * (E₁ : Set G) := by
      rw [sup_comm]; exact Subgroup.coe_mul_of_right_le_normalizer_left E₃ E₁ hnorm
    rw [← hcoe]; exact hxH
  obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_mul.mp hxset
  rw [SetLike.mem_coe] at hb ha
  by_cases ha1 : a = 1
  · -- `x = b ∈ E₃`
    have hxE3 : x ∈ E₃ := by rw [← hba, ha1, mul_one]; exact hb
    exact le_of_eq (by rw [hE3 x hxE3 hxne, hD])
  · -- `a ≠ 1`: collapse the coset `E₃·a` via (2.1) and force `c = 1`
    have hordvd : orderOf a ∣ Nat.card E₁ := by
      have h := orderOf_dvd_natCard (⟨a, ha⟩ : E₁); rwa [← Subgroup.orderOf_coe] at h
    have hcop_a : Nat.Coprime (orderOf a) (Nat.card E₃) := hcop.coprime_dvd_left hordvd
    have hnorm_a : ∀ y ∈ E₃, a * y * a⁻¹ ∈ E₃ := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (hnorm ha) y).mp hy
    obtain ⟨c, hcE3C, x', hx'E3, hconj⟩ :=
      OddOrder.GroupTheory.exists_mem_centralizer_conj hcop_a hnorm_a hb
    rw [hba] at hconj
    obtain ⟨hcE3, hcCa⟩ := Subgroup.mem_inf.mp hcE3C
    have hca : Commute c a := by
      rw [Subgroup.mem_centralizer_iff] at hcCa
      exact (hcCa a (Set.mem_singleton a)).symm
    have hcordvd : orderOf c ∣ Nat.card E₃ := by
      have h := orderOf_dvd_natCard (⟨c, hcE3⟩ : E₃); rwa [← Subgroup.orderOf_coe] at h
    have hcop_ca : Nat.Coprime (orderOf c) (orderOf a) :=
      (hcop.symm.coprime_dvd_left hcordvd).coprime_dvd_right hordvd
    have hordca : orderOf (c * a) = orderOf c * orderOf a :=
      hca.orderOf_mul_eq_mul_orderOf_of_coprime hcop_ca
    have hsc : SemiconjBy x' x (c * a) := by
      change x' * x = (c * a) * x'
      rw [← hconj]; group
    have hordeq : orderOf x = orderOf (c * a) := SemiconjBy.orderOf_eq x' hsc
    have hordane : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    have hc1 : c = 1 := by
      have hp : (orderOf c * orderOf a).Prime := by rw [← hordca, ← hordeq]; exact hxprime
      rcases Nat.prime_mul_iff.mp hp with ⟨_, ha0⟩ | ⟨_, hc0⟩
      · exact absurd ha0 hordane
      · exact orderOf_eq_one_iff.mp hc0
    rw [hc1, one_mul] at hconj
    have hfa : fixedByElement N a = fixedBy N E₁ := hE1 a ha ha1
    intro y hy
    rw [fixedByElement_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hy
    obtain ⟨hyN, hyC⟩ := hy
    have hyx : x * y = y * x := hyC x (Set.mem_singleton x)
    have hwN : x' * y * x'⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hN3 hx'E3) y).mp hyN
    have hwa : a * (x' * y * x'⁻¹) = (x' * y * x'⁻¹) * a := by
      rw [← hconj]
      calc x' * x * x'⁻¹ * (x' * y * x'⁻¹) = x' * (x * y) * x'⁻¹ := by group
        _ = x' * (y * x) * x'⁻¹ := by rw [hyx]
        _ = (x' * y * x'⁻¹) * (x' * x * x'⁻¹) := by group
    have hw_fix : x' * y * x'⁻¹ ∈ fixedBy N E₁ := by
      rw [← hfa, fixedByElement_def]
      exact Subgroup.mem_inf.mpr ⟨hwN, Subgroup.mem_centralizer_iff.mpr (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu; exact hwa)⟩
    rw [hD]
    rw [hD] at hw_fix
    have hgoal : x'⁻¹ * (x' * y * x'⁻¹) * x' ∈ fixedBy N E₃ := by
      have hnn := hE3normD (inv_mem hx'E3)
      rw [Subgroup.mem_normalizer_iff] at hnn
      simpa using (hnn (x' * y * x'⁻¹)).mp hw_fix
    have hyeq : x'⁻¹ * (x' * y * x'⁻¹) * x' = y := by group
    rwa [hyeq] at hgoal

/-- **Lemma 13.7 step 1** (witness 抽出): `E₁` が `E₃` に regular 作用しないなら、素数 `p, r` と
`P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)` で `R` が `P` を中心化するものが存在する。

`¬regular` から `g∈E₁#` と `h∈E₃#` (`[g,h]=1`) を取り、各々の素数べき部分
`P = ⟨g^{ord g/p}⟩`, `R = ⟨h^{ord h/r}⟩` (素数位数) を取る。`P ≤ ⟨g⟩`, `R ≤ ⟨h⟩` と
`Commute g h` から `R ≤ C(P)`。 -/
theorem exists_elemAbelian_centralizing_of_not_regular [Finite G] {E₁ E₃ : Subgroup G}
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ ∃ P R : Subgroup G,
      P ∈ elemAbelianOfRank G p 1 ∧ P ≤ E₁ ∧
      R ∈ elemAbelianOfRank G r 1 ∧ R ≤ E₃ ∧
      R ≤ Subgroup.centralizer (P : Set G) := by
  classical
  rw [actsRegularlyOn_iff] at hreg
  simp only [fixedByElement_def] at hreg
  push Not at hreg
  obtain ⟨g, hgE1, hgne, hfix⟩ := hreg
  obtain ⟨⟨he, he_mem⟩, he_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
  obtain ⟨heE3, heC⟩ := Subgroup.mem_inf.mp he_mem
  have he1 : he ≠ 1 := fun hc => he_ne (Subtype.ext (by simpa using hc))
  have hghe : Commute g he := by
    rw [Subgroup.mem_centralizer_iff] at heC; exact heC g (Set.mem_singleton g)
  -- order-`s` cyclic subgroup of `⟨x⟩` inside `K`, for any `x ∈ K#`.
  have key : ∀ {K : Subgroup G} (x : G), x ∈ K → x ≠ 1 →
      ∃ s : ℕ, s.Prime ∧ ∃ Q : Subgroup G,
        Q ∈ elemAbelianOfRank G s 1 ∧ Q ≤ K ∧ Q ≤ Subgroup.zpowers x := by
    intro K x hxK hx
    have hord1 : orderOf x ≠ 1 := fun hc => hx (orderOf_eq_one_iff.mp hc)
    have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨s, hs, hsdvd⟩ := (orderOf x).exists_prime_and_dvd hord1
    have : Fact s.Prime := ⟨hs⟩
    set d := orderOf x / s with hd
    have hdvd : d ∣ orderOf x := ⟨s, (Nat.div_mul_cancel hsdvd).symm⟩
    have hd0 : d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) hsdvd) hs.pos).ne'
    set y := x ^ d with hy
    have hyord : orderOf y = s := by
      rw [hy, orderOf_pow' x hd0, Nat.gcd_eq_right hdvd, hd, Nat.div_div_self hsdvd hord0]
    have hycard : Nat.card (Subgroup.zpowers y) = s := by rw [Nat.card_zpowers, hyord]
    refine ⟨s, hs, Subgroup.zpowers y, ?_, ?_, ?_⟩
    · exact ⟨Subgroup.IsElementaryAbelian.of_card_prime hycard, by rw [pow_one]; exact hycard⟩
    · rw [Subgroup.zpowers_le, hy]; exact K.pow_mem hxK d
    · rw [Subgroup.zpowers_le, hy]; exact pow_mem (Subgroup.mem_zpowers x) d
  obtain ⟨p, hp, P, hP, hPE1, hPg⟩ := key g hgE1 hgne
  obtain ⟨r, hr, R, hR, hRE3, hRhe⟩ := key he heE3 he1
  refine ⟨p, r, hp, hr, P, R, hP, hPE1, hR, hRE3, ?_⟩
  have hzz : Subgroup.zpowers he ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hu
    obtain ⟨k, rfl⟩ := hu
    exact (hghe.zpow_left k).eq
  exact hRhe.trans (hzz.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPg)))

/-- `P ∈ ℰ_s¹(X)` (`P ≤ X`, `s` 素数) + `ActsPrimeOn N X` ⟹ `C_N(P) = C_N(X)`
(`fixedBy N P = fixedBy N X`)。`P` は素数位数ゆえ生成元 `g∈P#` で `P=⟨g⟩`、
`C_N(P)=C_N(g)=C_N(X)` (prime action)。13.7 body の step 2/5 で `C_N(P)=C_N(E₁)` 等に使う。 -/
theorem fixedBy_eq_of_elemAbelian_one [Finite G] {N X P : Subgroup G} {s : ℕ} (hs : s.Prime)
    (hX : ActsPrimeOn N X) (hP : P ∈ elemAbelianOfRank G s 1) (hPX : P ≤ X) :
    fixedBy N P = fixedBy N X := by
  have : Fact s.Prime := ⟨hs⟩
  have hPcard : Nat.card P = s := by rw [← pow_one s]; exact hP.2
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcard; exact hs.one_lt.ne' hPcard.symm
  obtain ⟨⟨g, hgP⟩, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hg1 : g ≠ 1 := fun hc => hgne (Subtype.ext (by simpa using hc))
  have hog : orderOf g = s := by
    have hdvd : orderOf g ∣ Nat.card P := by
      have h := orderOf_dvd_natCard (⟨g, hgP⟩ : P); rwa [← Subgroup.orderOf_coe] at h
    rw [hPcard] at hdvd
    rcases hs.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h2
  have hPg : P = Subgroup.zpowers g :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgP)
      (by rw [Nat.card_zpowers, hog]; exact hPcard.le)).symm
  have hzC : Subgroup.centralizer (Subgroup.zpowers g : Set G)
      = Subgroup.centralizer ({g} : Set G) := by
    apply le_antisymm
    · exact Subgroup.centralizer_le (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; rw [hu]; exact Subgroup.mem_zpowers g)
    · intro w hw
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hu
      obtain ⟨k, rfl⟩ := hu
      have hc : Commute g w := hw g (Set.mem_singleton g)
      exact (hc.zpow_left k).eq
  calc fixedBy N P = fixedByElement N g := by rw [hPg, fixedBy_def, fixedByElement_def, hzC]
    _ = fixedBy N X := hX g (hPX hgP) hg1

/-- **Lemma 13.7 step 5(f)**: `E₁` (cyclic, `π(E₁)⊆τ₁(M*)`, `E₁≤M*`) と `P∈ℰ_p¹(E₁)` で
`P` が `R⊆M*_σ` を中心化するなら、`E₁` 全体が `R` を中心化する。

Hall 共役で `w•E₁ ≤ E₁*` (M* の Hall τ₁、E1_actsPrime で M*_σ に prime)。`P` の生成元を `w` で
共役した `z∈E₁*#` は `w•R⊆M*_σ` を中心化 ⟹ prime 作用で `E₁*` 全体が `w•R` を中心化 ⟹
`w•E₁≤E₁*` が `w•R` を中心化 ⟹ 共役を戻して `E₁` が `R` を中心化。prime-action 共役不変性を
直接使わず、R・P を M* の setup frame へ共役するのが鍵。 -/
theorem E1_centralizes_R_of_hall_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {E₁ Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G)
    (hE1ne : E₁ ≠ ⊥) (hE1M : E₁ ≤ Mstar)
    (hπ : ∀ s ∈ (Nat.card ↥E₁).primeFactors, s ∈ tau1 Mstar)
    {p : ℕ} (hp : p.Prime) {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) (hRMsig : R ≤ S10.Msigma Mstar)
    (hRcP : R ≤ Subgroup.centralizer (P : Set G)) :
    E₁ ≤ Subgroup.centralizer (R : Set G) := by
  classical
  obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMstar
  have hE1pi : Ch03.Subgroup.IsPiGroup (tau1 Mstar) (E₁.subgroupOf Mstar) := by
    intro s hs'
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE1M).toEquiv] at hs'
    exact hπ s hs'
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₁_le hs.E₁_hall
    (tau1_subset_sigma_compl Mstar) hE1M hE1pi
  -- element form of `w • E₁ ≤ E₁*`.
  have hconj : ∀ e ∈ E₁, w * e * w⁻¹ ∈ E1s := by
    intro e he
    exact hwle (Subgroup.smul_mem_pointwise_smul_iff.mpr he)
  -- `M*_σ` is `w`-stable (normal in `M*`, `w ∈ M*`).
  have hwMsig : ∀ x ∈ S10.Msigma Mstar, w * x * w⁻¹ ∈ S10.Msigma Mstar := by
    have hMle : Mstar ≤ Subgroup.normalizer (S10.Msigma Mstar : Set G) := by
      rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma Mstar) Mstar
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hMle hwM) x).mp hx
  -- nontrivial generator `p_elt` of `P` (order `p`).
  have hPcard : Nat.card P = p := by rw [← pow_one p]; exact hP.2
  have : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcard; exact hp.one_lt.ne' hPcard.symm
  obtain ⟨⟨p_elt, hp_eltP⟩, hp_eltne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hp_elt1 : p_elt ≠ 1 := fun hc => hp_eltne (Subtype.ext (by simpa using hc))
  -- `E₁* ≠ ⊥`, prime on `M*_σ`.
  have hE1sne : E1s ≠ ⊥ := by
    obtain ⟨⟨e₀, he₀⟩, he₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1ne
    have he₀1 : e₀ ≠ 1 := fun hc => he₀ne (Subtype.ext (by simpa using hc))
    intro hb
    have : w * e₀ * w⁻¹ ∈ E1s := hconj e₀ he₀
    rw [hb, Subgroup.mem_bot] at this
    exact he₀1 (by simpa using mul_eq_one_iff_eq_inv.mp this)
  have hE1sprime : ActsPrimeOn (S10.Msigma Mstar) E1s := E1_actsPrime hG hs hE1sne
  -- `z := w p_elt w⁻¹ ∈ E₁*#`.
  set z : G := w * p_elt * w⁻¹ with hz
  have hzE1s : z ∈ E1s := hconj p_elt (hPE1 hp_eltP)
  have hzne : z ≠ 1 := by
    rw [hz]; intro hc
    apply hp_elt1
    have hcc : MulAut.conj w p_elt = MulAut.conj w 1 := by rw [map_one]; exact hc
    exact (MulAut.conj w).injective hcc
  -- `z` centralizes `w • R`, and `w • R ⊆ M*_σ`.
  have hzfix := hE1sprime z hzE1s hzne
  have hwRsub : ∀ r ∈ R, w * r * w⁻¹ ∈ fixedByElement (S10.Msigma Mstar) z := by
    intro r hr
    rw [fixedByElement_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨hwMsig r (hRMsig hr), ?_⟩
    intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu
    -- `p_elt` and `r` commute (`r ∈ C(P)`, `p_elt ∈ P`).
    have hcomm : p_elt * r = r * p_elt :=
      (Subgroup.mem_centralizer_iff.mp (hRcP hr)) p_elt hp_eltP
    rw [hz]
    calc (w * p_elt * w⁻¹) * (w * r * w⁻¹) = w * (p_elt * r) * w⁻¹ := by group
      _ = w * (r * p_elt) * w⁻¹ := by rw [hcomm]
      _ = (w * r * w⁻¹) * (w * p_elt * w⁻¹) := by group
  -- hence `E₁*` centralizes `w • R`; transport back to `E₁` centralizing `R`.
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hwr_fix : w * r * w⁻¹ ∈ fixedBy (S10.Msigma Mstar) E1s := by rw [← hzfix]; exact hwRsub r hr
  rw [fixedBy_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hwr_fix
  have hcomm := hwr_fix.2 (w * e * w⁻¹) (hconj e he)
  -- `(wew⁻¹)(wrw⁻¹) = (wrw⁻¹)(wew⁻¹)` ⟹ `er = re` ⟹ `r e = e r`.
  have : w * (e * r) * w⁻¹ = w * (r * e) * w⁻¹ := by
    calc w * (e * r) * w⁻¹ = (w * e * w⁻¹) * (w * r * w⁻¹) := by group
      _ = (w * r * w⁻¹) * (w * e * w⁻¹) := hcomm
      _ = w * (r * e) * w⁻¹ := by group
  have her : e * r = r * e := mul_left_cancel (mul_right_cancel this)
  exact her.symm

/-- **Lemma 13.7 step 5(a)**: もし `x ∈ E₃#` で `C_{M_σ}(x) ≠ 1` なら `τ₂(M)` は空、
よって `E₂ = ⊥`、`E = E₁ ⊔ E₃`。`τ₂(M) ≠ ∅` ⟹ `∃ p∈τ₂(M), A∈ℰ_p²(E)` ⟹ Cor 12.6(d) で
`E₃` は `M_σ` に regular 作用 ⟹ `C_{M_σ}(x)=1` で矛盾。 -/
theorem E_eq_sup_of_E3_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥) :
    E = E₁ ⊔ E₃ := by
  have hE2 : E₂ = ⊥ := by
    by_contra hE2ne
    obtain ⟨p, hp_prime, hpdvd⟩ :=
      (Nat.card E₂).exists_prime_and_dvd (fun hc => hE2ne (Subgroup.card_eq_one.mp hc))
    have : Fact p.Prime := ⟨hp_prime⟩
    have hc2 : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hpτ2 : p ∈ tau2 M :=
      h.E₂_hall.1 p (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hp_prime, hpdvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hpτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  rw [h.eq_sup hG, hE2, sup_bot_eq]

/-- **Lemma 13.7 step 5(b) 補助**: `R ≤ E₃` なら `E ≤ N_G(R)` (`R ⊲ E`)。`E₃` は cyclic ゆえ
任意の部分群 `R` は characteristic、`E` は `E₃` を正規化する (Lem 12.1) ので `R` も正規化。 -/
theorem E_le_normalizer_of_le_E3 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {R : Subgroup G} (hRE3 : R ≤ E₃) : E ≤ Subgroup.normalizer (R : Set G) := by
  have : IsCyclic ↥E₃ := h.E3_isCyclic hG
  have : (R.subgroupOf E₃).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
  intro e he
  have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₃)
    (C := R.subgroupOf E₃) (h.E3_normal hG he)
  rwa [Subgroup.map_subgroupOf_eq_of_le hRE3] at hmem

/-- **BG Lemma 13.7, step 5** (strict case impossible): with `P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)`,
`R ≤ C(P)`, the strict containment `C_{M_σ}(E₁) ⊊ C_{M_σ}(E₃)` is contradictory.

証明 (a)-(g)、mmd L3640-3658:
(a) `1⊂R⊂E₃`, `C_{M_σ}(R)≠1` ⟹ Cor 12.6(d) で `τ₂(M)` empty ⟹ `E = E₁ ⊔ E₃`。
(b) `R ⊲ E`、`M* ∈ 𝓜(N_G(R))`、`E ⊆ M*`、`1⊂[C_{M_σ}(R),P] ⊆ [M_σ⊓M*, E₁]`。
(c) (13.2) ⟹ `C_{E₁}(M_σ⊓M*)=1` (helper `actsPrimeOn_inf_centralizer_eq_bot`)。
(d) Cor 13.2(b) ⟹ `π(E₁) ⊆ τ₁(M*)`。
(e) Cor 13.2(c) ⟹ `R ⊆ M*_σ`。
(f) `E₁ ⊆ E₁*` (Hall `τ₁(M*)`)、Thm 13.5 を M* に ⟹ `E₁` が `R` を中心化。
(g) `E=E₁E₃` + `E₁,E₃` が `R` 中心化 ⟹ `R⊆Z(E)`、`C_{E₃}(E)=1` (Lem 12.1) と矛盾。

詳細 = `notes/bg/s13_transition_lane_f.md`。 -/
theorem strict_centralizer_config_false [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) {P R : Subgroup G}
    (hP : P ∈ elemAbelianOfRank G p 1) (hPE1 : P ≤ E₁)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRE3 : R ≤ E₃)
    (hRcP : R ≤ Subgroup.centralizer (P : Set G))
    (hlt : fixedBy (S10.Msigma M) E₁ < fixedBy (S10.Msigma M) E₃) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hE1ne : E₁ ≠ ⊥ := fun hb =>
    (ne_bot_of_mem_elemAbelianOfRank_one hP) (le_bot_iff.mp (hPE1.trans hb.le))
  have hRne : R ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hR
  have hE1prime : ActsPrimeOn (S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- connect `hlt` to `P`, `R`.
  have hPeq : fixedBy (S10.Msigma M) P = fixedBy (S10.Msigma M) E₁ :=
    fixedBy_eq_of_elemAbelian_one hp hE1prime hP hPE1
  have hReq : fixedBy (S10.Msigma M) R = fixedBy (S10.Msigma M) E₃ :=
    fixedBy_eq_of_elemAbelian_one hr hE3prime hR hRE3
  have hlt' : fixedBy (S10.Msigma M) P < fixedBy (S10.Msigma M) R := by rw [hPeq, hReq]; exact hlt
  have hCRne : fixedBy (S10.Msigma M) R ≠ ⊥ := (lt_of_le_of_lt bot_le hlt').ne'
  -- (a) `E = E₁ ⊔ E₃`.
  obtain ⟨⟨r_elt, hr_eltR⟩, hr_eltne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have hr_elt1 : r_elt ≠ 1 := fun hc => hr_eltne (Subtype.ext (by simpa using hc))
  have hCre : S10.Msigma M ⊓ Subgroup.centralizer ({r_elt} : Set G) ≠ ⊥ := by
    refine fun hb => hCRne (le_bot_iff.mp ?_)
    rw [fixedBy_def, ← hb]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (by
      intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu; exact hr_eltR))
  have hEsup : E = E₁ ⊔ E₃ := E_eq_sup_of_E3_centralizer hG h (hRE3 hr_eltR) hr_elt1 hCre
  -- (b) `R ⊲ E`, extract `M* ∈ ℳ(N_G(R))`, `E ⊆ M*`.
  have hENR : E ≤ Subgroup.normalizer (R : Set G) := E_le_normalizer_of_le_E3 hG h hRE3
  have hRM : R ≤ M := hRE3.trans h.E3_le_M
  have hNRne : Subgroup.normalizer (R : Set G) ≠ ⊤ := by
    intro htop
    have : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal R inferInstance with hb | ht
    · exact hRne hb
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hRM))
  obtain ⟨Mstar, hMstarCo, hNRM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (R : Set G))).resolve_left hNRne
  have hMstarMem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNRM⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  have hEMstar : E ≤ Mstar := hENR.trans hNRM
  have hrτ3 : r ∈ tau3 M := by
    have hc3 : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    refine h.E₃_hall.1 r (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hr, ?_, Nat.card_pos.ne'⟩)
    have hdvd : Nat.card R ∣ Nat.card E₃ := Subgroup.card_dvd_of_le hRE3
    rwa [show Nat.card R = r by rw [← pow_one r]; exact hR.2] at hdvd
  have hRr : IsPGroup r ↥R := IsPGroup.of_card (by rw [hR.2, pow_one])
  have hCor132 := tau13_pSubgroup_centralizes hG h (Or.inr hrτ3) hRM hRne hRr hMstarMem
  -- (c) `C_{E₁}(M_σ ⊓ M*) = ⊥`.
  have hcommRP : ⁅fixedBy (S10.Msigma M) R, P⁆ ≠ ⊥ := by
    intro hb
    have hle : fixedBy (S10.Msigma M) R ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have hcontra : fixedBy (S10.Msigma M) R ≤ fixedBy (S10.Msigma M) P :=
      le_inf (by rw [fixedBy_def]; exact inf_le_left) hle
    exact absurd (le_antisymm hlt'.le hcontra) (ne_of_lt hlt')
  have hCRsub : fixedBy (S10.Msigma M) R ≤ S10.Msigma M ⊓ Mstar :=
    le_inf (by rw [fixedBy_def]; exact inf_le_left)
      (by rw [fixedBy_def]
          exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (R : Set G)).trans hNRM))
  have hcomm2 : ⁅(S10.Msigma M ⊓ Mstar : Subgroup G), E₁⁆ ≠ ⊥ := fun hb =>
    hcommRP (le_bot_iff.mp ((Subgroup.commutator_mono hCRsub hPE1).trans hb.le))
  have hCE1 : E₁ ⊓ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) = ⊥ :=
    actsPrimeOn_inf_centralizer_eq_bot hE1prime inf_le_left hcomm2
  -- (d) `π(E₁) ⊆ τ₁(M*)`.
  have hπ : ∀ s ∈ (Nat.card ↥E₁).primeFactors, s ∈ tau1 Mstar := by
    intro s hs
    by_contra hsτ1
    have hs_prime := Nat.prime_of_mem_primeFactors hs
    have : Fact s.Prime := ⟨hs_prime⟩
    have : Fintype ↥E₁ := Fintype.ofFinite _
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := ↥E₁) s
      (by rw [← Nat.card_eq_fintype_card]; exact (Nat.mem_primeFactors.mp hs).2.1)
    have hxE1 : (a : G) ∈ E₁ := a.2
    have hxord : orderOf (a : G) = s := by rw [Subgroup.orderOf_coe]; exact ha
    have hxne : (a : G) ≠ 1 := by
      intro hc; apply hs_prime.ne_one; rw [← hxord, hc, orderOf_one]
    have hzxEM : Subgroup.zpowers (a : G) ≤ E ⊓ Mstar :=
      le_inf (Subgroup.zpowers_le.mpr (h.E₁_le hxE1))
        (Subgroup.zpowers_le.mpr (hEMstar (h.E₁_le hxE1)))
    have hzxpi : Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) (Subgroup.zpowers (a : G)) := by
      intro t ht
      rw [Nat.card_zpowers, hxord, hs_prime.primeFactors, Finset.mem_singleton] at ht
      rw [ht]; exact hsτ1
    have hzxC := hCor132.2.1 (Subgroup.zpowers (a : G)) hzxEM hzxpi
    have hxbot : Subgroup.zpowers (a : G) ≤
        E₁ ⊓ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
      le_inf (Subgroup.zpowers_le.mpr hxE1) hzxC
    rw [hCE1] at hxbot
    exact hxne (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hxbot))
  -- (e) `R ⊆ M*_σ`.
  have hE1MM : E₁ ≤ M ⊓ Mstar := le_inf h.E1_le_M (h.E₁_le.trans hEMstar)
  have hcomm3 : ⁅(S10.Msigma M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ ≠ ⊥ := fun hb =>
    hcomm2 (le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hE1MM).trans hb.le))
  have hrσMstar : r ∈ S10.sigma Mstar := (hCor132.2.2 hcomm3).1
  have hRMstar : R ≤ Mstar := hRE3.trans (h.E₃_le.trans hEMstar)
  have hRpiσ : Ch03.Subgroup.IsPiGroup (S10.sigma Mstar) R := by
    intro t ht
    rw [show Nat.card ↥R = r by rw [← pow_one r]; exact hR.2, hr.primeFactors,
      Finset.mem_singleton] at ht
    rw [ht]; exact hrσMstar
  have hRMsig : R ≤ S10.Msigma Mstar :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMstarMax) hRMstar hRpiσ
  -- (f) `E₁` centralizes `R`.
  have hE1cR : E₁ ≤ Subgroup.centralizer (R : Set G) :=
    E1_centralizes_R_of_hall_tau1 hG hMstarMax hE1ne (h.E₁_le.trans hEMstar) hπ hp hP hPE1
      hRMsig hRcP
  -- (g) `E₃` centralizes `R`, hence `E` does, contradiction with `C_G(E) ⊓ E₃ = ⊥`.
  have hE3cR : E₃ ≤ Subgroup.centralizer (R : Set G) := by
    have : IsCyclic ↥E₃ := h.E3_isCyclic hG
    let : CommGroup ↥E₃ := IsCyclic.commGroup
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext_iff.mp (mul_comm (⟨u, hRE3 hu⟩ : ↥E₃) ⟨e, he⟩)
  have hEcR : E ≤ Subgroup.centralizer (R : Set G) := hEsup ▸ sup_le hE1cR hE3cR
  have hRcE : R ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcR)
  have hRbot : R ≤ Subgroup.centralizer (E : Set G) ⊓ E₃ := le_inf hRcE hRE3
  rw [(subgroupE_basic hG h).2.2.2.2.2.1] at hRbot
  exact hRne (le_bot_iff.mp hRbot)

/-- **BG Lemma 13.7** (mmd L3596): `E₁≠1` かつ `E₁` が `E₃` に regular 作用しないなら、`E₁E₃` は
`M_σ` に prime 作用。 -/
theorem E1E3_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ActsPrimeOn (S10.Msigma M) (E₁ ⊔ E₃) := by
  have hE1prime : ActsPrimeOn (S10.Msigma M) E₁ := E1_actsPrime hG h hE1
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- `E₁`, `E₃` have coprime orders (τ₁ vs τ₃ disjoint, Hall subgroups).
  have hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hsN : s.Prime := hs
    have hsE1 : s ∈ (Nat.card E₁).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hsN, hsm, Nat.card_pos.ne'⟩
    have hsE3 : s ∈ (Nat.card E₃).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hsN, hsn, Nat.card_pos.ne'⟩
    have hc1 : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    have hc3 : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    exact not_mem_tau3_of_mem_tau1 (h.E₁_hall.1 s (hc1 ▸ hsE1)) (h.E₃_hall.1 s (hc3 ▸ hsE3))
  have hnorm : E₁ ≤ Subgroup.normalizer (E₃ : Set G) := h.E₁_le.trans (h.E3_normal hG)
  have hN3 : E₃ ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    (h.E₃_le.trans h.E_le).trans
      (by rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma M) M)
  have hD : fixedBy (S10.Msigma M) E₁ = fixedBy (S10.Msigma M) E₃ := by
    -- step 1: extract `P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)` with `R ≤ C(P)`.
    obtain ⟨p, r, hp, hr, P, R, hP, hPE1, hR, hRE3, hRcP⟩ :=
      exists_elemAbelian_centralizing_of_not_regular hreg
    have : Fact p.Prime := ⟨hp⟩
    have : Fact r.Prime := ⟨hr⟩
    have hPcardp : Nat.card P = p := by rw [← pow_one p]; exact hP.2
    have hRcardr : Nat.card R = r := by rw [← pow_one r]; exact hR.2
    have hc1 : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    have hpτ1 : p ∈ tau1 M := by
      have hpdvd : p ∣ Nat.card E₁ := hPcardp ▸ Subgroup.card_dvd_of_le hPE1
      exact h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩)
    have hrπE : r ∈ (Nat.card E).primeFactors := by
      have hrdvd : r ∣ Nat.card E := hRcardr ▸ Subgroup.card_dvd_of_le (hRE3.trans h.E₃_le)
      exact Nat.mem_primeFactors.mpr ⟨hr, hrdvd, Nat.card_pos.ne'⟩
    -- step 2: `C_N(E₁) = C_N(P) ≤ C_N(R) = C_N(E₃)` (Theorem 13.4 + prime actions).
    have hPeq : fixedBy (S10.Msigma M) P = fixedBy (S10.Msigma M) E₁ :=
      fixedBy_eq_of_elemAbelian_one hp hE1prime hP hPE1
    have hReq : fixedBy (S10.Msigma M) R = fixedBy (S10.Msigma M) E₃ :=
      fixedBy_eq_of_elemAbelian_one hr hE3prime hR hRE3
    have hle : fixedBy (S10.Msigma M) E₁ ≤ fixedBy (S10.Msigma M) E₃ := by
      rw [← hPeq, ← hReq, fixedBy_def, fixedBy_def]
      exact centralizer_le_centralizer_of_tau1 hG h hpτ1 hrπE hP (hPE1.trans h.E₁_le) hR
        (le_inf (hRE3.trans h.E₃_le) hRcP)
    -- step 5: rule out the strict containment.
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (strict_centralizer_config_false hG h hp hr hP hPE1 hR hRE3 hRcP hlt).elim
    · exact heq
  exact actsPrimeOn_sup_of_eq_centralizer hE1prime hE3prime hcop hnorm hN3 hD

end OddOrder.BG.Ch3.S13


