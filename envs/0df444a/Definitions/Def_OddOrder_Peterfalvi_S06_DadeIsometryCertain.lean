-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_DadeIsometryCertain
-- name    : OddOrder_Peterfalvi_S06_DadeIsometryCertain
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:43:45.678385+00:00
-- url     : https://prove2.me/theorems/c4a1f9bf-09ea-45bc-9442-25fb3029287c
-- title:
--   Peterfalvi §6: the Dade isometry for a certain type of subgroup
-- statement:
--   Formalizes Peterfalvi §6 (pp. 21–24), the Dade isometry for a certain type of subgroup. It contains Hypothesis (4.2) over an abstract group $L$: $L=K\rtimes W_1$ with $W_1\ne1$ a cyclic Hall complement, $W_2=C_K(x)$ cyclic for all $x\in W_1^\#$, and $W=W_1\times W_2$ of odd order, with its elementary structure theory (the join $W=W_1\sqcup W_2$ is abelian, components of elements, the Bézout projection), and the carrier structures for the Dade isometry.
--
--   Main definitions: `Hypothesis` (Peterfalvi Hypothesis (4.2)), `exists_mul_of_mem_sup`, `supMulEquiv` ($W=W_1\times W_2$ as an internal direct product), `toTICyclicHypothesisOfV`, `toTICyclicHypothesis` (Peterfalvi (4.3)(a): Hypothesis (3.1) holds) and `sdiffTICyclicHypothesis` (the TI-cyclic setup on the larger TI set $W-W_2$, (4.3.a)).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_DadeIsometryCertain.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_TICyclic

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

/-- Two elements of a cyclic subgroup commute.  (Generic; upstream candidate
`Subgroup.commute_of_mem_of_isCyclic`.) -/
theorem commute_of_mem_of_isCyclic {L : Type*} [Group L] {H : Subgroup L}
    (hH : IsCyclic H) {x y : L} (hx : x ∈ H) (hy : y ∈ H) : Commute x y := by
  have := hH
  have hcomm : (⟨x, hx⟩ : H) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (MonoidHom.id H)
      (fun z hz => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
        rw [hz]
        exact Subgroup.one_mem _)).is_comm.comm
      ⟨x, hx⟩ ⟨y, hy⟩
  exact Subtype.ext_iff.mp hcomm

/-- **Peterfalvi Hypothesis (4.2)** (mmd 04.6 L9-L13), over an abstract group `L`.

* (a) `L = K ⋊ W₁`: `K ⊴ L` with complement `W₁ ≠ 1`, cyclic and **Hall** — by the
  complement decomposition the index of `W₁` is `|K|`, so the Hall property is recorded
  as the coprimality `gcd(|K|, |W₁|) = 1` (`card_coprime`).
* (b) `W₂ ≠ 1` is a cyclic subgroup of `K` with `C_K(x) = W₂` for all `x ∈ W₁^#`.
* (c) `W = W₁ × W₂` is of odd order.  `W` is encoded as the join `W₁ ⊔ W₂`;
  `W₁ ⊓ W₂ = ⊥` is automatic (`W_disjoint`), the join is abelian
  (`isMulCommutative_sup`), and its elements decompose as products
  (`exists_mul_of_mem_sup`), so the join is the internal direct product `W₁ × W₂`.

The ambient group of the §6 results (4.3)-(4.5) is `L` itself; the `G`-embedded variant
used from §8 on is `CertainTypeHypothesis`, which extends this structure with a §4 Dade
datum. -/
structure Hypothesis (L : Type*) [Group L] where
  /-- The normal "kernel" subgroup `K` of `L = K ⋊ W₁`. -/
  K : Subgroup L
  W1 : Subgroup L
  W2 : Subgroup L
  K_normal : K.Normal
  /-- (4.2)(a): `L = K ⋊ W₁` — `W₁` is a complement to the normal subgroup `K`. -/
  isComplement : Subgroup.IsComplement' K W1
  /-- (4.2)(a): `W₁ ≠ 1` is cyclic. -/
  W1_nontrivial : W1 ≠ ⊥
  W1_cyclic : IsCyclic W1
  /-- (4.2)(a): `W₁` is a **Hall** subgroup of `L`: by the complement `L = K·W₁` the
  index of `W₁` is `|K|`, so Hall-ness is the coprimality of `|K|` and `|W₁|`. -/
  card_coprime : Nat.Coprime (Nat.card K) (Nat.card W1)
  /-- (4.2)(b): `W₂ ≠ 1` is a cyclic subgroup of `K`. -/
  W2_nontrivial : W2 ≠ ⊥
  W2_cyclic : IsCyclic W2
  W2_le_K : W2 ≤ K
  /-- (4.2)(b): `C_K(x) = W₂` for every `x ∈ W₁^#`. -/
  centralizer_W2 : ∀ x : L, x ∈ W1 → x ≠ 1 →
    Subgroup.centralizer ({x} : Set L) ⊓ K = W2
  /-- (4.2)(c): `W = W₁ × W₂` has odd order. -/
  W_odd : Odd (Nat.card ↥(W1 ⊔ W2))

namespace Hypothesis

variable {L : Type*} [Group L] (h : Hypothesis L)

/-- `W₁ ⊓ W₂ = ⊥`: automatic from the complement (`W₁ ⊓ K = ⊥`) and `W₂ ≤ K`. -/
theorem W_disjoint : Disjoint h.W1 h.W2 :=
  h.isComplement.disjoint.symm.mono_right h.W2_le_K

/-- (4.2)(b) elementwise: `W₂` centralizes `W₁`.  For `x ≠ 1` this is `W₂ ≤ C_K(x)` from
`centralizer_W2`; for `x = 1` it is trivial. -/
theorem commute_of_mem_W1_of_mem_W2 {x y : L} (hx : x ∈ h.W1) (hy : y ∈ h.W2) :
    Commute x y := by
  rcases eq_or_ne x 1 with rfl | hx1
  · exact Commute.one_left y
  · have hyc : y ∈ Subgroup.centralizer ({x} : Set L) ⊓ h.K := by
      rw [h.centralizer_W2 x hx hx1]; exact hy
    exact Subgroup.mem_centralizer_iff.mp hyc.1 x rfl

/-- The Hall coprimality (4.2.a) descends along `W₂ ≤ K`: `gcd(|W₁|, |W₂|) = 1`. -/
theorem coprime_card_W1_card_W2 : Nat.Coprime (Nat.card h.W1) (Nat.card h.W2) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h.W2_le_K)
    h.card_coprime.symm

/-- `W = W₁ ⊔ W₂` is abelian: `W₁` and `W₂` are abelian (cyclic) and centralize each
other (`commute_of_mem_W1_of_mem_W2`), so the closure of `↑W₁ ∪ ↑W₂` is abelian. -/
theorem isMulCommutative_sup : IsMulCommutative ↥(h.W1 ⊔ h.W2) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (commute_of_mem_of_isCyclic h.W1_cyclic hx hy).eq
  · exact (h.commute_of_mem_W1_of_mem_W2 hx hy).eq
  · exact ((h.commute_of_mem_W1_of_mem_W2 hy hx).symm).eq
  · exact (commute_of_mem_of_isCyclic h.W2_cyclic hx hy).eq

/-- `W₁` and `W₂`, viewed inside `W = W₁ ⊔ W₂`, intersect trivially. -/
theorem W1_subgroupOf_inf_W2_subgroupOf_eq_bot :
    h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊓ h.W2.subgroupOf (h.W1 ⊔ h.W2) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
  have hxbot : (x : L) ∈ h.W1 ⊓ h.W2 := hx
  rw [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

/-- `W₁` and `W₂`, viewed inside `W = W₁ ⊔ W₂`, generate it. -/
theorem W1_subgroupOf_sup_W2_subgroupOf_eq_top :
    h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊔ h.W2.subgroupOf (h.W1 ⊔ h.W2) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

open scoped IsMulCommutative in
/-- Every element of `W = W₁ ⊔ W₂` is a product `x·y` with `x ∈ W₁`, `y ∈ W₂` (the join
is abelian, so it is the internal product of `W₁` and `W₂`). -/
theorem exists_mul_of_mem_sup {w : L} (hw : w ∈ h.W1 ⊔ h.W2) :
    ∃ x ∈ h.W1, ∃ y ∈ h.W2, x * y = w := by
  have := h.isMulCommutative_sup
  have hmem : (⟨w, hw⟩ : ↥(h.W1 ⊔ h.W2)) ∈
      h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊔ h.W2.subgroupOf (h.W1 ⊔ h.W2) := by
    rw [h.W1_subgroupOf_sup_W2_subgroupOf_eq_top]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem
  rw [Subgroup.mem_subgroupOf] at hx hy
  exact ⟨x, hx, y, hy, Subtype.ext_iff.mp hxy⟩

/-- A uniform integer exponent projecting products onto their `W₁`-component: there is
`n` with `(x·y)^n = x` for all `x ∈ W₁`, `y ∈ W₂`.  Bézout for `gcd(|W₁|, |W₂|) = 1`
gives `n ≡ 1 mod |W₁|` and `n ≡ 0 mod |W₂|`, and commutation
(`commute_of_mem_W1_of_mem_W2`) splits the power.  This recovers the `W₁`-component of
an element of `W` intrinsically — in particular compatibly with conjugation — which is
the engine of the TI argument in (4.3.a). -/
theorem exists_zpow_proj :
    ∃ n : ℤ, ∀ x ∈ h.W1, ∀ y ∈ h.W2, (x * y) ^ n = x := by
  set c₁ := Nat.card h.W1 with hc₁
  set c₂ := Nat.card h.W2 with hc₂
  have hbez : (c₁ : ℤ) * Nat.gcdA c₁ c₂ + c₂ * Nat.gcdB c₁ c₂ = 1 := by
    have hg := Nat.gcd_eq_gcd_ab c₁ c₂
    have h1 : Nat.gcd c₁ c₂ = 1 := h.coprime_card_W1_card_W2
    rw [h1] at hg
    exact_mod_cast hg.symm
  refine ⟨(c₂ : ℤ) * Nat.gcdB c₁ c₂, fun x hx y hy => ?_⟩
  have hcomm := h.commute_of_mem_W1_of_mem_W2 hx hy
  have hx1 : x ^ (c₁ : ℤ) = 1 := by
    rw [zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hx)
  have hy1 : y ^ (c₂ : ℤ) = 1 := by
    rw [zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hy)
  rw [hcomm.mul_zpow]
  have hyn : y ^ ((c₂ : ℤ) * Nat.gcdB c₁ c₂) = 1 := by
    rw [zpow_mul, hy1, one_zpow]
  have hxn : x ^ ((c₂ : ℤ) * Nat.gcdB c₁ c₂) = x := by
    have hn : (c₂ : ℤ) * Nat.gcdB c₁ c₂ = 1 - c₁ * Nat.gcdA c₁ c₂ := by
      linarith [hbez]
    rw [hn, zpow_sub, zpow_one, zpow_mul, hx1, one_zpow, inv_one, mul_one]
  rw [hxn, hyn, mul_one]

/-- **Peterfalvi (4.3)(a), centralizer form** (mmd 04.6 proof L25): for `x ∈ W₁^#`,
`C_L(x) = W = W₁ ⊔ W₂`.  `⊇`: `W₁` is abelian and `W₂` centralizes `W₁` (4.2.b).  `⊆`:
write `c = k·u` with `k ∈ K`, `u ∈ W₁` (complement); conjugation by `c` fixes `x` and
`u` commutes with `x` (`W₁` abelian), so `k ∈ C_K(x) = W₂` (4.2.b) and
`c = k·u ∈ W₂·W₁ ⊆ W`. -/
theorem centralizer_eq_sup {x : L} (hx : x ∈ h.W1) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set L) = h.W1 ⊔ h.W2 := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro c hc
    obtain ⟨⟨⟨kk, hk⟩, ⟨u, hu⟩⟩, hku, -⟩ :=
      Subgroup.IsComplement.existsUnique h.isComplement c
    change kk * u = c at hku
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x rfl
    have hxu : Commute x u := commute_of_mem_of_isCyclic h.W1_cyclic hx hu
    have hxk : x * kk = kk * x := by
      have h1 : x * kk * u = kk * x * u := by
        calc x * kk * u = x * (kk * u) := by rw [mul_assoc]
          _ = (kk * u) * x := by rw [hku]; exact hxc
          _ = kk * (u * x) := by rw [mul_assoc]
          _ = kk * (x * u) := by rw [← hxu.eq]
          _ = kk * x * u := by rw [← mul_assoc]
      exact mul_right_cancel h1
    have hkW2 : kk ∈ h.W2 := by
      have hkc : kk ∈ Subgroup.centralizer ({x} : Set L) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hxk
      rw [← h.centralizer_W2 x hx hx1]
      exact Subgroup.mem_inf.mpr ⟨hkc, hk⟩
    rw [← hku]
    exact Subgroup.mul_mem _ ((le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2) hkW2)
      ((le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hu)
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (commute_of_mem_of_isCyclic h.W1_cyclic hx hw).eq
  · intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (h.commute_of_mem_W1_of_mem_W2 hx hw).eq

/-- **Peterfalvi (4.3)(a), TI part** (mmd 04.6 L17, proof L25): `W − W₂` is a TI-subset
of `L` relative to `W = W₁ ⊔ W₂`.  For `g ∈ L` and `a = x·y ∈ W − W₂` (`x ∈ W₁^#`,
`y ∈ W₂`) with `g·a·g⁻¹ ∈ W − W₂`: the Bézout projection (`exists_zpow_proj`) recovers
`x = a^n` and shows `g·x·g⁻¹ = (g·a·g⁻¹)^n ∈ W₁`; writing `g = k·u` (complement) and
using that `W₁` is abelian and `K ⊴ L`, the commutator `g·x·g⁻¹·x⁻¹` lies in
`K ⊓ W₁ = ⊥` (this is the textbook step `x^g ∈ Kx ∩ W₁ = {x}` since `L/K` is abelian),
so `g` centralizes `x` and `g ∈ C_L(x) = W` (`centralizer_eq_sup`). -/
theorem isTISubset_sup_sdiff :
    OddOrder.GroupTheory.IsTISubset
      ((↑(h.W1 ⊔ h.W2) : Set L) \ ↑h.W2) (h.W1 ⊔ h.W2) := by
  obtain ⟨n, hn⟩ := h.exists_zpow_proj
  rintro g ⟨a, ha, hga⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_of_mem_sup ha.1
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact ha.2 (by rw [← hxy, one_mul]; exact hy)
  have hxa : a ^ n = x := by rw [← hxy]; exact hn x hx y hy
  obtain ⟨x', hx', y', hy', hxy'⟩ := h.exists_mul_of_mem_sup hga.1
  have hxa' : (g * a * g⁻¹) ^ n = x' := by rw [← hxy']; exact hn x' hx' y' hy'
  have hgx : g * x * g⁻¹ = x' := by
    rw [← hxa, ← hxa']
    have hmz := map_zpow (MulAut.conj g) a n
    simp only [MulAut.conj_apply] at hmz
    exact hmz
  obtain ⟨⟨⟨kk, hk⟩, ⟨u, hu⟩⟩, hku, -⟩ :=
    Subgroup.IsComplement.existsUnique h.isComplement g
  change kk * u = g at hku
  have hux : u * x * u⁻¹ = x := by
    have hc := commute_of_mem_of_isCyclic h.W1_cyclic hu hx
    rw [hc.eq]
    exact mul_inv_cancel_right x u
  have hkappaK : g * x * g⁻¹ * x⁻¹ ∈ h.K := by
    have hexp : g * x * g⁻¹ * x⁻¹ = kk * (u * x * u⁻¹) * kk⁻¹ * x⁻¹ := by
      rw [← hku]; group
    rw [hexp, hux]
    have hexp2 : kk * x * kk⁻¹ * x⁻¹ = kk * (x * kk⁻¹ * x⁻¹) := by group
    rw [hexp2]
    exact Subgroup.mul_mem _ hk (h.K_normal.conj_mem _ (Subgroup.inv_mem _ hk) x)
  have hkappaW1 : g * x * g⁻¹ * x⁻¹ ∈ h.W1 := by
    rw [hgx]
    exact Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ hx)
  have hgxx : g * x * g⁻¹ = x := by
    have hbot : g * x * g⁻¹ * x⁻¹ ∈ h.K ⊓ h.W1 := ⟨hkappaK, hkappaW1⟩
    rw [disjoint_iff.mp h.isComplement.disjoint, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp hbot
  have hgc : g ∈ Subgroup.centralizer ({x} : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    calc x * g = (g * x * g⁻¹) * g := by rw [hgxx]
      _ = g * x := by group
  rw [h.centralizer_eq_sup hx hx1] at hgc
  exact hgc

open scoped IsMulCommutative in
/-- `W = W₁ × W₂` as an internal direct product: multiplication is a group isomorphism
from the product of the `subgroupOf` copies onto `W = W₁ ⊔ W₂` (mirror of
`TICyclicHypothesis.wProdEquiv` at the (4.2) level — available *before* the
TI-cyclic hypothesis for `L` is assembled, and used to count `|W| = |W₁|·|W₂|`). -/
noncomputable def supMulEquiv :
    (h.W1.subgroupOf (h.W1 ⊔ h.W2)) × (h.W2.subgroupOf (h.W1 ⊔ h.W2)) ≃*
      ↥(h.W1 ⊔ h.W2) :=
  haveI := h.isMulCommutative_sup
  MulEquiv.ofBijective
    (MonoidHom.coprod (h.W1.subgroupOf (h.W1 ⊔ h.W2)).subtype
      (h.W2.subgroupOf (h.W1 ⊔ h.W2)).subtype) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype] at hab
      have hain : (a : ↥(h.W1 ⊔ h.W2)) ∈
          h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊓ h.W2.subgroupOf (h.W1 ⊔ h.W2) := by
        refine ⟨a.2, ?_⟩
        have hinv : (a : ↥(h.W1 ⊔ h.W2)) = ((b : ↥(h.W1 ⊔ h.W2)))⁻¹ :=
          mul_eq_one_iff_eq_inv.mp hab
        rw [hinv]
        exact (h.W2.subgroupOf (h.W1 ⊔ h.W2)).inv_mem b.2
      rw [h.W1_subgroupOf_inf_W2_subgroupOf_eq_bot, Subgroup.mem_bot] at hain
      have hb1 : (b : ↥(h.W1 ⊔ h.W2)) = 1 := by rw [hain, one_mul] at hab; exact hab
      exact Prod.ext (Subtype.ext hain) (Subtype.ext hb1)
    · intro w
      have hw : w ∈ h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊔ h.W2.subgroupOf (h.W1 ⊔ h.W2) := by
        rw [h.W1_subgroupOf_sup_W2_subgroupOf_eq_top]
        exact Subgroup.mem_top w
      rw [Subgroup.mem_sup] at hw
      obtain ⟨x, hx, y, hy, hxy⟩ := hw
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype]
      exact hxy

/-- The order count `|W| = |W₁| · |W₂|` for `W = W₁ ⊔ W₂`, via `supMulEquiv`. -/
theorem card_sup_eq_mul :
    Nat.card ↥(h.W1 ⊔ h.W2) = Nat.card h.W1 * Nat.card h.W2 :=
  calc Nat.card ↥(h.W1 ⊔ h.W2)
      = Nat.card ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) ×
          (h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
        (Nat.card_congr h.supMulEquiv.toEquiv).symm
    _ = Nat.card (h.W1.subgroupOf (h.W1 ⊔ h.W2)) *
          Nat.card (h.W2.subgroupOf (h.W1 ⊔ h.W2)) := Nat.card_prod _ _
    _ = Nat.card h.W1 * Nat.card h.W2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2)).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv]

/-- **Peterfalvi (4.2)(c)/(3.1) cyclicity**: `W = W₁ ⊔ W₂` is cyclic — it is the
internal direct product of the cyclic groups `W₁`, `W₂` of coprime orders, so the
product of two generators has order `|W₁|·|W₂| = |W|` (`card_sup_eq_mul`). -/
theorem isCyclic_sup [Finite L] : IsCyclic ↥(h.W1 ⊔ h.W2) := by
  have hc1 := h.W1_cyclic
  have hc2 := h.W2_cyclic
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥h.W1)
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := ↥h.W2)
  have hoa : orderOf (Subgroup.inclusion (le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) a) =
      Nat.card h.W1 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective _) a,
      orderOf_eq_card_of_forall_mem_zpowers ha]
  have hob : orderOf (Subgroup.inclusion (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2) b) =
      Nat.card h.W2 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective _) b,
      orderOf_eq_card_of_forall_mem_zpowers hb]
  have hcomm : Commute (Subgroup.inclusion (le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) a)
      (Subgroup.inclusion (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2) b) :=
    Subtype.ext (h.commute_of_mem_W1_of_mem_W2 a.2 b.2)
  refine isCyclic_of_orderOf_eq_card
    (Subgroup.inclusion (le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) a *
      Subgroup.inclusion (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2) b) ?_
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hoa, hob]; exact h.coprime_card_W1_card_W2),
    hoa, hob, h.card_sup_eq_mul]

open scoped IsMulCommutative in
/-- Build a TI-cyclic normalizer setup (Peterfalvi (3.1) data) on `W = W₁ ⊔ W₂` inside
`L` from any TI subset `V ⊆ W` avoiding `1`.  Because `W` is abelian
(`isMulCommutative_sup`), `W` normalizes every subset of itself, so only `1 ∉ V`,
`V ⊆ W` and the TI property vary between the §6 instantiations (the
`TICyclicHypothesis.V` field was deliberately kept free for exactly this reuse). -/
noncomputable def toTICyclicHypothesisOfV [Fintype L] (V : Set L)
    (hV1 : (1 : L) ∉ V) (hVW : V ⊆ ↑(h.W1 ⊔ h.W2))
    (hti : OddOrder.GroupTheory.IsTISubset V (h.W1 ⊔ h.W2)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis L where
  W := h.W1 ⊔ h.W2
  W1 := h.W1
  W2 := h.W2
  W1_le_W := le_sup_left
  W2_le_W := le_sup_right
  W1_nontrivial := h.W1_nontrivial
  W2_nontrivial := h.W2_nontrivial
  W_sup := rfl
  W_disjoint := h.W_disjoint
  W_card_coprime := h.coprime_card_W1_card_W2
  W_card_odd := h.W_odd
  W_cyclic := h.isCyclic_sup
  V := V
  V_subset_sharp := fun v hv => by
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    exact ⟨Set.mem_univ v, fun heq => hV1 (heq ▸ hv)⟩
  V_subset_W := hVW
  W_normalizes_V := by
    intro w v hv
    have := h.isMulCommutative_sup
    have h1 : (⟨v, hVW hv⟩ : ↥(h.W1 ⊔ h.W2)) * w = w * ⟨v, hVW hv⟩ := mul_comm _ _
    have h2 : (w : L) * v = v * (w : L) := (Subtype.ext_iff.mp h1).symm
    have h3 : (w : L) * v * (w : L)⁻¹ = v := by
      rw [h2]
      exact mul_inv_cancel_right v w
    rw [h3]
    exact hv
  V_ti := hti

/-- **Peterfalvi (4.3)(a), second half** (mmd 04.6 L17): Hypothesis (3.1) holds with
`L` in place of `G` — `W = W₁ ⊔ W₂` with `V = W − (W₁ ∪ W₂)` is a TI-cyclic
normalizer setup inside `L`.  The TI property of `V` follows from that of the larger
set `W − W₂` (`isTISubset_sup_sdiff` + `IsTISubset.subset`).  Through this
constructor the entire §5 σ-machinery ((3.2)-(3.9), `S05_SigmaIsometry`) applies
with `L` as the ambient group, as required by (4.3.b). -/
noncomputable def toTICyclicHypothesis [Fintype L] :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis L :=
  h.toTICyclicHypothesisOfV ((↑(h.W1 ⊔ h.W2) : Set L) \ (↑h.W1 ∪ ↑h.W2))
    (fun hmem => hmem.2 (Or.inl (Subgroup.one_mem h.W1)))
    (fun _ hv => hv.1)
    (h.isTISubset_sup_sdiff.subset
      (fun _ hv => ⟨hv.1, fun h2 => hv.2 (Or.inr h2)⟩))

/-- The TI-cyclic setup on the **larger** TI set `W − W₂` (4.3.a), used by (4.3.b) for
the induction isometry on `CF(W, W − W₂)` (the `ω_{ij} − ω_{0j}` live there, not in
`CF(W, V)`). -/
noncomputable def sdiffTICyclicHypothesis [Fintype L] :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis L :=
  h.toTICyclicHypothesisOfV ((↑(h.W1 ⊔ h.W2) : Set L) \ ↑h.W2)
    (fun hmem => hmem.2 (Subgroup.one_mem h.W2))
    (fun _ hv => hv.1)
    h.isTISubset_sup_sdiff

/-- The §4 Dade hypothesis (2.2) on `(L, W − W₂, W)` from (4.3.a), with the supported
set and normalizer stated in syntactic `W₁ ⊔ W₂` form (definitionally
`h.sdiffTICyclicHypothesis.toDadeHypothesis`, restated so that instance arguments
about `↥(W₁ ⊔ W₂)` resolve at use sites).  All its local subgroups are trivial,
`H(a) = ⊥`. -/
noncomputable def sdiffDadeHypothesis [Fintype L] :
    OddOrder.Peterfalvi.S04.Hypothesis L
      ((↑(h.W1 ⊔ h.W2) : Set L) \ ↑h.W2) (h.W1 ⊔ h.W2) :=
  h.sdiffTICyclicHypothesis.toDadeHypothesis

/-- **"`Ind_W^L` is an isometry on `CF(W, W − W₂)`"** (textbook (4.3) proof step,
mmd 04.6 L25): the §4 Dade isometry package — Theorem (2.6) — for the TI set
`W − W₂` of (4.3.a).  Its underlying Dade map *is* induction `Ind_W^L`
(`TICyclicHypothesis.tau_eq_induce`), it preserves inner products (`inner_eq`) and
virtual characters (`maps_virtualCharacter`), which is what (4.3.b) feeds into the
(1.4) difference machinery.  The `L`-equivariance input is automatic because all the
local subgroups `H(a)` of the TI-derived Dade hypothesis are trivial. -/
noncomputable def sdiffFullDadeIsometryData [Fintype L]
    [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] :
    OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := L) h.sdiffDadeHypothesis :=
  h.sdiffDadeHypothesis.fullDadeIsometryData

end Hypothesis

section CertainType

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G}

/-- The structural hypotheses used by Peterfalvi §6 before the concrete
character calculations begin, embedded in an ambient group `G`: the abstract
Hypothesis (4.2) for the subgroup `↥L` (fields `K`, `W1`, `W2`, … of the parent
`Hypothesis ↥L`), together with the §4 Dade datum on `(G, A, L)` that maps
class functions of `L` into `G`. -/
structure CertainTypeHypothesis (A : Set G) (L : Subgroup G) extends
    Hypothesis ↥L where
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A L

namespace CertainTypeHypothesis

variable {k : Type*} [CommRing k] [StarRing k]

variable [Fintype L] [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- A §6 application package: the structural §6 hypothesis plus a Dade map
known to satisfy the §4 pointwise and isometry interfaces. -/
structure DadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) = tau.toDadeMap :=
  rfl

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- A complex §6 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) = tau.toDadeMap :=
  rfl

end CertainTypeHypothesis

end CertainType

end OddOrder.Peterfalvi.S06


