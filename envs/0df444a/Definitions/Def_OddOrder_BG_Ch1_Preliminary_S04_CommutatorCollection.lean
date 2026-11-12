-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_CommutatorCollection
-- name    : OddOrder_BG_Ch1_Preliminary_S04_CommutatorCollection
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:44:58.917934+00:00
-- url     : https://prove2.me/theorems/0dd76c3f-df22-4ac9-9f5e-6b8d357312bc
-- title:
--   BG §4A: commutator collection and $\Omega_1$ exponent under small class (Lemma 4.2, Prop 4.3)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §4A: commutator and power identities with a central commutator (Lemma 4.2), the iterated collection formula (4.4) under class at most 3, and the $\Omega_1$ exponent facts of Proposition 4.3(a)(b).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 21 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04_CommutatorCollection.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_Representations
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_GroupTheory_IsMetacyclic
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_SCN
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

/-- **BG Theorem 2.6(b) の導来部分群形** (Blackburn 4.16 / Lemma 4.17 の `m(V)=2`
分岐エンジン, Cor 4.19 のエンジン).

奇数位数の有限群 `G` が標数 `p`(`p ∣ |G|`)の体 `F` 上で `2` 次元の faithful な
表現 `ρ` を持つとき, 導来部分群 `G'` (`commutator G`) は `p`-群である。

BG 原文では Lemma 4.17 (mmd L1732) と Cor 4.19 (mmd L1758) で
「`Aut V ≅ GL(2,p)` (resp. faithful irreducible on `U/V`) ゆえ Theorem 2.6 により
`(A/C)'` (resp. `(G/C)'`) は `p`-群」と一言で済ませる部分にあたる。

証明: Thm 2.6(b) (`odd_two_dim_sylow_abelian`) より, `p`-Sylow `P` は abelian で
`G' ≤ P` を満たす。`P` は `p`-群 (`Sylow.isPGroup'`) なので, その部分群
`G'` も `p`-群 (`IsPGroup.to_le`)。`Finite (Sylow p G)` は有限群から従う。 -/
theorem isPGroup_commutator_of_faithful_two_dim_charP
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hdim : Module.finrank F V = 2) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp_dvd : p ∣ Nat.card G) (hchar : CharP F p) :
    IsPGroup p (commutator G) := by
  -- 標準的な `p`-Sylow を取り Thm 2.6(b) を適用する。
  let P : Sylow p G := default
  obtain ⟨_hPab, hcomm_le⟩ :=
    odd_two_dim_sylow_abelian hodd hdim ρ hfaithful hp_dvd hchar P
  -- `P` は `p`-群, ゆえに `G' ≤ P` も `p`-群。
  exact P.isPGroup'.to_le hcomm_le

section CommutatorPowerIdentities

open scoped commutatorElement

variable {K : Type*} [Group K]

/-- Conjugation collection with a central commutator: if `z := ⁅x, y⁆` is central,
then `x ^ n * y * x⁻¹ ^ n = ⁅x, y⁆ ^ n * y`.

This is the engine for Lemma 4.2(a). Proof by induction using the base relation
`x * y * x⁻¹ = ⁅x, y⁆ * y` (immediate from `commutatorElement_def`) and centrality
of `z`. -/
private theorem conj_pow_eq_commutator_pow_mul_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    x ^ n * y * (x⁻¹) ^ n = ⁅x, y⁆ ^ n * y := by
  -- Base relation `x * y * x⁻¹ = z * y`, then treat `z = ⁅x, y⁆` as an opaque atom.
  have hbase : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have hcomm_x : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hz x
  set z := ⁅x, y⁆ with hz_def
  induction n with
  | zero => simp
  | succ k ih =>
    -- `x` commutes with `z ^ k`.
    have hxk : x * z ^ k = z ^ k * x := (hcomm_x.pow_right k).eq
    calc x ^ (k + 1) * y * (x⁻¹) ^ (k + 1)
        = x * (x ^ k * y * (x⁻¹) ^ k) * x⁻¹ := by
          rw [pow_succ', pow_succ]; simp only [mul_assoc]
      _ = x * (z ^ k * y) * x⁻¹ := by rw [ih]
      _ = (x * z ^ k) * (y * x⁻¹) := by rw [mul_assoc, mul_assoc, mul_assoc]
      _ = (z ^ k * x) * (y * x⁻¹) := by rw [hxk]
      _ = z ^ k * (x * y * x⁻¹) := by rw [mul_assoc, mul_assoc]
      _ = z ^ k * (z * y) := by rw [hbase]
      _ = z ^ (k + 1) * y := by rw [pow_succ]; rw [mul_assoc]

/-- **BG Lemma 4.2(a)**, left slot. If `⁅x, y⁆` is central then
`⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n` for all `n`.

Proof: `⁅x ^ n, y⁆ = x ^ n * y * x⁻¹ ^ n * y⁻¹ = ⁅x, y⁆ ^ n * y * y⁻¹ = ⁅x, y⁆ ^ n`
using `conj_pow_eq_commutator_pow_mul_of_central`. -/
theorem commutatorElement_pow_left_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  rw [commutatorElement_def, ← inv_pow, mul_assoc (x ^ n) y,
    show x ^ n * (y * (x⁻¹) ^ n) = x ^ n * y * (x⁻¹) ^ n by group,
    conj_pow_eq_commutator_pow_mul_of_central hz n]
  group

/-- **BG Lemma 4.2(a)**, right slot. If `⁅x, y⁆` is central then
`⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n` for all `n`.

Proof: pass to inverse commutators. `⁅x, y⁆⁻¹ = ⁅y, x⁆` (`commutatorElement_inv`),
which is also central, so `⁅y ^ n, x⁆ = ⁅y, x⁆ ^ n` by the left-slot version; invert
both sides and use `⁅y, x⁆⁻¹ = ⁅x, y⁆`. -/
theorem commutatorElement_pow_right_of_central {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  -- `⁅y, x⁆ = ⁅x, y⁆⁻¹` is central.
  have hz' : ⁅y, x⁆ ∈ Subgroup.center K := by
    rw [← commutatorElement_inv]; exact (Subgroup.center K).inv_mem hz
  have h := commutatorElement_pow_left_of_central hz' n
  -- `⁅x, y^n⁆ = ⁅y^n, x⁆⁻¹ = (⁅y, x⁆ ^ n)⁻¹ = (⁅x, y⁆⁻¹ ^ n)⁻¹ = ⁅x, y⁆ ^ n`.
  rw [← commutatorElement_inv, h, ← commutatorElement_inv, inv_pow, inv_inv]

end CommutatorPowerIdentities

section Prop43ClassThreeCollection

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Drop a central right factor inside a commutator's right slot: `⁅u, A * z⁆ = ⁅u, A⁆`
when `z` is central.

Used to discard the central correction term produced by the inductive expansion of
`⁅u ^ n, w⁆` before iterating the right slot. -/
private theorem commutatorElement_right_mul_central {u A z : G}
    (hz : z ∈ Subgroup.center G) : ⁅u, A * z⁆ = ⁅u, A⁆ := by
  simp only [commutatorElement_def]
  have hc : ∀ g : G, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  rw [mul_inv_rev]
  calc u * (A * z) * u⁻¹ * (z⁻¹ * A⁻¹)
      = u * A * (z * u⁻¹) * (z⁻¹ * A⁻¹) := by group
    _ = u * A * (u⁻¹ * z) * (z⁻¹ * A⁻¹) := by rw [hc u⁻¹]
    _ = u * A * u⁻¹ * A⁻¹ := by group

/-- Collect a central element to the right: `z ^ m * (a * z ^ j) * b = a * b * z ^ (j + m)`
when `z` is central.

The accumulation step for the `n.choose 2` exponent in the iterated commutator power
law: after the inductive step exposes `z ^ k` (with `k = (k.choose 2)`-th batch) and a
fresh `z ^ (k.choose 2)`, this merges them on the right past the non-central `a`, `b`. -/
private theorem mul_central_pow_collect (z a b : G) (hz : ∀ g : G, Commute z g)
    (m j : ℕ) : z ^ m * (a * z ^ j) * b = a * b * z ^ (j + m) := by
  have hzk : ∀ (i : ℕ) (g : G), Commute (z ^ i) g := fun i g => (hz g).pow_left i
  have hblock : Commute (z ^ j * z ^ m) b := (hzk j b).mul_left (hzk m b)
  have h1 : z ^ m * (a * z ^ j) = a * (z ^ j * z ^ m) := by
    rw [(hzk m (a * z ^ j)).eq, mul_assoc]
  rw [h1, mul_assoc a, hblock.eq, ← mul_assoc, pow_add]

/-- **BG Proposition 4.3(a), `(4.4)`-precursor: iterated commutator power law under
`cl ≤ 3`.** If `γ₃(G) = ⁅⁅G,G⁆,G⁆ ⊆ Z(G)` (here `hc3 : ∀ a b c, ⁅⁅a, b⁆, c⁆ ∈ Z(G)`),
then for all `u w : G` and `n : ℕ`,
`⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n * ⁅u, ⁅u, w⁆⁆ ^ (n.choose 2)`.

This is BG's `[u^n, w] = [u, w]^n · [u, w, u]^{C(n,2)}` in mathlib's commutator
convention `⁅a, b⁆ = a b a⁻¹ b⁻¹`; the correction commutator is
`⁅u, ⁅u, w⁆⁆ = ⁅⁅u, w⁆, u⁆⁻¹`, a `γ₃`-element, hence central, so the positive exponent
`n.choose 2` is recorded directly.

Proof: induction on `n`. The product rule
`⁅u ^ (k+1), w⁆ = ⁅u, ⁅u ^ k, w⁆⁆ · ⁅u ^ k, w⁆ · ⁅u, w⁆` (`group` after `commutatorElement_def`)
exposes a `⁅u, ⁅u ^ k, w⁆⁆`; substitute the inductive hypothesis, drop the central
correction factor inside its right slot (`commutatorElement_right_mul_central`),
iterate the right slot via the central-commutator law
`commutatorElement_pow_right_of_central` (Lemma 4.2(a), REUSED), and merge the central
powers (`mul_central_pow_collect`); the exponent satisfies
`(k+1).choose 2 = k.choose 2 + k` (`Nat.choose_succ_succ'`).

This is the genuine class-`3` analogue of Lemma 4.2(a)
(`commutatorElement_pow_left_of_central`, which needs `⁅u, w⁆` central) and the
class-`3` sibling of the repo's class-`≤ 2` collection
`OddOrder.GroupTheory.mul_pow_eq_commutator_pow_mul_of_class_le_two`. -/
theorem commutatorElement_pow_left_of_triple_central
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G) (u w : G) (n : ℕ) :
    ⁅u ^ n, w⁆ = ⁅u, w⁆ ^ n * ⁅u, ⁅u, w⁆⁆ ^ (n.choose 2) := by
  set d := ⁅u, ⁅u, w⁆⁆ with hd_def
  -- `d = ⁅u, ⁅u, w⁆⁆ = ⁅⁅u, w⁆, u⁆⁻¹` is a `γ₃`-element, hence central.
  have hd_cen : d ∈ Subgroup.center G := by
    rw [hd_def, ← commutatorElement_inv]; exact (Subgroup.center G).inv_mem (hc3 u w u)
  have hd_comm : ∀ g : G, Commute d g := fun g => (Subgroup.mem_center_iff.mp hd_cen g).symm
  induction n with
  | zero => simp
  | succ k ih =>
    -- Product rule for the left slot, pure group identity.
    have hbase : ⁅u ^ (k + 1), w⁆ = ⁅u, ⁅u ^ k, w⁆⁆ * ⁅u ^ k, w⁆ * ⁅u, w⁆ := by
      rw [pow_succ' u k]; simp only [commutatorElement_def]; group
    have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
    rw [hbase, ih,
        commutatorElement_right_mul_central
          (u := u) (A := ⁅u, w⁆ ^ k) (z := d ^ (k.choose 2))
          ((Subgroup.center G).pow_mem hd_cen _),
        commutatorElement_pow_right_of_central hd_cen k,
        hchoose, pow_succ ⁅u, w⁆ k]
    exact mul_central_pow_collect d (⁅u, w⁆ ^ k) ⁅u, w⁆ hd_comm k (k.choose 2)

/-- Bridge identity feeding the `(u*v)^n` collection induction: `v ^ k * u` exposes a
single left-slot commutator power, `v ^ k * u = ⁅v ^ k, u⁆ * u * v ^ k`.

Combined with `commutatorElement_pow_left_of_triple_central` (roles `v, u`) this yields
`v ^ k * u = ⁅v, u⁆ ^ k * ⁅v, ⁅v, u⁆⁆ ^ (k.choose 2) * u * v ^ k`, the step that moves a
block of `v`'s past a `u` during collection. -/
theorem pow_mul_eq_commutator_mul (u v : G) (k : ℕ) :
    v ^ k * u = ⁅v ^ k, u⁆ * u * v ^ k := by
  rw [commutatorElement_def]; group

/-- The weight-`3` commutator `⁅⁅v, u⁆, w⁆` is central under `γ₄(G) = 1`: indeed
`⁅⁅⁅v, u⁆, w⁆, g⁆ = 1` for every `g` (`hc4`). -/
private theorem triple_commutator_mem_center
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) :
    ⁅⁅v, u⁆, w⁆ ∈ Subgroup.center G :=
  Subgroup.mem_center_iff.2 fun g =>
    ((commutatorElement_eq_one_iff_commute.1 (hc4 v u w g)).symm).eq

/-- Move a power of the (non-central) commutator `c := ⁅v, u⁆` past a single element `w`,
picking up a central correction: `c ^ m * w = w * c ^ m * ⁅⁅v, u⁆, w⁆ ^ m`.

Only the centrality of `⁅⁅v, u⁆, w⁆ = ⁅c, w⁆` (from `hc4`) is needed: write
`c ^ m * w = ⁅c ^ m, w⁆ * w * c ^ m` (`pow_mul_eq_commutator_mul`) and
`⁅c ^ m, w⁆ = ⁅c, w⁆ ^ m` (`commutatorElement_pow_left_of_central`, since `⁅c, w⁆` is
central), then move the central correction to the right. With `w = u` this gives the
`d₁`-motion and with `w = v` the `d₂`-motion of BG's collection. -/
private theorem commutator_pow_mul_collect
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) (m : ℕ) :
    ⁅v, u⁆ ^ m * w = w * ⁅v, u⁆ ^ m * ⁅⁅v, u⁆, w⁆ ^ m := by
  have hcen := triple_commutator_mem_center hc4 u v w
  -- `⁅⁅v, u⁆, w⁆` central ⇒ commutes with everything, in particular `w` and `c = ⁅v, u⁆`.
  have hcd : ∀ g : G, Commute (⁅⁅v, u⁆, w⁆ ^ m) g :=
    fun g => (show Commute ⁅⁅v, u⁆, w⁆ g from (Subgroup.mem_center_iff.mp hcen g).symm).pow_left m
  rw [pow_mul_eq_commutator_mul w ⁅v, u⁆ m, commutatorElement_pow_left_of_central hcen m]
  -- Goal: `⁅..⁆^m * w * c^m = w * c^m * ⁅..⁆^m`; move the central correction to the right.
  rw [(hcd w).eq, mul_assoc, (hcd (⁅v, u⁆ ^ m)).eq, ← mul_assoc]

/-- Iterated form: move `c ^ k = ⁅v, u⁆ ^ k` past a *power* `w ^ j`,
`c ^ k * w ^ j = w ^ j * c ^ k * ⁅⁅v, u⁆, w⁆ ^ (k * j)`.

The commutator `⁅c ^ k, w ^ j⁆` collects to `⁅c, w⁆ ^ (k * j) = ⁅⁅v, u⁆, w⁆ ^ (k * j)` by the
central-commutator power laws (`commutatorElement_pow_left_of_central` then
`commutatorElement_pow_right_of_central`, both valid since `⁅⁅v, u⁆, w⁆` is central under
`hc4`); unfolding `⁅c ^ k, w ^ j⁆ = c^k w^j (c^k)⁻¹ (w^j)⁻¹` and moving the (central)
correction across gives the claim. Used to move the `c ^ k` block past `v ^ (k+1)`. -/
private theorem commutator_pow_mul_pow_collect
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v w : G) (k j : ℕ) :
    ⁅v, u⁆ ^ k * w ^ j = w ^ j * ⁅v, u⁆ ^ k * ⁅⁅v, u⁆, w⁆ ^ (k * j) := by
  have hcen := triple_commutator_mem_center hc4 u v w
  have hcomm : ∀ g : G, Commute ⁅⁅v, u⁆, w⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp hcen g).symm
  -- `⁅c, w^j⁆ = ⁅c, w⁆^j` is central, so the left slot collects too.
  have hcenj : ⁅⁅v, u⁆, w ^ j⁆ ∈ Subgroup.center G :=
    (commutatorElement_pow_right_of_central hcen j).symm ▸ (Subgroup.center G).pow_mem hcen j
  -- `⁅c^k, w^j⁆ = ⁅c, w^j⁆^k = (⁅c, w⁆^j)^k = ⁅⁅v,u⁆,w⁆^(k*j)`.
  have hcomm_collect : ⁅⁅v, u⁆ ^ k, w ^ j⁆ = ⁅⁅v, u⁆, w⁆ ^ (k * j) := by
    rw [commutatorElement_pow_left_of_central hcenj k,
      commutatorElement_pow_right_of_central hcen j, ← pow_mul, Nat.mul_comm]
  -- From `⁅c^k, w^j⁆ = c^k w^j (c^k)⁻¹ (w^j)⁻¹` solve for `c^k * w^j`.
  have hbase : ⁅v, u⁆ ^ k * w ^ j = ⁅⁅v, u⁆ ^ k, w ^ j⁆ * (w ^ j * ⁅v, u⁆ ^ k) := by
    rw [commutatorElement_def]; group
  -- Goal: `e^(k*j) * (w^j * c^k) = w^j * c^k * e^(k*j)`; `e^(k*j)` is central, move it right.
  rw [hbase, hcomm_collect, ((hcomm (w ^ j * ⁅v, u⁆ ^ k)).pow_left (k * j)).eq]

/-- The non-central collection step `(4.4)` for the skeleton `u ^ k * v ^ k * c ^ C(k,2)`:
multiplying by `u * v` advances `k ↦ k + 1` while emitting the central corrections
`d₁ ^ (k + C(k,2))` and `d₂ ^ (k * (k+1))`:
`u^k v^k c^C(k,2) (u*v) = u^(k+1) v^(k+1) c^C(k+1,2) ⁅⁅v,u⁆,u⁆^(k+C(k,2)) ⁅⁅v,u⁆,v⁆^(k(k+1))`.

This is the heart of the induction. Reading left to right (with `c := ⁅v, u⁆`,
`d₁ := ⁅⁅v, u⁆, u⁆`, `d₂ := ⁅⁅v, u⁆, v⁆`):

* `c^C(k,2) * u = u * c^C(k,2) * d₁^C(k,2)` (`commutator_pow_mul_collect`, `w = u`);
* `c^C(k,2) * v = v * c^C(k,2) * d₂^C(k,2)` (`commutator_pow_mul_collect`, `w = v`);
* `v^k * u = ⁅v^k, u⁆ * u * v^k` (`pow_mul_eq_commutator_mul`) with
  `⁅v^k, u⁆ = c^k * d₂⁻¹^C(k,2)` (`commutatorElement_pow_left_of_triple_central` and
  `⁅v, ⁅v, u⁆⁆ = d₂⁻¹`); the `d₂⁻¹^C(k,2)` cancels a `d₂^C(k,2)`;
* `c^k * u = u * c^k * d₁^k` and `c^k * v^(k+1) = v^(k+1) * c^k * d₂^(k*(k+1))`
  (`commutator_pow_mul_collect` / `commutator_pow_mul_pow_collect`).

The `c`-exponent lands on `k + C(k,2) = C(k+1,2)` and the central exponents on
`d₁^(k + C(k,2))`, `d₂^(k*(k+1))` (model-verified). -/
private theorem collect_skeleton_step
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G)
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v : G) (k : ℕ) :
    u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2) * (u * v)
      = u ^ (k + 1) * v ^ (k + 1) * ⁅v, u⁆ ^ ((k + 1).choose 2)
          * ⁅⁅v, u⁆, u⁆ ^ (k + k.choose 2) * ⁅⁅v, u⁆, v⁆ ^ (k * (k + 1)) := by
  -- Central correction atoms (`d₁, d₂` central by `hc4`). Abbreviations via `m` only.
  have hd1cen := triple_commutator_mem_center hc4 u v u
  have hd2cen := triple_commutator_mem_center hc4 u v v
  have hd1 : ∀ g : G, Commute ⁅⁅v, u⁆, u⁆ g := fun g => (Subgroup.mem_center_iff.mp hd1cen g).symm
  have hd2 : ∀ g : G, Commute ⁅⁅v, u⁆, v⁆ g := fun g => (Subgroup.mem_center_iff.mp hd2cen g).symm
  -- `⁅v^k, u⁆ = ⁅v,u⁆^k * d₂⁻¹^C(k,2)`.
  have hvk : ⁅v ^ k, u⁆ = ⁅v, u⁆ ^ k * (⁅⁅v, u⁆, v⁆⁻¹) ^ (k.choose 2) := by
    rw [commutatorElement_pow_left_of_triple_central hc3 v u k, commutatorElement_inv]
  set m := k.choose 2 with hm
  have hchoose : (k + 1).choose 2 = k + m := by
    rw [hm, Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
  -- `d₂⁻¹^m * d₂^m = 1`.
  have hcancel : (⁅⁅v, u⁆, v⁆⁻¹) ^ m * ⁅⁅v, u⁆, v⁆ ^ m = 1 := by rw [inv_pow, inv_mul_cancel]
  -- Central moves (push `d₁, d₂` powers rightward across an arbitrary tail `g`).
  have e1 : ∀ (a : ℕ) (g : G), ⁅⁅v, u⁆, u⁆ ^ a * g = g * ⁅⁅v, u⁆, u⁆ ^ a :=
    fun a g => ((hd1 g).pow_left a).eq
  have e2 : ∀ (a : ℕ) (g : G), ⁅⁅v, u⁆, v⁆ ^ a * g = g * ⁅⁅v, u⁆, v⁆ ^ a :=
    fun a g => ((hd2 g).pow_left a).eq
  have e2inv : ∀ (a : ℕ) (g : G), (⁅⁅v, u⁆, v⁆⁻¹) ^ a * g = g * (⁅⁅v, u⁆, v⁆⁻¹) ^ a :=
    fun a g => (((hd2 g).inv_left).pow_left a).eq
  -- Step A: expose `⁅v,u⁆^m * u` and `⁅v,u⁆^m * v`, applying the two single-element motions.
  rw [show u ^ k * v ^ k * ⁅v, u⁆ ^ m * (u * v) = u ^ k * v ^ k * (⁅v, u⁆ ^ m * u) * v by
        simp only [mul_assoc],
      commutator_pow_mul_collect hc4 u v u m]
  simp only [mul_assoc]
  -- Move the fresh `d₁^m` right past `v`, re-expose `⁅v,u⁆^m * v`, then the `v`-motion.
  rw [e1 m v, ← mul_assoc (⁅v, u⁆ ^ m) v, commutator_pow_mul_collect hc4 u v v m]
  simp only [mul_assoc]
  -- Step C: expose `v^k * u`, expand it (`⁅v^k,u⁆ = ⁅v,u⁆^k * d₂⁻¹^m`).
  rw [← mul_assoc (v ^ k) u, pow_mul_eq_commutator_mul u v k, hvk]
  simp only [mul_assoc]
  -- Push the central `d₂⁻¹^m` to the far right (past the whole tail).
  rw [e2inv m (u * (v ^ k * (v * (⁅v, u⁆ ^ m * (⁅⁅v, u⁆, v⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ m)))))]
  simp only [mul_assoc]
  -- Now `… * (d₂^m * (d₁^m * d₂⁻¹^m))`; commute `d₁^m` past `d₂⁻¹^m`, then `d₂^m * d₂⁻¹^m = 1`.
  rw [e1 m (⁅⁅v, u⁆, v⁆⁻¹ ^ m), inv_pow, ← mul_assoc (⁅⁅v, u⁆, v⁆ ^ m), mul_inv_cancel]
  simp only [one_mul]
  -- Step D: `⁅v,u⁆^k * u = u * ⁅v,u⁆^k * d₁^k`; merge `v^k * v = v^(k+1)`.
  rw [← mul_assoc (⁅v, u⁆ ^ k) u, commutator_pow_mul_collect hc4 u v u k]
  simp only [mul_assoc]
  -- Move `d₁^k` right past `v^k, v, ⁅v,u⁆^m`, merge with `d₁^m` into `d₁^(k+m)`.
  rw [e1 k (v ^ k * (v * (⁅v, u⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ m)))]
  simp only [mul_assoc]
  rw [← pow_add, Nat.add_comm m k]
  -- Step E: merge `v^k * v = v^(k+1)`; then `⁅v,u⁆^k * v^(k+1)` motion; merge `u^k*u`, `⁅v,u⁆`.
  rw [← mul_assoc (v ^ k) v, ← pow_succ, ← mul_assoc (⁅v, u⁆ ^ k) (v ^ (k + 1)),
      commutator_pow_mul_pow_collect hc4 u v v k (k + 1)]
  simp only [mul_assoc]
  -- Push `d₂^(k(k+1))` to the right of `⁅v,u⁆^m * d₁^(k+m)`, merge `⁅v,u⁆^k * ⁅v,u⁆^m`, `u^k*u`.
  rw [e2 (k * (k + 1)) (⁅v, u⁆ ^ m * ⁅⁅v, u⁆, u⁆ ^ (k + m))]
  simp only [mul_assoc]
  rw [← mul_assoc (⁅v, u⁆ ^ k) (⁅v, u⁆ ^ m), ← pow_add, ← hchoose,
      ← mul_assoc (u ^ k) u, ← pow_succ]

/-- Pascal recurrence for the `d₁`-exponent `FF n = (n+1).choose 3`:
`(k + k.choose 2) + (k+1).choose 3 = (k+2).choose 3`. The skeleton step emits `d₁^(k+C(k,2))`,
which combined with the carried `d₁^FF(k)` gives `d₁^FF(k+1)`. -/
private theorem ff_succ (k : ℕ) :
    k + k.choose 2 + (k + 1).choose 3 = (k + 2).choose 3 := by
  have hc2 : (k + 1).choose 2 = k + k.choose 2 := by
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right, Nat.add_comm]
  rw [show k + 2 = (k + 1) + 1 from rfl, Nat.choose_succ_succ' (k + 1) 2, hc2, Nat.add_comm]

/-- Pascal recurrence for the `d₂`-exponent `GG n = 2 * (n+1).choose 3`:
`k*(k+1) + 2 * (k+1).choose 3 = 2 * (k+2).choose 3`. The skeleton step emits `d₂^(k*(k+1))`,
which combined with the carried `d₂^GG(k)` gives `d₂^GG(k+1)`; note `k*(k+1) = 2*(k+1).choose 2`
(`Nat.choose_succ_right_eq`). -/
private theorem gg_succ (k : ℕ) :
    k * (k + 1) + 2 * (k + 1).choose 3 = 2 * (k + 2).choose 3 := by
  -- `k*(k+1) = 2 * (k+1).choose 2`.
  have htwo : k * (k + 1) = 2 * (k + 1).choose 2 := by
    have h := Nat.add_one_mul_choose_eq k 1
    rw [Nat.choose_one_right] at h
    -- `h : (k+1) * k = (k+1).choose 2 * 2`
    rw [Nat.mul_comm k (k + 1), h, Nat.mul_comm]
  rw [htwo, ← Nat.mul_add, show k + 2 = (k + 1) + 1 from rfl, Nat.choose_succ_succ' (k + 1) 2,
    Nat.add_comm ((k + 1).choose 2)]

/-- **BG Proposition 4.3(a), `(4.4)`: two-generator collection formula under `cl ≤ 3`.**
For `γ₃(G) ⊆ Z(G)` (`hc3`) and `γ₄(G) = 1` (`hc4`), and all `u, v : G`, `n : ℕ`,
`(u*v)^n = u^n v^n ⁅v,u⁆^(C(n,2)) ⁅⁅v,u⁆,u⁆^((n+1).choose 3) ⁅⁅v,u⁆,v⁆^(2*(n+1).choose 3)`.

This is BG's `(uv)^n = u^n v^n [v,u]^{C(n,2)} [v,u,u]^{f(n)} [v,u,v]^{g(n)}` (mmd L1430-1464), but
the BG-literal `f(n) = C(n,3)`, `g(n) = 2 C(n,3) + C(n,2)` are stated for the convention
`[a,b] = a⁻¹b⁻¹ab`; in mathlib's convention `⁅a,b⁆ = a b a⁻¹ b⁻¹` the correct closed forms are
`f(n) = (n+1).choose 3` and `g(n) = 2 * (n+1).choose 3` (model-verified by the Magnus embedding
of the free nilpotent class-`3` group on two generators, `n = 0..8`). The exponents are inlined
as closed forms (no `def`) so the statement is pinned to these values.

Proof: induction on `n`. The non-central skeleton step (advancing `k ↦ k+1` while emitting
`⁅⁅v,u⁆,u⁆^(k+C(k,2))` and `⁅⁅v,u⁆,v⁆^(k(k+1))`)
is `collect_skeleton_step`; the carried central factors `⁅⁅v,u⁆,u⁆^FF(k)`, `⁅⁅v,u⁆,v⁆^GG(k)`
commute to the right and combine via the Pascal recurrences `ff_succ`, `gg_succ`. -/
theorem mul_pow_eq_collect_of_triple_central
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G)
    (hc4 : ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1) (u v : G) (n : ℕ) :
    (u * v) ^ n
      = u ^ n * v ^ n * ⁅v, u⁆ ^ (n.choose 2)
          * ⁅⁅v, u⁆, u⁆ ^ ((n + 1).choose 3)
          * ⁅⁅v, u⁆, v⁆ ^ (2 * (n + 1).choose 3) := by
  -- `d₁, d₂` central (by `hc4`).
  have hd1 : ∀ g : G, Commute ⁅⁅v, u⁆, u⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (triple_commutator_mem_center hc4 u v u) g).symm
  have hd2 : ∀ g : G, Commute ⁅⁅v, u⁆, v⁆ g :=
    fun g => (Subgroup.mem_center_iff.mp (triple_commutator_mem_center hc4 u v v) g).symm
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 3)]
  | succ k ih =>
    rw [pow_succ, ih]
    -- Push the carried central `d₁^FF(k)`, `d₂^GG(k)` to the right of `(u*v)`.
    rw [mul_assoc (u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2) * ⁅⁅v, u⁆, u⁆ ^ ((k + 1).choose 3)),
        ((hd2 (u * v)).pow_left (2 * (k + 1).choose 3)).eq,
        ← mul_assoc, mul_assoc (u ^ k * v ^ k * ⁅v, u⁆ ^ (k.choose 2)),
        ((hd1 (u * v)).pow_left ((k + 1).choose 3)).eq, ← mul_assoc,
        collect_skeleton_step hc3 hc4 u v k]
    -- Now `… d₁^(k+C(k,2)) * (d₂^(k(k+1)) * (d₁^FF(k) * d₂^GG(k)))`; commute `d₂^(k(k+1))` past
    -- `d₁^FF(k)`, then combine the two `d₁` and the two `d₂` powers (`ff_succ`, `gg_succ`).
    simp only [mul_assoc]
    rw [← mul_assoc (⁅⁅v, u⁆, v⁆ ^ (k * (k + 1))),
        ((hd2 (⁅⁅v, u⁆, u⁆ ^ ((k + 1).choose 3))).pow_left (k * (k + 1))).eq]
    simp only [mul_assoc]
    rw [← mul_assoc (⁅⁅v, u⁆, u⁆ ^ (k + k.choose 2)), ← pow_add, ff_succ k,
        ← pow_add, gg_succ k]

end Prop43ClassThreeCollection

section Prop43ClassThree

open OddOrder.GroupTheory

open scoped commutatorElement

/-- From pointwise `γ₃ ⊆ Z` one gets `γ₄ = 1`: a `γ₃`-element `z = ⁅⁅a, b⁆, c⁆` is
central, so `⁅z, d⁆ = 1`. This supplies the `hc4` hypothesis of the collection
formula `(4.4)` from the packaged `cl ≤ 3` assumption (no `LCS` detour). -/
private theorem triple_commutator_eq_one_of_pointwise_central {G : Type*} [Group G]
    (hc3 : ∀ a b c : G, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center G) :
    ∀ a b c d : G, ⁅⁅⁅a, b⁆, c⁆, d⁆ = 1 := by
  intro a b c d
  exact commutatorElement_eq_one_iff_commute.2
    (Subgroup.mem_center_iff.mp (hc3 a b c) d).symm

/-- **`cl ≤ 3` descends to subgroups.** If `γ₃(R)` is pointwise central in `R` and
`S : Subgroup R`, then `γ₃(↥S)` is pointwise central in `↥S`.

Proof mirrors `commutator_le_center_of_le_of_class_le_two`: push the iterated
commutator through `S.subtype` (`map_commutatorElement`), use centrality in `R`,
and pull back along `Subtype.ext`. -/
private theorem class_le_three_descent {R : Type*} [Group R]
    (hc3 : ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R) (S : Subgroup R) :
    ∀ a b c : ↥S, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center ↥S := by
  intro a b c
  rw [Subgroup.mem_center_iff]
  intro d
  apply Subtype.ext
  -- Goal in `R`: `(⁅⁅a,b⁆,c⁆ : R) * (d:R) = (d:R) * (⁅⁅a,b⁆,c⁆ : R)`.
  have hcoe : ((⁅⁅a, b⁆, c⁆ : ↥S) : R) = ⁅⁅(a : R), (b : R)⁆, (c : R)⁆ := by
    push_cast [commutatorElement_def]; group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact Subgroup.mem_center_iff.mp (hc3 (a : R) (b : R) (c : R)) (d : R)

/-- For a normal subgroup `H`, the commutator `⁅a, b⁆` with `b ∈ H` lies in `H`
(`⁅a, b⁆ = (a b a⁻¹) b⁻¹`, conjugate of `b` times `b⁻¹`). -/
private theorem commutatorElement_mem_of_normal_right {G : Type*} [Group G]
    {H : Subgroup G} (hH : H.Normal) {b : G} (hb : b ∈ H) (a : G) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (hH.conj_mem b hb a) (H.inv_mem hb)

/-- For a normal subgroup `H`, the commutator `⁅a, b⁆` with `a ∈ H` lies in `H`
(`⁅a, b⁆ = a (b a⁻¹ b⁻¹)`). -/
private theorem commutatorElement_mem_of_normal_left {G : Type*} [Group G]
    {H : Subgroup G} (hH : H.Normal) {a : G} (ha : a ∈ H) (b : G) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  have : b * a⁻¹ * b⁻¹ ∈ H := hH.conj_mem a⁻¹ (H.inv_mem ha) b
  have h2 : a * (b * a⁻¹ * b⁻¹) ∈ H := H.mul_mem ha this
  simpa [mul_assoc] using h2

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]

/-- **BG Proposition 4.3(a)** (mmd L1398-1472, `p > 3` / `cl ≤ 3` branch combined with
the classical `cl ≤ 2` case). For an odd prime `p`, a finite `p`-group `R` with
`cl(R) ≤ 2` or (`p > 3` and `cl(R) ≤ 3`), every element `g ∈ Ω₁(R) = Omega R p 1`
satisfies `g ^ p = 1`; i.e. `Ω₁(R)` has exponent dividing `p`.

The `cl ≤ 2` case is `Omega.pow_eq_one_of_class_le_two`. The `cl ≤ 3` case is the
"regular `p`-group" argument: it suffices (since `Ω₁(R)` is generated by the
`g ^ p = 1`) that the set `{g | g ^ p = 1}` is closed under products, i.e.
`x ^ p = y ^ p = 1 ⇒ (x * y) ^ p = 1`. This product-closure is proved by induction on
`|R|`. If `⟨x⟩ = R` then `R` is abelian and `(x*y)^p = x^p y^p = 1`. Otherwise pick a
maximal (hence normal) `S ⊇ ⟨x⟩`; by induction `Ω₁(↥S)` has exponent `p`, so the
weight-`2,3` commutators `⁅y, x⁆, ⁅⁅y, x⁆, x⁆, ⁅⁅y, x⁆, y⁆` — all in the `R`-normal
subgroup `Ω₁(↥S)` (which contains `x`) — have `p`-th power `1`. The collection `(4.4)`
at `n = p` then gives `(x*y)^p = x^p y^p · (those commutators)^{C(p,2),FF(p),GG(p)}`,
and `p ∣ C(p,2), (p+1).choose 3` (for `p > 3`) kills every correction factor. -/
theorem omega1_pow_eq_one (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcl : _root_.commutator R ≤ Subgroup.center R ∨
           (3 < p ∧ ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R))
    {g : R} (hg : g ∈ Omega R p 1) : g ^ p = 1 := by
  rcases hcl with hc2 | ⟨hp3, hc3⟩
  · -- `cl ≤ 2`.
    exact Omega.pow_eq_one_of_class_le_two hp_odd hc2 hg
  -- `cl ≤ 3`, `p > 3`.
  have hc4 := triple_commutator_eq_one_of_pointwise_central hc3
  -- Product-closure of `{g | g^p = 1}` by `|R|`-strong-induction.
  suffices hclosed : ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 by
    -- `{g | g^p=1}` is a subgroup containing the generators, hence `Omega R p 1`.
    let omega1 : Subgroup R :=
      { carrier := {g : R | g ^ p = 1}
        mul_mem' := fun {x y} hx hy => hclosed x y hx hy
        one_mem' := one_pow p
        inv_mem' := fun {x} hx => by rw [Set.mem_ofPred_eq, inv_pow, hx, inv_one] }
    have hle : Omega R p 1 ≤ omega1 := by
      rw [Omega, Subgroup.closure_le]
      intro x hx
      change x ^ p = 1
      exact pow_one p ▸ hx
    simpa [omega1] using hle hg
  clear hg g
  -- Strong induction on `Nat.card R`.
  let motive : ℕ → Prop := fun n =>
    ∀ {R' : Type _} [Group R'] [Finite R'], IsPGroup p R' →
      (∀ a b c : R', ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R') → Nat.card R' = n →
        ∀ x y : R', x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1
  refine (Nat.strongRecOn (motive := motive) (Nat.card R) ?_) hR hc3 rfl
  clear hR hc3
  intro n ih R' _ _ hR' hc3' hcard x y hxp hyp
  have hc4' := triple_commutator_eq_one_of_pointwise_central hc3'
  by_cases hxtop : Subgroup.zpowers x = ⊤
  · -- `⟨x⟩ = ⊤`: `R'` is cyclic, hence abelian; `x, y` commute.
    have hxy : Commute x y := by
      have hy_mem : y ∈ Subgroup.zpowers x := hxtop ▸ Subgroup.mem_top y
      obtain ⟨k, hk⟩ := hy_mem
      rw [← hk]; exact (Commute.refl x).zpow_right k
    rw [hxy.mul_pow, hxp, hyp, mul_one]
  · -- `⟨x⟩ ≠ ⊤`: take a maximal (normal) subgroup `S ⊇ ⟨x⟩`.
    obtain ⟨S, hS_coatom, hxS_le⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hxtop
    have hS_normal : S.Normal := hS_coatom.normal_of_isPGroup hR'
    have hxS : x ∈ S := hxS_le (Subgroup.mem_zpowers x)
    -- `|↥S| < |R'| = n`.
    have hScard : Nat.card ↥S < n := by
      rw [← hcard]
      have h_dvd : Nat.card ↥S ∣ Nat.card R' := ⟨S.index, by rw [mul_comm, S.index_mul_card]⟩
      have h_le : Nat.card ↥S ≤ Nat.card R' := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne : Nat.card ↥S ≠ Nat.card R' := fun heq =>
        hS_coatom.1 (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le h_ne
    have hSpg : IsPGroup p ↥S := hR'.to_subgroup S
    have hc3S := class_le_three_descent hc3' S
    -- Inductive hypothesis: product-closure on `↥S`.
    have IHS : ∀ a b : ↥S, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
      ih (Nat.card ↥S) hScard hSpg hc3S rfl
    -- `Ω₁(↥S)` (as an `R'`-subgroup) is normal in `R'` and has exponent `p`.
    have : (Omega ↥S p 1).Characteristic := Omega.characteristic
    set H : Subgroup R' := (Omega ↥S p 1).map S.subtype with hH_def
    have hH_normal : H.Normal := by rw [hH_def]; infer_instance
    -- Every element of `H` has `p`-th power `1` (via `IHS` and `closure_le`).
    have hHpow : ∀ z ∈ H, z ^ p = 1 := by
      -- `{a : ↥S | a^p = 1}` is a subgroup of `↥S` (by `IHS`), containing the generators.
      let omega1S : Subgroup ↥S :=
        { carrier := {a : ↥S | a ^ p = 1}
          mul_mem' := fun {a b} ha hb => IHS a b ha hb
          one_mem' := one_pow p
          inv_mem' := fun {a} ha => by rw [Set.mem_ofPred_eq, inv_pow, ha, inv_one] }
      have hΩle : Omega ↥S p 1 ≤ omega1S := by
        rw [Omega, Subgroup.closure_le]
        intro a ha
        change a ^ p = 1
        exact pow_one p ▸ ha
      intro z hz
      rw [hH_def, Subgroup.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      have hap : a ^ p = 1 := by simpa [omega1S] using hΩle ha
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hap, Subgroup.coe_one]
    -- `x ∈ H`.
    have hxH : x ∈ H := by
      rw [hH_def, Subgroup.mem_map]
      refine ⟨⟨x, hxS⟩, ?_, by rw [Subgroup.coe_subtype]⟩
      exact Omega.mem_of_pow_eq_one (by rw [pow_one]; exact Subtype.ext (by simpa using hxp))
    -- The three collection commutators lie in `H`, hence have `p`-th power `1`.
    have hcomm_xy : ⁅y, x⁆ ∈ H := commutatorElement_mem_of_normal_right hH_normal hxH y
    have h45a : ⁅y, x⁆ ^ p = 1 := hHpow _ hcomm_xy
    have h45b : ⁅⁅y, x⁆, x⁆ ^ p = 1 :=
      hHpow _ (commutatorElement_mem_of_normal_right hH_normal hxH ⁅y, x⁆)
    have h45c : ⁅⁅y, x⁆, y⁆ ^ p = 1 :=
      hHpow _ (commutatorElement_mem_of_normal_left hH_normal hcomm_xy y)
    -- The three correction factors vanish: `p ∣ C(p,2), (p+1).choose 3` and the bases
    -- have `p`-th power `1`.
    have hpc2 : p ∣ p.choose 2 :=
      Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) (by omega)
    have hpc3 : p ∣ (p + 1).choose 3 :=
      Nat.Prime.dvd_choose (Fact.out : p.Prime) (by omega) (by omega) (by omega)
    have e1 : ⁅y, x⁆ ^ (p.choose 2) = 1 := by
      obtain ⟨m2, hm2⟩ := hpc2; rw [hm2, pow_mul, h45a, one_pow]
    have e2 : ⁅⁅y, x⁆, x⁆ ^ ((p + 1).choose 3) = 1 := by
      obtain ⟨m3, hm3⟩ := hpc3; rw [hm3, pow_mul, h45b, one_pow]
    have e3 : ⁅⁅y, x⁆, y⁆ ^ (2 * (p + 1).choose 3) = 1 := by
      obtain ⟨m3, hm3⟩ := hpc3
      rw [show 2 * (p + 1).choose 3 = p * (2 * m3) by rw [hm3]; ring, pow_mul, h45c, one_pow]
    -- Collection `(4.4)` at `n = p`, roles `u = x, v = y`.
    rw [mul_pow_eq_collect_of_triple_central hc3' hc4' x y p, hxp, hyp, e1, e2, e3,
        mul_one, mul_one, mul_one, one_mul]

/-- **BG Proposition 4.3(b)** (mmd L1398-1472). For an odd prime `p`, a finite
`p`-group `R` with `cl(R) ≤ 2` or (`p > 3` and `cl(R) ≤ 3`), and `R' ⊆ Ω₁(R)`, the
`p`-th power map is "multiplicative": `(x * y) ^ p = x ^ p * y ^ p` for all `x, y`.

(The map `x ↦ x ^ p` is not a `MonoidHom` on a nonabelian group, so this is stated as
the bare equation rather than via `mk'`.)

The `cl ≤ 2` case follows from `mul_pow_eq_commutator_pow_mul_of_class_le_two`: the
single correction factor `⁅y, x⁆ ^ (p(p-1)/2)` vanishes since `⁅y, x⁆ ∈ R' ⊆ Ω₁(R)`
gives `⁅y, x⁆ ^ p = 1` and `p ∣ p(p-1)/2` for odd `p`. The `cl ≤ 3` case substitutes
`n = p` into the collection `(4.4)`; each correction commutator lies in `R' ⊆ Ω₁(R)`,
so (by part (a) = `omega1_pow_eq_one`) has `p`-th power `1`, and the exponents
`C(p,2), (p+1).choose 3` are divisible by `p`. -/
theorem pow_mul_eq_mul_pow_of_commutator_le_omega1 (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcl : _root_.commutator R ≤ Subgroup.center R ∨
           (3 < p ∧ ∀ a b c : R, ⁅⁅a, b⁆, c⁆ ∈ Subgroup.center R))
    (hsub : _root_.commutator R ≤ Omega R p 1) (x y : R) :
    (x * y) ^ p = x ^ p * y ^ p := by
  -- `⁅y, x⁆ ∈ R' ⊆ Ω₁(R)`.
  have hyx_mem : ⁅y, x⁆ ∈ Omega R p 1 :=
    hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have h1 : ⁅y, x⁆ ^ p = 1 := omega1_pow_eq_one hR hp_odd hcl hyx_mem
  rcases hcl with hc2 | ⟨hp3, hc3⟩
  · -- `cl ≤ 2`: single correction factor.
    rw [mul_pow_eq_commutator_pow_mul_of_class_le_two hc2 x y p]
    have hdvd : p ∣ p * (p - 1) / 2 := by
      obtain ⟨k, rfl⟩ := hp_odd
      rw [show 2 * k + 1 - 1 = 2 * k by omega,
        Nat.mul_div_assoc _ (Dvd.intro k rfl : 2 ∣ 2 * k), Nat.mul_div_cancel_left k two_pos]
      exact Dvd.intro k rfl
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, h1, one_pow, one_mul]
  -- `cl ≤ 3`, `p > 3`.
  have hc4 := triple_commutator_eq_one_of_pointwise_central hc3
  -- The other two correction commutators are also in `R' ⊆ Ω₁(R)`.
  have h2 : ⁅⁅y, x⁆, x⁆ ^ p = 1 :=
    omega1_pow_eq_one hR hp_odd (Or.inr ⟨hp3, hc3⟩)
      (hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top ⁅y, x⁆) (Subgroup.mem_top x)))
  have h3 : ⁅⁅y, x⁆, y⁆ ^ p = 1 :=
    omega1_pow_eq_one hR hp_odd (Or.inr ⟨hp3, hc3⟩)
      (hsub (Subgroup.commutator_mem_commutator (Subgroup.mem_top ⁅y, x⁆) (Subgroup.mem_top y)))
  have hpc2 : p ∣ p.choose 2 :=
    Nat.Prime.dvd_choose_self (Fact.out : p.Prime) (by norm_num) (by omega)
  have hpc3 : p ∣ (p + 1).choose 3 :=
    Nat.Prime.dvd_choose (Fact.out : p.Prime) (by omega) (by omega) (by omega)
  have e1 : ⁅y, x⁆ ^ (p.choose 2) = 1 := by
    obtain ⟨m2, hm2⟩ := hpc2; rw [hm2, pow_mul, h1, one_pow]
  have e2 : ⁅⁅y, x⁆, x⁆ ^ ((p + 1).choose 3) = 1 := by
    obtain ⟨m3, hm3⟩ := hpc3; rw [hm3, pow_mul, h2, one_pow]
  have e3 : ⁅⁅y, x⁆, y⁆ ^ (2 * (p + 1).choose 3) = 1 := by
    obtain ⟨m3, hm3⟩ := hpc3
    rw [show 2 * (p + 1).choose 3 = p * (2 * m3) by rw [hm3]; ring, pow_mul, h3, one_pow]
  rw [mul_pow_eq_collect_of_triple_central hc3 hc4 x y p, e1, e2, e3, mul_one, mul_one, mul_one]

end Prop43ClassThree

end OddOrder.BG.Ch1.S04


