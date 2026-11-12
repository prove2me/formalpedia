-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:09:31.31783+00:00
-- url     : https://prove2.me/theorems/a4b6ca4e-8a21-43a0-85de-72e669379497
-- title:
--   Isaacs §4A: Theorems 4.7 and 4.8 (maximal class $p$-groups, $\Omega_r$)
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §4A, Thm 4.7/4.8 (pp. 113–122) on $p$-groups of maximal class and the subgroups $\Omega_r$.
--
--   Main definitions: `setOfPowEqOne` (Theorem 4.8(a): for $p>2$ and a group $G$ with $G'\le Z(G)$, the set of elements with $x^p=1$) and `powPHom` (Theorem 4.8(b): for odd $p$ and class at most $2$, the $p$-th power map as a homomorphism).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/CommutatorBasics.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/CommutatorBasics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorIdentities
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- General identity: `y * x = ⁅y, x⁆ * x * y` (no hypothesis). -/
private lemma mul_eq_commutator_mul (x y : G) :
    y * x = ⁅y, x⁆ * x * y := by
  simp only [commutatorElement_def]
  group

/-- In class ≤ 2 (`commutator G ≤ Z(G)`): `y * x = x * y * ⁅y, x⁆`.
`⁅y, x⁆` 中心で `y * x = ⁅y, x⁆ * (x * y) = (x * y) * ⁅y, x⁆`. -/
lemma mul_comm_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  rw [mul_eq_commutator_mul, mul_assoc]
  exact (Subgroup.mem_center_iff.mp hc (x * y)).symm

/-- In class ≤ 2: `⁅y, x⁆` は中心で全ての元と可換. -/
private lemma commute_commutator_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    Commute ⁅y, x⁆ z := by
  have hc : ⁅y, x⁆ ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  exact (Subgroup.mem_center_iff.mp hc z).symm

/-- In class ≤ 2: `y^k * x = x * y^k * ⁅y, x⁆^k` (induction on `k`).
各回 `y` を `x` の右に passing で `⁅y, x⁆` が 1 個発生. -/
private lemma pow_mul_eq_mul_pow_commutator_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (k : ℕ) :
    y^k * x = x * y^k * ⁅y, x⁆^k := by
  induction k with
  | zero => simp
  | succ j ih =>
    -- ⁅y, x⁆^j commutes with y (central).
    have h_pow_y : ⁅y, x⁆^j * y = y * ⁅y, x⁆^j :=
      (commute_commutator_of_class_le_two hC x y y).pow_left j
    -- 計算 chain
    have step : y^(j+1) * x = x * y^(j+1) * ⁅y, x⁆^(j+1) := by
      rw [pow_succ y j, mul_assoc (y^j) y x,
          mul_comm_commutator_of_class_le_two hC x y]
      -- Goal: y^j * (x * y * ⁅y, x⁆) = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show y^j * (x * y * ⁅y, x⁆) = y^j * x * y * ⁅y, x⁆ by ac_rfl]
      rw [ih]
      -- Goal: x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * ⁅y, x⁆^j * y * ⁅y, x⁆ =
            x * y^j * (⁅y, x⁆^j * y) * ⁅y, x⁆ by ac_rfl, h_pow_y]
      -- Goal: x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ = x * y^(j+1) * ⁅y, x⁆^(j+1)
      rw [show x * y^j * (y * ⁅y, x⁆^j) * ⁅y, x⁆ =
            x * (y^j * y) * (⁅y, x⁆^j * ⁅y, x⁆) by ac_rfl]
      rw [← pow_succ y j, ← pow_succ ⁅y, x⁆ j]
    exact step

/-- **Commutator collection formula in class ≤ 2**:
`(x * y)^n = x^n * y^n * ⁅y, x⁆^(n*(n-1)/2)`.

**証明** (Isaacs p.120): `n` についての induction. step:
`(xy)^(k+1) = (xy)^k · xy = x^k y^k ⁅y,x⁆^(k(k-1)/2) · xy`. 中心元と移動可換で
`y^k · x = x · y^k · ⁅y,x⁆^k` (上記 helper). 整理して指数加法 `k + k(k-1)/2 = k(k+1)/2`. -/
theorem mul_pow_of_class_le_two
    (hC : _root_.commutator G ≤ Subgroup.center G) (x y : G) (n : ℕ) :
    (x * y)^n = x^n * y^n * ⁅y, x⁆^(n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    -- Goal: x^k * y^k * ⁅y,x⁆^(k(k-1)/2) * (x*y) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    -- ⁅y, x⁆^(k(k-1)/2) commutes with x and y separately.
    have h_xy : ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) = (x * y) * ⁅y, x⁆^(k * (k - 1) / 2) :=
      ((commute_commutator_of_class_le_two hC x y (x * y)).pow_left _)
    -- ⁅y, x⁆^k commutes with y.
    have h_ky : ⁅y, x⁆^k * y = y * ⁅y, x⁆^k :=
      ((commute_commutator_of_class_le_two hC x y y).pow_left k)
    -- Re-associate to bring (y^k * x) together
    rw [show x^k * y^k * ⁅y, x⁆^(k * (k - 1) / 2) * (x * y) =
          x^k * y^k * (⁅y, x⁆^(k * (k - 1) / 2) * (x * y)) by ac_rfl, h_xy]
    -- Goal: x^k * y^k * ((x*y) * ⁅y,x⁆^(k(k-1)/2)) = ...
    rw [show x^k * y^k * (x * y * ⁅y, x⁆^(k * (k - 1) / 2)) =
          x^k * (y^k * x) * y * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        pow_mul_eq_mul_pow_commutator_pow_of_class_le_two hC x y k]
    -- Goal: x^k * (x * y^k * ⁅y,x⁆^k) * y * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * (x * y^k * ⁅y, x⁆^k) * y * ⁅y, x⁆^(k * (k - 1) / 2) =
          x^k * x * y^k * (⁅y, x⁆^k * y) * ⁅y, x⁆^(k * (k - 1) / 2) by ac_rfl,
        h_ky]
    -- Goal: x^k * x * y^k * (y * ⁅y,x⁆^k) * ⁅y,x⁆^(k(k-1)/2) = ...
    rw [show x^k * x * y^k * (y * ⁅y, x⁆^k) * ⁅y, x⁆^(k * (k - 1) / 2) =
          (x^k * x) * (y^k * y) * (⁅y, x⁆^k * ⁅y, x⁆^(k * (k - 1) / 2)) by ac_rfl]
    rw [← pow_succ x k, ← pow_succ y k, ← pow_add]
    -- Goal: x^(k+1) * y^(k+1) * ⁅y,x⁆^(k + k(k-1)/2) = x^(k+1) * y^(k+1) * ⁅y,x⁆^((k+1)k/2)
    congr 2
    -- k + k(k-1)/2 = (k+1)k/2 over Nat. Need that k*(k-1) is even.
    rcases k with _ | j
    · simp
    · -- k = j+1: (j+1) + (j+1)*j/2 = (j+2)*(j+1)/2
      simp only [Nat.add_succ_sub_one, Nat.add_zero]
      -- (j+1)*j and (j+2)*(j+1) are both even (consecutive integers)
      have h1 : 2 ∣ (j+1) * j := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
      have h2 : 2 ∣ (j+1+1) * (j+1) := by
        rw [Nat.mul_comm]; exact (Nat.even_mul_succ_self (j+1)).two_dvd
      obtain ⟨m, hm⟩ := h1
      obtain ⟨n, hn⟩ := h2
      -- Eliminate quadratics: (j+2)(j+1) = (j+1)*j + 2*(j+1)
      have key : (j+1+1) * (j+1) = (j+1) * j + 2 * (j+1) := by ring
      rw [key, hm] at hn
      omega

/-- **Isaacs Theorem 4.8(a)**: `p > 2`, `G` is a group with `commutator G ≤ Z(G)`
(class ≤ 2). Then `{x ∈ G : x^p = 1}` is a subgroup.

**証明**: 唯一の閉性 (mul_mem). `x^p = y^p = 1` ⇒
`(xy)^p = x^p y^p ⁅y, x⁆^(p(p-1)/2) = ⁅y, x⁆^(p(p-1)/2)` (collection).
`⁅·, x⁆` 左 hom + `y^p = 1` ⇒ `⁅y, x⁆^p = ⁅y^p, x⁆ = ⁅1, x⁆ = 1`.
`p > 2 odd` ⇒ `(p-1)/2 ∈ ℕ` ⇒ `p(p-1)/2 = p · (p-1)/2` で `p` の倍数 ⇒
`⁅y, x⁆^(p(p-1)/2) = (⁅y, x⁆^p)^((p-1)/2) = 1`. -/
def setOfPowEqOne (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ}
    (hp : Odd p) : Subgroup G where
  carrier := {x | x^p = 1}
  one_mem' := by change (1 : G)^p = 1; exact one_pow p
  inv_mem' := by
    intro x (hx : x^p = 1)
    change x⁻¹^p = 1
    rw [inv_pow, hx, inv_one]
  mul_mem' := by
    intro x y (hx : x^p = 1) (hy : y^p = 1)
    change (x * y)^p = 1
    rw [mul_pow_of_class_le_two hC, hx, hy, one_mul, one_mul]
    -- Goal: ⁅y, x⁆^(p*(p-1)/2) = 1
    have hcom_p : ⁅y, x⁆^p = 1 := by
      rw [← commutatorElement_pow_left_of_class_le_two hC, hy, commutatorElement_one_left]
    -- p odd ⇒ p - 1 = 2k for some k ⇒ p*(p-1)/2 = p*k.
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow]

/-- **Isaacs Theorem 4.8(b)**: `p > 2` (odd), `commutator G ≤ Z(G)` (class ≤ 2),
全交換子の `p` 乗が `1` ⇒ `x ↦ x^p : G →* G` は (Monoid) 準同型.

**証明**: collection formula `(xy)^p = x^p · y^p · ⁅y, x⁆^(p(p-1)/2)`.
仮定で `⁅y, x⁆^p = 1` + `p` odd ⇒ `p ∣ p(p-1)/2` ⇒ `⁅y, x⁆^(p(p-1)/2) = 1`.
よって `(xy)^p = x^p · y^p`. `1^p = 1` は自明. -/
def powPHom (hC : _root_.commutator G ≤ Subgroup.center G) {p : ℕ} (hp : Odd p)
    (hcomp : ∀ c ∈ _root_.commutator G, c ^ p = 1) : G →* G where
  toFun x := x^p
  map_one' := one_pow p
  map_mul' x y := by
    show (x * y)^p = x^p * y^p
    rw [mul_pow_of_class_le_two hC]
    -- Goal: x^p * y^p * ⁅y, x⁆^(p*(p-1)/2) = x^p * y^p
    have hcom_p : ⁅y, x⁆^p = 1 := hcomp ⁅y, x⁆ (commutatorElement_mem_commutator_top y x)
    obtain ⟨k, hk⟩ := hp
    have hdiv : p * (p - 1) / 2 = p * k := by
      subst hk
      have h1 : 2 * k + 1 - 1 = 2 * k := by omega
      rw [h1, Nat.mul_div_assoc _ (Dvd.intro k rfl)]
      rw [show 2 * k / 2 = k from Nat.mul_div_cancel_left k (by norm_num : (0 : ℕ) < 2)]
    rw [hdiv, pow_mul, hcom_p, one_pow, mul_one]

end

end OddOrder.Isaacs.Ch04


