-- Prove2me | Definitions.Def_OddOrder_GroupTheory_SemiDihedral
-- name    : OddOrder_GroupTheory_SemiDihedral
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:25.24731+00:00
-- url     : https://prove2.me/theorems/19415fe6-9e0d-4418-9f7d-ebbc212f6e38
-- title:
--   The semidihedral group
-- statement:
--   Defines the semidihedral (quasidihedral) group $SD_{2^{n+1}}$ of order $2^{n+1}$, given by the presentation $\langle c,a\mid c^{2^n}=1,\ a^2=1,\ aca^{-1}=c^{2^{n-1}-1}\rangle$. Together with the cyclic, dihedral and generalized quaternion groups it is one of the four classes of 2-groups with a cyclic maximal subgroup.
--
--   Main definitions: `SemiDihedralGroup n` (defined for all $n$), `twist` (the factor $r$ in $aca^{-1}=c^r$), and the group operations (`mul`, `one`, `inv`) built from explicit multiplication formulas.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/SemiDihedral.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/SemiDihedral.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.LinearCombination

namespace OddOrder.GroupTheory

/-- The **semidihedral group** (a.k.a. **quasidihedral group**) `SemiDihedralGroup n`
of order `2 ^ (n+1)`. It is defined by the presentation
$\langle c, a \mid c^{2^n} = 1,\ a^2 = 1,\ a c a^{-1} = c^{2^{n-1} - 1}\rangle$.
We write `c i` for $c^i$ and `ca i` for $a \cdot c^i$. -/
inductive SemiDihedralGroup (n : ℕ) : Type
  | c : ZMod (2 ^ n) → SemiDihedralGroup n
  | ca : ZMod (2 ^ n) → SemiDihedralGroup n
  deriving DecidableEq

namespace SemiDihedralGroup

variable {n : ℕ}

/-- The twist factor `r` appearing in the relation `a c a⁻¹ = c^r`.

Mathematically, `r := 2^(n-1) - 1`, valid for `n ≥ 2`. The genuine semidihedral
group requires `n ≥ 3`. For `n = 0` we get `ZMod 1` (trivial). For `n = 1` the
formula `2^0 - 1 = 0` would make the construction non-associative
(`r² = 0 ≠ 1` in `ZMod 2`); so we override and set `twist 1 := 1` to keep
the construction a valid group (in this degenerate case it coincides with
the Klein four group `ZMod 2 × ZMod 2`). -/
def twist : (n : ℕ) → ZMod (2 ^ n)
  | 0 => 0
  | 1 => 1
  | n + 2 => (2 ^ (n + 1) : ZMod (2 ^ (n + 2))) - 1

/-- The key arithmetic identity that makes the multiplication associative:
`r * r = 1` in `ZMod (2^n)`.

For `n ≥ 2`, `r = 2^(n-1) - 1` and `r² = 2^(2n-2) - 2 · 2^(n-1) + 1 = 2^(2n-2) - 2^n + 1`,
and modulo `2^n` both `2^(2n-2)` and `2^n` vanish. For `n ≤ 1` we check by `decide`. -/
theorem twist_mul_self : twist n * twist n = 1 := by
  match n with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    change ((2 ^ (k + 1) : ZMod (2 ^ (k + 2))) - 1) *
         ((2 ^ (k + 1) : ZMod (2 ^ (k + 2))) - 1) = 1
    have h2 : (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) = 0 := by
      have key : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
      have eq1 : (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) =
          ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) * (2 ^ k : ZMod (2 ^ (k + 2))) := by
        push_cast
        ring
      rw [eq1, key, zero_mul]
    have h3 : (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) = 0 := by
      have key : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
      have eq1 : (2 : ZMod (2 ^ (k + 2))) * (2 ^ (k + 1)) =
          ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) := by
        push_cast; rw [pow_succ]; ring
      rw [eq1, key]
    linear_combination h2 - h3

/-- Multiplication on the semidihedral group, given by the formulas derived from
`a c = c^r a` (equivalently `c a = a c^r`), where `r := 2^(n-1) - 1`. -/
private def mul : SemiDihedralGroup n → SemiDihedralGroup n → SemiDihedralGroup n
  | c i, c j => c (i + j)
  | c i, ca j => ca (twist n * i + j)
  | ca i, c j => ca (i + j)
  | ca i, ca j => c (twist n * i + j)

/-- The identity element `1` is `c 0 = c^0`. -/
private def one : SemiDihedralGroup n := c 0

instance : Inhabited (SemiDihedralGroup n) := ⟨one⟩

/-- Inverse on the semidihedral group. For `c i`, the inverse is `c (-i)`.
For `ca i`, we need `ca i * ca j = c (twist n * i + j) = 1`, so `j = -(twist n * i)`. -/
private def inv : SemiDihedralGroup n → SemiDihedralGroup n
  | c i => c (-i)
  | ca i => ca (-(twist n * i))

/-- The group structure on `SemiDihedralGroup n`. -/
instance : Group (SemiDihedralGroup n) where
  mul := mul
  mul_assoc := by
    have hr : twist n * twist n = 1 := twist_mul_self
    rintro (i | i) (j | j) (k | k) <;>
      (change mul (mul _ _) _ = mul _ (mul _ _)) <;>
      simp only [mul] <;>
      first
        | rfl
        | (refine congr_arg c ?_; linear_combination i * hr)
        | (refine congr_arg ca ?_; linear_combination i * hr)
        | (refine congr_arg c ?_; ring)
        | (refine congr_arg ca ?_; ring)
  one := one
  one_mul := by
    rintro (i | i)
    · exact congr_arg c (zero_add i)
    · change ca (twist n * 0 + i) = ca i
      rw [mul_zero, zero_add]
  mul_one := by
    rintro (i | i)
    · exact congr_arg c (add_zero i)
    · exact congr_arg ca (add_zero i)
  inv := inv
  inv_mul_cancel := by
    rintro (i | i)
    · exact congr_arg c (neg_add_cancel i)
    · change c (twist n * (-(twist n * i)) + i) = one
      have hcalc : twist n * (-(twist n * i)) = -(twist n * twist n * i) := by ring
      rw [hcalc, twist_mul_self, one_mul, neg_add_cancel]
      rfl

@[simp]
theorem c_mul_c (i j : ZMod (2 ^ n)) : c i * c j = c (i + j) := rfl

@[simp]
theorem c_mul_ca (i j : ZMod (2 ^ n)) : c i * ca j = ca (twist n * i + j) := rfl

@[simp]
theorem ca_mul_c (i j : ZMod (2 ^ n)) : ca i * c j = ca (i + j) := rfl

@[simp]
theorem ca_mul_ca (i j : ZMod (2 ^ n)) : ca i * ca j = c (twist n * i + j) := rfl

@[simp]
theorem inv_c (i : ZMod (2 ^ n)) : (c i)⁻¹ = c (-i) := rfl

@[simp]
theorem inv_ca (i : ZMod (2 ^ n)) : (ca i)⁻¹ = ca (-(twist n * i)) := rfl

@[simp]
theorem c_zero : c 0 = (1 : SemiDihedralGroup n) := rfl

/-- The equivalence between `SemiDihedralGroup n` and the disjoint sum of two
copies of `ZMod (2 ^ n)`. -/
@[simps]
def equivSum : SemiDihedralGroup n ≃ ZMod (2 ^ n) ⊕ ZMod (2 ^ n) where
  toFun
    | c j => .inl j
    | ca j => .inr j
  invFun
    | .inl j => c j
    | .inr j => ca j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

instance : NeZero (2 ^ n) := ⟨(Nat.two_pow_pos n).ne'⟩

instance : Fintype (SemiDihedralGroup n) :=
  Fintype.ofEquiv _ equivSum.symm

instance : Nontrivial (SemiDihedralGroup n) :=
  ⟨⟨c 0, ca 0, by by_contra h; injection h⟩⟩

/-- `SemiDihedralGroup n` has `2 ^ (n+1)` elements. -/
theorem card : Fintype.card (SemiDihedralGroup n) = 2 ^ (n + 1) := by
  rw [Fintype.card_eq.mpr ⟨equivSum⟩, Fintype.card_sum, ZMod.card, ← two_mul, pow_succ, mul_comm]

@[simp]
theorem c_one_pow (k : ℕ) : (c 1 : SemiDihedralGroup n) ^ k = c k := by
  induction k with
  | zero => rw [Nat.cast_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, c_mul_c]
    congr 1
    push_cast
    ring

@[simp]
theorem c_pow (i : ZMod (2 ^ n)) (k : ℕ) :
    (c i) ^ k = c (i * (k : ZMod (2 ^ n))) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, mul_zero]; rfl
  | succ k IH =>
    rw [pow_succ, IH, c_mul_c]
    congr 1
    push_cast
    ring

theorem c_one_pow_n : (c 1 : SemiDihedralGroup n) ^ (2 ^ n) = 1 := by
  rw [c_one_pow]
  show c ((2 ^ n : ℕ) : ZMod (2 ^ n)) = 1
  rw [ZMod.natCast_self]
  rfl

/-- `orderOf (c 1) = 2 ^ n`. For `n = 0` both sides are `1` (the group is trivial-or-`Z/2`,
and `c 1 = c 0 = 1`); for `n ≥ 1` the element `c 1` generates a cyclic subgroup of index 2. -/
@[simp]
theorem orderOf_c_one : orderOf (c 1 : SemiDihedralGroup n) = 2 ^ n := by
  apply (Nat.le_of_dvd (NeZero.pos _)
    (orderOf_dvd_of_pow_eq_one c_one_pow_n)).lt_or_eq.resolve_left
  intro h
  have h1 : (c 1 : SemiDihedralGroup n) ^ orderOf (c 1 : SemiDihedralGroup n) = 1 :=
    pow_orderOf_eq_one _
  rw [c_one_pow] at h1
  have h_eq : (c ((orderOf (c 1 : SemiDihedralGroup n) : ℕ) : ZMod (2 ^ n)) :
      SemiDihedralGroup n) = c 0 := h1
  injection h_eq with h2
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
  exact absurd h2 (orderOf_pos _).ne'

@[simp]
theorem ca_sq (i : ZMod (2 ^ n)) : (ca i : SemiDihedralGroup n) ^ 2 = c (twist n * i + i) := by
  rw [sq, ca_mul_ca]

end SemiDihedralGroup

end OddOrder.GroupTheory


