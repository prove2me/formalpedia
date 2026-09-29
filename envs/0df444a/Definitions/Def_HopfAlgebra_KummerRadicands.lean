-- Prove2me | Definitions.Def_HopfAlgebra_KummerRadicands
-- name    : HopfAlgebra_KummerRadicands
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/f2647da3-514e-5cb3-9500-b1a8e6eb9c0f
-- title:
--   Kummer radicands and carry cocycle for unit exponent vectors
-- statement:
--   Throughout, $O$ is a commutative ring, $n$ and $t$ are natural numbers, and $u \colon \mathrm{Fin}\,t \to O^\times$ is a family of units (the radicands). Exponent vectors are elements of $(\mathbb{Z}/n)^t$, written as functions $k \colon \mathrm{Fin}\,t \to \mathbb{Z}/n$, and each coordinate is lifted to a natural number by the canonical representative `ZMod.val`.
--
--   Two definitions are made. The radicand attached to $k$ is the unit $\operatorname{rad}(k) = \prod_{i} u_i^{\,\mathrm{val}(k_i)}$, and the carry attached to a pair $(k,k')$ is $\operatorname{carry}(k,k') = \prod_i u_i^{-\lfloor (\mathrm{val}(k_i)+\mathrm{val}(k'_i))/n \rfloor}$, the product over coordinates of inverse powers of $u_i$ with exponent the integer quotient by $n$ of the sum of the two chosen representatives. Both take values in $O^\times$.
--
--   The accompanying lemmas record the algebraic identities these satisfy. `rad_zero` gives $\operatorname{rad}(0)=1$; `carry_comm` gives symmetry $\operatorname{carry}(k,k')=\operatorname{carry}(k',k)$; under the standing assumption $n \neq 0$, `carry_zero_left` and `carry_zero_right` give normalisation $\operatorname{carry}(0,k)=\operatorname{carry}(k,0)=1$. The single-coordinate computation `inv_pow_div_pow_mul` states, for a unit $v$ and $a,b \in \mathbb{Z}/n$, that $(v^{-1})^{\lfloor(\mathrm{val}(a)+\mathrm{val}(b))/n\rfloor \cdot n} \cdot v^{\mathrm{val}(a)}v^{\mathrm{val}(b)} = v^{\mathrm{val}(a+b)}$; taking the product over coordinates yields `carry_pow_mul_rad_mul_rad`, the identity
--   $$\operatorname{carry}(k,k')^{\,n}\,\operatorname{rad}(k)\,\operatorname{rad}(k') = \operatorname{rad}(k+k').$$
--   Finally `div_add_mod_add_div` is the arithmetic of carrying in a triple sum, $(a+b)/n + ((a+b)\bmod n + c)/n = (b+c)/n + (a + (b+c)\bmod n)/n$ for $n>0$, and it gives `carry_mul_carry_add`, the $2$-cocycle identity
--   $$\operatorname{carry}(k,k')\,\operatorname{carry}(k+k',k'') = \operatorname{carry}(k',k'')\,\operatorname{carry}(k,k'+k'').$$
--
--   **Relation to Mathlib.** Mathlib has no notion of such radicand/carry data; these are the project's own definitions, built from Mathlib's `ZMod.val` and products of units.
--
--   **Where it is used.** This is the elementary input for the construction of a Kummer-type Hopf order: the algebra $\prod_{k \in (\mathbb{Z}/n)^t} O[X]/(X^n - \operatorname{rad}(k))$, whose comultiplication sends a root to $\operatorname{carry}$ times the tensor product of roots, so that the $2$-cocycle identity is coassociativity and `carry_pow_mul_rad_mul_rad` makes the multiplication well defined. It is used by the module establishing the existence of such a Kummer carrier from this cocycle data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HopfAlgebra_KummerRadicands.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace HopfAlgebra.KummerRadicands

variable {O : Type*} [CommRing O] {n : ℕ} {t : ℕ} (u : Fin t → Oˣ)

def rad (k : Fin t → ZMod n) : Oˣ := ∏ i, u i ^ (k i).val

def carry (k k' : Fin t → ZMod n) : Oˣ := ∏ i, (u i)⁻¹ ^ (((k i).val + (k' i).val) / n)

theorem rad_zero : rad u (0 : Fin t → ZMod n) = 1 := by
  simp [rad]

theorem carry_comm (k k' : Fin t → ZMod n) : carry u k k' = carry u k' k := by
  simp only [carry, Nat.add_comm (k _).val]

variable [NeZero n]

theorem carry_zero_left (k : Fin t → ZMod n) : carry u 0 k = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Pi.zero_apply, ZMod.val_zero, zero_add, Nat.div_eq_of_lt (ZMod.val_lt (k i)), pow_zero]

theorem carry_zero_right (k : Fin t → ZMod n) : carry u k 0 = 1 := by
  rw [carry_comm, carry_zero_left]

theorem inv_pow_div_pow_mul (v : Oˣ) (a b : ZMod n) :
    (v⁻¹ ^ ((a.val + b.val) / n)) ^ n * (v ^ a.val * v ^ b.val) = v ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add]
  set s := a.val + b.val
  have h := Nat.mod_add_div s n
  calc (v⁻¹ ^ (s / n)) ^ n * v ^ s = (v⁻¹ ^ (s / n)) ^ n * v ^ (s % n + n * (s / n)) := by rw [h]
    _ = v ^ (s % n) * ((v⁻¹ ^ (s / n)) ^ n * (v ^ (s / n)) ^ n) := by
        rw [pow_add, pow_mul', mul_left_comm]
    _ = v ^ (s % n) := by rw [← mul_pow, inv_pow, inv_mul_cancel, one_pow, mul_one]

theorem carry_pow_mul_rad_mul_rad (k k' : Fin t → ZMod n) :
    carry u k k' ^ n * (rad u k * rad u k') = rad u (k + k') := by
  simp only [carry, rad, ← Finset.prod_pow, ← Finset.prod_mul_distrib, Pi.add_apply]
  exact Finset.prod_congr rfl fun i _ => inv_pow_div_pow_mul (u i) (k i) (k' i)

omit [NeZero n] in

theorem div_add_mod_add_div (a b c : ℕ) (hn : 0 < n) :
    (a + b) / n + ((a + b) % n + c) / n = (b + c) / n + (a + (b + c) % n) / n := by
  have h1 : (a + b + c) / n = (a + b) / n + ((a + b) % n + c) / n := by
    conv_lhs => rw [← Nat.mod_add_div (a + b) n, add_right_comm, Nat.add_mul_div_left _ _ hn]
    omega
  have h2 : (a + b + c) / n = (b + c) / n + (a + (b + c) % n) / n := by
    conv_lhs => rw [add_assoc, ← Nat.mod_add_div (b + c) n, ← add_assoc, Nat.add_mul_div_left _ _ hn]
    omega
  omega

theorem carry_mul_carry_add (k k' k'' : Fin t → ZMod n) :
    carry u k k' * carry u (k + k') k'' = carry u k' k'' * carry u k (k' + k'') := by
  simp only [carry, ← Finset.prod_mul_distrib, Pi.add_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, ← pow_add, ZMod.val_add, ZMod.val_add, div_add_mod_add_div _ _ _ (NeZero.pos n)]

end HopfAlgebra.KummerRadicands


