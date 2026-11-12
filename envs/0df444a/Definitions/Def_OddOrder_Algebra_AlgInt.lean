-- Prove2me | Definitions.Def_OddOrder_Algebra_AlgInt
-- name    : OddOrder_Algebra_AlgInt
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:07.476198+00:00
-- url     : https://prove2.me/theorems/91616923-a4b3-4e67-82b0-009a19f780bc
-- title:
--   Algebraic-integer congruences in $\mathbb{C}$
-- statement:
--   Formalizes congruence modulo an integer in the algebraic integers, the relation $\alpha \equiv \beta \pmod n$ used throughout Peterfalvi, *Character Theory for the Odd Order Theorem*, notably in the proof of (6.7) (pp. 31–32). The basic relation is that $(\alpha-\beta)/n$ is an algebraic integer over $\mathbb{Z}$; it is shown to be an additive congruence, closed under multiplication of one side by any algebraic integer.
--
--   The main definition is `AlgInt.Cong`, the congruence $\alpha \equiv \beta \pmod n$ on $\mathbb{C}$ (`IsIntegral ℤ ((α - β) / n)`).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/AlgInt.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/AlgInt.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Norm
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace OddOrder.AlgInt

/-- **Algebraic-integer congruence in `ℂ`** (Peterfalvi, proof of (6.7)): `α ≡ β (mod n)` means
`(α - β) / n` is an algebraic integer over `ℤ`.  (In Peterfalvi's full notation one additionally
requires `α` and `β` to be algebraic integers; in the §6 applications that part is supplied
separately, e.g. by `character_isIntegral`.) -/
def Cong (n : ℤ) (α β : ℂ) : Prop :=
  IsIntegral ℤ ((α - β) / (n : ℂ))

@[inherit_doc Cong] scoped notation3:50 α " ≡ " β " [ALGMOD " n "]" => Cong n α β

variable {n : ℤ} {a b c d : ℂ}

theorem cong_def (n : ℤ) (α β : ℂ) : (α ≡ β [ALGMOD n]) ↔ IsIntegral ℤ ((α - β) / (n : ℂ)) :=
  Iff.rfl

namespace Cong

/-- Reflexivity: `α ≡ α (mod n)`, since `(α - α)/n = 0` is integral. -/
@[refl] theorem refl (n : ℤ) (α : ℂ) : α ≡ α [ALGMOD n] := by
  unfold Cong
  rw [sub_self, zero_div]
  exact isIntegral_zero

/-- Symmetry: `α ≡ β (mod n)` ⇒ `β ≡ α (mod n)`, via `(β - α)/n = -((α - β)/n)`. -/
@[symm] theorem symm (h : a ≡ b [ALGMOD n]) : b ≡ a [ALGMOD n] := by
  unfold Cong at h ⊢
  rw [show (b - a) / (n : ℂ) = -((a - b) / (n : ℂ)) by ring]
  exact h.neg

/-- Transitivity: `α ≡ β` and `β ≡ γ` ⇒ `α ≡ γ (mod n)`, via
`(α - γ)/n = (α - β)/n + (β - γ)/n`. -/
@[trans] theorem trans (hab : a ≡ b [ALGMOD n]) (hbc : b ≡ c [ALGMOD n]) :
    a ≡ c [ALGMOD n] := by
  unfold Cong at hab hbc ⊢
  rw [show (a - c) / (n : ℂ) = (a - b) / (n : ℂ) + (b - c) / (n : ℂ) by ring]
  exact hab.add hbc

/-- Congruences add: `a ≡ b` and `c ≡ d` ⇒ `a + c ≡ b + d (mod n)`. -/
theorem add (hab : a ≡ b [ALGMOD n]) (hcd : c ≡ d [ALGMOD n]) :
    a + c ≡ b + d [ALGMOD n] := by
  unfold Cong at hab hcd ⊢
  rw [show (a + c - (b + d)) / (n : ℂ) = (a - b) / (n : ℂ) + (c - d) / (n : ℂ) by ring]
  exact hab.add hcd

/-- Congruences subtract: `a ≡ b` and `c ≡ d` ⇒ `a - c ≡ b - d (mod n)`. -/
theorem sub (hab : a ≡ b [ALGMOD n]) (hcd : c ≡ d [ALGMOD n]) :
    a - c ≡ b - d [ALGMOD n] := by
  unfold Cong at hab hcd ⊢
  rw [show (a - c - (b - d)) / (n : ℂ) = (a - b) / (n : ℂ) - (c - d) / (n : ℂ) by ring]
  exact hab.sub hcd

/-- Scale by an algebraic integer on the left: if `k` is an algebraic integer and `a ≡ b (mod n)`,
then `k·a ≡ k·b (mod n)`, via `(k·a - k·b)/n = k·((a - b)/n)`.

This is the central multiplicative step in Peterfalvi (6.7.2)/(6.7.3): one multiplies a congruence
through by `ψ(1)`, by a structure constant `a_{ij}`, or by another integral central-character value,
all of which are algebraic integers. -/
theorem smul_left {k : ℂ} (hk : IsIntegral ℤ k) (h : a ≡ b [ALGMOD n]) :
    k * a ≡ k * b [ALGMOD n] := by
  unfold Cong at h ⊢
  rw [show (k * a - k * b) / (n : ℂ) = k * ((a - b) / (n : ℂ)) by ring]
  exact hk.mul h

/-- **Cancel a coprime integer factor from a congruence.** If `(c : ℂ)·a ≡ (c : ℂ)·b (mod n)` with
`c` coprime to the modulus `n` (as integers), and the endpoints `a`, `b` are themselves algebraic
integers, then `a ≡ b (mod n)`.

This is the "divide by `|C₁|`" step of Peterfalvi (6.7.3): `|C₁|` is prime to `p` (hence coprime to
`n = |P| = p^k`), so it may be cancelled from a congruence modulo `|P|`.  The endpoint-integrality
hypotheses are essential and are supplied by `character_isIntegral` (`a = ψ(z)`, `b = ψ(1)`).
Bézout `u·c + v·n = 1` writes `(a-b)/n = u·(c·(a-b)/n) + v·(a-b)`, integral since both
`c·(a-b)/n = (c·a - c·b)/n` and `a - b` are integral. -/
theorem intMul_cancel_left {c : ℤ} (hcop : IsCoprime c n) (ha : IsIntegral ℤ a)
    (hb : IsIntegral ℤ b) (h : (c : ℂ) * a ≡ (c : ℂ) * b [ALGMOD n]) :
    a ≡ b [ALGMOD n] := by
  unfold Cong at h ⊢
  obtain ⟨u, v, huv⟩ := hcop
  -- `t := (a - b)/n`; the hypothesis gives `c·t` integral, and `a - b` is integral.
  set t : ℂ := (a - b) / (n : ℂ) with ht
  have hct : IsIntegral ℤ ((c : ℂ) * t) := by
    have : ((c : ℂ) * a - (c : ℂ) * b) / (n : ℂ) = (c : ℂ) * t := by rw [ht]; ring
    rwa [this] at h
  have hab : IsIntegral ℤ (a - b) := ha.sub hb
  -- `t = u·(c·t) + v·(a - b)` by Bézout `u·c + v·n = 1` (note `n·t = a - b` after clearing).
  by_cases hn0 : (n : ℂ) = 0
  · -- `n = 0`: then `t = (a-b)/0 = 0`, integral.
    rw [ht, hn0, div_zero]; exact isIntegral_zero
  · have hnt : (n : ℂ) * t = a - b := by
      rw [ht]; field_simp
    have hbez : (u : ℂ) * (c : ℂ) + (v : ℂ) * (n : ℂ) = 1 := by
      have hc : ((u * c + v * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [huv]
      push_cast at hc; linear_combination hc
    have hrw : t = (u : ℂ) * ((c : ℂ) * t) + (v : ℂ) * (a - b) := by
      have hcollect : (u : ℂ) * ((c : ℂ) * t) + (v : ℂ) * (a - b)
          = ((u : ℂ) * (c : ℂ) + (v : ℂ) * (n : ℂ)) * t := by rw [← hnt]; ring
      rw [hcollect, hbez, one_mul]
    rw [hrw]
    exact ((isIntegral_algebraMap (x := u)).mul hct).add
      ((isIntegral_algebraMap (x := v)).mul hab)

end Cong

/-- **Introduction form.** If `α - β = n · c` with `c` an algebraic integer, then `α ≡ β (mod n)`,
provided `n ≠ 0` (so that `(α - β)/n = c`).  This is how congruences are *produced* in the §6
arguments: one exhibits the difference as `n` times an integral element. -/
theorem cong_of_exists_isIntegral (hn : (n : ℂ) ≠ 0) {c : ℂ} (hc : IsIntegral ℤ c)
    (h : a - b = (n : ℂ) * c) : a ≡ b [ALGMOD n] := by
  unfold Cong
  rw [h, mul_div_cancel_left₀ _ hn]
  exact hc

end OddOrder.AlgInt

namespace OddOrder.RepresentationTheory

/-- **A root of unity is an algebraic integer.** If `x` in a commutative ring satisfies
`x ^ n = 1` with `n ≠ 0`, then `x` is integral over `ℤ` — it is a root of the monic polynomial
`X ^ n - 1`. -/
theorem isIntegral_of_pow_eq_one {R : Type*} [CommRing R] {x : R} {n : ℕ} (hn : n ≠ 0)
    (hx : x ^ n = 1) : IsIntegral ℤ x := by
  refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C 1 hn
  · simp [hx]

/-- **A complex number of unit modulus with real part `1` is `1`.** If `‖z‖ = 1` and `z.re = 1`
then `z = 1`: from `z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 = 1` and `z.re = 1` we get `z.im = 0`. -/
private theorem eq_one_of_norm_eq_one_of_re_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hre : z.re = 1) :
    z = 1 := by
  -- `z.im ^ 2 = ‖z‖ ^ 2 - z.re ^ 2 = 1 - 1 = 0`, so `z.im = 0`; with `z.re = 1` this is `1`.
  have hns : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im, hns, hre]
  apply Complex.ext <;> simp [hre, him]

/-- **A complex number of unit modulus has real part at most `1`.** -/
private theorem re_le_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z.re ≤ 1 := by
  have hns : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1), hns]

/-- **Unit complex numbers summing to their count are all `1`** (the equality case of the triangle
inequality, for the keystone `character g = degree ⟹ ρ g = id`).  If a multiset `s` of complex
numbers has `‖z‖ = 1` for every `z ∈ s` and `∑_{z ∈ s} z = card s`, then `z = 1` for every
`z ∈ s`.

Proof (real-part / non-negative-sum argument).  Taking real parts of `∑ z = card s` gives
`∑ z.re = card s`.  Each `z.re ≤ ‖z‖ = 1`, so the multiset `card s · 1 - ∑ z.re = ∑ (1 - z.re)`
is a sum of non-negatives equal to `0`; hence every `1 - z.re = 0`, i.e. `z.re = 1`.  A unit-modulus
complex number with real part `1` is `1` (`eq_one_of_norm_eq_one_of_re_eq_one`). -/
theorem all_eq_one_of_norm_eq_one_of_sum_eq_card {s : Multiset ℂ}
    (hnorm : ∀ z ∈ s, ‖z‖ = 1) (hsum : s.sum = (Multiset.card s : ℂ)) :
    ∀ z ∈ s, z = 1 := by
  -- Reduce to `z.re = 1` for every `z ∈ s`, then apply the unit-modulus rigidity.
  suffices hre : ∀ z ∈ s, z.re = 1 by
    intro z hz; exact eq_one_of_norm_eq_one_of_re_eq_one (hnorm z hz) (hre z hz)
  -- The deficits `1 - z.re ≥ 0` sum to `card s - ∑ z.re = card s - (∑ z).re = card s - card s = 0`.
  have hdef_sum : (s.map fun z => 1 - z.re).sum = 0 := by
    -- `∑ (1 - z.re) = card s · 1 - ∑ z.re`, computed by induction on the multiset.
    have key : ∀ t : Multiset ℂ,
        (t.map fun z => 1 - z.re).sum = (Multiset.card t : ℝ) - (t.map fun z => z.re).sum := by
      intro t
      induction t using Multiset.induction with
      | empty => simp
      | cons a t ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          ih, Nat.cast_add, Nat.cast_one]; ring
    rw [key]
    -- `(∑ z).re = ∑ z.re` (real part is additive over the multiset).
    have hre_sum : (s.map fun z => z.re).sum = ((s.sum).re : ℝ) := by
      have := map_multiset_sum Complex.reAddGroupHom s
      simpa [Complex.coe_reAddGroupHom] using this.symm
    rw [hre_sum, hsum]; simp
  -- Each deficit is non-negative, and their sum is `0`, so each deficit is `0`.
  have hnn : ∀ x ∈ (s.map fun z => 1 - z.re), (0 : ℝ) ≤ x := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨z, hzs, rfl⟩ := hx
    linarith [re_le_one_of_norm_eq_one (hnorm z hzs)]
  have hzero := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hdef_sum
  intro z hz
  have : (1 : ℝ) - z.re = 0 := hzero _ (Multiset.mem_map_of_mem _ hz)
  linarith

/-- **A rational algebraic integer is an integer.** If `q : ℚ` is integral over `ℤ` when viewed
inside `ℂ`, then `q` is the image of an integer: there is `n : ℤ` with `(q : ℂ) = n`.

`ℤ` is integrally closed (it is a `UniqueFactorizationMonoid`, hence integrally closed in its
fraction field `ℚ`).  Transferring `IsIntegral ℤ (q : ℂ)` down the injective `ℚ`-algebra map
`ℚ ↪ ℂ` gives `IsIntegral ℤ q`, and integral closure then yields the integer. -/
theorem isIntegral_rat_imp_int {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) :
    ∃ n : ℤ, (q : ℂ) = n := by
  -- `(q : ℂ) = algebraMap ℚ ℂ q`; transfer integrality down the injection `ℚ ↪ ℂ`.
  have hqℂ : (q : ℂ) = algebraMap ℚ ℂ q := (eq_ratCast (algebraMap ℚ ℂ) q).symm
  rw [hqℂ] at h
  have hQ : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp h
  -- `ℤ` is integrally closed in `ℚ` (it is a UFD), so `q = (n : ℚ)` for some `n : ℤ`.
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hQ
  refine ⟨n, ?_⟩
  -- `hn : algebraMap ℤ ℚ n = q`, i.e. `(n : ℚ) = q`; cast up to `ℂ`.
  rw [algebraMap_int_eq, Int.coe_castRingHom] at hn
  rw [← hn]
  push_cast
  ring

end OddOrder.RepresentationTheory


