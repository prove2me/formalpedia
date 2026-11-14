-- Prove2me | Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
-- name    : BuhaiPapers_Background_PolyTime_Rat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:02:25.820586+00:00
-- url     : https://prove2.me/theorems/8339ba28-331f-47ec-9de1-41730f568480
-- title:
--   Background.PolyTime.Rat — Rational arithmetic in polynomial time
-- statement:
--   This is module `Background.PolyTime.Rat`, shared background material of the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0), published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) uses it.
--
--   Rational numbers are encoded by their numerator and denominator in lowest terms
--   (`Encoding.encRat`). Each arithmetic operation computes a numerator and a denominator with integer
--   arithmetic and reduces them by their gcd, as `Rat.normalize` does, so it runs in polynomial time on
--   multitape Turing machines with complexitylib's binary integers.
--
--   The certificates are plain `Turing.MultiTapeTM.ComputableInPolyTime` statements, registered with
--   `fun_prop` in the style of complexitylib: `rat_add` and `rat_add'` for a computed pair of rationals,
--   and so on.
--
--   **Contents.** The module is published as a whole: 42 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Background/PolyTime/Rat.lean

module

public import Definitions.Def_BuhaiPapers_Background_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Gcd
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
public import Definitions.Def_Complexitylib_0ebd467_Computability_PolyTime_Int_ExactDiv
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Length
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Membership
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Div
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Pi
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
public import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init
public import Mathlib.Data.Rat.Floor

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `Background.PolyTime.Rat` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Rational arithmetic in polynomial time

Rational numbers are encoded by their numerator and denominator in lowest terms
(`Encoding.encRat`). Each arithmetic operation computes a numerator and a denominator with integer
arithmetic and reduces them by their gcd, as `Rat.normalize` does, so it runs in polynomial time on
multitape Turing machines with complexitylib's binary integers.

The certificates are plain `Turing.MultiTapeTM.ComputableInPolyTime` statements, registered with
`fun_prop` in the style of complexitylib: `rat_add` and `rat_add'` for a computed pair of rationals,
and so on.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Numerators and denominators -/

theorem rat_numDen : ComputableInPolyTime (fun q : ℚ => (q.num, q.den)) encRat
    (encPair encIntBin encNat) :=
  of_eq fun _ => rfl

theorem rat_num : ComputableInPolyTime (fun q : ℚ => q.num) encRat encIntBin :=
  (fst encIntBin encNat).comp rat_numDen

theorem rat_den : ComputableInPolyTime (fun q : ℚ => q.den) encRat encNat :=
  (snd encIntBin encNat).comp rat_numDen

@[fun_prop]
theorem rat_num' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => (f a).num) input encIntBin :=
  rat_num.comp hf

@[fun_prop]
theorem rat_den' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => (f a).den) input encNat :=
  rat_den.comp hf

/-- A rational is computed once its numerator and denominator in lowest terms are. -/
theorem rat_of_numDen {f : α → ℚ} {g : α → ℤ × ℕ}
    (hg : ComputableInPolyTime g input (encPair encIntBin encNat))
    (h : ∀ a, g a = ((f a).num, (f a).den)) : ComputableInPolyTime f input encRat :=
  hg.of_enc_eq fun a => by rw [h a]; rfl

/-- `Rat.normalize n d`, in lowest terms: numerator and denominator divided by their gcd. -/
theorem rat_normalize_numDen (n : ℤ) {d : ℕ} (hd : d ≠ 0) :
    ((Rat.normalize n d hd).num, (Rat.normalize n d hd).den) =
      (n / ((n.natAbs.gcd d : ℕ) : ℤ), d / n.natAbs.gcd d) := by
  rw [Rat.num_normalize, Rat.den_normalize]

/-- Reducing a numerator and a positive denominator by their gcd. -/
theorem reduce_polytime : ComputableInPolyTime
    (fun p : ℤ × ℕ => (p.1 / ((p.1.natAbs.gcd p.2 : ℕ) : ℤ), p.2 / p.1.natAbs.gcd p.2))
    (encPair encIntBin encNat) (encPair encIntBin encNat) := by
  fun_prop

/-! ### Arithmetic -/

theorem rat_add : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 + p.2) (encPair encRat encRat)
    encRat := by
  refine rat_of_numDen (reduce_polytime.comp (g := fun p : ℚ × ℚ =>
    (p.1.num * p.2.den + p.2.num * p.1.den, p.1.den * p.2.den)) (by fun_prop)) fun p => ?_
  simp only [Function.comp_apply]
  rw [Rat.add_def, rat_normalize_numDen]

@[fun_prop]
theorem rat_add' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => f a + g a) input encRat :=
  rat_add.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem rat_neg : ComputableInPolyTime (fun q : ℚ => -q) encRat encRat :=
  rat_of_numDen (g := fun q : ℚ => (-q.num, q.den)) (by fun_prop) fun q => by
    rw [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]

@[fun_prop]
theorem rat_neg' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => -f a) input encRat :=
  rat_neg.comp hf

@[fun_prop]
theorem rat_sub' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => f a - g a) input encRat := by
  simp only [sub_eq_add_neg]
  fun_prop

theorem rat_mul : ComputableInPolyTime (fun p : ℚ × ℚ => p.1 * p.2) (encPair encRat encRat)
    encRat := by
  refine rat_of_numDen (reduce_polytime.comp (g := fun p : ℚ × ℚ =>
    (p.1.num * p.2.num, p.1.den * p.2.den)) (by fun_prop)) fun p => ?_
  simp only [Function.comp_apply]
  rw [Rat.mul_def, rat_normalize_numDen]

@[fun_prop]
theorem rat_mul' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => f a * g a) input encRat :=
  rat_mul.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem rat_inv : ComputableInPolyTime (fun q : ℚ => q⁻¹) encRat encRat :=
  rat_of_numDen (g := fun q : ℚ =>
      (q.num.sign * q.den, if decide (q.num = 0) then 1 else q.num.natAbs))
    (by fun_prop) fun q => by
    rw [Rat.num_inv, Rat.den_inv]
    simp

@[fun_prop]
theorem rat_inv' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => (f a)⁻¹) input encRat :=
  rat_inv.comp hf

@[fun_prop]
theorem rat_div' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => f a / g a) input encRat := by
  simp only [div_eq_mul_inv]
  fun_prop

theorem rat_intCast : ComputableInPolyTime (fun z : ℤ => (z : ℚ)) encIntBin encRat :=
  rat_of_numDen (g := fun z : ℤ => (z, 1)) (by fun_prop) fun z => by
    rw [Rat.num_intCast, Rat.den_intCast]

@[fun_prop]
theorem rat_intCast' {f : α → ℤ} (hf : ComputableInPolyTime f input encIntBin) :
    ComputableInPolyTime (fun a => (f a : ℚ)) input encRat :=
  rat_intCast.comp hf

theorem rat_natCast : ComputableInPolyTime (fun n : ℕ => (n : ℚ)) encNat encRat :=
  rat_of_numDen (g := fun n : ℕ => ((n : ℤ), 1)) (by fun_prop) fun n => by
    rw [Rat.num_natCast, Rat.den_natCast]

@[fun_prop]
theorem rat_natCast' {f : α → ℕ} (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => (f a : ℚ)) input encRat :=
  rat_natCast.comp hf

/-! ### Comparisons and rounding -/

theorem rat_le : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 ≤ p.2))
    (encPair encRat encRat) encBool := by
  have h : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1.num * p.2.den ≤ p.2.num * p.1.den))
      (encPair encRat encRat) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_le'
      (ComputableInPolyTime.tidy (by fun_prop)) (ComputableInPolyTime.tidy (by fun_prop)))
  exact h.of_enc_eq fun p => congrArg encBool (decide_eq_decide.2 (Rat.le_iff p.1 p.2))

@[fun_prop]
theorem rat_le' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => decide (f a ≤ g a)) input encBool :=
  rat_le.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem rat_lt : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1 < p.2))
    (encPair encRat encRat) encBool := by
  have h : ComputableInPolyTime (fun p : ℚ × ℚ => decide (p.1.num * p.2.den < p.2.num * p.1.den))
      (encPair encRat encRat) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_lt'
      (ComputableInPolyTime.tidy (by fun_prop)) (ComputableInPolyTime.tidy (by fun_prop)))
  exact h.of_enc_eq fun p => congrArg encBool (decide_eq_decide.2 (Rat.lt_iff p.1 p.2))

@[fun_prop]
theorem rat_lt' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => decide (f a < g a)) input encBool :=
  rat_lt.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem rat_floor : ComputableInPolyTime (fun q : ℚ => ⌊q⌋) encRat encIntBin := by
  have h : ComputableInPolyTime (fun q : ℚ => q.num / (q.den : ℤ)) encRat encIntBin := by
    fun_prop
  exact h.of_enc_eq fun q => by rw [Rat.floor_def']

@[fun_prop]
theorem rat_floor' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => ⌊f a⌋) input encIntBin :=
  rat_floor.comp hf

@[fun_prop]
theorem rat_sq' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => f a ^ 2) input encRat := by
  have : ComputableInPolyTime (fun a => f a * f a) input encRat :=
    rat_mul.comp (g := fun a => (f a, f a)) (hf.prod hf)
  simpa only [sq] using this

@[fun_prop]
theorem rat_min' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => min (f a) (g a)) input encRat := by
  have h : ComputableInPolyTime (fun a => if decide (f a ≤ g a) = true then f a else g a) input
      encRat := ite' (rat_le' hf hg) hf hg
  convert h using 1
  funext a
  simp only [decide_eq_true_eq]
  exact min_def _ _

@[fun_prop]
theorem rat_max' {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a => max (f a) (g a)) input encRat := by
  have h : ComputableInPolyTime (fun a => if decide (f a ≤ g a) = true then g a else f a) input
      encRat := ite' (rat_le' hf hg) hg hf
  convert h using 1
  funext a
  simp only [decide_eq_true_eq]
  exact max_def _ _

@[fun_prop]
theorem rat_two_pow' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a => (2 : ℚ) ^ f a) input encRat := by
  have : ComputableInPolyTime (fun a => ((2 ^ f a : ℕ) : ℚ)) input encRat :=
    rat_natCast' (binary_two_pow.comp (g := f) hf)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using this

theorem rat_abs : ComputableInPolyTime (fun q : ℚ => |q|) encRat encRat := by
  have h : ComputableInPolyTime (fun q : ℚ => if decide (0 ≤ q) = true then q else -q) encRat
      encRat := ite' (rat_le' (const 0) id') id' (rat_neg' id')
  convert h using 1
  funext q
  split_ifs with hq
  · simp only [decide_eq_true_eq] at hq
    exact abs_of_nonneg hq
  · simp only [decide_eq_true_eq, not_le] at hq
    exact abs_of_neg hq

@[fun_prop]
theorem rat_abs' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a => |f a|) input encRat :=
  rat_abs.comp (g := f) hf

/-! ### Sums -/

/-- The product of the denominators of a list of rationals. -/
def denProd (l : List ℚ) : ℤ := (l.map fun q => (q.den : ℤ)).prod

theorem denProd_pos (l : List ℚ) : 0 < denProd l :=
  List.prod_pos fun z hz => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
    exact_mod_cast q.den_pos

/-- A sum of rationals over the common denominator `∏ dᵢ`: `(∑ nᵢ (D / dᵢ)) / D`. -/
theorem sum_eq_div_denProd (l : List ℚ) :
    l.sum = (((l.map fun q => q.num * (denProd l / q.den)).sum : ℤ) : ℚ) / (denProd l : ℚ) := by
  have hD : (denProd l : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos l).ne'
  have hterm : ∀ q ∈ l, ((q.num * (denProd l / q.den) : ℤ) : ℚ) = q * denProd l := by
    intro q hq
    have hdvd : (q.den : ℤ) ∣ denProd l :=
      List.dvd_prod (List.mem_map_of_mem (f := fun q : ℚ => (q.den : ℤ)) hq)
    obtain ⟨e, he⟩ := hdvd
    have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [he, Int.mul_ediv_cancel_left _ hden]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  rw [eq_div_iff hD, Int.cast_list_sum, List.map_map]
  have hmap : List.map ((Int.cast : ℤ → ℚ) ∘ fun q => q.num * (denProd l / q.den)) l =
      List.map (fun q => q * (denProd l : ℚ)) l :=
    List.map_congr_left fun q hq => hterm q hq
  rw [hmap, List.sum_map_mul_right, List.map_id']

theorem rat_sum : ComputableInPolyTime List.sum (encList encRat) encRat := by
  have hD : ComputableInPolyTime denProd (encList encRat) encIntBin := by
    unfold denProd
    have h : ComputableInPolyTime (fun l : List ℚ => l.map fun q => (q.den : ℤ))
        (encList encRat) (encList encIntBin) := by fun_prop
    exact .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp h.tidy)
  have hnum : ComputableInPolyTime
      (fun l : List ℚ => (l.map fun q => q.num * (denProd l / q.den)).sum)
      (encList encRat) encIntBin := by
    have h : ComputableInPolyTime (fun l : List ℚ => l.map fun q => q.num * (denProd l / q.den))
        (encList encRat) (encList encIntBin) :=
      mapWithInput (by fun_prop) (by fun_prop)
    exact .of_tidy (ComputableTidilyInPolyTime.intBin_sum.comp h.tidy)
  have h : ComputableInPolyTime
      (fun l : List ℚ => (((l.map fun q => q.num * (denProd l / q.den)).sum : ℤ) : ℚ) /
        (denProd l : ℚ)) (encList encRat) encRat := by fun_prop
  exact h.of_enc_eq fun l => by rw [← sum_eq_div_denProd]

@[fun_prop]
theorem rat_sum' {f : α → List ℚ} (hf : ComputableInPolyTime f input (encList encRat)) :
    ComputableInPolyTime (fun a => (f a).sum) input encRat :=
  rat_sum.comp (g := f) hf

/-! ### Products -/

/-- A product of rationals: the product of the numerators over the product of the
denominators. -/
theorem prod_eq_div (l : List ℚ) :
    l.prod = (((l.map fun q => q.num).prod : ℤ) : ℚ) /
      (((l.map fun q => (q.den : ℤ)).prod : ℤ) : ℚ) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    push_cast
    have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [mul_div_mul_comm, Rat.num_div_den]

theorem rat_prod : ComputableInPolyTime List.prod (encList encRat) encRat := by
  have hn : ComputableInPolyTime (fun l : List ℚ => (l.map fun q => q.num).prod)
      (encList encRat) encIntBin := by
    have h : ComputableInPolyTime (fun l : List ℚ => l.map fun q => q.num)
        (encList encRat) (encList encIntBin) := by fun_prop
    exact .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp h.tidy)
  have hd : ComputableInPolyTime (fun l : List ℚ => (l.map fun q => (q.den : ℤ)).prod)
      (encList encRat) encIntBin := by
    have h : ComputableInPolyTime (fun l : List ℚ => l.map fun q => (q.den : ℤ))
        (encList encRat) (encList encIntBin) := by fun_prop
    exact .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp h.tidy)
  have h : ComputableInPolyTime
      (fun l : List ℚ => (((l.map fun q => q.num).prod : ℤ) : ℚ) /
        (((l.map fun q => (q.den : ℤ)).prod : ℤ) : ℚ)) (encList encRat) encRat := by fun_prop
  exact h.of_enc_eq fun l => by rw [← prod_eq_div]

@[fun_prop]
theorem rat_prod' {f : α → List ℚ} (hf : ComputableInPolyTime f input (encList encRat)) :
    ComputableInPolyTime (fun a => (f a).prod) input encRat :=
  rat_prod.comp (g := f) hf

end Turing.MultiTapeTM.ComputableInPolyTime


