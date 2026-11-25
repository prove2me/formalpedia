-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_34
-- name    : LinearSetReconciliation327_Main_B65_34
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T04:14:42.399893+00:00
-- url     : https://prove2.me/theorems/a3bf622c-8679-4d22-8186-27837b6d75da
-- title:
--   Theorem 6.5 dependency bundle 34
-- statement:
--   Theorem 6.5 dependency bundle 34
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Mathlib
set_option autoImplicit false

section S_Upstream626520261123
set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LinearSetReconciliation327.Main.Upstream6265

/-! ## Pinsketch uniqueness (self-contained copy of the uniqueness half of
Proposition 2.1)

`s612_pin_unique` says that a vector of weight at most `t` is determined by its syndrome
`Pin_{N,t}`; the lemmas below it are the characteristic-two and Vandermonde ingredients.
Inlined so that this file needs no open platform theorem. -/
section FieldFacts

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- A field that is a `ZMod 2`-algebra has characteristic two. -/
theorem s612_pinsketch_two_eq_zero : (2 : F) = 0 := by
  have h : ((2 : ℕ) : F) = 0 := by
    rw [← map_natCast (algebraMap (ZMod 2) F) 2, CharP.cast_eq_zero (ZMod 2) 2, map_zero]
  simpa using h

theorem s612_pinsketch_charP : CharP F 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero s612_pinsketch_two_eq_zero

/-- In characteristic two, `a + a = 0`. -/
theorem s612_pinsketch_add_self (a : F) : a + a = 0 := by
  haveI := s612_pinsketch_charP (F := F)
  exact CharTwo.add_self_eq_zero a

/-- In characteristic two, `a + b = 0` forces `a = b`. -/
theorem s612_pinsketch_eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  haveI := s612_pinsketch_charP (F := F)
  exact CharTwo.add_eq_zero.mp h

/-- The freshman's dream: squaring is additive in characteristic two. -/
theorem s612_pinsketch_sum_sq {α : Type} (s : Finset α) (f : α → F) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  haveI := s612_pinsketch_charP (F := F)
  exact CharTwo.sum_sq s f

/-- `(n : F)` is `0` or `1` according to the parity of `n`, in characteristic two. -/
theorem s612_pinsketch_natCast_eq_ite (n : ℕ) : (n : F) = if Even n then 0 else 1 := by
  haveI := s612_pinsketch_charP (F := F)
  exact CharTwo.natCast_eq_ite n

/-- The only two elements of `ZMod 2`. -/
theorem s612_zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact h z

/-- Scalar multiplication by a `ZMod 2`-element is either `0` or the identity. -/
theorem s612_zmod2_smul_eq (z : ZMod 2) (v : F) : z • v = if z = 1 then v else 0 := by
  rcases s612_zmod2_eq_zero_or_one z with h | h <;> simp [h]

end FieldFacts

/-! ## Power sums as sums over the support -/

section PowerSums

variable {F : Type} [Field F] [Algebra (ZMod 2) F]
variable {N : ℕ}

/-- The `ZMod 2`-support of a binary vector, written exactly as in the statement. -/
def s612_binSupp (x : Fin N → ZMod 2) : Finset (Fin N) := univ.filter (fun i => x i = 1)

theorem s612_mem_binSupp {x : Fin N → ZMod 2} {i : Fin N} : i ∈ s612_binSupp x ↔ x i = 1 := by
  simp [s612_binSupp]

/-- `P_a(x)` is the `a`-th power sum of the field elements indexed by the support. -/
theorem s612_pinPower_eq_sum_supp (ι : ℕ → F) (a : ℕ) (x : Fin N → ZMod 2) :
    pinPower ι a x = ∑ i ∈ s612_binSupp x, ι i.val ^ a := by
  rw [pinPower]
  calc ∑ i, x i • ι i.val ^ a
      = ∑ i, (if x i = 1 then ι i.val ^ a else 0) := by
        exact Finset.sum_congr rfl (fun i _ => s612_zmod2_smul_eq (x i) _)
    _ = ∑ i ∈ univ.filter (fun i => x i = 1), ι i.val ^ a :=
        (Finset.sum_filter (s := univ) (p := fun i => x i = 1) (f := fun i => ι i.val ^ a)).symm

/-- The power sums are additive: the map `x ↦ P_a(x)` is `F₂`-linear. -/
theorem s612_pinPower_add (ι : ℕ → F) (a : ℕ) (x y : Fin N → ZMod 2) :
    pinPower ι a (x + y) = pinPower ι a x + pinPower ι a y := by
  simp only [pinPower, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- The power sums commute with scalar multiplication. -/
theorem s612_pinPower_smul (ι : ℕ → F) (a : ℕ) (c : ZMod 2) (x : Fin N → ZMod 2) :
    pinPower ι a (c • x) = c • pinPower ι a x := by
  have h : ∀ i : Fin N, (c • x) i • (ι i.val ^ a) = c • (x i • (ι i.val ^ a)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, smul_smul]
  simp only [pinPower]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

/-- **Frobenius**, as in the paper: in characteristic two, `P_{2a}(x) = P_a(x)^2`. -/
theorem s612_pinPower_frobenius (ι : ℕ → F) (a : ℕ) (x : Fin N → ZMod 2) :
    pinPower ι (2 * a) x = (pinPower ι a x) ^ 2 := by
  rw [s612_pinPower_eq_sum_supp, s612_pinPower_eq_sum_supp]
  calc ∑ i ∈ s612_binSupp x, ι i.val ^ (2 * a)
      = ∑ i ∈ s612_binSupp x, (ι i.val ^ a) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Nat.mul_comm 2 a, pow_mul]
    _ = (∑ i ∈ s612_binSupp x, ι i.val ^ a) ^ 2 := (s612_pinsketch_sum_sq _ _).symm

/-- Two binary vectors with the same support of the sum: the support of `x + x'` is contained in
the union of the supports. -/
theorem s612_binSupp_add_subset (x x' : Fin N → ZMod 2) :
    s612_binSupp (x + x') ⊆ s612_binSupp x ∪ s612_binSupp x' := by
  intro i hi
  simp only [s612_binSupp, mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  rcases s612_zmod2_eq_zero_or_one (x i) with hx | hx <;> rcases s612_zmod2_eq_zero_or_one (x' i) with hy | hy
  · rw [Pi.add_apply, hx, hy] at hi; simp at hi
  · exact Or.inr hy
  · exact Or.inl hx
  · rw [Pi.add_apply, hx, hy] at hi; simp at hi

end PowerSums
section Uniqueness

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

/-- **Vandermonde lemma.** `m` distinct nonzero field elements cannot have `m` consecutive
vanishing power sums starting at `s`: the Vandermonde matrix of the family is invertible, so the
vector of all ones would be zero. -/
theorem s612_vandermonde_window {α : Type} [Fintype α]
    (v : α → F) (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0) (s : ℕ)
    (h : ∀ j : Fin (Fintype.card α), ∑ i : α, v i ^ (s + j.val) = 0) :
    Fintype.card α = 0 := by
  classical
  by_contra hcard
  have hpos : 0 < Fintype.card α := Nat.pos_of_ne_zero hcard
  let v' : Fin (Fintype.card α) → F := fun k => v ((Fintype.equivFin α).symm k)
  have hinj' : Function.Injective v' := by
    intro a b hab
    exact (Fintype.equivFin α).symm.injective (hinj hab)
  have hne' : ∀ k : Fin (Fintype.card α), v' k ≠ 0 := fun k => hne _
  have h' : ∀ j : Fin (Fintype.card α),
      ∑ k : Fin (Fintype.card α), v' k ^ (s + j.val) = 0 := by
    intro j
    have hsumeq := Fintype.sum_equiv (Fintype.equivFin α)
      (fun i : α => v i ^ (s + j.val)) (fun k : Fin (Fintype.card α) => v' k ^ (s + j.val))
      (fun i => by simp [v'])
    rw [← hsumeq]
    exact h j
  -- the vector of `s`-th powers and its Vandermonde image
  let c : Fin (Fintype.card α) → F := fun k => v' k ^ s
  have hker : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde v')) c = 0 := by
    funext j
    simp only [Pi.zero_apply]
    have h0 := h' j
    have hthis : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde v')) c j
        = ∑ k : Fin (Fintype.card α), v' k ^ (s + j.val) := by
      rw [Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.transpose_apply, Matrix.vandermonde_apply]
      show v' k ^ (j : ℕ) * v' k ^ s = v' k ^ (s + j.val)
      rw [← pow_add, Nat.add_comm]
    rw [hthis, h0]
  have hdet : (Matrix.transpose (Matrix.vandermonde v')).det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj'
  have hc : c = 0 :=
    Matrix.mulVec_injective_of_det_ne_zero hdet (by rw [hker, Matrix.mulVec_zero])
  have hlast : v' ⟨0, hpos⟩ ^ s = 0 := by
    have := congrFun hc ⟨0, hpos⟩
    simpa [c] using this
  exact (pow_ne_zero s (hne' ⟨0, hpos⟩)) hlast

/-- **Proposition 2.1, recovery of every light vector**, as in the paper: a vector of weight at
most `t` is determined by its syndrome `Pin_{N,t}(x)`. -/
theorem s612_pin_unique {N t : ℕ} (ι : ℕ → F) (h0 : ∀ v < N, ι v ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) {x x' : Fin N → ZMod 2}
    (hx : (univ.filter fun i => x i = 1).card ≤ t)
    (hx' : (univ.filter fun i => x' i = 1).card ≤ t)
    (hp : pin ι t x = pin ι t x') : x = x' := by
  classical
  set y : Fin N → ZMod 2 := x + x' with hy
  -- the weight of the difference is at most `2t`
  have hm2 : (s612_binSupp y).card ≤ 2 * t := by
    calc (s612_binSupp y).card ≤ (s612_binSupp x ∪ s612_binSupp x').card :=
          Finset.card_le_card (s612_binSupp_add_subset x x')
      _ ≤ (s612_binSupp x).card + (s612_binSupp x').card := Finset.card_union_le _ _
      _ ≤ t + t := Nat.add_le_add hx hx'
      _ = 2 * t := by omega
  -- the odd power sums vanish
  have hodd : ∀ j : Fin t, pinPower ι (2 * j.val + 1) y = 0 := by
    intro j
    have hpj : pinPower ι (2 * j.val + 1) x = pinPower ι (2 * j.val + 1) x' := by
      have h1 := congrFun hp j
      simpa [pin] using h1
    rw [hy, s612_pinPower_add, hpj, s612_pinsketch_add_self]
  -- Frobenius upgrades this to all power sums up to `2t - 1`
  have hP : ∀ a, 1 ≤ a → a ≤ 2 * t - 1 → pinPower ι a y = 0 := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha1 ha2
      rcases Nat.even_or_odd a with he | ho
      · obtain ⟨k, rfl⟩ := he
        have hkpos : 0 < k := by omega
        have hklt : k < k + k := by omega
        have hk1 : 1 ≤ k := hkpos
        have hk2 : k ≤ 2 * t - 1 := by omega
        have hstep : pinPower ι (k + k) y = (pinPower ι k y) ^ 2 := by
          rw [show k + k = 2 * k by omega, s612_pinPower_frobenius]
        rw [hstep, ih k hklt hk1 hk2]
        simp
      · obtain ⟨k, rfl⟩ := ho
        have hkt : k < t := by omega
        exact hodd ⟨k, hkt⟩
  -- the window of `|supp y|` consecutive power sums that vanishes
  have hm0 : (s612_binSupp y).card = 0 := by
    have hcard : Fintype.card {i : Fin N // i ∈ s612_binSupp y} = (s612_binSupp y).card := by
      simp
    have hz : Fintype.card {i : Fin N // i ∈ s612_binSupp y} = 0 := by
      refine s612_vandermonde_window (α := {i : Fin N // i ∈ s612_binSupp y})
        (v := fun i => ι (i : Fin N).val) ?_ ?_
        (if Even (s612_binSupp y).card then 0 else 1) ?_
      · intro a b hab
        exact Subtype.ext (Fin.ext (hinj a.1.isLt b.1.isLt hab))
      · intro i
        exact h0 i.1.val i.1.isLt
      · intro j
        have hjlt : j.val < (s612_binSupp y).card := by
          rw [← hcard]
          exact j.isLt
        have h1 : pinPower ι ((if Even (s612_binSupp y).card then 0 else 1) + j.val) y = 0 := by
          by_cases hme : Even (s612_binSupp y).card
          · rw [if_pos hme, Nat.zero_add]
            by_cases hj0 : j.val = 0
            · rw [hj0, s612_pinPower_eq_sum_supp]
              simp only [pow_zero]
              rw [Finset.sum_const, nsmul_eq_mul, mul_one, s612_pinsketch_natCast_eq_ite, if_pos hme]
            · have ha1 : 1 ≤ j.val := Nat.pos_of_ne_zero hj0
              have ha2 : j.val ≤ 2 * t - 1 := by omega
              exact hP j.val ha1 ha2
          · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hme
            rw [if_neg hme]
            have ha1 : 1 ≤ 1 + j.val := by omega
            have ha2 : 1 + j.val ≤ 2 * t - 1 := by omega
            exact hP (1 + j.val) ha1 ha2
        rw [s612_pinPower_eq_sum_supp] at h1
        exact (Finset.sum_coe_sort (s612_binSupp y)
          (fun i : Fin N => ι i.val ^ ((if Even (s612_binSupp y).card then 0 else 1) + j.val))).trans h1
    rw [hcard] at hz
    exact hz
  -- hence the difference vanishes
  have hempty : s612_binSupp y = ∅ := Finset.card_eq_zero.mp hm0
  have hy0 : y = 0 := by
    funext i
    have hi : i ∉ s612_binSupp y := by rw [hempty]; simp
    simp only [s612_binSupp, mem_filter, mem_univ, true_and, not_not] at hi
    rcases s612_zmod2_eq_zero_or_one (y i) with h | h
    · exact h
    · exact absurd h hi
  funext i
  have hxy : x i + x' i = 0 := by
    have h1 := congrFun hy0 i
    simpa [hy, Pi.add_apply] using h1
  exact s612_pinsketch_eq_of_add_eq_zero hxy

end Uniqueness


/-! ## Generic finite-probability helpers -/

lemma prU_nonneg {α : Type} [Fintype α] (P : α → Prop) : 0 ≤ prU P := by
  unfold prU
  positivity

lemma prU_le_one {α : Type} [Fintype α] (P : α → Prop) : prU P ≤ 1 := by
  classical
  unfold prU
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · have hisempty : IsEmpty α := Fintype.card_eq_zero_iff.mp h
    have h0 : (univ.filter P).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact fun x _ => hisempty.false x
    rw [h0]; simp
  · have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_univ _

lemma prU_congr {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a ↔ Q a) :
    prU P = prU Q := by
  classical
  have hf : Finset.univ.filter P = Finset.univ.filter Q := by
    ext a; simp [h a]
  unfold prU
  rw [hf]

lemma prU_mono {α : Type} [Fintype α] [Nonempty α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    prU P ≤ prU Q := by
  classical
  have hpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hsub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  have hcard : ((Finset.univ.filter P).card : ℝ) ≤ ((Finset.univ.filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  unfold prU
  exact (div_le_div_iff_of_pos_right hpos).mpr hcard

lemma expU_le {α : Type} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : expU f ≤ expU g := by
  unfold expU
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma expU_sum_finset {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    expU (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expU (f i) := by
  unfold expU
  rw [← Finset.sum_div, Finset.sum_comm]

lemma expU_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) : expU (fun _ : α => c) = c := by
  unfold expU
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h.ne'
  field_simp

lemma card_filter_classical {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ℝ) =
      ((@Finset.filter α p (fun a => Classical.propDecidable (p a)) s).card : ℝ) :=
  congrArg (fun z : Finset α => (z.card : ℝ))
    (Finset.filter_congr_decidable s p (fun a => Classical.propDecidable (p a))).symm

lemma expU_indicator {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    expU (fun a => if P a then (1:ℝ) else 0) = prU P := by
  have hsum : (∑ a : α, if P a then (1:ℝ) else 0) =
      ((@Finset.filter α P (fun a => Classical.propDecidable (P a)) univ).card : ℝ) := by
    have h1 : (∑ a : α, if P a then (1:ℝ) else 0) =
        ((∑ a : α, if P a then (1:ℕ) else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [h1, Finset.sum_boole]
    exact card_filter_classical univ P
  unfold expU prU
  rw [hsum]

lemma expU_fst_prod {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : expU (fun p : α × β => f p.1) = expU f := by
  have hsum : (∑ p : α × β, f p.1) = (Fintype.card β : ℝ) * (∑ a : α, f a) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
  have hb : ((Fintype.card β : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast h.ne'
  have ha : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h.ne'
  unfold expU
  rw [hsum, Fintype.card_prod, Nat.cast_mul]
  field_simp

/-! ## Parameter facts -/

lemma two_pow_sub_one_pos' {w : ℕ} (hw : 1 ≤ w) : (0:ℝ) < (2:ℝ)^w - 1 := by
  have h2 : (2:ℝ)^1 ≤ (2:ℝ)^w := pow_le_pow_right₀ (by norm_num) hw
  norm_num at h2
  linarith

section Params

variable (P : TopParams)

lemma Pn_pos (hargs : P.Args) : 0 < P.n := by
  have h1 := hargs.1; have h2 := hargs.2.1; omega

lemma Pd_pos (hargs : P.Args) : 0 < P.d := by have h1 := hargs.1; omega

lemma Pd_two (hargs : P.Args) : 2 ≤ P.d := hargs.1

lemma Pd_le_n (hargs : P.Args) : P.d ≤ P.n := hargs.2.1

lemma PN_pos (hargs : P.Args) : 0 < P.N := by
  have hd : (0:ℝ) < (P.d:ℝ) := by exact_mod_cast Pd_pos P hargs
  have hn : (0:ℝ) < (P.n:ℝ) := by exact_mod_cast Pn_pos P hargs
  show 0 < ⌈(P.n : ℝ) / (P.d : ℝ)⌉₊
  exact Nat.ceil_pos.mpr (div_pos hn hd)

lemma PN_one_le (hargs : P.Args) : 1 ≤ P.N :=
  Nat.one_le_iff_ne_zero.mpr (PN_pos P hargs).ne'

lemma Pw_pos (hargs : P.Args) : 0 < P.w := by
  have hN : (1:ℝ) ≤ (P.N:ℝ) := by exact_mod_cast PN_one_le P hargs
  have h1 : (1:ℝ) < (P.N:ℝ) + 1 := by linarith
  have h2 : 0 < lg ((P.N:ℝ) + 1) := by
    unfold lg
    exact Real.logb_pos (by norm_num) h1
  show 0 < ⌈lg ((P.N : ℝ) + 1)⌉₊
  exact Nat.ceil_pos.mpr h2

lemma two_pow_sub_one_pos (hargs : P.Args) : (0:ℝ) < (2:ℝ)^P.w - 1 :=
  two_pow_sub_one_pos' (Pw_pos P hargs)

end Params

/-! ## The word distribution `p_k = 2^{w-k-1}/(2^w-1)` -/

/-- The paper's `p_k`, as an abstract function of the word length `w`. -/
def pw (w k : ℕ) : ℝ := (2:ℝ)^(w-(k+1)) / ((2:ℝ)^w - 1)

lemma p_eq_pw (P : TopParams) (k : ℕ) : P.p k = pw P.w k := rfl

lemma sum_range_pow_two (w : ℕ) : ∑ j ∈ range w, (2:ℝ)^j = (2:ℝ)^w - 1 := by
  rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
  norm_num

lemma sum_range_mul_pow_two (w : ℕ) :
    ∑ j ∈ range w, (j:ℝ) * (2:ℝ)^j = ((w:ℝ) - 2) * (2:ℝ)^w + 2 := by
  induction w with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

lemma sum_range_pw_numerator (w : ℕ) :
    ∑ k ∈ range w, (2:ℝ)^(w-(k+1)) = (2:ℝ)^w - 1 := by
  have h1 : ∑ k ∈ range w, (2:ℝ)^(w-(k+1)) = ∑ k ∈ range w, (2:ℝ)^(w-1-k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 1
    omega
  rw [h1, Finset.sum_range_reflect (fun j => (2:ℝ)^j) w, sum_range_pow_two]

/- **Conjunct 2 of Lemma 6.2, as in the paper** (lem:top-bit-bounds): the first-error distribution
p_k = 2^{w-k-1}/(2^w-1) (eq:top-first-error) is a probability law. -/
theorem sum_pw_eq_one (w : ℕ) (hw : 1 ≤ w) : ∑ k ∈ range w, pw w k = 1 := by
  have hpos : (0:ℝ) < (2:ℝ)^w - 1 := two_pow_sub_one_pos' hw
  have hne : (2:ℝ)^w - 1 ≠ 0 := hpos.ne'
  unfold pw
  rw [← Finset.sum_div, sum_range_pw_numerator]
  exact div_self hne

lemma sum_p_eq_one (P : TopParams) (hargs : P.Args) : ∑ k ∈ range P.w, P.p k = 1 :=
  sum_pw_eq_one P.w (Pw_pos P hargs)

lemma sum_range_weighted (w : ℕ) :
    ∑ k ∈ range w, ((w-1-k : ℕ) : ℝ) * (2:ℝ)^(w-1-k) = ((w:ℝ) - 2) * (2:ℝ)^w + 2 := by
  rw [Finset.sum_range_reflect (fun j => (j:ℝ) * (2:ℝ)^j) w, sum_range_mul_pow_two]

lemma sum_univ_weighted (w : ℕ) :
    ∑ k : Fin w, ((w-1-k.val : ℕ) : ℝ) * (2:ℝ)^(w-1-k.val)
      = ((w:ℝ) - 2) * (2:ℝ)^w + 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ((w-1-j : ℕ) : ℝ) * (2:ℝ)^(w-1-j)) w,
    sum_range_weighted]

lemma sum_univ_pow (w : ℕ) :
    ∑ k : Fin w, (2:ℝ)^(w-1-k.val) = (2:ℝ)^w - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (2:ℝ)^(w-1-j)) w]
  rw [Finset.sum_range_reflect (fun j => (2:ℝ)^j) w, sum_range_pow_two]

/-- Termwise shape of the entropy of `pw`. -/
lemma pw_entropy_term (w : ℕ) (hw : 1 ≤ w) (k : Fin w) :
    pw w k.val * lg (1 / pw w k.val) =
      (2:ℝ)^(w-1-k.val) / ((2:ℝ)^w - 1) *
        (lg ((2:ℝ)^w - 1) - ((w-1-k.val : ℕ) : ℝ)) := by
  have hk : k.val < w := k.isLt
  set M : ℝ := (2:ℝ)^w - 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact two_pow_sub_one_pos' hw
  have hMne : M ≠ 0 := hMpos.ne'
  have hpow : (0:ℝ) < (2:ℝ)^(w-1-k.val) := pow_pos (by norm_num) _
  have hpowe : (w - (k.val + 1)) = (w - 1 - k.val) := by omega
  have hp : pw w k.val = (2:ℝ)^(w-1-k.val) / M := by
    unfold pw
    rw [hpowe, hMdef]
  have h1 : 1 / ((2:ℝ)^(w-1-k.val) / M) = M / (2:ℝ)^(w-1-k.val) := by
    field_simp
  have h2 : lg (M / (2:ℝ)^(w-1-k.val)) = lg M - ((w-1-k.val : ℕ) : ℝ) := by
    unfold lg
    rw [Real.logb_div hMne (ne_of_gt hpow), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]
  rw [hp, h1, h2]

/-- The exact entropy of `pw`, as a closed-form expression. -/
theorem entropyFin_pw_eq (w : ℕ) (hw : 1 ≤ w) :
    entropyFin (fun k : Fin w => pw w k.val) =
      lg ((2:ℝ)^w - 1) - (((w:ℝ) - 2) * (2:ℝ)^w + 2) / ((2:ℝ)^w - 1) := by
  set M : ℝ := (2:ℝ)^w - 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact two_pow_sub_one_pos' hw
  have hMne : M ≠ 0 := hMpos.ne'
  have hstep1 : entropyFin (fun k : Fin w => pw w k.val)
      = ∑ k : Fin w, ((2:ℝ)^(w-1-k.val) / M * (lg M - ((w-1-k.val : ℕ) : ℝ))) := by
    unfold entropyFin
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hMdef]
    exact pw_entropy_term w hw k
  have hsplit : ∑ k : Fin w, ((2:ℝ)^(w-1-k.val) / M * (lg M - ((w-1-k.val : ℕ) : ℝ)))
      = lg M / M * (∑ k : Fin w, (2:ℝ)^(w-1-k.val))
        - (1/M) * (∑ k : Fin w, ((w-1-k.val : ℕ) : ℝ) * (2:ℝ)^(w-1-k.val)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hstep1, hsplit, sum_univ_pow, sum_univ_weighted]
  have hMeq : (2:ℝ)^w - 1 = M := hMdef.symm
  rw [hMeq]
  field_simp

/-- Conjunct 3: the truncated geometric law on `w` positions has entropy at most `2`. -/
theorem entropyFin_pw_le_two (w : ℕ) (hw : 1 ≤ w) :
    entropyFin (fun k : Fin w => pw w k.val) ≤ 2 := by
  rw [entropyFin_pw_eq w hw]
  set M : ℝ := (2:ℝ)^w - 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    exact two_pow_sub_one_pos' hw
  have hle : lg M ≤ (w:ℝ) := by
    have h1 : M ≤ (2:ℝ)^w := by rw [hMdef]; linarith
    unfold lg
    calc Real.logb 2 M ≤ Real.logb 2 ((2:ℝ)^w) :=
          Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hMpos h1
      _ = (w:ℝ) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one]
  by_cases hw2 : 2 ≤ w
  · have hA : (0:ℝ) ≤ (w:ℝ) - 2 := by
      have h2 : (2:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw2
      linarith
    have hratio : (1:ℝ) ≤ (2:ℝ)^w / M := by
      rw [le_div_iff₀ hMpos, one_mul]
      rw [hMdef]
      linarith
    have hkey : (((w:ℝ) - 2) * (2:ℝ)^w + 2) / M
        = ((w:ℝ) - 2) * ((2:ℝ)^w / M) + 2 / M := by
      field_simp
    rw [hkey]
    have h2M : (0:ℝ) ≤ 2 / M := div_nonneg (by norm_num) hMpos.le
    have h3 := mul_le_mul_of_nonneg_left hratio hA
    nlinarith [hle, h3, h2M, hA]
  · have hw1 : w = 1 := by omega
    subst hw1
    rw [hMdef]
    norm_num [lg]

lemma entropyFin_p_eq (P : TopParams) (hargs : P.Args) :
    entropyFin (fun k : Fin P.w => P.p k.val) ≤ 2 :=
  entropyFin_pw_le_two P.w (Pw_pos P hargs)

/-! ## Counting the nonzero vectors with a prescribed coefficient pattern -/

/-- The pattern of a first error at bit `k`: earlier bits vanish, bit `k` is one. -/
def Qvec {w : ℕ} (k : Fin w) (v : Fin w → ZMod 2) : Prop :=
  (∀ k' : Fin w, k'.val < k.val → v k' = 0) ∧ v k = 1

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x = ((x.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val x).symm
  have hlt : x.val < 2 := ZMod.val_lt x
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h <;> rw [hx, h] <;> simp

/-- The nonzero vectors with a prescribed pattern on the first `k+1` coordinates are the vectors on
the remaining `w-k-1` coordinates. -/
def goodEquiv {w : ℕ} (k : Fin w) :
    {v : Fin w → ZMod 2 // Qvec k v} ≃ ((i : {i : Fin w // k.val < i.val}) → ZMod 2) where
  toFun v := fun i => v.1 i.1
  invFun f := ⟨fun i => if h : i.val < k.val then 0 else if _h2 : i.val = k.val then 1
      else f ⟨i, by omega⟩, by
      unfold Qvec
      constructor
      · intro k' hk'
        simp only [dif_pos hk']
      · simp only [dif_neg (by omega : ¬ k.val < k.val)]
        simp⟩
  left_inv v := by
    have hv : (∀ k' : Fin w, k'.val < k.val → v.1 k' = 0) ∧ v.1 k = 1 := v.2
    refine Subtype.ext (funext fun i => ?_)
    by_cases h : i.val < k.val
    · simp only [dif_pos h]
      exact (hv.1 i h).symm
    · simp only [dif_neg h]
      by_cases h2 : i.val = k.val
      · simp only [dif_pos h2]
        have hik : i = k := Fin.ext h2
        rw [hik]
        exact (hv.2).symm
      · simp only [dif_neg h2]
  right_inv f := by
    funext i
    have h1 : ¬ i.1.val < k.val := by omega
    have h2 : ¬ i.1.val = k.val := by omega
    simp only [dif_neg h1, dif_neg h2]

lemma goodVec_card {w : ℕ} (k : Fin w) :
    (univ.filter fun v : Fin w → ZMod 2 => Qvec k v).card = 2 ^ (w - (k.val + 1)) := by
  classical
  have hcard : (univ.filter (fun i : Fin w => k.val < i.val)).card = w - (k.val + 1) := by
    have hinj : Set.InjOn (fun i : Fin w => i.val - (k.val + 1))
        ↑(univ.filter (fun i : Fin w => k.val < i.val)) := by
      intro i hi i' hi' h
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hi hi'
      beta_reduce at h
      exact Fin.ext (by omega)
    have himg : (univ.filter (fun i : Fin w => k.val < i.val)).image
        (fun i : Fin w => i.val - (k.val + 1)) = range (w - (k.val + 1)) := by
      ext t
      simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · intro ht
        refine ⟨⟨k.val + 1 + t, by omega⟩, ?_, ?_⟩
        · show k.val < k.val + 1 + t
          omega
        · show (⟨k.val + 1 + t, by omega⟩ : Fin w).val - (k.val + 1) = t
          simp
    rw [← Finset.card_image_of_injOn hinj, himg, card_range]
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (goodEquiv k), Fintype.card_fun, ZMod.card, Fintype.card_subtype, hcard]

section Count

variable {P : TopParams}
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- In a field every nonzero element is a unit. -/
def mkUnit (y : F) (hy : y ≠ 0) : Fˣ where
  val := y
  inv := y⁻¹
  val_inv := mul_inv_cancel₀ hy
  inv_val := inv_mul_cancel₀ hy

@[simp] lemma coe_mkUnit (y : F) (hy : y ≠ 0) : (mkUnit y hy : F) = y := rfl

/-- `Fˣ` is the set of nonzero field elements. -/
def unitsEquivNeZero : Fˣ ≃ {y : F // y ≠ 0} where
  toFun u := ⟨(u : F), Units.ne_zero u⟩
  invFun y := mkUnit y.1 y.2
  left_inv u := Units.ext rfl
  right_inv y := Subtype.ext rfl

lemma card_F (b : Module.Basis (Fin P.w) (ZMod 2) F) : Fintype.card F = 2 ^ P.w := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [ZMod.card, Module.finrank_eq_card_basis b] at h
  simpa using h

lemma card_units (b : Module.Basis (Fin P.w) (ZMod 2) F) : Fintype.card Fˣ = 2 ^ P.w - 1 := by
  classical
  have h1 : Fintype.card Fˣ = Fintype.card {y : F // y ≠ 0} := Fintype.card_congr unitsEquivNeZero
  rw [h1, Fintype.card_subtype]
  have h2 : (univ.filter fun y : F => y ≠ 0) = univ.erase 0 := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_erase, ne_eq, and_true]
  rw [h2, Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, card_F b]

/-- The number of units `u` such that `u * c` has a prescribed `w`-bit pattern, `c ≠ 0`. -/
lemma card_twist (b : Module.Basis (Fin P.w) (ZMod 2) F) (k : Fin P.w) {c : F} (hc : c ≠ 0) :
    (univ.filter fun u : Fˣ => Qvec k (b.repr ((u : F) * c))).card
      = 2 ^ (P.w - (k.val + 1)) := by
  classical
  have h1 : (univ.filter fun u : Fˣ => Qvec k (b.repr ((u : F) * c))).card
      = (univ.filter fun y : {y : F // y ≠ 0} => Qvec k (b.repr (y.1 * c))).card := by
    refine Finset.card_bij (fun u _ => (⟨(u : F), Units.ne_zero u⟩ : {y : F // y ≠ 0})) ?_ ?_ ?_
    · intro u hu
      simpa only [mem_filter, mem_univ, true_and] using hu
    · intro u _ u' _ h
      exact Units.ext (congrArg Subtype.val h)
    · intro y hy
      refine ⟨mkUnit y.1 y.2, ?_, Subtype.ext rfl⟩
      simpa only [mem_filter, mem_univ, true_and, coe_mkUnit] using hy
  have h2 : (univ.filter fun y : {y : F // y ≠ 0} => Qvec k (b.repr (y.1 * c))).card
      = (univ.filter fun y : {y : F // y ≠ 0} => Qvec k (b.repr y.1)).card := by
    refine Finset.card_bij (fun y _ => (⟨y.1 * c, mul_ne_zero y.2 hc⟩ : {y : F // y ≠ 0})) ?_ ?_ ?_
    · intro y hy
      simpa only [mem_filter, mem_univ, true_and] using hy
    · intro y₁ _ y₂ _ h
      refine Subtype.ext ?_
      exact mul_right_cancel₀ hc (congrArg Subtype.val h)
    · intro y hy
      refine ⟨⟨y.1 / c, div_ne_zero y.2 hc⟩, ?_, ?_⟩
      · simpa only [mem_filter, mem_univ, true_and, div_mul_cancel₀ y.1 hc] using hy
      · exact Subtype.ext (div_mul_cancel₀ y.1 hc)
  have h3 : (univ.filter fun y : {y : F // y ≠ 0} => Qvec k (b.repr y.1)).card
      = (univ.filter fun v : Fin P.w → ZMod 2 => Qvec k v).card := by
    refine Finset.card_bij (fun y _ => (b.repr y.1 : Fin P.w → ZMod 2)) ?_ ?_ ?_
    · intro y hy
      simpa only [mem_filter, mem_univ, true_and] using hy
    · intro y₁ _ y₂ _ h
      exact Subtype.ext (b.repr.injective (Finsupp.ext (fun i => congrFun h i)))
    · intro v hv
      have hvQ : Qvec k v := by simpa only [mem_filter, mem_univ, true_and] using hv
      have hv0 : v ≠ 0 := by
        intro h0
        rw [h0] at hvQ
        exact zero_ne_one hvQ.2
      obtain ⟨V, hV⟩ : ∃ V : Fin P.w →₀ ZMod 2, (V : Fin P.w → ZMod 2) = v :=
        ⟨Finsupp.equivFunOnFinite.symm v, by simp⟩
      refine ⟨⟨b.repr.symm V, ?_⟩, ?_, ?_⟩
      · intro h0
        apply hv0
        rw [← hV, ← LinearEquiv.apply_symm_apply b.repr V, h0, map_zero]
        simp
      · simpa only [mem_filter, mem_univ, true_and, LinearEquiv.apply_symm_apply, hV] using hvQ
      · show (b.repr (b.repr.symm V) : Fin P.w → ZMod 2) = v
        rw [LinearEquiv.apply_symm_apply, hV]
  rw [h1, h2, h3]
  exact goodVec_card k

lemma prU_fst_prod {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (Pp : α → Prop) : prU (fun p : α × β => Pp p.1) = prU Pp := by
  classical
  have h1 : (univ.filter fun p : α × β => Pp p.1).card
      = (univ.filter Pp).card * Fintype.card β := by
    rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
    have hstep : ∀ a : α, (∑ b : β, if Pp a then (1:ℕ) else 0)
        = if Pp a then Fintype.card β else 0 := by
      intro a
      by_cases h : Pp a
      · rw [if_pos h, if_pos h, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      · rw [if_neg h, if_neg h, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
  unfold prU
  rw [h1, Fintype.card_prod]
  have ha : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h.ne'
  have hb : ((Fintype.card β : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast h.ne'
  push_cast
  field_simp

/- **Step 1 of the paper (conditioning identity of lem:top-bit-bounds), abstract form.** On a
product of a "rest" space with the uniform group of units, requiring a prescribed pattern of the
twisted difference has exactly the geometric probability p_k, independently of the base event.
This is the paper's argument: the unscaled difference is nonzero exactly when the word prediction is
wrong, so multiplying it by the independent uniform scalar makes it a uniform nonzero w-bit vector;
the first nonzero bit is at position k for exactly 2^{w-k-1} of the 2^w - 1 nonzero vectors. -/
lemma prU_prod_twist (b : Module.Basis (Fin P.w) (ZMod 2) F) {S : Type} [Fintype S] [Nonempty S]
    (Base : S → Prop) (d : S → F) (hd : ∀ s, Base s → d s ≠ 0) (hw : 1 ≤ P.w) (k : Fin P.w) :
    prU (fun p : S × Fˣ => Base p.1 ∧ Qvec k (b.repr ((p.2 : F) * d p.1)))
      = (2:ℝ) ^ (P.w - (k.val + 1)) / ((2:ℝ) ^ P.w - 1) * prU (fun p : S × Fˣ => Base p.1) := by
  classical
  have hK : Fintype.card Fˣ = 2 ^ P.w - 1 := card_units b
  have hGR : (Fintype.card Fˣ : ℝ) = (2:ℝ) ^ P.w - 1 := by
    rw [hK]
    have h1 : 1 ≤ 2 ^ P.w := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero P.w (by norm_num))
    push_cast [h1]
    ring
  have hcard : (univ.filter (fun p : S × Fˣ =>
        Base p.1 ∧ Qvec k (b.repr ((p.2 : F) * d p.1)))).card
      = (univ.filter Base).card * 2 ^ (P.w - (k.val + 1)) := by
    rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
    have hinner : ∀ s : S, (∑ u : Fˣ,
        if (Base s ∧ Qvec k (b.repr ((u : F) * d s))) then (1:ℕ) else 0)
        = if Base s then 2 ^ (P.w - (k.val + 1)) else 0 := by
      intro s
      by_cases hs : Base s
      · rw [if_pos hs]
        have hstep : (∑ u : Fˣ,
            if (Base s ∧ Qvec k (b.repr ((u : F) * d s))) then (1:ℕ) else 0)
            = ∑ u : Fˣ, if Qvec k (b.repr ((u : F) * d s)) then (1:ℕ) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          simp only [hs, true_and]
        rw [hstep, ← Finset.card_filter]
        exact card_twist b k (hd s hs)
      · rw [if_neg hs]
        refine Finset.sum_eq_zero fun u _ => ?_
        rw [if_neg (by tauto)]
    rw [Finset.sum_congr rfl (fun s _ => hinner s), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
  have hbase : prU (fun p : S × Fˣ => Base p.1) = prU Base := prU_fst_prod Base
  have hcardR : ((univ.filter (fun p : S × Fˣ =>
        Base p.1 ∧ Qvec k (b.repr ((p.2 : F) * d p.1)))).card : ℝ)
      = ((univ.filter Base).card : ℝ) * (2:ℝ) ^ (P.w - (k.val + 1)) := by
    rw [hcard]
    push_cast
    ring
  have hprod : (Fintype.card (S × Fˣ) : ℝ) = (Fintype.card S : ℝ) * ((2:ℝ) ^ P.w - 1) := by
    rw [Fintype.card_prod]
    push_cast
    rw [hGR]
  have hSne : ((Fintype.card S : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast h.ne'
  have hKne : ((2:ℝ) ^ P.w - 1) ≠ 0 := (two_pow_sub_one_pos' hw).ne'
  have hmain : ((univ.filter (fun p : S × Fˣ =>
        Base p.1 ∧ Qvec k (b.repr ((p.2 : F) * d p.1)))).card : ℝ)
        / (Fintype.card (S × Fˣ) : ℝ)
      = (2:ℝ) ^ (P.w - (k.val + 1)) / ((2:ℝ) ^ P.w - 1) *
          (((univ.filter Base).card : ℝ) / (Fintype.card S : ℝ)) := by
    rw [hcardR, hprod]
    field_simp
  have hprUB : prU Base = ((univ.filter Base).card : ℝ) / (Fintype.card S : ℝ) := rfl
  rw [hbase, hprUB]
  refine Eq.trans ?_ hmain
  unfold prU
  simp only [card_filter_classical]

end Count

/-! ## Conjunct 1: the conditioning identity of Lemma 6.2 -/

section Part1

variable (P : TopParams) (hargs : P.Args)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
variable (x : Finset ℕ)

/-! ### Accessors for the local seed

`(P.scheme b ι).LocalSeed` is `Equiv.Perm (Fin (P.scheme b ι).N) × (Fin (P.scheme b ι).m →
(P.scheme b ι).Rand)` by structure projection, so `lr.1` and `lr.2` do not carry the expected
types syntactically.  All access below goes through the three accessors `rowPerm`, `rowRnd`,
`mkSeed`, which fix the types once and for all. -/

/-- The public permutation of a local seed. -/
def rowPerm (lr : (P.scheme b ι).LocalSeed) : Equiv.Perm (Fin P.n) := lr.1

/-- The row randomness of a local seed. -/
def rowRnd (lr : (P.scheme b ι).LocalSeed) : Fin P.d → Fin P.B → Fˣ := lr.2

/-- A local seed assembled from its two components. -/
def mkSeed (π : Equiv.Perm (Fin P.n)) (β : Fin P.d → Fin P.B → Fˣ) :
    (P.scheme b ι).LocalSeed := (π, β)

@[simp] lemma rowPerm_mkSeed (π : Equiv.Perm (Fin P.n)) (β : Fin P.d → Fin P.B → Fˣ) :
    rowPerm P b ι (mkSeed P b ι π β) = π := rfl

@[simp] lemma rowRnd_mkSeed (π : Equiv.Perm (Fin P.n)) (β : Fin P.d → Fin P.B → Fˣ) :
    rowRnd P b ι (mkSeed P b ι π β) = β := rfl

@[simp] lemma mkSeed_rowPerm_rowRnd (lr : (P.scheme b ι).LocalSeed) :
    mkSeed P b ι (rowPerm P b ι lr) (rowRnd P b ι lr) = lr := rfl

/-- Replace the `(j,a)`-th scalar of a row-randomness family by `1`. -/
def delCoord (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) :
    Fin P.d → Fin P.B → Fˣ :=
  Function.update β j (Function.update (β j) a 1)

/-- Insert `u` at the `(j,a)`-th scalar. -/
def insCoord (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ) :
    Fin P.d → Fin P.B → Fˣ :=
  Function.update β j (Function.update (β j) a u)

lemma delCoord_self (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) :
    delCoord P j a β j = Function.update (β j) a 1 := by
  simp [delCoord]

lemma delCoord_at (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (a' : Fin P.B) :
    delCoord P j a β j a' = if a' = a then 1 else β j a' := by
  rw [delCoord_self, Function.update_apply]

lemma delCoord_at_other (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ)
    (a' : Fin P.B) {j' : Fin P.d} (h : j' ≠ j) : delCoord P j a β j' a' = β j' a' := by
  simp [delCoord, Function.update_apply, h]

lemma insCoord_at (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ)
    (a' : Fin P.B) : insCoord P j a β u j a' = if a' = a then u else β j a' := by
  simp [insCoord, Function.update_apply]

lemma insCoord_at_other (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ)
    (a' : Fin P.B) {j' : Fin P.d} (h : j' ≠ j) : insCoord P j a β u j' a' = β j' a' := by
  simp [insCoord, Function.update_apply, h]

lemma insCoord_same (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ) :
    insCoord P j a β u j a = u := by
  rw [insCoord_at, if_pos rfl]

lemma delCoord_insCoord (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ) :
    delCoord P j a (insCoord P j a β u) = delCoord P j a β := by
  funext j' a'
  by_cases hj : j' = j
  · rw [hj, delCoord_at P j a (insCoord P j a β u) a', delCoord_at P j a β a',
      insCoord_at P j a β u a']
    by_cases ha : a' = a
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  · rw [delCoord_at_other P j a (insCoord P j a β u) a' hj, delCoord_at_other P j a β a' hj, insCoord_at_other P j a β u a' hj]

lemma insCoord_delCoord (j : Fin P.d) (a : Fin P.B) (β : Fin P.d → Fin P.B → Fˣ) :
    insCoord P j a (delCoord P j a β) (β j a) = β := by
  funext j' a'
  by_cases hj : j' = j
  · rw [hj, insCoord_at P j a (delCoord P j a β) (β j a) a',
      delCoord_at P j a β a']
    by_cases ha : a' = a
    · simp only [if_pos ha]; rw [ha]
    · simp only [if_neg ha]
  · rw [insCoord_at_other P j a (delCoord P j a β) (β j a) a' hj,
      delCoord_at_other P j a β a' hj]

lemma delCoord_of_eq_one {j : Fin P.d} {a : Fin P.B} {β : Fin P.d → Fin P.B → Fˣ}
    (h : β j a = 1) : delCoord P j a β = β := by
  funext j' a'
  by_cases hj : j' = j
  · rw [hj, delCoord_at P j a β a']
    by_cases ha : a' = a
    · simp only [if_pos ha]; rw [ha, h]
    · simp only [if_neg ha]
  · rw [delCoord_at_other P j a β a' hj]

/-- The row seeds together with the value of their `(j,a)`-th scalar. -/
abbrev RestSeed (j : Fin P.d) (a : Fin P.B) : Type :=
  {p : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) // p.2 j a = 1}

/-- Splitting a row seed into its `(j,a)`-th scalar and the rest. -/
def splitSeed (j : Fin P.d) (a : Fin P.B) :
    (P.scheme b ι).LocalSeed ≃ (RestSeed (F := F) P j a × Fˣ) where
  toFun lr := (⟨(lr.1, delCoord P j a lr.2), by
    show delCoord P j a lr.2 j a = 1
    rw [delCoord_at P j a lr.2 a, if_pos rfl]⟩, lr.2 j a)
  invFun q := (q.1.1.1, insCoord P j a q.1.1.2 q.2)
  left_inv lr := by
    obtain ⟨π, β⟩ : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) := lr
    show (π, insCoord P j a (delCoord P j a β) (β j a)) = (π, β)
    refine Prod.ext rfl ?_
    show insCoord P j a (delCoord P j a β) (β j a) = β
    exact insCoord_delCoord P j a β
  right_inv q := by
    obtain ⟨⟨⟨π, β⟩, hβ⟩, u⟩ := q
    show ((⟨(π, delCoord P j a (insCoord P j a β u)), by
        show delCoord P j a (insCoord P j a β u) j a = 1
        rw [delCoord_at P j a (insCoord P j a β u) a, if_pos rfl]⟩ :
          RestSeed (F := F) P j a), insCoord P j a β u j a) = (⟨(π, β), hβ⟩, u)
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      refine Prod.ext rfl ?_
      show delCoord P j a (insCoord P j a β u) = β
      rw [delCoord_insCoord P, delCoord_of_eq_one P hβ]
    · show insCoord P j a β u j a = u
      exact insCoord_same P j a β u
lemma prU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (Q : β → Prop) :
    prU (fun a => Q (e a)) = prU Q := by
  classical
  unfold prU
  rw [Fintype.card_congr e]
  have h : (univ.filter fun a : α => Q (e a)).card = (univ.filter Q).card := by
    refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
    · intro a ha; simpa using ha
    · intro a1 _ a2 _ h; exact e.injective h
    · intro bb hb; exact ⟨e.symm bb, by simpa using hb, by simp⟩
  rw [h]

/-! ### The candidate depends only on the other words -/

lemma wordOf_congr {z z' : List (ZMod 2)} {i : ℕ}
    (hz : ∀ p, p < i * P.w → z.getD p 0 = z'.getD p 0) {a : Fin P.B} (ha : a.val < i) :
    P.wordOf b z a.val = P.wordOf b z' a.val := by
  unfold TopParams.wordOf
  refine Finset.sum_congr rfl fun k _ => ?_
  have hpos : a.val * P.w + k.val < i * P.w := by
    have h1 : a.val + 1 ≤ i := ha
    have h2 : (a.val + 1) * P.w ≤ i * P.w := Nat.mul_le_mul_right _ h1
    have h3 : a.val * P.w + k.val < a.val * P.w + P.w := by
      have := k.isLt; omega
    have h4 : a.val * P.w + P.w = (a.val + 1) * P.w := by ring
    omega
  rw [hz _ hpos]

lemma cand_congr {j : ℕ} {α α' : Fin P.B → Fˣ} {z z' : List (ZMod 2)} {i : ℕ}
    (hα : ∀ a' : Fin P.B, a'.val < i → α a' = α' a')
    (hz : ∀ p, p < i * P.w → z.getD p 0 = z'.getD p 0) :
    P.cand b ι j α z i = P.cand b ι j α' z' i := by
  unfold TopParams.cand
  have hfilter : (range (rowLen P.n P.d j)).powerset.filter (fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) S = ((α a)⁻¹ : Fˣ) * P.wordOf b z a.val)
      = (range (rowLen P.n P.d j)).powerset.filter (fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) S = ((α' a)⁻¹ : Fˣ) * P.wordOf b z' a.val) := by
    refine Finset.filter_congr ?_
    intro S _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun a ha => by
        rw [← hα a ha, ← wordOf_congr P b hz ha]
        exact h2 a ha⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun a ha => by
        rw [hα a ha, wordOf_congr P b hz ha]
        exact h2 a ha⟩
  rw [hfilter]

/-- The top-level row code, in concrete form. -/
def code6 (α : Fin P.B → Fˣ) (S : Finset ℕ) (s : Fin P.ell) : ZMod 2 :=
  b.repr (((α (P.wordIdx s)) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1) S)
    (P.bitIdx s)

lemma truePrefix_getD (j : Fin P.d) (α : Fin P.B → Fˣ) (S : Finset ℕ) {m q : ℕ}
    (hq : q < m) (hm : m ≤ P.ell) :
    ((P.scheme b ι).truePrefix j α S m).getD q 0 = code6 P b ι α S ⟨q, lt_of_lt_of_le hq hm⟩ := by
  simp only [RowScheme.truePrefix]
  have hlen : (((List.finRange (P.scheme b ι).ℓ).take m).map ((P.scheme b ι).code j α S)).length
      = m := by
    rw [List.length_map, List.length_take, List.length_finRange]
    show min m P.ell = m
    omega
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hq), List.getElem_map]
  have h2 : q < ((List.finRange (P.scheme b ι).ℓ).take m).length := by
    rw [List.length_take, List.length_finRange]
    show q < min m P.ell
    omega
  rw [List.getElem_take]
  have h3 : q < (List.finRange (P.scheme b ι).ℓ).length := by
    rw [List.length_finRange]
    show q < P.ell
    omega
  rw [List.getElem_finRange]
  rfl

lemma truePrefix_getD_eq (j : Fin P.d) {α α' : Fin P.B → Fˣ} {S S' : Finset ℕ} {m : ℕ}
    (hm : m ≤ P.ell) (hSS' : S = S')
    (hα : ∀ s : Fin P.ell, s.val < m → α (P.wordIdx s) = α' (P.wordIdx s))
    {p : ℕ} (hp : p < m) :
    ((P.scheme b ι).truePrefix j α S m).getD p 0
      = ((P.scheme b ι).truePrefix j α' S' m).getD p 0 := by
  rw [truePrefix_getD P b ι j α S hp hm, truePrefix_getD P b ι j α' S' hp hm, hSS']
  simp only [code6]
  rw [hα ⟨p, lt_of_lt_of_le hp hm⟩ hp]

/-- The candidate of the exact prefix of `a` words, in concrete form. -/
def cands6 (j : Fin P.d) (a : Fin P.B) (lr : (P.scheme b ι).LocalSeed) : Option (Finset ℕ) :=
  P.cand b ι j.val (lr.2 j)
    ((P.scheme b ι).truePrefix j (lr.2 j) ((P.scheme b ι).rowOf lr x j) (a.val * P.w)) a.val

/- The wrong-word event: the algorithm's candidate from the exact prefix is not the true row support
(its (2a+1)-st power sum differs). This is the conditioning event of the paper's Lemma 6.2. -/
def wrong6 (j : Fin P.d) (a : Fin P.B) (lr : (P.scheme b ι).LocalSeed) : Prop :=
  ∃ C, cands6 P b ι x j a lr = some C ∧
    TopParams.power ι (2 * a.val + 1) C ≠
      TopParams.power ι (2 * a.val + 1) ((P.scheme b ι).rowOf lr x j)

lemma cands6_congr (j : Fin P.d) (a : Fin P.B) {β β' : Fin P.d → Fin P.B → Fˣ}
    (π : Equiv.Perm (Fin P.n)) (hβ : ∀ a' : Fin P.B, a' ≠ a → β j a' = β' j a') :
    cands6 P b ι x j a (π, β) = cands6 P b ι x j a (π, β') := by
  unfold cands6
  have hrow : (P.scheme b ι).rowOf (π, β) x j = (P.scheme b ι).rowOf (π, β') x j := rfl
  refine cand_congr P b ι (j := j.val) (i := a.val) ?_ ?_
  · intro a' ha'
    exact hβ a' (fun he => by rw [he] at ha'; exact absurd ha' (lt_irrefl _))
  · intro p hp
    refine truePrefix_getD_eq P b ι j ?_ hrow ?_ hp
    · show a.val * P.w ≤ P.ell
      unfold TopParams.ell
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt a.isLt)
    · intro s hs
      have hne : P.wordIdx s ≠ a := by
        intro he
        have hv : s.val / P.w = a.val := congrArg Fin.val he
        have hlt : s.val / P.w < a.val := by
          apply Nat.div_lt_of_lt_mul
          rw [Nat.mul_comm]
          exact hs
        rw [hv] at hlt
        exact absurd hlt (lt_irrefl _)
      exact hβ _ hne

/-! ### Conjunct 1: the conditioning identity of `lem:top-bit-bounds`

The paper's argument: "Both the predicted and true field elements are multiplied by an independent
random scalar `α_{j,a}`.  If its unscaled prediction is incorrect, the difference from the true
value is nonzero, so multiplication by `α_{j,a}` makes the difference uniform over all nonzero
`w`-bit vectors.  The first nonzero bit is at position `k` when the first `k-1` bits are zero and
bit `k` is one".

We split the local seed into the `(j,a)`-th scalar and the rest, observe that the candidate (hence
the wrong-word event) does not depend on that scalar, and apply `prU_prod_twist`. -/

/-- The paper's joint event of `lem:top-bit-bounds`, first claim: the word prediction of row `j`
for word `a` is wrong (`wrong6`), the algorithm produced a candidate `C`, and the first bit at
which the twisted prediction `α_{j,a} P_{2a+1}(C)` differs from the true word
`α_{j,a} P_{2a+1}(x_j)` is bit `k`. -/
def joint6 (j : Fin P.d) (a : Fin P.B) (k : Fin P.w) (lr : (P.scheme b ι).LocalSeed) : Prop :=
  wrong6 P b ι x j a lr ∧ ∃ C, cands6 P b ι x j a lr = some C ∧
    (let α : F := ((lr.2 j : Fin P.B → Fˣ) a : F)
     let bu := b.repr (α * TopParams.power ι (2 * a.val + 1) C)
     let bv := b.repr (α * TopParams.power ι (2 * a.val + 1) ((P.scheme b ι).rowOf lr x j))
     (∀ k' : Fin P.w, k'.val < k.val → bu k' = bv k') ∧ bu k ≠ bv k)

/-- The true row support, as a function of a rest seed. -/
def restRow (j : Fin P.d) (a : Fin P.B) (r : RestSeed (F := F) P j a) : Finset ℕ :=
  (P.scheme b ι).rowOf r.1 x j

/-- The conditioning event `wrongWord`, as a function of a rest seed. -/
def restWrong (j : Fin P.d) (a : Fin P.B) (r : RestSeed (F := F) P j a) : Prop :=
  wrong6 P b ι x j a r.1

/-- The unscaled difference between the predicted word `a` (from the candidate of the exact prefix)
and the true word `a`, as a function of a rest seed.  On `restWrong` it is nonzero, which is the
hypothesis `hd` of `prU_prod_twist`. -/
def restDiff (j : Fin P.d) (a : Fin P.B) (r : RestSeed (F := F) P j a) : F :=
  match cands6 P b ι x j a r.1 with
  | some C => TopParams.power ι (2 * a.val + 1) C -
      TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)
  | none => 0

lemma restDiff_some (j : Fin P.d) (a : Fin P.B) (r : RestSeed (F := F) P j a) {C : Finset ℕ}
    (hC : cands6 P b ι x j a r.1 = some C) :
    restDiff P b ι x j a r = TopParams.power ι (2 * a.val + 1) C -
      TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r) := by
  unfold restDiff
  rw [hC]

lemma restDiff_ne_zero (j : Fin P.d) (a : Fin P.B) (r : RestSeed (F := F) P j a)
    (h : restWrong P b ι x j a r) : restDiff P b ι x j a r ≠ 0 := by
  unfold restWrong at h
  obtain ⟨C, hC, hne⟩ := h
  rw [restDiff_some P b ι x j a r hC]
  exact sub_ne_zero.mpr hne

/-- `wrong6` only depends on a local seed away from its `(j,a)`-th scalar. -/
lemma wrong6_update (j : Fin P.d) (a : Fin P.B) (π : Equiv.Perm (Fin P.n))
    {β β' : Fin P.d → Fin P.B → Fˣ} (hβ : ∀ a' : Fin P.B, a' ≠ a → β' j a' = β j a') :
    wrong6 P b ι x j a ((π, β') : (P.scheme b ι).LocalSeed) ↔
      wrong6 P b ι x j a ((π, β) : (P.scheme b ι).LocalSeed) := by
  unfold wrong6
  rw [cands6_congr P b ι x j a π (fun a' ha' => (hβ a' ha').symm)]
  rfl

/-- The candidate of the exact prefix ignores the `(j,a)`-th scalar. -/
lemma cands6_insCoord (j : Fin P.d) (a : Fin P.B) (π : Equiv.Perm (Fin P.n))
    (β : Fin P.d → Fin P.B → Fˣ) (u : Fˣ) :
    cands6 P b ι x j a ((π, insCoord P j a β u) : (P.scheme b ι).LocalSeed) =
      cands6 P b ι x j a ((π, β) : (P.scheme b ι).LocalSeed) := by
  refine cands6_congr P b ι x j a π ?_
  intro a' ha'
  rw [insCoord_at, if_neg ha']

/-- In `ZMod 2`, a difference is one exactly when the two entries differ. -/
lemma zmod2_sub_eq_one_iff (x y : ZMod 2) : x - y = 1 ↔ x ≠ y := by
  constructor
  · intro h hxy
    rw [hxy, sub_self] at h
    exact zero_ne_one h
  · intro h
    rcases zmod2_eq_zero_or_one (x - y) with h0 | h1
    · exact absurd (sub_eq_zero.mp h0) h
    · exact h1

/-- The "first nonzero bit is `k`" condition on the twisted difference, expressed through
`restDiff`.  This is the paper's `2^{w-k-1}` out of `2^w - 1` count, in membership form. -/
lemma pattern_iff_qvec (j : Fin P.d) (a : Fin P.B) (k : Fin P.w)
    (r : RestSeed (F := F) P j a) (u : Fˣ) :
    (∃ C, cands6 P b ι x j a r.1 = some C ∧
      (∀ k' : Fin P.w, k'.val < k.val →
        (b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C)) k' =
          (b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r))) k') ∧
      (b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C)) k ≠
          (b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r))) k)
      ↔ Qvec k (b.repr ((u : F) * restDiff P b ι x j a r)) := by
  classical
  constructor
  · rintro ⟨C, hC, h1, h2⟩
    have hmul : b.repr ((u : F) * (TopParams.power ι (2 * a.val + 1) C -
        TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)))
        = b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C) -
          b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)) := by
      rw [mul_sub, map_sub]
    rw [restDiff_some P b ι x j a r hC, hmul]
    refine ⟨fun k' hk' => ?_, ?_⟩
    · show b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C) k' -
        b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)) k' = 0
      rw [h1 k' hk']
      exact sub_self _
    · show b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C) k -
        b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)) k = 1
      exact (zmod2_sub_eq_one_iff _ _).mpr h2
  · intro hQ
    have hnone : cands6 P b ι x j a r.1 ≠ none := by
      intro hC
      have hd : restDiff P b ι x j a r = 0 := by unfold restDiff; rw [hC]
      rw [hd, mul_zero, map_zero] at hQ
      simpa using hQ.2
    cases hc : cands6 P b ι x j a r.1 with
    | none => exact absurd hc hnone
    | some C =>
      have hd := restDiff_some P b ι x j a r hc
      have hmul : b.repr ((u : F) * (TopParams.power ι (2 * a.val + 1) C -
          TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)))
          = b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) C) -
            b.repr ((u : F) * TopParams.power ι (2 * a.val + 1) (restRow P b ι x j a r)) := by
        rw [mul_sub, map_sub]
      rw [hd, hmul] at hQ
      refine ⟨C, rfl, ?_, ?_⟩
      · intro k' hk'
        have h := hQ.1 k' hk'
        exact sub_eq_zero.mp h
      · exact (zmod2_sub_eq_one_iff _ _).mp hQ.2

/-- Splitting off the `(j,a)`-th scalar: the paper's joint event is the conditioning event of the
rest of the seed together with "the first wrong bit of the twisted difference is `k`". -/
lemma joint6_split (j : Fin P.d) (a : Fin P.B) (k : Fin P.w)
    (q : RestSeed (F := F) P j a × Fˣ) :
    joint6 P b ι x j a k ((splitSeed P b ι j a).symm q) ↔
      restWrong P b ι x j a q.1 ∧ Qvec k (b.repr ((q.2 : F) * restDiff P b ι x j a q.1)) := by
  classical
  obtain ⟨⟨⟨π, β⟩, hβ⟩, u⟩ := q
  have hins : ∀ a' : Fin P.B, a' ≠ a → insCoord P j a β u j a' = β j a' := by
    intro a' ha'
    rw [insCoord_at, if_neg ha']
  show joint6 P b ι x j a k ((π, insCoord P j a β u) : (P.scheme b ι).LocalSeed) ↔
    restWrong P b ι x j a (⟨(π, β), hβ⟩ : RestSeed (F := F) P j a) ∧
      Qvec k (b.repr ((u : F) * restDiff P b ι x j a ⟨(π, β), hβ⟩))
  have hrow : (P.scheme b ι).rowOf ((π, insCoord P j a β u) : (P.scheme b ι).LocalSeed) x j
      = restRow P b ι x j a (⟨(π, β), hβ⟩ : RestSeed (F := F) P j a) := rfl
  unfold joint6 restWrong
  rw [wrong6_update P b ι x j a π (β := β) (β' := insCoord P j a β u) hins]
  rw [cands6_insCoord P b ι x j a π β u]
  rw [hrow]
  simp only [insCoord_same]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (pattern_iff_qvec P b ι x j a k
      (⟨(π, β), hβ⟩ : RestSeed (F := F) P j a) u).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (pattern_iff_qvec P b ι x j a k
      (⟨(π, β), hβ⟩ : RestSeed (F := F) P j a) u).mpr h2⟩

/-- **Conjunct 1 of Lemma 6.2** (`lem:top-bit-bounds`), in the paper's joint form: conditional on
the word prediction being wrong, the first wrong bit `k` has probability `p_k = 2^{w-k-1}/(2^w-1)`.
Written as a joint identity because the conditioning event may be null. -/
lemma joint6_eq (j : Fin P.d) (a : Fin P.B) (k : Fin P.w) (hw : 1 ≤ P.w) :
    prU (joint6 P b ι x j a k) = P.p k.val * prU (wrong6 P b ι x j a) := by
  classical
  haveI hneS : Nonempty (RestSeed (F := F) P j a) := ⟨⟨(1, fun _ _ => 1), rfl⟩⟩
  haveI hneU : Nonempty Fˣ := ⟨1⟩
  have key : ∀ (π : Equiv.Perm (Fin P.n)) (β : Fin P.d → Fin P.B → Fˣ),
      wrong6 P b ι x j a ((π, delCoord P j a β) : (P.scheme b ι).LocalSeed) ↔
        wrong6 P b ι x j a ((π, β) : (P.scheme b ι).LocalSeed) := by
    intro π β
    exact wrong6_update P b ι x j a π (β := β) (β' := delCoord P j a β)
      (fun a' ha' => by rw [delCoord_at, if_neg ha'])
  have hback : prU (fun r : RestSeed (F := F) P j a => restWrong P b ι x j a r) =
      prU (fun lr : (P.scheme b ι).LocalSeed => wrong6 P b ι x j a lr) := by
    rw [← prU_fst_prod (α := RestSeed (F := F) P j a) (β := Fˣ)
      (fun r : RestSeed (F := F) P j a => restWrong P b ι x j a r)]
    rw [← prU_equiv (splitSeed P b ι j a)
      (fun q : RestSeed (F := F) P j a × Fˣ => restWrong P b ι x j a q.1)]
    refine prU_congr (fun lr => ?_)
    obtain ⟨π, β⟩ := lr
    exact key π β
  have hsplit : prU (joint6 P b ι x j a k) =
      prU (fun q : RestSeed (F := F) P j a × Fˣ =>
        joint6 P b ι x j a k ((splitSeed P b ι j a).symm q)) :=
    (prU_equiv (splitSeed P b ι j a).symm (joint6 P b ι x j a k)).symm
  rw [hsplit]
  rw [prU_congr (fun q => joint6_split P b ι x j a k q)]
  rw [prU_prod_twist (P := P) (S := RestSeed (F := F) P j a)
    b (restWrong P b ι x j a) (restDiff P b ι x j a)
    (fun r hr => restDiff_ne_zero P b ι x j a r hr) hw k]
  rw [prU_fst_prod (α := RestSeed (F := F) P j a) (β := Fˣ)]
  rw [hback]
  rfl

end Part1

/-! ## Conjunct 4: `E V_{a,k} ≤ q_a p_k` (Step 2 of `lem:top-bit-bounds`)

The paper: "The algorithm returns `⊥` for the rest of the word after its first wrong bit, so each
row makes at most one incorrect prediction per word.  By Lemma `lem:top-word-bounds`, only rows with
`T_j ≥ a` can make such an error."  Formally, a wrong bit at column `(a,k)` forces (i) the word
prediction to be wrong, and (ii) that its first wrong bit is `k`; step 1 then gives the factor `p_k`,
and Pinsketch uniqueness converts "wrong word" into "the row holds at least `a+1` nonzeros". -/

section Conj4

variable (P : TopParams) (hargs : P.Args)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
variable (x : Finset ℕ)

/-! ### Row images and their cardinalities -/

open Classical in
lemma mem_rowImage {N m : ℕ} {π : Equiv.Perm (Fin N)} {j : ℕ} {S : Finset ℕ} {y : ℕ} :
    y ∈ rowImage N m π j S ↔
      ∃ i : Fin N, i.val ∈ S ∧ (π i).val % m = j ∧ (π i).val / m = y := by
  rw [rowImage, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.2.1, hi.2.2, rfl⟩
  · rintro ⟨i, hS, hmod, hdiv⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS, hmod⟩, hdiv⟩

lemma rowImage_mono {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) {S T : Finset ℕ}
    (h : S ⊆ T) : rowImage N m π j S ⊆ rowImage N m π j T := by
  intro y hy
  rw [mem_rowImage] at hy ⊢
  obtain ⟨i, hiS, h1, h2⟩ := hy
  exact ⟨i, h hiS, h1, h2⟩

lemma rowImage_card_le {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) {S T : Finset ℕ}
    (h : S ⊆ T) : (rowImage N m π j S).card ≤ (rowImage N m π j T).card :=
  Finset.card_le_card (rowImage_mono π j h)

lemma div_lt_rowLen {N m : ℕ} (hm : 0 < m) {t : ℕ} (ht : t < N) :
    t / m < rowLen N m (t % m) := by
  set r := t % m
  have hrlt : r < m := Nat.mod_lt _ hm
  have ht_eq : m * (t / m) + r = t := Nat.div_add_mod t m
  have hmaps : Set.MapsTo (fun a => m * a + r) ↑(range (t / m + 1))
      ↑((range N).filter fun p => p % m = r) := by
    intro a ha
    simp only [mem_coe, mem_range] at ha
    simp only [mem_coe, mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have h1 : m * a ≤ m * (t / m) := Nat.mul_le_mul_left m (by omega)
      omega
    · rw [show m * a + r = r + m * a by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt]
  have hinj : Set.InjOn (fun a => m * a + r) ↑(range (t / m + 1)) := by
    intro a _ b _ hab
    have h : m * a = m * b := Nat.add_right_cancel hab
    exact Nat.eq_of_mul_eq_mul_left hm h
  have hle := Finset.card_le_card_of_injOn (fun a => m * a + r) hmaps hinj
  rw [card_range] at hle
  simpa [rowLen] using hle

lemma rowImage_subset_range_rowLen {N m : ℕ} (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S : Finset ℕ) : rowImage N m π j S ⊆ range (rowLen N m j) := by
  intro y hy
  rw [mem_rowImage] at hy
  obtain ⟨i, -, hmod, hdiv⟩ := hy
  rw [mem_range, ← hdiv, ← hmod]
  exact div_lt_rowLen hm (π i).isLt

/-- The row length of a row of `[n]` split into `d` rows is at most `N = ⌈n/d⌉`. -/
lemma div_lt_N (hargs : P.Args) {p : ℕ} (hp : p < P.n) : p / P.d < P.N := by
  have hd : 0 < P.d := Pd_pos P hargs
  rw [Nat.div_lt_iff_lt_mul hd]
  rw [TopParams.N]
  have h1 : (P.n : ℝ) / (P.d : ℝ) ≤ (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (P.n : ℝ) ≤ (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) * P.d := by
    have h3 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) P.d)
    rw [div_mul_cancel₀] at h3
    · exact h3
    · exact ne_of_gt (by exact_mod_cast hd)
  have h3 : (p : ℝ) < (⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℝ) * P.d := by
    have : (p : ℝ) < (P.n : ℝ) := by exact_mod_cast hp
    linarith
  exact_mod_cast h3

lemma rowLen_le_N (hargs : P.Args) (j : ℕ) : rowLen P.n P.d j ≤ P.N := by
  have hd : 0 < P.d := Pd_pos P hargs
  have hinj : Set.InjOn (fun p : ℕ => p / P.d)
      ↑((range P.n).filter (fun p => p % P.d = j)) := by
    intro a ha b hb hab
    simp only [mem_coe, mem_filter, mem_range] at ha hb
    have hab' : a / P.d = b / P.d := hab
    calc a = P.d * (a / P.d) + a % P.d := (Nat.div_add_mod _ _).symm
      _ = P.d * (b / P.d) + b % P.d := by rw [hab', ha.2, hb.2]
      _ = b := Nat.div_add_mod _ _
  have himg : ((range P.n).filter (fun p => p % P.d = j)).image (fun p => p / P.d) ⊆
      range P.N := by
    intro y hy
    rw [mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [mem_range]
    exact div_lt_N P hargs (by simpa using (mem_filter.mp hp).1)
  calc rowLen P.n P.d j = ((range P.n).filter (fun p => p % P.d = j)).card := rfl
    _ = (((range P.n).filter (fun p => p % P.d = j)).image (fun p => p / P.d)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (range P.N).card := Finset.card_le_card himg
    _ = P.N := card_range _

lemma card_fin_filter_lt {n d : ℕ} (hdn : d ≤ n) :
    (univ.filter fun i : Fin n => i.val < d).card = d := by
  have h5 : (univ.filter fun i : Fin n => i.val < d).card = (univ : Finset (Fin d)).card := by
    refine Finset.card_bij (fun (a : Fin n)
      (ha : a ∈ univ.filter fun i : Fin n => i.val < d) =>
      (⟨a.val, by simpa using ha⟩ : Fin d)) ?_ ?_ ?_
    · intro a ha; simp
    · intro a1 ha1 a2 ha2 h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro b _; exact ⟨⟨b.val, b.isLt.trans_le hdn⟩, by simp [b.isLt], by simp⟩
  rw [h5]
  simp

/-! ### Pinsketch uniqueness (Proposition 2.1) -/

/-- The uniqueness clause of Proposition 2.1 (Pinsketch): light vectors are determined by
their syndrome. -/
lemma pin_unique {N t : ℕ} (hN : 1 ≤ N) (ht : t ≤ N)
    (w : ℕ) (hw : w = ⌈lg ((N : ℝ) + 1)⌉₊)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (x x' : Fin N → ZMod 2)
    (hx : (univ.filter fun i => x i = 1).card ≤ t)
    (hx' : (univ.filter fun i => x' i = 1).card ≤ t)
    (hp : pin ι t x = pin ι t x') : x = x' := by
  exact s612_pin_unique ι h0 hinj hx hx' hp

/-- The Pinsketch power sums of the indicator vector of a finset. -/
lemma pin_indicator {N t : ℕ} (ι : ℕ → F)
    (S : Finset ℕ) (hS : S ⊆ range N) (j : Fin t) :
    pin ι t (fun i : Fin N => if i.val ∈ S then 1 else 0) j =
      TopParams.power ι (2 * j.val + 1) S := by
  show pinPower ι (2 * j.val + 1) (fun i : Fin N => if i.val ∈ S then 1 else 0) = _
  unfold pinPower TopParams.power
  rw [Finset.sum_fin_eq_sum_range]
  have h1 : ∀ v ∈ range N, (if h : v < N then (fun i : Fin N => if i.val ∈ S then (1 : ZMod 2) else 0) ⟨v, h⟩ • ι (⟨v, h⟩ : Fin N).val ^ (2 * j.val + 1) else 0) =
      (if v ∈ S then ι v ^ (2 * j.val + 1) else 0) := by
    intro v hv
    rw [dif_pos (mem_range.mp hv)]
    by_cases h : v ∈ S <;> simp [h]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  congr 1
  ext v
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, hv⟩; exact hv
  · intro hv; exact ⟨by simpa using hS hv, hv⟩

lemma card_indicator {N : ℕ} (S : Finset ℕ) (hS : S ⊆ range N) :
    (univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1).card = S.card := by
  have himg : (univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1).image
      (fun i => i.val) = S := by
    ext v
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i.val ∈ S
      · exact h
      · simp [h] at hi
    · intro hv
      refine ⟨⟨v, by simpa using hS hv⟩, ?_, rfl⟩
      simp [hv]
  have hinj : Set.InjOn (fun i : Fin N => i.val)
      ↑(univ.filter fun i : Fin N => (if i.val ∈ S then (1 : ZMod 2) else 0) = 1) :=
    fun a _ b _ hab => Fin.ext hab
  rw [← Finset.card_image_of_injOn hinj, himg]

lemma pin_unique_sets {N t : ℕ} (hN : 1 ≤ N) (ht : t ≤ N)
    (w : ℕ) (hw : w = ⌈lg ((N : ℝ) + 1)⌉₊)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (S T : Finset ℕ) (hS : S ⊆ range N) (hT : T ⊆ range N)
    (hSc : S.card ≤ t) (hTc : T.card ≤ t)
    (hp : ∀ j : Fin t, TopParams.power ι (2 * j.val + 1) S = TopParams.power ι (2 * j.val + 1) T) : S = T := by
  set x : Fin N → ZMod 2 := fun i => if i.val ∈ S then 1 else 0 with hx
  set x' : Fin N → ZMod 2 := fun i => if i.val ∈ T then 1 else 0 with hx'
  have hp' : pin ι t x = pin ι t x' := by
    funext j
    rw [hx, hx', pin_indicator ι S hS j, pin_indicator ι T hT j]
    exact hp j
  have hxx : x = x' := by
    refine pin_unique hN ht w hw b ι h0 hinj x x' ?_ ?_ hp'
    · rw [hx]; exact le_trans (le_of_eq (card_indicator S hS)) hSc
    · rw [hx']; exact le_trans (le_of_eq (card_indicator T hT)) hTc
  ext v
  by_cases hvN : v < N
  · have h1 : x ⟨v, hvN⟩ = x' ⟨v, hvN⟩ := by rw [hxx]
    constructor
    · intro hv
      have h2 : x ⟨v, hvN⟩ = 1 := by simp [hx, hv]
      rw [h2] at h1
      by_contra hcon
      simp [hx', hcon] at h1
    · intro hv
      have h2 : x' ⟨v, hvN⟩ = 1 := by simp [hx', hv]
      rw [← h1] at h2
      by_contra hcon
      simp [hx, hcon] at h2
  · have h1 : v ∉ S := fun h => hvN (mem_range.mp (hS h))
    have h2 : v ∉ T := fun h => hvN (mem_range.mp (hT h))
    simp [h1, h2]

/-! ### Extending the support and exchangeability -/

lemma exists_superset {n d : ℕ} {x : Finset ℕ} (hx : x ⊆ range n) (hxd : x.card ≤ d)
    (hdn : d ≤ n) : ∃ X : Finset ℕ, x ⊆ X ∧ X ⊆ range n ∧ X.card = d := by
  classical
  set x' : Finset (Fin n) := univ.filter (fun i : Fin n => i.val ∈ x) with hx'
  have hx'card : x'.card = x.card := by
    have himg : x'.image (fun i : Fin n => i.val) = x := by
      ext v
      simp only [hx', mem_image, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hv⟩ => hv ▸ hi, fun hv =>
        ⟨⟨v, by simpa using hx hv⟩, hv, rfl⟩⟩
    have hinj : Set.InjOn (fun i : Fin n => i.val) ↑x' := fun a _ b _ hab => Fin.ext hab
    rw [← Finset.card_image_of_injOn hinj, himg]
  obtain ⟨X', hx'sub, hX'card⟩ := Finset.exists_superset_card_eq (s := x') (n := d)
    (by rw [hx'card]; exact hxd) (by simpa using hdn)
  refine ⟨X'.image (fun i : Fin n => i.val), ?_, ?_, ?_⟩
  · intro v hv
    have hv' : (⟨v, by simpa using hx hv⟩ : Fin n) ∈ x' := by
      simp only [hx', mem_filter, mem_univ, true_and]; exact hv
    exact mem_image.mpr ⟨_, hx'sub hv', rfl⟩
  · intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    exact mem_range.mpr i.isLt
  · have hinj : Set.InjOn (fun i : Fin n => i.val) ↑X' := fun a _ b _ hab => Fin.ext hab
    rw [Finset.card_image_of_injOn hinj]; exact hX'card

lemma subtypeCongr_apply_of {α : Type} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : p a) :
    Equiv.subtypeCongr e f a = e ⟨a, h⟩ := by
  rw [Equiv.subtypeCongr]
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos h]
  rfl

lemma subtypeCongr_apply_of_not {α : Type} {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) {a : α} (h : ¬p a) :
    Equiv.subtypeCongr e f a = f ⟨a, h⟩ := by
  rw [Equiv.subtypeCongr]
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg h]
  rfl

/-- Every `d`-subset of `[n]` is the image of `{0,…,d-1}` under some permutation. -/
lemma exists_perm_range {n d : ℕ} (hdn : d ≤ n) (X : Finset ℕ) (hX : X ⊆ range n)
    (hXc : X.card = d) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, ((σ i).val ∈ X ↔ i.val < d) := by
  classical
  set U : Finset (Fin n) := univ.filter (fun i : Fin n => i.val < d) with hU
  set V : Finset (Fin n) := univ.filter (fun i : Fin n => i.val ∈ X) with hV
  have hUc : U.card = d := card_fin_filter_lt hdn
  have hVc : V.card = d := by
    have himg : V.image (fun i : Fin n => i.val) = X := by
      ext v
      simp only [hV, mem_image, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨i, hi, hv⟩ => hv ▸ hi, fun hv =>
        ⟨⟨v, by simpa using hX hv⟩, hv, rfl⟩⟩
    have hinj : Set.InjOn (fun i : Fin n => i.val) ↑V := fun a _ b _ hab => Fin.ext hab
    rw [← Finset.card_image_of_injOn hinj, himg]; exact hXc
  have he : {i // i ∈ U} ≃ {i // i ∈ V} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hUc, hVc])
  have hf : {i // ¬ i ∈ U} ≃ {i // ¬ i ∈ V} := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hUc, hVc]
  refine ⟨Equiv.subtypeCongr he hf, fun i => ?_⟩
  have hmemV : ∀ z : Fin n, (z ∈ V ↔ z.val ∈ X) := by
    intro z; simp [hV]
  by_cases hi : i.val < d
  · have hiU : i ∈ U := by simp [hU, hi]
    rw [subtypeCongr_apply_of he hf hiU]
    exact ⟨fun _ => hi, fun _ => (hmemV _).mp (he ⟨i, hiU⟩).2⟩
  · have hiU : ¬ i ∈ U := by simp [hU, hi]
    rw [subtypeCongr_apply_of_not he hf hiU]
    exact ⟨fun hcon => False.elim ((hf ⟨i, hiU⟩).2 ((hmemV _).mpr hcon)),
      fun hcon => absurd hcon hi⟩

lemma prU_mul_right {n : ℕ} (τ : Equiv.Perm (Fin n)) (Q : Equiv.Perm (Fin n) → Prop) :
    prU (fun π => Q (π * τ)) = prU Q := by
  have h := prU_equiv (Equiv.mulRight τ) Q
  simpa [Equiv.mulRight] using h

lemma perm_rowImage (n d : ℕ) (X : Finset ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i : Fin n, ((σ i).val ∈ X ↔ i.val < d))
    (π : Equiv.Perm (Fin n)) (j : Fin d) :
    rowImage n d (π * σ⁻¹) j.val X = rowImage n d π j.val (range d) := by
  ext y
  rw [mem_rowImage, mem_rowImage]
  constructor
  · rintro ⟨i, hiX, hmod, hdiv⟩
    refine ⟨σ⁻¹ i, ?_, ?_, ?_⟩
    · rw [mem_range]
      exact (hσ (σ⁻¹ i)).mp (by simpa using hiX)
    · simpa using hmod
    · simpa using hdiv
  · rintro ⟨u, hu, hmod, hdiv⟩
    refine ⟨σ u, ?_, ?_, ?_⟩
    · exact (hσ u).mpr (mem_range.mp hu)
    · simpa using hmod
    · simpa using hdiv

/-! ### The column index -/

lemma wordIdx_mul_add {a' k : ℕ} (hk : k < P.w) (h : a' * P.w + k < P.ell)
    (hA : a' < P.B) : P.wordIdx ⟨a' * P.w + k, h⟩ = ⟨a', hA⟩ := by
  apply Fin.ext
  show (a' * P.w + k) / P.w = a'
  rw [show a' * P.w + k = P.w * a' + k by ring,
    Nat.mul_add_div (by omega : 0 < P.w), Nat.div_eq_of_lt hk, Nat.add_zero]

lemma bitIdx_mul_add {a' k : ℕ} (hk : k < P.w) (h : a' * P.w + k < P.ell)
    (hk' : k < P.w) : P.bitIdx ⟨a' * P.w + k, h⟩ = ⟨k, hk'⟩ := by
  apply Fin.ext
  show (a' * P.w + k) % P.w = k
  rw [show a' * P.w + k = k + P.w * a' by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hk]

/-- The true prefix of length `s.val = a*w + k` reads word `a'` as the twisted true word `a'`. -/
lemma wordOf_truePrefix6 (hargs : P.Args) (j : Fin P.d) (α : Fin P.B → Fˣ) (S : Finset ℕ)
    {a a' : ℕ} (hA : a' < P.B) (ha : (a' + 1) * P.w ≤ a) (haell : a ≤ P.ell) :
    P.wordOf b ((P.scheme b ι).truePrefix j α S a) a' =
      (α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S := by
  have hw : 0 < P.w := Pw_pos P hargs
  unfold TopParams.wordOf
  have h1 : ∀ k : Fin P.w,
      ((P.scheme b ι).truePrefix j α S a).getD (a' * P.w + k.val) 0 =
        b.repr ((α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S) k := by
    intro k
    have hklt : a' * P.w + k.val < a := by
      have hk := k.isLt
      nlinarith
    rw [truePrefix_getD P b ι j α S hklt haell]
    simp only [code6]
    rw [wordIdx_mul_add (P := P) k.isLt (by omega) hA,
      bitIdx_mul_add (P := P) k.isLt (by omega) k.isLt]
  rw [Finset.sum_congr rfl fun k _ => by rw [h1 k]]
  exact b.sum_repr ((α ⟨a', hA⟩ : F) * TopParams.power ι (2 * a' + 1) S)

/-- A bit of the true prefix of length `s.val`, read at an earlier bit of the same word. -/
lemma prefix_getD_eq (hargs : P.Args) (j : Fin P.d) (α : Fin P.B → Fˣ) (s : Fin P.ell)
    (lr : (P.scheme b ι).LocalSeed) {k' : Fin P.w} (hk' : k'.val < (P.bitIdx s).val) :
    ((P.scheme b ι).truePrefix j α ((P.scheme b ι).rowOf lr x j) s.val).getD
        ((P.wordIdx s).val * P.w + k'.val) 0 =
      b.repr ((α (P.wordIdx s) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1)
        ((P.scheme b ι).rowOf lr x j)) k' := by
  have hw : 0 < P.w := Pw_pos P hargs
  have hsval : s.val = (P.wordIdx s).val * P.w + (P.bitIdx s).val := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod s.val P.w).symm
  have hq : (P.wordIdx s).val * P.w + k'.val < s.val := by rw [hsval]; omega
  have hcol : (P.wordIdx s).val * P.w + k'.val < P.ell := lt_of_lt_of_le hq (le_of_lt s.isLt)
  rw [truePrefix_getD P b ι j α ((P.scheme b ι).rowOf lr x j) hq (le_of_lt s.isLt)]
  simp only [code6]
  rw [wordIdx_mul_add (P := P) k'.isLt hcol (P.wordIdx s).isLt,
    bitIdx_mul_add (P := P) k'.isLt hcol k'.isLt]

/-! ### The candidate equals the true row on light rows -/

/-- The inverse of a unit cancels against its value. -/
lemma units_inv_mul_val (u : Fˣ) (c : F) : ((u⁻¹ : Fˣ) : F) * ((u : F) * c) = c := by
  rw [← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero u), one_mul]

/-- If the true row support `R` has at most `i` nonzeros and matches the power sums that `cand`
asks for, then `cand` returns exactly `R` (Pinsketch uniqueness). -/
lemma cand_eq_rowOf (hargs : P.Args) (hι : P.IsAddress ι)
    (j : Fin P.d) (i : ℕ) (hi : i ≤ P.B) (α : Fin P.B → Fˣ)
    (z : List (ZMod 2)) {R : Finset ℕ}
    (hRsub : R ⊆ range (rowLen P.n P.d j.val)) (hRcard : R.card ≤ i)
    (hz : ∀ a' : Fin P.B, a'.val < i →
      P.wordOf b z a' = (α a' : F) * TopParams.power ι (2 * a'.val + 1) R) :
    P.cand b ι j.val α z i = some R := by
  classical
  set Fs := (range (rowLen P.n P.d j.val)).powerset.filter (fun S =>
      S.card ≤ i ∧ ∀ a' : Fin P.B, a'.val < i →
        TopParams.power ι (2 * a'.val + 1) S = ((α a')⁻¹ : Fˣ) * P.wordOf b z a'.val) with hFs
  have hmem : R ∈ Fs := by
    rw [hFs, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hRsub, hRcard, ?_⟩
    intro a' ha'
    rw [hz a' ha', units_inv_mul_val]
  have huniq : ∀ S ∈ Fs, S = R := by
    intro S hS
    rw [hFs, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hScard, hSpow⟩ := hS
    have hSN : S ⊆ range P.N := fun v hv =>
      Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp (hSsub hv)) (rowLen_le_N P hargs j.val))
    have hRN : R ⊆ range P.N := fun v hv =>
      Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp (hRsub hv)) (rowLen_le_N P hargs j.val))
    refine pin_unique_sets (N := P.N) (t := i) (PN_one_le P hargs)
      (le_trans hi (min_le_left _ _)) P.w rfl b ι hι.1 hι.2 S R hSN hRN hScard hRcard ?_
    intro a'
    have h1 := hSpow ⟨a'.val, lt_of_lt_of_le a'.isLt hi⟩ a'.isLt
    have h2 := hz ⟨a'.val, lt_of_lt_of_le a'.isLt hi⟩ a'.isLt
    rw [h1, h2, units_inv_mul_val]
  unfold TopParams.cand
  show Fs.toList.head? = some R
  have hhead : ∃ S, Fs.toList.head? = some S := by
    cases hl : Fs.toList with
    | nil => exact absurd (hl ▸ (Finset.mem_toList.mpr hmem)) (by simp)
    | cons S rest => exact ⟨S, rfl⟩
  obtain ⟨S, hS⟩ := hhead
  have hSmem : S ∈ Fs := by
    have hmemlist : S ∈ Fs.toList := by
      cases hl : Fs.toList with
      | nil => rw [hl] at hS; exact absurd hS (by simp)
      | cons S' rest =>
          rw [hl] at hS
          simp only [List.head?_cons, Option.some.injEq] at hS
          rw [← hS]
          exact List.mem_cons_self ..
    exact Finset.mem_toList.mp hmemlist
  rw [hS, huniq S hSmem]

/-- A wrong word prediction forces the row to hold at least `a+1` nonzeros: on a lighter row the
candidate of the exact prefix is the true row support, by Pinsketch uniqueness. -/
lemma le_of_wrong6 (hargs : P.Args) (hι : P.IsAddress ι)
    (j : Fin P.d) (a : Fin P.B) (lr : (P.scheme b ι).LocalSeed) :
    wrong6 P b ι x j a lr → a.val + 1 ≤ ((P.scheme b ι).rowOf lr x j).card := by
  classical
  intro hw
  obtain ⟨C, hC, hne⟩ := hw
  by_contra hcon
  push_neg at hcon
  have hwpos : 0 < P.w := Pw_pos P hargs
  set R : Finset ℕ := (P.scheme b ι).rowOf lr x j with hR
  have hRsub : R ⊆ range (rowLen P.n P.d j.val) :=
    rowImage_subset_range_rowLen (Pd_pos P hargs) lr.1 j.val x
  have hRcard : R.card ≤ a.val := by omega
  have hz : ∀ a' : Fin P.B, a'.val < a.val →
      P.wordOf b ((P.scheme b ι).truePrefix j (lr.2 j) R (a.val * P.w)) a' =
        ((lr.2 j) a' : F) * TopParams.power ι (2 * a'.val + 1) R := by
    intro a' ha'
    refine wordOf_truePrefix6 P b ι hargs j (lr.2 j) R (lt_trans ha' a.isLt) ?_ ?_
    · have hw : 0 < P.w := Pw_pos P hargs
      nlinarith
    · have h1 : a.val * P.w ≤ P.B * P.w := Nat.mul_le_mul_right _ a.isLt.le
      simpa [TopParams.ell] using h1
  have hcand : cands6 P b ι x j a lr = some R := by
    unfold cands6
    exact cand_eq_rowOf P b ι hargs hι j a.val a.isLt.le (lr.2 j)
      ((P.scheme b ι).truePrefix j (lr.2 j) R (a.val * P.w))
      hRsub hRcard hz
  have hCR : C = R := by
    have h1 := hC
    rw [hcand] at h1
    exact (Option.some.inj h1).symm
  exact hne (by rw [hCR])

/-! ### The wrong-word probability is bounded by the row load -/

lemma prU_wrong6_le (hargs : P.Args) (hι : P.IsAddress ι)
    (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (s : Fin P.ell) (j : Fin P.d) :
    prU (fun lr : (P.scheme b ι).LocalSeed => wrong6 P b ι x j (P.wordIdx s) lr) ≤
      prU (fun π : Equiv.Perm (Fin P.n) => (P.wordIdx s).val + 1 ≤ P.refLoad π j) := by
  classical
  haveI hneL : Nonempty (P.scheme b ι).LocalSeed := ⟨(1, fun _ _ => 1)⟩
  haveI hneP : Nonempty (Equiv.Perm (Fin P.n)) := ⟨1⟩
  have hd : 0 < P.d := Pd_pos P hargs
  have hdn : P.d ≤ P.n := Pd_le_n P hargs
  have hstep1 : prU (fun lr : (P.scheme b ι).LocalSeed =>
        wrong6 P b ι x j (P.wordIdx s) lr) ≤
      prU (fun lr : (P.scheme b ι).LocalSeed =>
        (P.wordIdx s).val + 1 ≤ ((P.scheme b ι).rowOf lr x j).card) :=
    prU_mono (fun lr h => le_of_wrong6 P b ι x hargs hι j (P.wordIdx s) lr h)
  have hstep2 : prU (fun lr : (P.scheme b ι).LocalSeed =>
        (P.wordIdx s).val + 1 ≤ ((P.scheme b ι).rowOf lr x j).card) =
      prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val x).card) :=
    prU_fst_prod (α := Equiv.Perm (Fin P.n)) (β := Fin P.d → Fin P.B → Fˣ)
      (Pp := fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val x).card)
  obtain ⟨X, hxX, hXsub, hXcard⟩ := exists_superset hx hxd hdn
  have hstep3 : prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val x).card) ≤
      prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card) :=
    prU_mono (fun π h => le_trans h (rowImage_card_le π j.val hxX))
  have hstep4 : prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card) =
      prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val (range P.d)).card) := by
    obtain ⟨σ, hσ⟩ := exists_perm_range hdn X hXsub hXcard
    rw [← prU_mul_right (σ⁻¹) (fun π : Equiv.Perm (Fin P.n) =>
      (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val X).card)]
    congr 1
    ext π
    rw [perm_rowImage P.n P.d X σ hσ π j]
  have hstep5 : prU (fun π : Equiv.Perm (Fin P.n) =>
        (P.wordIdx s).val + 1 ≤ (rowImage P.n P.d π j.val (range P.d)).card) =
      prU (fun π : Equiv.Perm (Fin P.n) => (P.wordIdx s).val + 1 ≤ P.refLoad π j) := rfl
  exact le_trans hstep1 (le_trans (le_of_eq hstep2) (le_trans hstep3 (le_of_eq (hstep4.trans hstep5))))

end Conj4

/-! ## Conjunct 4, final assembly -/

section Conj4Final

variable (P : TopParams) (hargs : P.Args)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
variable (x : Finset ℕ)

/-- The event that row `j` predicts bit `s` incorrectly in the exact execution. -/
abbrev err6 (j : Fin P.d) (s : Fin P.ell) (lr : (P.scheme b ι).LocalSeed) : Prop :=
  ∃ e : ZMod 2, (P.scheme b ι).exactPred lr x ∅ s j = some e ∧
    e ≠ (P.scheme b ι).code j (lr.2 j) ((P.scheme b ι).rowOf lr x j) s

/-- Casting a `ℕ`-valued sum to `ℝ` termwise. -/
lemma nat_cast_sum_real {ι : Type} [Fintype ι] (f : ι → ℕ) :
    ((∑ i, f i : ℕ) : ℝ) = ∑ i, (f i : ℝ) := by
  push_cast
  rfl

lemma V6_eq_sum (s : Fin P.ell) (lr : (P.scheme b ι).LocalSeed) :
    ((P.scheme b ι).V lr x ∅ s : ℝ) =
      ∑ j : Fin P.d, (if err6 P b ι x j s lr then (1:ℝ) else 0) := by
  classical
  have hV : (P.scheme b ι).V lr x ∅ s =
      ∑ j : Fin P.d, (if err6 P b ι x j s lr then (1:ℕ) else 0) := by
    unfold RowScheme.V
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : ∃ e : ZMod 2, (P.scheme b ι).exactPred lr x ∅ s j = some e ∧
        e ≠ (P.scheme b ι).code j (lr.2 j) ((P.scheme b ι).rowOf lr x j) s
    · rw [if_pos h]
    · rw [if_neg h]
  rw [hV, nat_cast_sum_real]
  exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)

lemma expU_V6 (s : Fin P.ell) :
    expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).V lr x ∅ s : ℝ)) =
      ∑ j : Fin P.d, prU (fun lr : (P.scheme b ι).LocalSeed => err6 P b ι x j s lr) := by
  classical
  have h : (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).V lr x ∅ s : ℝ)) =
      fun lr => ∑ j : Fin P.d, (if err6 P b ι x j s lr then (1:ℝ) else 0) := by
    funext lr
    exact V6_eq_sum P b ι x s lr
  rw [h, expU_sum_finset]
  exact Finset.sum_congr rfl
    (fun j _ => expU_indicator (fun lr : (P.scheme b ι).LocalSeed => err6 P b ι x j s lr))

/-- An incorrect bit prediction forces the paper's joint event: the word is wrong and its first
wrong bit is the predicted column's bit. -/
lemma err_joint6 (hargs : P.Args) (j : Fin P.d) (s : Fin P.ell)
    (lr : (P.scheme b ι).LocalSeed) :
    err6 P b ι x j s lr → joint6 P b ι x j (P.wordIdx s) (P.bitIdx s) lr := by
  classical
  intro h
  obtain ⟨e, hpred, hne⟩ := h
  set R : Finset ℕ := (P.scheme b ι).rowOf lr x j with hR
  have hneR : e ≠ (P.scheme b ι).code j (lr.2 j) R s := hne
  set z : List (ZMod 2) := (P.scheme b ι).truePrefix j (lr.2 j) R s.val with hz
  have hlen : z.length = s.val := by
    rw [hz]
    simp only [RowScheme.truePrefix, List.length_map, List.length_take, List.length_finRange]
    show min s.val P.ell = s.val
    omega
  change P.predictTop b ι j.val (lr.2 j) z = some e at hpred
  unfold TopParams.predictTop at hpred
  have hlt : z.length < P.ell := by rw [hlen]; exact s.isLt
  rw [dif_pos hlt] at hpred
  dsimp only at hpred
  have hs : (⟨z.length, hlt⟩ : Fin P.ell) = s := Fin.ext hlen
  rw [hs] at hpred
  cases hc : P.cand b ι j.val (lr.2 j) z (P.wordIdx s).val with
  | none =>
      rw [hc] at hpred
      exact absurd hpred (by simp)
  | some C =>
    rw [hc] at hpred
    rw [Option.bind_some] at hpred
    have hzagree : ∀ p, p < (P.wordIdx s).val * P.w →
        z.getD p 0 =
          ((P.scheme b ι).truePrefix j (lr.2 j) ((P.scheme b ι).rowOf lr x j)
            ((P.wordIdx s).val * P.w)).getD p 0 := by
      intro p hp
      have hsval : s.val = (P.wordIdx s).val * P.w + (P.bitIdx s).val := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod s.val P.w).symm
      have hp1 : p < s.val := by rw [hsval]; omega
      have hell : (P.wordIdx s).val * P.w ≤ P.ell := by
        have h1 : (P.wordIdx s).val * P.w ≤ P.B * P.w :=
          Nat.mul_le_mul_right _ (P.wordIdx s).isLt.le
        simpa [TopParams.ell] using h1
      rw [hz, truePrefix_getD P b ι j (lr.2 j) R hp1 (le_of_lt s.isLt),
        truePrefix_getD P b ι j (lr.2 j) R hp hell]
    have hcand6 : cands6 P b ι x j (P.wordIdx s) lr = some C := by
      unfold cands6
      rw [← cand_congr P b ι (j := j.val) (i := (P.wordIdx s).val)
        (α := lr.2 j) (α' := lr.2 j) (z := z)
        (z' := (P.scheme b ι).truePrefix j (lr.2 j) ((P.scheme b ι).rowOf lr x j)
          ((P.wordIdx s).val * P.w))
        (fun a' _ => rfl) hzagree]
      exact hc
    by_cases hcond : ∀ k' : Fin P.w, k'.val < (P.bitIdx s).val →
        (b.repr (((lr.2 j) (P.wordIdx s) : F) *
          TopParams.power ι (2 * (P.wordIdx s).val + 1) C)) k' =
          z.getD ((P.wordIdx s).val * P.w + k'.val) 0
    · rw [if_pos hcond] at hpred
      simp only [Option.some.injEq] at hpred
      have hbv : (P.scheme b ι).code j (lr.2 j) R s =
          b.repr (((lr.2 j) (P.wordIdx s) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1) R)
            (P.bitIdx s) := rfl
      have hbit : b.repr (((lr.2 j) (P.wordIdx s) : F) *
          TopParams.power ι (2 * (P.wordIdx s).val + 1) C) (P.bitIdx s) ≠
          b.repr (((lr.2 j) (P.wordIdx s) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1) R)
            (P.bitIdx s) := by
        intro hEq
        exact hneR (by rw [← hpred, hEq, hbv])
      have hpat : ∀ k' : Fin P.w, k'.val < (P.bitIdx s).val →
          b.repr (((lr.2 j) (P.wordIdx s) : F) *
            TopParams.power ι (2 * (P.wordIdx s).val + 1) C) k' =
          b.repr (((lr.2 j) (P.wordIdx s) : F) *
            TopParams.power ι (2 * (P.wordIdx s).val + 1) R) k' := by
        intro k' hk'
        rw [hcond k' hk', hz]
        exact prefix_getD_eq P b ι x hargs j (lr.2 j) s lr hk'
      have hpowne : TopParams.power ι (2 * (P.wordIdx s).val + 1) C ≠
          TopParams.power ι (2 * (P.wordIdx s).val + 1) R := by
        intro hEq
        exact hbit (by rw [hEq])
      exact ⟨⟨C, hcand6, hpowne⟩, ⟨C, hcand6, hpat, hbit⟩⟩
    · rw [if_neg hcond] at hpred
      exact absurd hpred (by simp)

end Conj4Final

section Assemble

variable (P : TopParams) (hargs : P.Args)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

lemma p_pos (hargs : P.Args) (k : ℕ) : 0 < P.p k := by
  unfold TopParams.p
  exact div_pos (pow_pos (by norm_num) _) (two_pow_sub_one_pos P hargs)

lemma sum_fin_q (hargs : P.Args) (a : ℕ) :
    (∑ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j)) = P.q a := by
  rw [TopParams.q, Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl (fun j hj => by rw [dif_pos (Finset.mem_range.mp hj)])

end Assemble

section Conj4Assemble

variable (P : TopParams) (hargs : P.Args)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
variable (x : Finset ℕ)

/-- **Conjunct 4 of Lemma 6.2** (`lem:top-bit-bounds`), as in the paper:
`E V_{a,k} ≤ q_a p_k`, where the sum over rows is bounded by the row-load probabilities `q_a`. -/
lemma conj4 (hargs : P.Args) (hι : P.IsAddress ι)
    (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (s : Fin P.ell) :
    expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).V lr x ∅ s : ℝ)) ≤
      P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val := by
  classical
  rw [expU_V6 P b ι x s]
  have hterm : ∀ j : Fin P.d,
      prU (fun lr : (P.scheme b ι).LocalSeed => err6 P b ι x j s lr) ≤
        P.p (P.bitIdx s).val * prU (fun π : Equiv.Perm (Fin P.n) =>
          (P.wordIdx s).val + 1 ≤ P.refLoad π j) := by
    intro j
    have h1 : prU (fun lr : (P.scheme b ι).LocalSeed => err6 P b ι x j s lr) ≤
        prU (joint6 P b ι x j (P.wordIdx s) (P.bitIdx s)) :=
      prU_mono (fun lr h => err_joint6 P b ι x hargs j s lr h)
    rw [joint6_eq P b ι x j (P.wordIdx s) (P.bitIdx s) (Pw_pos P hargs)] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left
      (prU_wrong6_le P b ι x hargs hι hx hxd s j) (p_pos P hargs _).le)
  calc ∑ j : Fin P.d, prU (fun lr : (P.scheme b ι).LocalSeed => err6 P b ι x j s lr)
      ≤ ∑ j : Fin P.d, P.p (P.bitIdx s).val * prU (fun π : Equiv.Perm (Fin P.n) =>
          (P.wordIdx s).val + 1 ≤ P.refLoad π j) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = P.p (P.bitIdx s).val * ∑ j : Fin P.d, prU (fun π : Equiv.Perm (Fin P.n) =>
          (P.wordIdx s).val + 1 ≤ P.refLoad π j) := by rw [Finset.mul_sum]
    _ = P.p (P.bitIdx s).val * P.q ((P.wordIdx s).val + 1) := by rw [sum_fin_q P hargs]
    _ = P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val := by ring

end Conj4Assemble

open Classical in
/-- Lemma 6.2 (Within a word), PDF p.29 (printed p.28). Conditioning is written as a joint-event
identity, since the conditioning event may have probability zero. `u` is the unscaled prediction from
the candidate of the exact prefix, `v` the true value; source indices `a, k` are `a + 1, k + 1`. -/
theorem lemma_6_2 (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    let sch := P.scheme b ι
    let cands : sch.LocalSeed → Fin P.d → Fin P.B → Option (Finset ℕ) := fun lr j a =>
      P.cand b ι j.val (lr.2 j)
        (sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) (a.val * P.w)) a.val
    let wrongWord : sch.LocalSeed → Fin P.d → Fin P.B → Prop := fun lr j a =>
      ∃ C, cands lr j a = some C ∧
        TopParams.power ι (2 * a.val + 1) C ≠
          TopParams.power ι (2 * a.val + 1) (sch.rowOf lr x j)
    (∀ (j : Fin P.d) (a : Fin P.B) (k : Fin P.w),
      prU (fun lr : sch.LocalSeed => wrongWord lr j a ∧ ∃ C, cands lr j a = some C ∧
          let α : F := ((lr.2 j : Fin P.B → Fˣ) a : F)
          let bu := b.repr (α * TopParams.power ι (2 * a.val + 1) C)
          let bv := b.repr (α * TopParams.power ι (2 * a.val + 1) (sch.rowOf lr x j))
          (∀ k' : Fin P.w, k'.val < k.val → bu k' = bv k') ∧ bu k ≠ bv k) =
        P.p k.val * prU (fun lr : sch.LocalSeed => wrongWord lr j a)) ∧
    (∑ k ∈ range P.w, P.p k = 1) ∧
    entropyFin (fun k : Fin P.w => P.p k.val) ≤ 2 ∧
    (∀ s : Fin P.ell,
      expU (fun lr : sch.LocalSeed => (sch.V lr x ∅ s : ℝ)) ≤
        P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val) := by
  dsimp only
  refine ⟨?_, sum_p_eq_one P hargs, entropyFin_p_eq P hargs, ?_⟩
  · intro j a k
    show prU (joint6 P b ι x j a k) = P.p k.val * prU (wrong6 P b ι x j a)
    exact joint6_eq P b ι x j a k (Pw_pos P hargs)
  · intro s
    exact conj4 P b ι x hargs hι hx hxd s

end LinearSetReconciliation327.Main.Upstream6265
#print axioms LinearSetReconciliation327.Main.Upstream6265.lemma_6_2
end
end S_Upstream626520261123


