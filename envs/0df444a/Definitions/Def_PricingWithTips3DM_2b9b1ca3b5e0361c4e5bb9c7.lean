-- Prove2me | Definitions.Def_PricingWithTips3DM_2b9b1ca3b5e0361c4e5bb9c7
-- name    : PricingWithTips3DM_2b9b1ca3b5e0361c4e5bb9c7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:21.597699+00:00
-- url     : https://prove2.me/theorems/6f3be0f8-34ef-4fcd-8624-23675db9c0a6
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Cert.Language
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_PricingWithTips3DM_06e60956ff918030951e5808
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# A certified builder language

A deep-embedded combinator language for instance transformations that are
polynomial-time *by construction*. Programs are syntax (`Code`); the library
proves once and for all that evaluation cost and output size of every program
are polynomially bounded in the input size (`Code.cost_size_le_polyBound`).

Design notes:
* Point-free combinators instead of a binder-based language: no contexts, no
  de Bruijn indices, and composition of certificates is a constructor.
* A closed universe `Ty` of first-order types keeps every value encodable and
  gives a canonical size function. Numbers are charged by *bit length*
  (`Nat.size`), never by value, per the succinct-representation discipline:
  there is deliberately no combinator that iterates a numerically-encoded
  number of times.
* Cost is charged by a naive interpreter model: constant per structural step,
  bit-length costs for arithmetic, one unit per element for list traversals,
  and — for the one exponentiation primitive — the cost of repeated
  multiplication. The absolute constants are irrelevant; only polynomial
  boundedness matters.
-/

namespace Hardness
namespace Cert

/-! ## The type universe -/

/-- First-order instance types. -/
inductive Ty : Type where
  | nat
  | bool
  | pair : Ty → Ty → Ty
  | list : Ty → Ty
deriving DecidableEq, Repr

/-- Interpretation of the type universe. Reducible so that instances on the
underlying types (arithmetic, coercions, numerals) apply directly. -/
@[reducible] def Ty.denote : Ty → Type
  | .nat => ℕ
  | .bool => Bool
  | .pair t₁ t₂ => t₁.denote × t₂.denote
  | .list t => List t.denote

/-- The size of a value: bit-length for numbers (plus one so that sizes are
positive), constant for booleans, and structural sums for pairs and lists. -/
def Ty.size : (t : Ty) → t.denote → ℕ
  | .nat, n => n.size + 1
  | .bool, _ => 1
  | .pair t₁ t₂, (a, b) => t₁.size a + t₂.size b + 1
  | .list t, l => (l.map (t.size ·)).sum + l.length + 1

@[simp] theorem Ty.size_nat (n : ℕ) : Ty.size .nat n = n.size + 1 := rfl

@[simp] theorem Ty.size_bool (b : Bool) : Ty.size .bool b = 1 := rfl

@[simp] theorem Ty.size_pair {t₁ t₂ : Ty} (x : (Ty.pair t₁ t₂).denote) :
    Ty.size (.pair t₁ t₂) x = t₁.size x.1 + t₂.size x.2 + 1 := rfl

@[simp] theorem Ty.size_list {t : Ty} (l : List t.denote) :
    Ty.size (.list t) l = (l.map (t.size ·)).sum + l.length + 1 := rfl

/-- Every element of a list is at most as large as the list. -/
theorem Ty.size_elem_le {t : Ty} {l : List t.denote} {a : t.denote} (ha : a ∈ l) :
    t.size a ≤ Ty.size (.list t) l := by
  rw [Ty.size_list]
  have h := List.single_le_sum (l := l.map (t.size ·)) (fun x _ ↦ Nat.zero_le x) _
    (List.mem_map_of_mem ha)
  omega

/-! ## Bit-length arithmetic lemmas -/

theorem size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  calc a + b < 2 ^ a.size + 2 ^ b.size :=
        Nat.add_lt_add (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ ≤ 2 ^ max a.size b.size + 2 ^ max a.size b.size :=
        Nat.add_le_add
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
          (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    _ ≤ 2 ^ (max a.size b.size + 1) := by rw [pow_succ]; omega

theorem size_sub_le (a b : ℕ) : (a - b).size ≤ a.size := by
  rw [Nat.size_le]
  exact lt_of_le_of_lt (Nat.sub_le a b) (Nat.lt_size_self a)

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
    (Nat.zero_le _) (Nat.zero_le _)

/-- The bit-length of a power grows linearly in the exponent: `b ^ n` needs at
most `n` copies of `b`'s bits. This is what makes exponentiation safe when the
exponent is a list *length* (bounded by the input size) and catastrophic when
it is a binary-encoded value. -/
theorem size_pow_le (b n : ℕ) : (b ^ n).size ≤ n * b.size + 1 := by
  rw [Nat.size_le]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · calc b ^ n < (2 ^ b.size) ^ n := Nat.pow_lt_pow_left (Nat.lt_size_self b) (by omega)
      _ = 2 ^ (n * b.size) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (n * b.size + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem size_le_succ_self (n : ℕ) : n.size ≤ n + 1 := by
  rw [Nat.size_le]
  calc n < n + 1 := Nat.lt_succ_self n
    _ ≤ 2 ^ (n + 1) := Nat.lt_two_pow_self.le

/-- The bit-length of the sum of a list is bounded by the total bit content of
the list: each addition grows the bit-length by at most one carry bit, charged
to the `+ 1` of its summand. -/
theorem sum_size_le (l : List ℕ) : l.sum.size ≤ (l.map fun n ↦ n.size + 1).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    have h := size_add_le a l.sum
    omega

/-! ## Monomial bounds

We state all resource bounds in the fixed monomial shape `C * (s + 1) ^ d`,
which is closed under the compositions we need and avoids `Polynomial ℕ`
bookkeeping. -/

/-- The monomial bound `C * (s + 1) ^ d`. -/
def polyBound (C d s : ℕ) : ℕ := C * (s + 1) ^ d

theorem polyBound_mono {C C' d d' s s' : ℕ} (hC : C ≤ C') (hd : d ≤ d') (hs : s ≤ s') :
    polyBound C d s ≤ polyBound C' d' s' := by
  unfold polyBound
  have h1 : (s + 1) ^ d ≤ (s' + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : (s' + 1) ^ d ≤ (s' + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  exact Nat.mul_le_mul hC (h1.trans h2)

theorem one_le_polyBound_one (d s : ℕ) : 1 ≤ polyBound 1 d s := by
  unfold polyBound
  simpa using Nat.one_le_pow d (s + 1) (by omega)

/-- Composition of monomial bounds: plugging one bound into another stays
monomial. -/
theorem polyBound_comp {C₁ d₁ C₂ d₂ s t : ℕ} (ht : t ≤ polyBound C₁ d₁ s) :
    polyBound C₂ d₂ t ≤ polyBound (C₂ * (C₁ + 1) ^ d₂) (d₁ * d₂) s := by
  unfold polyBound at *
  calc C₂ * (t + 1) ^ d₂
      ≤ C₂ * (C₁ * (s + 1) ^ d₁ + 1) ^ d₂ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ C₂ * ((C₁ + 1) * (s + 1) ^ d₁) ^ d₂ := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
        have h1 : 1 ≤ (s + 1) ^ d₁ := Nat.one_le_pow _ _ (by omega)
        rw [add_mul, one_mul]
        omega
    _ = C₂ * ((C₁ + 1) ^ d₂ * ((s + 1) ^ d₁) ^ d₂) := by rw [mul_pow]
    _ = C₂ * ((C₁ + 1) ^ d₂ * (s + 1) ^ (d₁ * d₂)) := by rw [← pow_mul]
    _ = C₂ * (C₁ + 1) ^ d₂ * (s + 1) ^ (d₁ * d₂) := (mul_assoc _ _ _).symm

/-- Sums of lists of naturals are bounded by length times an element bound.
(Self-contained induction to keep atoms aligned for `omega`.) -/
theorem list_sum_le_length_mul (L : List ℕ) (B : ℕ) (hB : ∀ x ∈ L, x ≤ B) :
    L.sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.sum_cons, List.length_cons]
    rw [add_mul, one_mul]
    have h1 := hB y (List.mem_cons_self ..)
    have h2 := ih fun x hx ↦ hB x (List.mem_cons_of_mem _ hx)
    omega

/-- Elements of `zipIdx` come from the list, with in-range indices. -/
theorem mem_zipIdx_bounds {α : Type*} {l : List α} {x : α × ℕ} (hx : x ∈ l.zipIdx) :
    x.1 ∈ l ∧ x.2 < l.length := by
  rw [List.mem_zipIdx_iff_getElem?] at hx
  obtain ⟨h, heq⟩ := List.getElem?_eq_some_iff.mp hx
  exact ⟨heq ▸ List.getElem_mem h, h⟩

/-- An "each element with its index" computation over a list is an indexed
family over its positions: `List.zipIdx` and `List.ofFn` are inverse views. -/
theorem map_zipIdx_eq_ofFn {α β : Type*} (l : List α) (f : α → ℕ → β) :
    (l.zipIdx.map fun p ↦ f p.1 p.2) = List.ofFn fun j : Fin l.length ↦ f l[(j : ℕ)] (j : ℕ) :=
  List.ext_getElem (by simp) fun i h₁ h₂ ↦ by simp

/-- Summing an "each element with its index" computation, as a sum over
positions. -/
theorem sum_map_zipIdx {α : Type*} (l : List α) (f : α → ℕ → ℕ) :
    (l.zipIdx.map fun p ↦ f p.1 p.2).sum = ∑ j : Fin l.length, f l[(j : ℕ)] (j : ℕ) := by
  rw [map_zipIdx_eq_ofFn, List.sum_ofFn]

private theorem filter_zipIdx_eq_singleton_aux {α : Type*} (l : List α) (s k : ℕ)
    (h : k < l.length) : ((l.zipIdx s).filter fun q ↦ decide (q.2 = s + k)) = [(l[k], s + k)] := by
  induction l generalizing s k with
  | nil => simp at h
  | cons a t ih =>
    rw [show (a :: t).zipIdx s = (a, s) :: t.zipIdx (s + 1) from rfl]
    match k with
    | 0 =>
      rw [List.filter_cons_of_pos (by simp),
        List.filter_eq_nil_iff.mpr fun q hq ↦ by
          have := List.le_snd_of_mem_zipIdx hq
          simp only [decide_eq_true_eq]
          omega]
      simp
    | k + 1 =>
      have hk : k < t.length := by simp only [List.length_cons] at h; omega
      rw [List.filter_cons_of_neg (by simp), show s + (k + 1) = s + 1 + k by omega, ih (s + 1) k hk]
      simp

/-- Enumerating commutes with a map on the elements — the positions do not
move — so a filter-then-map over the enumeration of a mapped list is one over
the enumeration of the original. This is the transport that lets a certificate
compare its output with a construction carried out on decoded elements. -/
theorem filter_map_zipIdx {α β γ : Type*} (l : List α) (f : α → β) (s : ℕ)
    (p : β × ℕ → Bool) (F : β × ℕ → γ) :
    (((l.map f).zipIdx s).filter p).map F
      = ((l.zipIdx s).filter fun q ↦ p (f q.1, q.2)).map fun q ↦ F (f q.1, q.2) := by
  induction l generalizing s with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons,
      show (f a :: t.map f).zipIdx s = (f a, s) :: (t.map f).zipIdx (s + 1) from rfl,
      show (a :: t).zipIdx s = (a, s) :: t.zipIdx (s + 1) from rfl,
      List.filter_cons, List.filter_cons]
    by_cases h : p (f a, s) = true
    · rw [if_pos h, if_pos h, List.map_cons, List.map_cons, ih]
    · rw [if_neg h, if_neg h, ih]

/-- Reading a value out of a list, in a language with no indexing primitive:
filtering the enumeration by position leaves exactly the element there. -/
theorem filter_zipIdx_eq_singleton {α : Type*} {l : List α} {k : ℕ} (h : k < l.length) :
    (l.zipIdx.filter fun q ↦ decide (q.2 = k)) = [(l[k], k)] := by
  have h0 := filter_zipIdx_eq_singleton_aux l 0 k h
  rwa [Nat.zero_add] at h0

private theorem filter_zipIdx_lastOcc_aux {α : Type*} [DecidableEq α] (l : List α) (s : ℕ) :
    ((l.zipIdx s).filter fun q ↦
        (l.zipIdx s).all fun r ↦ !(decide (q.2 < r.2) && decide (r.1 = q.1))).map
      Prod.fst = l.dedup := by
  induction l generalizing s with
  | nil => rfl
  | cons a t ih =>
    rw [List.zipIdx_cons, List.filter_cons]
    have hfst : ∀ r : α × ℕ, r ∈ t.zipIdx (s + 1) → r.1 ∈ t := fun r hr ↦
      List.zipIdx_map_fst (s + 1) t ▸ List.mem_map_of_mem hr
    have htail : ∀ q ∈ t.zipIdx (s + 1),
        (((a, s) :: t.zipIdx (s + 1)).all fun r ↦
            !(decide (q.2 < r.2) && decide (r.1 = q.1)))
          = (t.zipIdx (s + 1)).all fun r ↦ !(decide (q.2 < r.2) && decide (r.1 = q.1)) := by
      intro q hq
      have hq2 : s + 1 ≤ q.2 := List.le_snd_of_mem_zipIdx hq
      rw [List.all_cons, decide_eq_false (show ¬(q.2 < s) by omega), Bool.false_and,
        Bool.not_false, Bool.true_and]
    by_cases hmem : a ∈ t
    · have hhead : ¬((((a, s) :: t.zipIdx (s + 1)).all fun r ↦
          !(decide (s < r.2) && decide (r.1 = a))) = true) := by
        rw [← List.zipIdx_map_fst (s + 1) t] at hmem
        obtain ⟨r, hr, hra⟩ := List.mem_map.mp hmem
        intro hall
        have h := List.all_eq_true.mp hall r (List.mem_cons_of_mem _ hr)
        rw [decide_eq_true (show s < r.2 by have := List.le_snd_of_mem_zipIdx hr; omega),
          decide_eq_true hra, Bool.true_and, Bool.not_true] at h
        exact Bool.false_ne_true h
      rw [if_neg hhead, List.filter_congr htail, ih (s + 1), List.dedup_cons_of_mem hmem]
    · have hhead : (((a, s) :: t.zipIdx (s + 1)).all fun r ↦
          !(decide (s < r.2) && decide (r.1 = a))) = true := by
        rw [List.all_eq_true]
        rintro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · rw [decide_eq_false (lt_irrefl s), Bool.false_and, Bool.not_false]
        · rw [decide_eq_false (show ¬(r.1 = a) from fun h ↦ hmem (h ▸ hfst r hr')),
            Bool.and_false, Bool.not_false]
      rw [if_pos hhead, List.map_cons, List.filter_congr htail, ih (s + 1),
        List.dedup_cons_of_notMem hmem]

/-- The last-occurrence filter computes `List.dedup`: keeping exactly the
enumerated positions whose value never recurs later leaves each distinct value
once. (Mathlib's `dedup` keeps *last* occurrences, which is why the test looks
forward, not back.) -/
theorem filter_zipIdx_lastOcc_map_fst_eq_dedup {α : Type*} [DecidableEq α] (l : List α) :
    ((l.zipIdx.filter fun q ↦
        l.zipIdx.all fun r ↦ !(decide (q.2 < r.2) && decide (r.1 = q.1))).map
      Prod.fst) = l.dedup :=
  filter_zipIdx_lastOcc_aux l 0

/-! ## Per-primitive resource bounds

Stated as standalone lemmas over `ℕ` so that the corresponding cases of the
main induction close by `exact` (definitional unfolding), avoiding fragile
`simp` matching against `Ty.size` on concrete types. -/

private theorem natAdd_case (a b : ℕ) :
    (max a.size b.size + 1) + ((a + b).size + 1)
      ≤ polyBound 4 1 (a.size + 1 + (b.size + 1) + 1) := by
  have h := size_add_le a b
  simp only [polyBound, pow_one]
  omega

private theorem natSub_case (a b : ℕ) :
    (a.size + b.size + 1) + ((a - b).size + 1)
      ≤ polyBound 3 1 (a.size + 1 + (b.size + 1) + 1) := by
  have h := size_sub_le a b
  simp only [polyBound, pow_one]
  omega

private theorem natMul_case (a b : ℕ) :
    (a.size * b.size + 1) + ((a * b).size + 1)
      ≤ polyBound 3 2 (a.size + 1 + (b.size + 1) + 1) := by
  have h := size_mul_le a b
  simp only [polyBound]
  nlinarith [h, Nat.zero_le (a.size * b.size)]

private theorem natLe_case (a b : ℕ) :
    (max a.size b.size + 1) + 1 ≤ polyBound 3 1 (a.size + 1 + (b.size + 1) + 1) := by
  simp only [polyBound, pow_one]
  omega

/-- The exponentiation case. Both the charged cost `((n + 1) * (bits b)) ^ 2`
and the output bit-length `n * bits b` are bounded by the square of the input
size, because the exponent `n` is a list length and therefore *itself* bounded
by the input size — the crux of why `natPowLen` is safe. -/
private theorem natPowLen_case (b n s : ℕ) :
    ((n + 1) * (b.size + 1)) ^ 2 + 1 + ((b ^ n).size + 1)
      ≤ polyBound 3 4 (b.size + 1 + (s + n + 1) + 1) := by
  set S := b.size + 1 + (s + n + 1) + 1 with hS
  have hfac : (n + 1) * (b.size + 1) ≤ S * S :=
    Nat.mul_le_mul (by omega) (by omega)
  have hcost : ((n + 1) * (b.size + 1)) ^ 2 ≤ S ^ 4 := by
    calc ((n + 1) * (b.size + 1)) ^ 2 ≤ (S * S) ^ 2 := Nat.pow_le_pow_left hfac 2
      _ = S ^ 4 := by ring
  have hout : (b ^ n).size ≤ S ^ 2 := by
    have h := size_pow_le b n
    have : n * b.size + 1 ≤ (n + 1) * (b.size + 1) := by nlinarith
    calc (b ^ n).size ≤ (n + 1) * (b.size + 1) := by omega
      _ ≤ S * S := hfac
      _ = S ^ 2 := by ring
  have h4 : S ^ 4 ≤ (S + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : S ^ 2 ≤ (S + 1) ^ 4 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h0 : 3 ≤ (S + 1) ^ 4 := by
    have : (4 : ℕ) ^ 4 ≤ (S + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  simp only [polyBound]
  linarith

/-! ## The combinator language -/

/-- Programs of the builder language: syntactic certificates that an instance
transformation is polynomial-time by construction. -/
inductive Code : Ty → Ty → Type where
  /-- Identity. -/
  | id : Code σ σ
  /-- Sequential composition (diagrammatic order). -/
  | comp : Code σ τ → Code τ ρ → Code σ ρ
  /-- First projection. -/
  | fst : Code (.pair τ₁ τ₂) τ₁
  /-- Second projection. -/
  | snd : Code (.pair τ₁ τ₂) τ₂
  /-- Pairing (with implicit duplication of the input). -/
  | pair : Code σ τ₁ → Code σ τ₂ → Code σ (.pair τ₁ τ₂)
  /-- A constant output. -/
  | const : (t : Ty) → t.denote → Code σ t
  /-- Branching on a computed condition. -/
  | branch : Code σ .bool → Code σ τ → Code σ τ → Code σ τ
  /-- Addition of binary naturals. -/
  | natAdd : Code (.pair .nat .nat) .nat
  /-- Truncated subtraction of binary naturals. -/
  | natSub : Code (.pair .nat .nat) .nat
  /-- Multiplication of binary naturals (grade-school cost). -/
  | natMul : Code (.pair .nat .nat) .nat
  /-- Comparison of binary naturals. -/
  | natLe : Code (.pair .nat .nat) .bool
  /-- Length of a list (as a binary natural). -/
  | listLen : Code (.list τ) .nat
  /-- Mapping a program over a list. -/
  | listMap : Code σ τ → Code (.list σ) (.list τ)
  /-- Boolean negation. -/
  | boolNot : Code .bool .bool
  /-- Boolean conjunction. -/
  | boolAnd : Code (.pair .bool .bool) .bool
  /-- Boolean disjunction. -/
  | boolOr : Code (.pair .bool .bool) .bool
  /-- Equality test on binary naturals. -/
  | natEq : Code (.pair .nat .nat) .bool
  /-- The singleton list. -/
  | listSingle : Code τ (.list τ)
  /-- List concatenation. -/
  | listAppend : Code (.pair (.list τ) (.list τ)) (.list τ)
  /-- Flattening a list of lists. -/
  | listJoin : Code (.list (.list τ)) (.list τ)
  /-- Filtering a list by a computed predicate. -/
  | listFilter : Code σ .bool → Code (.list σ) (.list σ)
  /-- Mapping a program over a list with an environment threaded through:
  the fundamental binder-free "loop body with context". -/
  | listMapEnv : Code (.pair ρ σ) τ → Code (.pair ρ (.list σ)) (.list τ)
  /-- Pairing each element with its position index (as a binary natural). -/
  | listEnum : Code (.list τ) (.list (.pair τ .nat))
  /-- Sum of a list of binary naturals — the one aggregate combinator. A
  general fold is deliberately impossible (it would break the blanket
  polynomial theorem); an individually-charged sum is safe because the sum's
  bit-length is bounded by the list's total bit content (`sum_size_le`). -/
  | listSum : Code (.list .nat) .nat
  /-- Exponentiation with the exponent given by a *list length*:
  `(b, l) ↦ b ^ l.length`. Charging exponentiation at all is delicate — with a
  binary-encoded exponent the output alone is exponentially long — so the
  exponent is not a number of the language at all: it can only be read off a
  list, and lists are bounded by the input size. A program wanting `b ^ j` must
  therefore exhibit a list of length `j`, which is exactly the discipline that
  keeps the blanket polynomial theorem true. -/
  | natPowLen : Code (.pair .nat (.list τ)) .nat

namespace Code

/-- Evaluation of programs. -/
def eval : Code σ τ → σ.denote → τ.denote
  | .id, x => x
  | .comp f g, x => eval g (eval f x)
  | .fst, (a, _) => a
  | .snd, (_, b) => b
  | .pair f g, x => (eval f x, eval g x)
  | .const _ v, _ => v
  | .branch b f g, x => if eval b x then eval f x else eval g x
  | .natAdd, (a, b) => a + b
  | .natSub, (a, b) => a - b
  | .natMul, (a, b) => a * b
  | .natLe, (a, b) => decide (a ≤ b)
  | .listLen, l => l.length
  | .listMap f, l => l.map (eval f)
  | .boolNot, b => !b
  | .boolAnd, (a, b) => a && b
  | .boolOr, (a, b) => a || b
  | .natEq, (a, b) => decide (a = b)
  | .listSingle, a => [a]
  | .listAppend, (l₁, l₂) => l₁ ++ l₂
  | .listJoin, l => l.flatten
  | .listFilter p, l => l.filter (fun a ↦ eval p a)
  | .listMapEnv f, (e, l) => l.map (fun a ↦ eval f (e, a))
  | .listEnum, l => l.zipIdx
  | .listSum, l => l.sum
  | .natPowLen, (b, l) => b ^ l.length

/-- Interpreter cost of programs, in the naive charging model. -/
def cost : Code σ τ → σ.denote → ℕ
  | .id, _ => 1
  | .comp f g, x => cost f x + cost g (eval f x) + 1
  | .fst, _ => 1
  | .snd, _ => 1
  | .pair f g, x => cost f x + cost g x + 1
  | .const t v, _ => t.size v + 1
  | .branch b f g, x => cost b x + (if eval b x then cost f x else cost g x) + 1
  | .natAdd, (a, b) => max a.size b.size + 1
  | .natSub, (a, b) => a.size + b.size + 1
  | .natMul, (a, b) => a.size * b.size + 1
  | .natLe, (a, b) => max a.size b.size + 1
  | .listLen, l => l.length + 1
  | .listMap f, l => (l.map (fun a ↦ cost f a + 1)).sum + 1
  | .boolNot, _ => 1
  | .boolAnd, _ => 1
  | .boolOr, _ => 1
  | .natEq, (a, b) => max a.size b.size + 1
  | .listSingle, _ => 1
  | .listAppend, (l₁, l₂) => l₁.length + l₂.length + 1
  | .listJoin, l => (l.map (fun s ↦ s.length + 1)).sum + 1
  | .listFilter p, l => (l.map (fun a ↦ cost p a + 1)).sum + 1
  | .listMapEnv f, (e, l) => (l.map (fun a ↦ cost f (e, a) + 1)).sum + 1
  | .listEnum, l => (l.length + 1) * (l.length + 1) + 1
  | .listSum, l => (l.map fun n ↦ n.size + 1).sum + 1
  | .natPowLen, (b, l) => ((l.length + 1) * (b.size + 1)) ^ 2 + 1

/-- **The generic safety theorem**: cost and output size of every program of
the builder language are polynomially bounded in the input size. Proved once,
by induction on syntax; individual reductions never reason about resources. -/
theorem cost_size_le_polyBound {σ τ : Ty} (c : Code σ τ) :
    ∃ C d, ∀ x : σ.denote,
      cost c x + τ.size (eval c x) ≤ polyBound C d (σ.size x) := by
  induction c with
  | @id σ =>
    refine ⟨2, 1, fun x ↦ ?_⟩
    simp only [cost, eval, polyBound, pow_one]
    omega
  | @comp σ τ ρ f g ihf ihg =>
    obtain ⟨C₁, d₁, h₁⟩ := ihf
    obtain ⟨C₂, d₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂ * (C₁ + 1) ^ d₂ + 1, d₁ * d₂ + d₁, fun x ↦ ?_⟩
    have hf := h₁ x
    have hg := h₂ (eval f x)
    have hsize : τ.size (eval f x) ≤ polyBound C₁ d₁ (σ.size x) :=
      le_trans (Nat.le_add_left _ _) hf
    have hcomp : polyBound C₂ d₂ (τ.size (eval f x))
        ≤ polyBound (C₂ * (C₁ + 1) ^ d₂) (d₁ * d₂) (σ.size x) :=
      polyBound_comp hsize
    have e1 : polyBound C₁ d₁ (σ.size x) ≤ polyBound C₁ (d₁ * d₂ + d₁) (σ.size x) :=
      polyBound_mono le_rfl (Nat.le_add_left d₁ (d₁ * d₂)) le_rfl
    have e2 : polyBound (C₂ * (C₁ + 1) ^ d₂) (d₁ * d₂) (σ.size x)
        ≤ polyBound (C₂ * (C₁ + 1) ^ d₂) (d₁ * d₂ + d₁) (σ.size x) :=
      polyBound_mono le_rfl (Nat.le_add_right _ _) le_rfl
    have e3 : (1 : ℕ) ≤ polyBound 1 (d₁ * d₂ + d₁) (σ.size x) :=
      one_le_polyBound_one _ _
    have hsum : polyBound C₁ (d₁ * d₂ + d₁) (σ.size x)
        + polyBound (C₂ * (C₁ + 1) ^ d₂) (d₁ * d₂ + d₁) (σ.size x)
        + polyBound 1 (d₁ * d₂ + d₁) (σ.size x)
        = polyBound (C₁ + C₂ * (C₁ + 1) ^ d₂ + 1) (d₁ * d₂ + d₁) (σ.size x) := by
      simp only [polyBound]; ring
    simp only [cost, eval]
    omega
  | @fst τ₁ τ₂ =>
    refine ⟨2, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    simp only [cost, eval, polyBound, pow_one, Ty.size_pair]
    omega
  | @snd τ₁ τ₂ =>
    refine ⟨2, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    simp only [cost, eval, polyBound, pow_one, Ty.size_pair]
    omega
  | @pair σ τ₁ τ₂ f g ihf ihg =>
    obtain ⟨C₁, d₁, h₁⟩ := ihf
    obtain ⟨C₂, d₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂ + 2, d₁ + d₂, fun x ↦ ?_⟩
    have hf := h₁ x
    have hg := h₂ x
    have e1 : polyBound C₁ d₁ (σ.size x) ≤ polyBound C₁ (d₁ + d₂) (σ.size x) :=
      polyBound_mono le_rfl (by omega) le_rfl
    have e2 : polyBound C₂ d₂ (σ.size x) ≤ polyBound C₂ (d₁ + d₂) (σ.size x) :=
      polyBound_mono le_rfl (by omega) le_rfl
    have e3 : (1 : ℕ) ≤ polyBound 1 (d₁ + d₂) (σ.size x) :=
      one_le_polyBound_one _ _
    have hsum : polyBound C₁ (d₁ + d₂) (σ.size x) + polyBound C₂ (d₁ + d₂) (σ.size x)
        + 2 * polyBound 1 (d₁ + d₂) (σ.size x)
        = polyBound (C₁ + C₂ + 2) (d₁ + d₂) (σ.size x) := by
      simp only [polyBound]; ring
    simp only [cost, eval, Ty.size_pair]
    omega
  | @const σ t v =>
    refine ⟨2 * t.size v + 2, 0, fun x ↦ ?_⟩
    simp only [cost, eval, polyBound, pow_zero]
    omega
  | @branch σ τ b f g ihb ihf ihg =>
    obtain ⟨C₀, d₀, h₀⟩ := ihb
    obtain ⟨C₁, d₁, h₁⟩ := ihf
    obtain ⟨C₂, d₂, h₂⟩ := ihg
    refine ⟨C₀ + C₁ + C₂ + 1, d₀ + d₁ + d₂, fun x ↦ ?_⟩
    have hb := h₀ x
    have hf := h₁ x
    have hg := h₂ x
    have e0 : polyBound C₀ d₀ (σ.size x) ≤ polyBound C₀ (d₀ + d₁ + d₂) (σ.size x) :=
      polyBound_mono le_rfl (by omega) le_rfl
    have e1 : polyBound C₁ d₁ (σ.size x) ≤ polyBound C₁ (d₀ + d₁ + d₂) (σ.size x) :=
      polyBound_mono le_rfl (by omega) le_rfl
    have e2 : polyBound C₂ d₂ (σ.size x) ≤ polyBound C₂ (d₀ + d₁ + d₂) (σ.size x) :=
      polyBound_mono le_rfl (by omega) le_rfl
    have e3 : (1 : ℕ) ≤ polyBound 1 (d₀ + d₁ + d₂) (σ.size x) :=
      one_le_polyBound_one _ _
    have hsum : polyBound C₀ (d₀ + d₁ + d₂) (σ.size x)
        + polyBound C₁ (d₀ + d₁ + d₂) (σ.size x)
        + polyBound C₂ (d₀ + d₁ + d₂) (σ.size x)
        + polyBound 1 (d₀ + d₁ + d₂) (σ.size x)
        = polyBound (C₀ + C₁ + C₂ + 1) (d₀ + d₁ + d₂) (σ.size x) := by
      simp only [polyBound]; ring
    simp only [cost, eval]
    by_cases hcond : eval b x = true
    · simp only [if_pos hcond]
      omega
    · simp only [if_neg hcond]
      omega
  | natAdd =>
    refine ⟨4, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    exact natAdd_case a b
  | natSub =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    exact natSub_case a b
  | natMul =>
    refine ⟨3, 2, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    exact natMul_case a b
  | natLe =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    exact natLe_case a b
  | @listLen τ =>
    refine ⟨3, 1, fun l ↦ ?_⟩
    have h := size_le_succ_self l.length
    simp only [cost, eval, polyBound, pow_one, Ty.size_list, Ty.size_nat]
    omega
  | @listMap σ τ f ih =>
    obtain ⟨C, d, h⟩ := ih
    refine ⟨2 * C + 2, d + 1, fun l ↦ ?_⟩
    set S := Ty.size (.list σ) l with hS
    have hlen : l.length ≤ S := by rw [hS, Ty.size_list]; omega
    -- each element is bounded by the whole input
    have helem : ∀ a ∈ l, cost f a + τ.size (eval f a) ≤ polyBound C d S := fun a ha ↦
      (h a).trans (polyBound_mono le_rfl le_rfl (Ty.size_elem_le ha))
    -- bound the interpreter cost
    have hcost : (l.map (fun a ↦ cost f a + 1)).sum
        ≤ l.length * polyBound C d S + l.length := by
      have hb := list_sum_le_length_mul (l.map (fun a ↦ cost f a + 1)) (polyBound C d S + 1)
        (by
          intro x hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          have := helem a ha
          omega)
      simp only [List.length_map] at hb
      have hexp : l.length * (polyBound C d S + 1) = l.length * polyBound C d S + l.length := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    -- bound the output size
    have hout : ((l.map (eval f)).map (τ.size ·)).sum ≤ l.length * polyBound C d S := by
      have hb := list_sum_le_length_mul ((l.map (eval f)).map (τ.size ·)) (polyBound C d S)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
          have := helem a ha
          omega)
      simp only [List.length_map] at hb
      exact hb
    have hlenmap : (l.map (eval f)).length = l.length := by simp
    -- `len * B ≤ B * S`, aligning atoms for the final omega
    have hpb : l.length * polyBound C d S ≤ polyBound C d S * S := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hlen
    have hstep : polyBound C d S * S + S + 1 ≤ polyBound (C + 1) (d + 1) S := by
      have h1 : 1 ≤ (S + 1) ^ d := Nat.one_le_pow _ _ (by omega)
      simp only [polyBound, pow_succ]
      nlinarith [h1]
    have hfinal : polyBound (C + 1) (d + 1) S + polyBound (C + 1) (d + 1) S
        = polyBound (2 * C + 2) (d + 1) S := by
      simp only [polyBound]; ring
    simp only [cost, eval, Ty.size_list, hlenmap]
    omega
  | boolNot =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    simp only [cost, polyBound, pow_one, Ty.size_bool]
    omega
  | boolAnd =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    simp only [cost, polyBound, pow_one, Ty.size_bool, Ty.size_pair]
    omega
  | boolOr =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    simp only [cost, polyBound, pow_one, Ty.size_bool, Ty.size_pair]
    omega
  | natEq =>
    refine ⟨3, 1, fun x ↦ ?_⟩
    obtain ⟨a, b⟩ := x
    exact natLe_case a b
  | @listSingle τ =>
    refine ⟨3, 1, fun a ↦ ?_⟩
    simp only [cost, eval, Ty.size_list, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil, polyBound, pow_one]
    omega
  | @listAppend τ =>
    refine ⟨2, 1, fun x ↦ ?_⟩
    obtain ⟨l₁, l₂⟩ := x
    simp only [cost, eval, Ty.size_pair, Ty.size_list, List.map_append, List.sum_append,
      List.length_append, polyBound, pow_one]
    omega
  | @listJoin τ =>
    refine ⟨3, 1, fun L ↦ ?_⟩
    have hA : (L.map (fun s ↦ s.length + 1)).sum
        ≤ (L.map (fun l ↦ (l.map (τ.size ·)).sum + l.length + 1)).sum :=
      List.sum_le_sum fun l _ ↦ by omega
    have hB : (L.flatten.map (τ.size ·)).sum
        ≤ (L.map (fun l ↦ (l.map (τ.size ·)).sum + l.length + 1)).sum := by
      rw [List.map_flatten, List.sum_flatten, List.map_map]
      exact List.sum_le_sum fun l _ ↦ by simp only [Function.comp_apply]; omega
    have hC : L.flatten.length
        ≤ (L.map (fun l ↦ (l.map (τ.size ·)).sum + l.length + 1)).sum := by
      rw [List.length_flatten]
      exact List.sum_le_sum fun l _ ↦ by omega
    simp only [cost, eval, Ty.size_list, polyBound, pow_one]
    omega
  | @listFilter σ p ihp =>
    obtain ⟨C, d, h⟩ := ihp
    refine ⟨C + 2, d + 1, fun l ↦ ?_⟩
    set S := Ty.size (.list σ) l with hS
    have hlen : l.length ≤ S := by rw [hS, Ty.size_list]; omega
    have helem : ∀ a ∈ l, cost p a ≤ polyBound C d S := fun a ha ↦
      le_trans (Nat.le_add_right _ _)
        ((h a).trans (polyBound_mono le_rfl le_rfl (Ty.size_elem_le ha)))
    have hcost : (l.map (fun a ↦ cost p a + 1)).sum
        ≤ l.length * polyBound C d S + l.length := by
      have hb := list_sum_le_length_mul (l.map (fun a ↦ cost p a + 1)) (polyBound C d S + 1)
        (by
          intro x hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          have := helem a ha
          omega)
      simp only [List.length_map] at hb
      have hexp : l.length * (polyBound C d S + 1) = l.length * polyBound C d S + l.length := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    have hout : Ty.size (.list σ) (l.filter (fun a ↦ eval p a)) ≤ S := by
      rw [hS]
      simp only [Ty.size_list]
      have hsub : List.Sublist ((l.filter (fun a ↦ eval p a)).map (σ.size ·))
          (l.map (σ.size ·)) :=
        List.filter_sublist.map _
      have h1 : ((l.filter (fun a ↦ eval p a)).map (σ.size ·)).sum
          ≤ (l.map (σ.size ·)).sum :=
        hsub.sum_le_sum fun a _ ↦ Nat.zero_le a
      have h2 : (l.filter (fun a ↦ eval p a)).length ≤ l.length :=
        List.length_filter_le _ _
      omega
    have hpb : l.length * polyBound C d S ≤ polyBound C d S * S := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hlen
    have hstep : polyBound C d S * S + 2 * S + 2 ≤ polyBound (C + 2) (d + 1) S := by
      have h1 : 1 ≤ (S + 1) ^ d := Nat.one_le_pow _ _ (by omega)
      simp only [polyBound, pow_succ]
      nlinarith [h1]
    simp only [cost, eval]
    omega
  | @listMapEnv ρ σ τ f ih =>
    obtain ⟨C, d, h⟩ := ih
    refine ⟨2 * C + 2, d + 1, fun x ↦ ?_⟩
    obtain ⟨e, l⟩ := x
    set S := Ty.size (.pair ρ (.list σ)) (e, l) with hS
    have hSl : Ty.size (.list σ) l ≤ S := by
      rw [hS]
      simp only [Ty.size_pair]
      omega
    have hlen : l.length ≤ S := by
      have hl : l.length ≤ Ty.size (.list σ) l := by rw [Ty.size_list]; omega
      omega
    have helem : ∀ a ∈ l, cost f (e, a) + τ.size (eval f (e, a)) ≤ polyBound C d S := by
      intro a ha
      refine (h (e, a)).trans (polyBound_mono le_rfl le_rfl ?_)
      have h1 : σ.size a ≤ Ty.size (.list σ) l := Ty.size_elem_le ha
      rw [hS]
      simp only [Ty.size_pair]
      omega
    have hcost : (l.map (fun a ↦ cost f (e, a) + 1)).sum
        ≤ l.length * polyBound C d S + l.length := by
      have hb := list_sum_le_length_mul (l.map (fun a ↦ cost f (e, a) + 1))
        (polyBound C d S + 1)
        (by
          intro x hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          have := helem a ha
          omega)
      simp only [List.length_map] at hb
      have hexp : l.length * (polyBound C d S + 1) = l.length * polyBound C d S + l.length := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
    have hout : ((l.map (fun a ↦ eval f (e, a))).map (τ.size ·)).sum
        ≤ l.length * polyBound C d S := by
      have hb := list_sum_le_length_mul ((l.map (fun a ↦ eval f (e, a))).map (τ.size ·))
        (polyBound C d S)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
          have := helem a ha
          omega)
      simp only [List.length_map] at hb
      exact hb
    have hlenmap : (l.map (fun a ↦ eval f (e, a))).length = l.length := by simp
    have hpb : l.length * polyBound C d S ≤ polyBound C d S * S := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hlen
    have hstep : polyBound C d S * S + S + 1 ≤ polyBound (C + 1) (d + 1) S := by
      have h1 : 1 ≤ (S + 1) ^ d := Nat.one_le_pow _ _ (by omega)
      simp only [polyBound, pow_succ]
      nlinarith [h1]
    have hfinal : polyBound (C + 1) (d + 1) S + polyBound (C + 1) (d + 1) S
        = polyBound (2 * C + 2) (d + 1) S := by
      simp only [polyBound]; ring
    simp only [cost, eval, Ty.size_list, hlenmap]
    omega
  | @listEnum τ =>
    refine ⟨5, 2, fun l ↦ ?_⟩
    set S := Ty.size (.list τ) l with hS
    have hlen : l.length ≤ S := by rw [hS, Ty.size_list]; omega
    have helem : ∀ x ∈ l.zipIdx, Ty.size (.pair τ .nat) x ≤ 2 * S + 2 := by
      intro x hx
      obtain ⟨hmem, hidx⟩ := mem_zipIdx_bounds hx
      obtain ⟨a, i⟩ := x
      have h1 : τ.size a ≤ S := by rw [hS]; exact Ty.size_elem_le hmem
      have h2 : i.size ≤ i + 1 := size_le_succ_self i
      have hidx' : i < l.length := hidx
      simp only [Ty.size_pair, Ty.size_nat]
      omega
    have hsum : (l.zipIdx.map (Ty.size (.pair τ .nat) ·)).sum ≤ l.length * (2 * S + 2) := by
      have hb := list_sum_le_length_mul (l.zipIdx.map (Ty.size (.pair τ .nat) ·)) (2 * S + 2)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact helem y hy)
      simpa only [List.length_map, List.length_zipIdx] using hb
    have hY : S + 1 ≤ (S + 1) * (S + 1) := by nlinarith
    have hc1 : (l.length + 1) * (l.length + 1) ≤ (S + 1) * (S + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hc2 : l.length * (2 * S + 2) ≤ 2 * ((S + 1) * (S + 1)) := by nlinarith [hlen]
    have hpow : polyBound 5 2 S = 5 * ((S + 1) * (S + 1)) := by
      simp only [polyBound]; ring
    simp only [cost, eval, Ty.size_list, List.length_zipIdx]
    omega
  | listSum =>
    refine ⟨2, 1, fun l ↦ ?_⟩
    have h : (List.sum l).size ≤ (l.map fun n ↦ n.size + 1).sum := sum_size_le l
    simp only [cost, eval, polyBound, pow_one, Ty.size_list, Ty.size_nat]
    omega
  | @natPowLen τ =>
    refine ⟨3, 4, fun x ↦ ?_⟩
    obtain ⟨b, l⟩ := x
    exact natPowLen_case b l.length ((l.map (τ.size ·)).sum)

/-! ### Derived combinators

Combinations of the primitives need no new cost cases: their bounds follow
from composition. -/

/-- Cartesian product of two lists, derived from `listMapEnv` and `listJoin`:
`(l₁, l₂) ↦ [(a, b) | a ∈ l₁, b ∈ l₂]`. -/
def cross : Code (.pair (.list σ) (.list τ)) (.list (.pair σ τ)) :=
  .comp (.pair .snd .fst)
    (.comp (.listMapEnv (.comp (.pair .snd .fst) (.listMapEnv .id))) .listJoin)

/-- Exchange the components of a pair. The program that turns a symmetric
relation given by one orientation of each pair into both — a graph's edge list
into a digraph's arc list, say. -/
def swap : Code (.pair σ τ) (.pair τ σ) := .pair .snd .fst

/-- Inequality test on binary naturals. -/
def natNe : Code (.pair .nat .nat) .bool := .comp .natEq .boolNot

/-- Strict order test on binary naturals. -/
def natLt : Code (.pair .nat .nat) .bool :=
  .comp (.comp (.pair .snd .fst) .natLe) .boolNot

/-- Mathlib's pairing bijection `Nat.pair` as a program:
`(a, b) ↦ if a < b then b * b + a else a * a + a + b`.

This is the naming device for gadget constructions in the concrete layer.
Fresh names in the mathematical layer are *tagged tuples* of input objects
(`Sum.inr (i, k)` and the like); a concrete instance has only `ℕ` labels, so
the tags have to be realized as numbers, and an injective pairing is what
makes that realization faithful. Squaring costs one doubling of bit length,
which is why the labels stay honest under the size discipline. -/
def natPair : Code (.pair .nat .nat) .nat :=
  .branch natLt
    (.comp (.pair (.comp (.pair .snd .snd) .natMul) .fst) .natAdd)
    (.comp (.pair (.comp (.pair (.comp (.pair .fst .fst) .natMul) .fst) .natAdd) .snd)
      .natAdd)

/-- Componentwise equality test on pairs of binary naturals (index pairs). -/
def natPairEq : Code (.pair (.pair .nat .nat) (.pair .nat .nat)) .bool :=
  .comp (.pair (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) .natEq)
               (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq)) .boolAnd

/-- Boolean inequality (exclusive or). -/
def boolNe : Code (.pair .bool .bool) .bool :=
  .comp (.pair (.comp (.pair .fst (.comp .snd .boolNot)) .boolAnd)
               (.comp (.pair (.comp .fst .boolNot) .snd) .boolAnd)) .boolOr

/-- Cons: prepend the result of one program to a computed list, derived from
`listSingle` and `listAppend`. -/
def cons (a : Code σ τ) (l : Code σ (.list τ)) : Code σ (.list τ) :=
  .comp (.pair (.comp a .listSingle) l) .listAppend

/-- Applied addition: `natAdd` fed by two computed summands. Point-free index
arithmetic is unreadable without the applied forms. -/
def add (a b : Code σ .nat) : Code σ .nat := .comp (.pair a b) .natAdd

/-- Applied multiplication. -/
def mul (a b : Code σ .nat) : Code σ .nat := .comp (.pair a b) .natMul

/-- Applied strict comparison. -/
def lt (a b : Code σ .nat) : Code σ .bool := .comp (.pair a b) Code.natLt

/-- Applied conjunction. -/
def and (a b : Code σ .bool) : Code σ .bool := .comp (.pair a b) .boolAnd

/-- Applied concatenation. -/
def append (l₁ l₂ : Code σ (.list τ)) : Code σ (.list τ) :=
  .comp (.pair l₁ l₂) .listAppend

/-- The positions of a list, as a list of binary naturals: `l ↦ [0, 1, …]`.
The language has no `range` primitive — positions are read off the
enumeration, which is the only thing that can produce them. -/
def indices : Code (.list τ) (.list .nat) := .comp .listEnum (.listMap .snd)

/-- Emptiness of a computed list. The shape every branch condition of the form
"nothing violates the test" takes: filter out the offenders, then ask whether
any survived. -/
def isNil {σ τ : Ty} (l : Code σ (.list τ)) : Code σ .bool :=
  .comp (.pair (.comp l .listLen) (.const .nat 0)) .natEq

/-- **Filter-then-map with an environment in scope.** `listFilter`'s predicate
cannot see the environment, so every annex that filters against a computed
quantity has had to hand-roll the `listMapEnv`-of-`branch`-then-`listJoin`
idiom. This is that idiom, once: elements failing `test` emit `[]`, survivors
emit `[f a]`, and the flattening concatenates. -/
def filterMapEnv {ε τ τ' : Ty} (test : Code (.pair ε τ) .bool)
    (f : Code (.pair ε τ) τ') : Code (.pair ε (.list τ)) (.list τ') :=
  .comp (.listMapEnv (.branch test (.comp f .listSingle) (.const (.list τ') [])))
    .listJoin

/-- Filtering with an environment in scope, the survivors passed through
unchanged. -/
def filterEnv {ε τ : Ty} (test : Code (.pair ε τ) .bool) :
    Code (.pair ε (.list τ)) (.list τ) :=
  filterMapEnv test .snd

/-- The strict-prefix test: with an index `j` riding in the environment, an
enumerated element `(a, i)` survives exactly when `i < j`. -/
def prefixTest : Code (.pair .nat (.pair τ .nat)) .bool :=
  .comp (.comp (.pair .fst (.comp .snd .snd)) .natLe) .boolNot

/-- Tag each element of a list with its base-`b` place value:
`(b, l) ↦ [(a₀, b ^ 0), (a₁, b ^ 1), …]`.

Derived rather than primitive, and the derivation is the whole point of
`natPowLen`'s interface: an exponent may only be read off a list, so a program
wanting `b ^ j` must *exhibit* a list of length `j`. The list exhibited here is
the prefix of the enumerated input strictly before position `j` — so the
geometric progression is built without ever exponentiating a number. -/
def powEnum : Code (.pair .nat (.list τ)) (.list (.pair τ .nat)) :=
  .comp (.pair (.pair .fst (.comp .snd .listEnum)) (.comp .snd .listEnum))
    (.listMapEnv
      (.pair (.comp .snd .fst)
        (.comp (.pair (.comp .fst .fst)
                      (.comp (.pair (.comp .snd .snd) (.comp .fst .snd))
                        (filterEnv prefixTest)))
          .natPowLen)))

/-- Keep-at-position test: with an index `k` in the environment, an enumerated
element `(a, i)` survives exactly when `i = k`. -/
def nthTest : Code (.pair .nat (.pair τ .nat)) .bool :=
  .comp (.pair (.comp .snd .snd) .fst) .natEq

/-- The element of a list at a position, as a one-element list — empty when
the position is out of range. The language has no indexing primitive: the
enumeration is filtered down to the wanted position instead. -/
def listNth : Code (.pair (.list τ) .nat) (.list τ) :=
  .comp (.pair .snd (.comp .fst .listEnum))
    (.comp (filterEnv nthTest) (.listMap .fst))

/-- The later-equal test behind `dedupBy`: with the reference element `(a, p)`
in the environment, an enumerated element `(b, i)` survives when it sits
strictly later (`p < i`) and `eq` judges `b` equal to `a`. -/
def laterEqTest (eq : Code (.pair τ τ) .bool) :
    Code (.pair (.pair τ .nat) (.pair τ .nat)) .bool :=
  .comp (.pair (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) natLt)
               (.comp (.pair (.comp .snd .fst) (.comp .fst .fst)) eq))
    .boolAnd

/-- Deduplication by an equality test, keeping *last* occurrences — exactly
mathlib's `List.dedup` (`dedupBy_eval`). Keep-or-drop over the enumeration: a
position survives iff no later position holds an equal value. The language has
no type-generic equality, so the test is a parameter (`natEq` for labels). -/
def dedupBy (eq : Code (.pair τ τ) .bool) : Code (.list τ) (.list τ) :=
  .comp (.pair .listEnum .listEnum)
    (filterMapEnv
      (.comp (.pair (.comp (.comp (.pair .snd .fst) (filterEnv (laterEqTest eq))) .listLen)
               (.const .nat 0)) .natEq)
      (.comp .snd .fst))

example : boolNe.eval (true, false) = true := by rfl
example : boolNe.eval (true, true) = false := by rfl

example : (listNth (τ := .nat)).eval ([4, 5, 6], 1) = [5] := by rfl
example : (listNth (τ := .nat)).eval ([4, 5, 6], 7) = [] := by rfl

example : (dedupBy .natEq).eval [1, 2, 1, 3, 2] = [1, 3, 2] := by rfl
example : (dedupBy .natEq).eval [] = [] := by rfl

example : (cross (σ := .nat) (τ := .bool)).eval ([1, 2], [true, false]) =
    [(1, true), (1, false), (2, true), (2, false)] := by rfl

example : (cons (σ := .pair (.list .nat) .nat) .snd .fst).eval ([2, 3], 1) = [1, 2, 3] := by
  rfl

example : (powEnum (τ := .nat)).eval (4, [7, 8, 9]) = [(7, 1), (8, 4), (9, 16)] := by rfl

example : (indices (τ := .nat)).eval [7, 8, 9] = [0, 1, 2] := by rfl

example : natPair.eval (2, 5) = 27 := by rfl
example : natPair.eval (5, 2) = 32 := by rfl

end Code

/-- Resolving a `branch` whose condition is known true. -/
theorem branch_eval_true {σ τ : Ty} {b : Code σ .bool} (f g : Code σ τ)
    {x : σ.denote} (h : b.eval x = true) :
    (Code.branch b f g).eval x = f.eval x := by
  have he : (Code.branch b f g).eval x
      = if b.eval x = true then f.eval x else g.eval x := rfl
  rw [he, if_pos h]

/-- `Code.isNil` decides emptiness. -/
theorem isNil_eval_true {σ τ : Ty} (l : Code σ (.list τ)) (x : σ.denote) :
    (Code.isNil l).eval x = true ↔ l.eval x = [] := by
  have h : (Code.isNil l).eval x = decide ((l.eval x).length = 0) := rfl
  rw [h, decide_eq_true_iff, List.length_eq_zero_iff]

/-- Resolving a `branch` whose condition is known false. -/
theorem branch_eval_false {σ τ : Ty} {b : Code σ .bool} (f g : Code σ τ)
    {x : σ.denote} (h : b.eval x = false) :
    (Code.branch b f g).eval x = g.eval x := by
  have he : (Code.branch b f g).eval x
      = if b.eval x = true then f.eval x else g.eval x := rfl
  rw [he, if_neg (by rw [h]; exact Bool.false_ne_true)]

/-! ### The filter-with-environment idiom

`listFilter`'s predicate cannot see the environment, so environment-dependent
filtering goes through `listMapEnv` + `listJoin`: map a `branch` emitting `[a]`
or `[]`, then flatten. These lemmas identify that idiom with `List.filter`;
the specifications below and the certificate annexes lean on them. -/

/-- The keep-or-drop idiom computes a filter, and the kept elements may be
transformed on the way out: mapping a `branch` that emits `[f a]` or `[]` and
flattening is exactly filter-then-map. -/
theorem flatten_map_ite_eq_map_filter {α β : Type*} (l : List α) (p : α → Bool)
    (f : α → β) :
    (l.map fun a ↦ if p a = true then [f a] else []).flatten = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatten_cons, ih, List.filter_cons]
    by_cases h : p a = true
    · rw [if_pos h, if_pos h, List.map_cons, List.cons_append, List.nil_append]
    · rw [if_neg h, if_neg h, List.nil_append]

/-- The keep-or-drop idiom computes a filter: mapping a `branch` that emits
`[a]` or `[]` and flattening is exactly `List.filter`. -/
theorem flatten_map_ite_eq_filter {α : Type*} (l : List α) (p : α → Bool) :
    (l.map fun a ↦ if p a = true then [a] else []).flatten = l.filter p := by
  have h := flatten_map_ite_eq_map_filter l p id
  rwa [List.map_id] at h

/-! ### Specifications of the derived combinators -/

/-- `Code.boolNe` decides boolean inequality. -/
theorem boolNe_eval_true (a b : Bool) : Code.boolNe.eval (a, b) = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp [Code.boolNe, Code.eval]

/-- Membership in the derived Cartesian-product combinator `Code.cross`. -/
theorem mem_cross_eval {σ τ : Ty} (l₁ : List σ.denote) (l₂ : List τ.denote)
    (q : (Ty.pair σ τ).denote) :
    q ∈ (Code.cross (σ := σ) (τ := τ)).eval (l₁, l₂) ↔ q.1 ∈ l₁ ∧ q.2 ∈ l₂ := by
  have h : (Code.cross (σ := σ) (τ := τ)).eval (l₁, l₂) =
      (l₁.map fun a ↦ l₂.map fun b ↦ (a, b)).flatten := rfl
  rw [h, List.mem_flatten]
  constructor
  · rintro ⟨L, hL, hq⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hL
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
    exact ⟨ha, hb⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨l₂.map fun b ↦ (q.1, b), List.mem_map_of_mem h₁,
      List.mem_map_of_mem h₂⟩

/-- `Code.add` adds. -/
theorem add_eval {σ : Ty} (a b : Code σ .nat) (x : σ.denote) :
    (Code.add a b).eval x = a.eval x + b.eval x := rfl

/-- `Code.mul` multiplies. -/
theorem mul_eval {σ : Ty} (a b : Code σ .nat) (x : σ.denote) :
    (Code.mul a b).eval x = a.eval x * b.eval x := rfl

/-- `Code.indices` lists the positions of its input. -/
theorem indices_eval {τ : Ty} (l : List τ.denote) :
    (Code.indices (τ := τ)).eval l = List.range l.length := by
  have h : (Code.indices (τ := τ)).eval l = l.zipIdx.map Prod.snd := rfl
  rw [h, List.zipIdx_map_snd, ← List.range_eq_range']

/-- The length of a Cartesian product is the product of the lengths — which is
how a certificate builds an element list of a *prescribed* size out of the
lists it already has. -/
theorem length_cross_eval {σ τ : Ty} (l₁ : List σ.denote) (l₂ : List τ.denote) :
    ((Code.cross (σ := σ) (τ := τ)).eval (l₁, l₂)).length = l₁.length * l₂.length := by
  have h : (Code.cross (σ := σ) (τ := τ)).eval (l₁, l₂) =
      (l₁.map fun a ↦ l₂.map fun b ↦ (a, b)).flatten := rfl
  have hmap : (l₁.map (List.length ∘ fun a ↦ l₂.map fun b ↦ (a, b)))
      = l₁.map fun _ ↦ l₂.length :=
    List.map_congr_left fun a _ ↦ by simp
  rw [h, List.length_flatten, List.map_map, hmap, List.map_const', List.sum_replicate,
    smul_eq_mul]

/-- `Code.natPairEq` decides equality of index pairs. -/
theorem natPairEq_eval_true (p q : ℕ × ℕ) :
    Code.natPairEq.eval (p, q) = true ↔ p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  have h : Code.natPairEq.eval ((a, b), (c, d)) =
      (decide (a = c) && decide (b = d)) := rfl
  rw [h, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, Prod.mk.injEq]

/-- `Code.natLt` decides the strict order. -/
theorem natLt_eval_true (a b : ℕ) : Code.natLt.eval (a, b) = true ↔ a < b := by
  have h : Code.natLt.eval (a, b) = !decide (b ≤ a) := rfl
  rw [h, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]

/-- `Code.natLt`, as a `decide`. -/
theorem natLt_eval (a b : ℕ) : Code.natLt.eval (a, b) = decide (a < b) := by
  have h : Code.natLt.eval (a, b) = !decide (b ≤ a) := rfl
  rw [h, ← decide_not, decide_eq_decide]
  exact Nat.not_le

/-- `Code.lt` decides the strict order on its two computed arguments. -/
theorem lt_eval_true {σ : Ty} (a b : Code σ .nat) (x : σ.denote) :
    (Code.lt a b).eval x = true ↔ a.eval x < b.eval x :=
  natLt_eval_true _ _

/-- `Code.and` decides the conjunction of its two computed arguments. -/
theorem and_eval_true {σ : Ty} (a b : Code σ .bool) (x : σ.denote) :
    (Code.and a b).eval x = true ↔ a.eval x = true ∧ b.eval x = true := by
  have h : (Code.and a b).eval x = (a.eval x && b.eval x) := rfl
  rw [h, Bool.and_eq_true]

/-- `Code.swap` exchanges the components. -/
theorem swap_eval {σ τ : Ty} (x : (Ty.pair σ τ).denote) :
    (Code.swap (σ := σ) (τ := τ)).eval x = (x.2, x.1) := rfl

/-- `Code.append` concatenates. -/
theorem append_eval {σ τ : Ty} (l₁ l₂ : Code σ (.list τ)) (x : σ.denote) :
    (Code.append l₁ l₂).eval x = l₁.eval x ++ l₂.eval x := rfl

/-- `Code.filterMapEnv` filters against `test` and maps the survivors through
`f`, both with the environment in scope. -/
theorem filterMapEnv_eval {ε τ τ' : Ty} (test : Code (.pair ε τ) .bool)
    (f : Code (.pair ε τ) τ') (e : ε.denote) (l : List τ.denote) :
    (Code.filterMapEnv test f).eval (e, l)
      = (l.filter fun a ↦ test.eval (e, a)).map fun a ↦ f.eval (e, a) := by
  have h : (Code.filterMapEnv test f).eval (e, l) =
      (l.map fun a ↦ if test.eval (e, a) = true then [f.eval (e, a)] else []).flatten :=
    rfl
  rw [h, flatten_map_ite_eq_map_filter]

/-- Membership in a `filterMapEnv`: the images of the elements that pass. -/
theorem mem_filterMapEnv_eval {ε τ τ' : Ty} (test : Code (.pair ε τ) .bool)
    (f : Code (.pair ε τ) τ') (e : ε.denote) (l : List τ.denote) (y : τ'.denote) :
    y ∈ (Code.filterMapEnv test f).eval (e, l) ↔
      ∃ a ∈ l, test.eval (e, a) = true ∧ f.eval (e, a) = y := by
  rw [filterMapEnv_eval, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha, ht⟩ := List.mem_filter.mp ha
    exact ⟨a, ha, ht, rfl⟩
  · rintro ⟨a, ha, ht, rfl⟩
    exact ⟨a, List.mem_filter.mpr ⟨ha, ht⟩, rfl⟩

/-- `Code.filterEnv` filters, with the environment in scope. -/
theorem filterEnv_eval {ε τ : Ty} (test : Code (.pair ε τ) .bool)
    (e : ε.denote) (l : List τ.denote) :
    (Code.filterEnv test).eval (e, l) = l.filter fun a ↦ test.eval (e, a) := by
  rw [Code.filterEnv, filterMapEnv_eval]
  exact List.map_id _

/-- `Code.natPair` computes mathlib's pairing bijection — in particular it is
injective, which is what fresh-name constructions need. -/
theorem natPair_eval (a b : ℕ) : Code.natPair.eval (a, b) = Nat.pair a b := by
  have h : Code.natPair.eval (a, b) =
      if Code.natLt.eval (a, b) = true then b * b + a else a * a + a + b := rfl
  rw [h, Nat.pair]
  by_cases hab : a < b
  · rw [if_pos ((natLt_eval_true a b).mpr hab), if_pos hab]
  · rw [if_neg (fun hc ↦ hab ((natLt_eval_true a b).mp hc)), if_neg hab]

/-- `Code.prefixTest` decides the strict-prefix condition. -/
theorem prefixTest_eval {τ : Ty} (j : ℕ) (q : Ty.denote (.pair τ .nat)) :
    (Code.prefixTest (τ := τ)).eval (j, q) = decide (q.2 < j) := by
  have h : (Code.prefixTest (τ := τ)).eval (j, q) = !decide (j ≤ q.2) := rfl
  rw [h, ← decide_not, decide_eq_decide]
  exact Nat.not_le

/-- The prefix filter behind `Code.powEnum`: the elements of an enumerated list
whose index is below `j`. -/
theorem prefixTest_filterEnv_eval {τ : Ty} (j : ℕ) (L : List (Ty.denote (.pair τ .nat))) :
    (Code.filterEnv (Code.prefixTest (τ := τ))).eval (j, L) = L.filter fun q ↦ q.2 < j := by
  rw [filterEnv_eval]
  exact congrArg (fun p ↦ List.filter p L) (funext fun q ↦ prefixTest_eval j q)

/-- Counting the entries of `range m` below `j`. -/
theorem countP_range_lt (j : ℕ) : ∀ m : ℕ, ((List.range m).countP fun i ↦ i < j) = min j m
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_lt j m]
    by_cases h : m < j <;> simp [h] <;> omega

/-- The prefix of an enumerated list strictly before position `j` has length
`j` — this is what lets `Code.powEnum` feed the exponent `j` to `natPowLen` as
a list length. -/
theorem length_filter_zipIdx_lt {α : Type*} (l : List α) (j : ℕ) :
    ((l.zipIdx.filter fun q ↦ q.2 < j).length) = min j l.length := by
  rw [← List.countP_eq_length_filter]
  have h : (l.zipIdx.countP fun q ↦ q.2 < j)
      = (l.zipIdx.map Prod.snd).countP fun i ↦ i < j := by
    rw [List.countP_map]; rfl
  rw [h, List.zipIdx_map_snd, ← List.range_eq_range', countP_range_lt]

/-- `Code.listNth` reads the element at an in-range position. -/
theorem listNth_eval {τ : Ty} {l : List τ.denote} {k : ℕ} (h : k < l.length) :
    (Code.listNth (τ := τ)).eval (l, k) = [l[k]] := by
  have h1 : (Code.listNth (τ := τ)).eval (l, k) =
      ((l.zipIdx.map fun q ↦ if decide (q.2 = k) = true then [q] else []).flatten).map
        Prod.fst := rfl
  rw [h1, flatten_map_ite_eq_filter, filter_zipIdx_eq_singleton h, List.map_cons,
    List.map_nil]

/-- `Code.listNth` reads *nothing* at an out-of-range position. The companion
of `listNth_eval`, and what makes the combinator a total `getElem?`: appending
a default to the result and reading position `0` of that is the language's
`getD`, which is how a program pads a short list (precedent: `padLit`, the
padding of a clause to three literals in `Nae3Sat/FromSat3/Code.lean`). -/
theorem listNth_eval_of_le {τ : Ty} {l : List τ.denote} {k : ℕ} (h : l.length ≤ k) :
    (Code.listNth (τ := τ)).eval (l, k) = [] := by
  have h1 : (Code.listNth (τ := τ)).eval (l, k) =
      ((l.zipIdx.map fun q ↦ if decide (q.2 = k) = true then [q] else []).flatten).map
        Prod.fst := rfl
  have hnil : (l.zipIdx.filter fun q ↦ decide (q.2 = k)) = [] :=
    List.filter_eq_nil_iff.mpr fun q hq hd ↦ by
      have hb := (mem_zipIdx_bounds hq).2
      have hk : q.2 = k := of_decide_eq_true hd
      omega
  rw [h1, flatten_map_ite_eq_filter, hnil, List.map_nil]

/-- `Code.dedupBy` computes mathlib's `List.dedup` whenever its parameter
computes equality (as `natEq` does, by `rfl`). -/
theorem dedupBy_eval {τ : Ty} [DecidableEq τ.denote] {eq : Code (.pair τ τ) .bool}
    (heq : ∀ a b : τ.denote, eq.eval (a, b) = decide (a = b)) (l : List τ.denote) :
    (Code.dedupBy eq).eval l = l.dedup := by
  have h1 : (Code.dedupBy eq).eval l =
      (l.zipIdx.map fun q ↦
        if decide (((l.zipIdx.map fun r ↦
              if (!decide (r.2 ≤ q.2) && eq.eval (r.1, q.1)) = true
              then [r] else []).flatten).length = 0) = true
        then [q.1] else []).flatten := rfl
  rw [h1, flatten_map_ite_eq_map_filter]
  have hcond : ∀ q ∈ l.zipIdx,
      (decide (((l.zipIdx.map fun r ↦
            if (!decide (r.2 ≤ q.2) && eq.eval (r.1, q.1)) = true
            then [r] else []).flatten).length = 0))
        = l.zipIdx.all fun r ↦ !(decide (q.2 < r.2) && decide (r.1 = q.1)) := by
    intro q _
    rw [flatten_map_ite_eq_filter]
    refine Bool.eq_iff_iff.mpr ?_
    rw [decide_eq_true_iff, List.length_eq_zero_iff, List.filter_eq_nil_iff,
      List.all_eq_true]
    constructor
    · intro h r hr
      have hh := h r hr
      by_cases hle : r.2 ≤ q.2
      · rw [decide_eq_false (Nat.not_lt.mpr hle), Bool.false_and, Bool.not_false]
      · rw [decide_eq_false hle, Bool.not_false, Bool.true_and, heq] at hh
        rw [Bool.eq_false_iff.mpr hh, Bool.and_false, Bool.not_false]
    · intro h r hr
      have hh := h r hr
      intro hc
      rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le, heq] at hc
      rw [decide_eq_true hc.1, Bool.true_and, Bool.not_eq_true'] at hh
      exact Bool.false_ne_true (hh ▸ hc.2)
  rw [List.filter_congr hcond]
  exact filter_zipIdx_lastOcc_map_fst_eq_dedup l

/-- `Code.powEnum` tags each element with its base-`b` place value. -/
theorem powEnum_eval {τ : Ty} (b : ℕ) (l : List τ.denote) :
    (Code.powEnum (τ := τ)).eval (b, l) = l.zipIdx.map fun p ↦ (p.1, b ^ p.2) := by
  have h : (Code.powEnum (τ := τ)).eval (b, l) =
      l.zipIdx.map fun p ↦ (p.1, b ^
        ((Code.filterEnv (Code.prefixTest (τ := τ))).eval (p.2, l.zipIdx)).length) := rfl
  rw [h]
  refine List.map_congr_left fun p hp ↦ ?_
  rw [prefixTest_filterEnv_eval, length_filter_zipIdx_lt,
    Nat.min_eq_left (le_of_lt (mem_zipIdx_bounds hp).2)]

end Cert
end Hardness


