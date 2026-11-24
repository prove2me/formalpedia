-- Prove2me | Definitions.Def_CSL_Shared_Memory_Address
-- name    : CSL_Shared_Memory_Address
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:39.300948+00:00
-- url     : https://prove2.me/theorems/a844a9d2-6575-4519-82f9-c3b8efd17535
-- title:
--   Coded sorting library: Shared / Memory / Address
-- statement:
--   Module `CodedSorting.Shared.Memory.Address` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Address algebra. This file proves identities on addresses and on streams whose positions are changed by the corresponding address maps.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.Address

import Definitions.Def_CSL_Compat
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic

/-! Address algebra. This file proves identities on addresses and on streams whose positions are changed by the corresponding address maps. 






-/

namespace CSL.Address

/-- The five address fields in Section 5.1.  `high` and `low` have the
same type; all other fields must remain unchanged by the exchange. -/
structure FullAddress (Prefix Field Gap Suffix : Type*) where
  prefixCoord : Prefix
  high : Field
  gap : Gap
  low : Field
  suffix : Suffix
  deriving DecidableEq

variable {Prefix Field Gap Suffix : Type*}

/-- A destination address, not an operation on the data value. -/
def exchange (a : FullAddress Prefix Field Gap Suffix) :
    FullAddress Prefix Field Gap Suffix :=
  ⟨a.prefixCoord, a.low, a.gap, a.high, a.suffix⟩

theorem exchange_twice (a : FullAddress Prefix Field Gap Suffix) :
    exchange (exchange a) = a := by
  cases a
  rfl

theorem exchange_preserves_other_fields
    (a : FullAddress Prefix Field Gap Suffix) :
    (exchange a).prefixCoord = a.prefixCoord ∧ (exchange a).gap = a.gap ∧
      (exchange a).suffix = a.suffix := ⟨rfl, rfl, rfl⟩

/-- The whole-record suffix is untouched: individual bits of a record
have the same destination record and retain their within-record offsets. -/
theorem exchange_record (p : Prefix) (h d : Field) (g : Gap) (z : Suffix) :
    exchange (FullAddress.mk p h g d z) = FullAddress.mk p d g h z := rfl

def exchangeEquiv : FullAddress Prefix Field Gap Suffix ≃
    FullAddress Prefix Field Gap Suffix where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_twice
  right_inv := exchange_twice

/-- Lift a two-field permutation while keeping every spectator coordinate.
The spectator types need not be small or have cardinality one. -/
def mapPair (e : (Field × Field) ≃ (Field × Field))
    (a : FullAddress Prefix Field Gap Suffix) :
    FullAddress Prefix Field Gap Suffix :=
  ⟨a.prefixCoord, (e (a.high, a.low)).1, a.gap,
    (e (a.high, a.low)).2, a.suffix⟩

theorem mapPair_preserves_spectators (e : (Field × Field) ≃ (Field × Field))
    (a : FullAddress Prefix Field Gap Suffix) :
    (mapPair e a).prefixCoord = a.prefixCoord ∧ (mapPair e a).gap = a.gap ∧
      (mapPair e a).suffix = a.suffix := ⟨rfl, rfl, rfl⟩

theorem mapPair_inverse (e : (Field × Field) ≃ (Field × Field))
    (a : FullAddress Prefix Field Gap Suffix) :
    mapPair e.symm (mapPair e a) = a := by
  cases a
  simp [mapPair]

def mapPairEquiv (e : (Field × Field) ≃ (Field × Field)) :
    FullAddress Prefix Field Gap Suffix ≃ FullAddress Prefix Field Gap Suffix where
  toFun := mapPair e
  invFun := mapPair e.symm
  left_inv := mapPair_inverse e
  right_inv a := by
    simpa using mapPair_inverse e.symm a

/-- The valid, unpadded positions are invariant under field exchange.
Thus restricting after an exchange never deletes a valid input bit. -/
theorem exchange_valid_iff (bound : ℕ)
    (a : FullAddress Prefix ℕ Gap Suffix) :
    ((exchange a).high < bound ∧ (exchange a).low < bound) ↔
      (a.high < bound ∧ a.low < bound) := by
  simp [exchange, and_comm]

section FieldUpdates

variable {A : Type*} [AddCommGroup A]

def lowerSubtract (x : A × A) : A × A := (x.1, x.2 - x.1)
def upperAdd (x : A × A) : A × A := (x.1 + x.2, x.2)
def lowerReflect (x : A × A) : A × A := (x.1, x.1 - x.2)
def lowerAdd (x : A × A) : A × A := (x.1, x.2 + x.1)

/-- Figure 7(a).  Every operation uses the CURRENT two field values.
This is valid in particular in `ZMod (q ^ f)`; primality is not needed. -/
theorem three_updates_exchange (x : A × A) :
    lowerReflect (upperAdd (lowerSubtract x)) = (x.2, x.1) := by
  apply Prod.ext <;> dsimp [lowerReflect, upperAdd, lowerSubtract] <;> abel

/-- Figure 8: a short-field addition reduces algebraically to one swap.
The theorem does not assert that the other two operations cost a scan. -/
theorem short_addition_via_exchange (x : A × A) :
    lowerReflect (Prod.swap (lowerAdd x)) = upperAdd x := by
  apply Prod.ext <;> dsimp [lowerReflect, lowerAdd, upperAdd] <;> abel

/-- The first and last operations in Figure 7 leave the earlier field
unchanged.  Their physical scanning cost is a separate claim. -/
theorem outer_updates_fix_high (x : A × A) :
    (lowerSubtract x).1 = x.1 ∧ (lowerReflect x).1 = x.1 := ⟨rfl, rfl⟩

end FieldUpdates

section Reindexing

variable {Addr Value : Type*}

/-- Push data forward: the value at `a` moves to `e a`.  Therefore the
value seen at destination `b` is the old value at `e.symm b`. -/
def transport (e : Addr ≃ Addr) (F : Addr → Value) : Addr → Value :=
  fun b => F (e.symm b)

theorem transport_at_destination (e : Addr ≃ Addr) (F : Addr → Value)
    (a : Addr) : transport e F (e a) = F a := by
  simp [transport]

theorem transport_comp (e₁ e₂ : Addr ≃ Addr) (F : Addr → Value) :
    transport e₂ (transport e₁ F) = transport (e₁.trans e₂) F := rfl

theorem transport_inverse (e : Addr ≃ Addr) (F : Addr → Value) :
    transport e.symm (transport e F) = F := by
  funext a
  simp [transport]

/-- A common reindexing commutes with ANY pointwise two-input gate.
For the paper the operation is XOR, and `Value = Bool`. -/
theorem transport_pointwise (e : Addr ≃ Addr) (op : Value → Value → Value)
    (F G : Addr → Value) :
    transport e (fun a => op (F a) (G a)) =
      fun a => op (transport e F a) (transport e G a) := rfl

theorem transport_xor (e : Addr ≃ Addr) (F G : Addr → Bool) :
    transport e (fun a => Bool.xor (F a) (G a)) =
      fun a => Bool.xor (transport e F a) (transport e G a) := rfl

/-- Reindexing cannot discard information. -/
theorem transport_injective (e : Addr ≃ Addr) :
    Function.Injective (transport (Value := Value) e) := by
  intro F G h
  have h' := congrArg (transport e.symm) h
  simpa only [transport_inverse] using h'

end Reindexing

section Shears

variable {H D Value : Type*} [AddCommGroup H]

/-- Address shear `(h,d) ↦ (h + C d,d)`.  These identities hold even
for a general function `C`; matrices and linear maps are special cases. -/
def shear (C : D → H) : (H × D) ≃ (H × D) where
  toFun x := (x.1 + C x.2, x.2)
  invFun x := (x.1 - C x.2, x.2)
  left_inv x := by
    apply Prod.ext <;> simp
  right_inv x := by
    apply Prod.ext <;> simp

def phi (C : D → H) (F : H × D → Value) : H × D → Value :=
  transport (shear C) F

theorem phi_apply (C : D → H) (F : H × D → Value) (h : H) (d : D) :
    phi C F (h, d) = F (h - C d, d) := rfl

theorem phi_preserves_payload (C : D → H) (F : H × D → Value)
    (h : H) (d : D) : phi C F (h + C d, d) = F (h, d) := by
  simp [phi, transport, shear]

theorem phi_comp (C' C : D → H) (F : H × D → Value) :
    phi C' (phi C F) = phi (C' + C) F := by
  funext x
  change F (x.1 - C' x.2 - C x.2, x.2) =
    F (x.1 - (C' x.2 + C x.2), x.2)
  apply congrArg F
  apply Prod.ext
  · abel
  · rfl

theorem phi_zero (F : H × D → Value) : phi (0 : D → H) F = F := by
  funext x
  simp [phi, transport, shear]

theorem phi_neg_left (C : D → H) (F : H × D → Value) :
    phi (-C) (phi C F) = F := by
  rw [phi_comp, neg_add_cancel, phi_zero]

theorem phi_neg_right (C : D → H) (F : H × D → Value) :
    phi C (phi (-C) F) = F := by
  rw [phi_comp, add_neg_cancel, phi_zero]

theorem phi_pointwise (C : D → H) (op : Value → Value → Value)
    (F G : H × D → Value) :
    phi C (fun a => op (F a) (G a)) =
      fun a => op (phi C F a) (phi C G a) := rfl

/-- Execute a finite ordered list of address shears. -/
def applyShears : List (D → H) → (H × D → Value) → (H × D → Value)
  | [], F => F
  | C :: Cs, F => applyShears Cs (phi C F)

/-- Sequential coordinate additions realize the sum of their updates.
In particular this applies to the nonzero entries of a sparse `P`, once
its decomposition has been supplied; it does not prove their number. -/
theorem applyShears_sum (Cs : List (D → H)) (F : H × D → Value) :
    applyShears Cs F = phi Cs.sum F := by
  induction Cs generalizing F with
  | nil => simp [applyShears, phi_zero]
  | cons C Cs ih =>
    rw [applyShears, ih, phi_comp, List.sum_cons]
    rw [add_comm Cs.sum C]

/-- A local edge correction changes the source layout into the target
layout.  This is algebraic correctness, not a method for executing it. -/
theorem edge_layout_change (Mu Mv : D → H) (F : H × D → Value) :
    phi (Mv - Mu) (phi Mu F) = phi Mv F := by
  rw [phi_comp, sub_add_cancel]

/-- The conceptual logical input `phi (-Ms) F` describes the existing
physical input `F`: the equality itself requires no extra materialization. -/
theorem logical_input_description (Ms : D → H) (F : H × D → Value) :
    phi Ms (phi (-Ms) F) = F := phi_neg_right Ms F

theorem endpoint_difference (Ms Mt : D → H) (F : H × D → Value) :
    phi Mt (phi (-Ms) F) = phi (Mt - Ms) F := by
  rw [phi_comp, sub_eq_add_neg]

/-- Once a logical stream has been transmitted correctly, source/target
label difference `C` produces exactly address update `C`. -/
theorem endpoint_update (Ms Mt C : D → H) (hlabels : Mt - Ms = C)
    (F : H × D → Value) :
    phi Mt (phi (-Ms) F) = phi C F := by
  rw [endpoint_difference, hlabels]

/-- In the manuscript the endpoint matrix difference is the identity,
so the resulting address update is `(h,d) ↦ (h+d,d)`. -/
theorem endpoint_identity (Ms Mt : H → H)
    (hlabels : Mt - Ms = id) (F : H × H → Value) (h d : H) :
    phi Mt (phi (-Ms) F) (h + d, d) = F (h, d) := by
  rw [endpoint_update Ms Mt id hlabels]
  exact phi_preserves_payload id F h d

end Shears

section FullShears

variable {H Value : Type*} [AddCommGroup H]

/-- The shear on the complete five-field array.  The prefix, gap and
suffix remain part of the stream address throughout the computation. -/
def fullPhi (C : H → H) (F : FullAddress Prefix H Gap Suffix → Value) :
    FullAddress Prefix H Gap Suffix → Value :=
  transport (mapPairEquiv (shear C)) F

theorem fullPhi_apply (C : H → H)
    (F : FullAddress Prefix H Gap Suffix → Value)
    (p : Prefix) (h : H) (g : Gap) (d : H) (z : Suffix) :
    fullPhi C F ⟨p, h, g, d, z⟩ = F ⟨p, h - C d, g, d, z⟩ := rfl

theorem fullPhi_preserves_payload (C : H → H)
    (F : FullAddress Prefix H Gap Suffix → Value)
    (p : Prefix) (h : H) (g : Gap) (d : H) (z : Suffix) :
    fullPhi C F ⟨p, h + C d, g, d, z⟩ = F ⟨p, h, g, d, z⟩ := by
  rw [fullPhi_apply, add_sub_cancel_right]

theorem fullPhi_comp (C' C : H → H)
    (F : FullAddress Prefix H Gap Suffix → Value) :
    fullPhi C' (fullPhi C F) = fullPhi (C' + C) F := by
  funext a
  cases a with
  | mk p h g d z =>
    simp only [fullPhi_apply, Pi.add_apply]
    have heq : h - C' d - C d = h - (C' d + C d) := by abel
    rw [heq]

theorem fullPhi_pointwise (C : H → H) (op : Value → Value → Value)
    (F G : FullAddress Prefix H Gap Suffix → Value) :
    fullPhi C (fun a => op (F a) (G a)) =
      fun a => op (fullPhi C F a) (fullPhi C G a) := rfl

theorem fullPhi_edge_layout (Mu Mv : H → H)
    (F : FullAddress Prefix H Gap Suffix → Value) :
    fullPhi (Mv - Mu) (fullPhi Mu F) = fullPhi Mv F := by
  rw [fullPhi_comp, sub_add_cancel]

/-- Correct net address update with every spectator coordinate retained. -/
theorem fullPhi_endpoint_identity (Ms Mt : H → H)
    (hlabels : Mt - Ms = id)
    (F : FullAddress Prefix H Gap Suffix → Value)
    (p : Prefix) (h : H) (g : Gap) (d : H) (z : Suffix) :
    fullPhi Mt (fullPhi (-Ms) F) ⟨p, h + d, g, d, z⟩ =
      F ⟨p, h, g, d, z⟩ := by
  rw [fullPhi_comp, ← sub_eq_add_neg, hlabels]
  exact fullPhi_preserves_payload id F p h g d z

end FullShears

section LinearCoordinates

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Algebraic part of `A = E₁ P E₂`: conjugating a sparse update by
coordinate changes realizes the original update.  No triangularity,
factorization existence, rank claim, or scan bound is assumed proved here. -/
theorem coordinate_change_update
    (E₁ E₂ : V ≃ₗ[R] V) (P : V →ₗ[R] V) (h d : V) :
    (E₁ (E₁.symm h + P (E₂ d)), E₂.symm (E₂ d)) =
      (h + E₁ (P (E₂ d)), d) := by
  simp

end LinearCoordinates

section MatrixLabels

variable {R I Value : Type*} [Ring R] [Fintype I]

/-- Concrete matrix action, separated from the stream's value type.
For Section 5 one may use `R = ZMod (q ^ f)` and `Value = Bool`. -/
def matrixPhi (M : Matrix I I R)
    (F : (I → R) × (I → R) → Value) : (I → R) × (I → R) → Value :=
  phi M.mulVec F

theorem matrixPhi_comp (M' M : Matrix I I R)
    (F : (I → R) × (I → R) → Value) :
    matrixPhi M' (matrixPhi M F) = matrixPhi (M' + M) F := by
  unfold matrixPhi
  rw [phi_comp]
  apply congrArg (fun C => phi C F)
  funext d
  exact (Matrix.add_mulVec M' M d).symm

theorem matrixPhi_zero (F : (I → R) × (I → R) → Value) :
    matrixPhi (0 : Matrix I I R) F = F := by
  have hzero : (0 : Matrix I I R).mulVec = (0 : (I → R) → (I → R)) := by
    funext d
    simp
  simpa only [matrixPhi, hzero] using (phi_zero F)

theorem matrixPhi_inverse (M : Matrix I I R)
    (F : (I → R) × (I → R) → Value) :
    matrixPhi (-M) (matrixPhi M F) = F := by
  rw [matrixPhi_comp, neg_add_cancel, matrixPhi_zero]

theorem matrix_edge_layout (Mu Mv : Matrix I I R)
    (F : (I → R) × (I → R) → Value) :
    matrixPhi (Mv - Mu) (matrixPhi Mu F) = matrixPhi Mv F := by
  rw [matrixPhi_comp, sub_add_cancel]

variable [DecidableEq I]

/-- This is the manuscript's concrete endpoint calculation, including
the preservation of the bit at its new destination address. -/
theorem matrix_endpoint_identity (Ms Mt : Matrix I I R)
    (hlabels : Mt - Ms = 1)
    (F : (I → R) × (I → R) → Value) (h d : I → R) :
    matrixPhi Mt (matrixPhi (-Ms) F) (h + d, d) = F (h, d) := by
  rw [matrixPhi_comp, ← sub_eq_add_neg, hlabels]
  change phi (1 : Matrix I I R).mulVec F (h + d, d) = F (h, d)
  have hone : (1 : Matrix I I R).mulVec = (id : (I → R) → (I → R)) := by
    funext x
    exact Matrix.one_mulVec x
  rw [hone]
  exact phi_preserves_payload id F h d

theorem matrix_action_endpoint_labels (Ms Mt : Matrix I I R)
    (hlabels : Mt - Ms = 1) : Mt.mulVec - Ms.mulVec = id := by
  funext d
  change Mt.mulVec d - Ms.mulVec d = d
  rw [← Matrix.sub_mulVec, hlabels, Matrix.one_mulVec]

/-- Concrete matrix endpoint identity on the full address, including
all prefix, gap and suffix coordinates and the unchanged payload. -/
theorem matrix_full_endpoint_identity (Ms Mt : Matrix I I R)
    (hlabels : Mt - Ms = 1)
    (F : FullAddress Prefix (I → R) Gap Suffix → Value)
    (p : Prefix) (h : I → R) (g : Gap) (d : I → R) (z : Suffix) :
    fullPhi Mt.mulVec (fullPhi (-Ms).mulVec F) ⟨p, h + d, g, d, z⟩ =
      F ⟨p, h, g, d, z⟩ := by
  have hneg : (-Ms).mulVec = -Ms.mulVec := by
    funext x
    exact Matrix.neg_mulVec x Ms
  rw [hneg]
  exact fullPhi_endpoint_identity Ms.mulVec Mt.mulVec
    (matrix_action_endpoint_labels Ms Mt hlabels) F p h g d z

end MatrixLabels

section GoodPrime

/-- A single odd prime works for every modulus `q^f` and every entry of
a fixed finite set of nonzero natural coefficients.  The set may contain
denominators and absolute values of nonzero diagonal numerators.

This is the finite-coefficient prime-selection step only.  It does not
construct the rational matrix factorizations from which the set is drawn. -/
theorem exists_good_prime (coefficients : Finset ℕ)
    (hnonzero : ∀ a ∈ coefficients, a ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧
      ∀ a ∈ coefficients, ∀ f : ℕ, IsUnit (a : ZMod (q ^ f)) := by
  obtain ⟨q, hqbound, hqprime⟩ :=
    Nat.exists_infinite_primes (max 2 (coefficients.sup id) + 1)
  have hlarge : max 2 (coefficients.sup id) < q := Nat.lt_of_succ_le hqbound
  have htwo : 2 < q := lt_of_le_of_lt (le_max_left _ _) hlarge
  refine ⟨q, hqprime, hqprime.odd_of_ne_two (ne_of_gt htwo), ?_⟩
  intro a ha f
  have hamax : a ≤ coefficients.sup id := Finset.le_sup (f := id) ha
  have haq : a < q :=
    lt_of_le_of_lt (hamax.trans (le_max_right _ _)) hlarge
  have hapos : 0 < a := Nat.pos_of_ne_zero (hnonzero a ha)
  have hnotdvd : ¬q ∣ a := by
    intro hdvd
    exact (not_le_of_gt haq) (Nat.le_of_dvd hapos hdvd)
  have hcoprime : a.Coprime q :=
    (hqprime.coprime_iff_not_dvd.mpr hnotdvd).symm
  exact (ZMod.isUnit_iff_coprime a (q ^ f)).mpr (hcoprime.pow_right f)

end GoodPrime

end CSL.Address


