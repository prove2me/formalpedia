-- Prove2me | Definitions.Def_LARLLL_Foundation01
-- name    : LARLLL_Foundation01
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:54:13.691832+00:00
-- url     : https://prove2.me/theorems/f4035a09-396b-4921-a8b5-529996ea8da6
-- title:
--   Checked vector and matrix foundations for the native LLL algorithm
-- statement:
--   Source-faithful supporting definitions for the existing integer and rational LLL implementation: exact-division laws, array and vector constructors, list folds, row-major matrices and elementary operations. This bundle preserves the original computable implementations and the six checked csimp equalities that select them. Its short supporting proofs are required by data definitions or compiler replacements. It introduces no assumption about LLL bit complexity.
-- source:
--   Apache-2.0 sources from leanprover/hex-basic commit f3ec4bd78149d07b4fd2372010563334f285b37e and leanprover/hex-matrix commit 29ad1c6634e830d472c915198bf4178e050c4e4d, ported to Lean 4.33.1 in the checked native LLL workspace. Exact original source locations and SHA-256 values are recorded in validation.json source_segments. The official Lean declaration and syntax oracles select whole source commands, retain copyright/modification notices, and preserve all types and non-theorem values by kernel-checked equality. Source SHA-256: d6fc8c6d4714957a805d6a00a96011e9a75239b42a179119dd1a490f97f26b32.

import Init
import Init.Data.List.Sort.Basic
import Init.Grind.Ring.Field
import Std
import Std.Data.ExtTreeMap.Lemmas

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Kernel-reducible {name}`DecidableEq` instances for {name}`Array` and
{name}`Vector`.

Three exposure gaps in core stop `decide` / `rfl` reducing over these types
across a module boundary. In each case an exposed definition delegates to a
plain `def` whose body is unavailable downstream, so reduction stalls:

* {name}`Array.instDecidableEq` delegates its nonempty/nonempty case to
  {name}`Array.instDecidableEqImpl`;
* every `deriving DecidableEq` instance delegates to a generated `decEq`,
  which is how {name}`Vector` gets its instance;
* {name}`Array.ofFn` delegates to its `ofFn.go` auxiliary.

The instances below route through {name}`List` equality, which is fully exposed, and
take priority over the core ones. They are `scoped`, so they apply only inside
`namespace Hex` or after `open scoped Hex`, and never leak into the released
libraries that depend on `hex-basic` or into their consumers. A module that
forgets to activate them gets a stuck `decide`, which is loud. {name}`List` is
the wrong shape for compiled code, where {name}`Array.toList` is an `O(n)`
conversion that allocates both lists in full
before comparison begins and gives up early exit, so each carries a `@[csimp]`
redirect back to the core instance. The `List` route is then paid only in the
kernel, which is where it is needed.

Remove these scoped instances and their compiler redirects when the pinned
toolchain reaches Lean v4.35.0-rc1, which includes the upstream fixes for
{name}`Array` equality (<https://github.com/leanprover/lean4/pull/14270>) and
{name}`Vector` equality (<https://github.com/leanprover/lean4/pull/14988>).
-/

namespace Hex



/-- `DecidableEq (Vector α n)` that reduces in the kernel under the module
system. `Vector`'s core instance is derived, and derived instances are opaque
across a module boundary. -/
scoped instance (priority := 1100) instDecidableEqVector
    {α : Type u} {n : Nat} [DecidableEq α] : DecidableEq (Vector α n) := fun a b =>
  match h : decEq a.toArray.toList b.toArray.toList with
  | isTrue ht => isTrue (by
      cases a with | mk ba ha => cases b with | mk bb hb =>
      have hba : ba = bb := by cases ba; cases bb; exact congrArg Array.mk ht
      subst hba; rfl)
  | isFalse hf => isFalse (by intro hab; subst hab; exact hf rfl)



/-- The {name}`Hex.instDecidableEqVector` analogue of
{name}`Hex.instDecidableEqArray_eq`. -/
@[csimp] theorem instDecidableEqVector_eq :
    @instDecidableEqVector = @_root_.instDecidableEqVector := by
  funext α n _ a b; exact Subsingleton.elim _ _

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Shared exact scalar division.

The executable operations reuse the coefficient type's existing `/` and make
division by zero deterministic. Algebraic correctness is isolated in
`ExactDivLaws`; computational consumers need only the operations, while proof
consumers opt into the law package.

This module is coefficient-independent: it fixes the contract and the
cancellation lemmas that hold for every carrier, leaving carrier-specific
operations and instances (dense polynomials, matrices) to their consumers.

Nothing here shadows a Mathlib root name, and that is deliberate. `HexBasic`
sits below the whole graph, so a declaration `Hex.foo` added here is in scope
for every `Hex*Theory` file wherever `open Hex` is in effect, and a bare `foo`
in that scope is an ambiguous term when Mathlib also defines `_root_.foo`.
That rules out hosting the binary-power helpers here: `Hex.mul_pow`,
`Hex.pow_mul`, and `Hex.pow_ne_zero` all collide that way, and
`HexGFqTheory/Primitivity.lean` is a live site. They stay with their
Brown-recurrence consumer in `HexResultant/ExactDiv.lean`, along with `powNat`
and `divExp`, which nothing below `hex-resultant` needs.
-/
namespace Hex

universe u

/-- A quotient operation is exact when multiplication by every nonzero right
factor can be undone by division by that factor. -/
class ExactDivLaws (R : Type u) [Zero R] [Mul R] [Div R] : Prop where
  /-- Right multiplication followed by division by a nonzero factor cancels. -/
  mul_div_cancel_right : ∀ a b : R, b ≠ 0 → (a * b) / b = a

namespace ExactDivLaws

variable {R : Type u}



/-- Exact division and commutative-ring laws rule out nonzero products
vanishing. -/
theorem mul_ne_zero [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hzero
  have hdiv := congrArg (fun x : R => x / b) hzero
  have hzdiv : (0 : R) / b = 0 := by
    simpa [Lean.Grind.Semiring.zero_mul] using
      (ExactDivLaws.mul_div_cancel_right (0 : R) b hb)
  rw [ExactDivLaws.mul_div_cancel_right a b hb, hzdiv] at hdiv
  exact ha hdiv

end ExactDivLaws

variable {R : Type u}





/-- Total exact quotient wrapper. The zero denominator is a documented junk
input and returns zero. -/
@[expose]
def exactDiv [Zero R] [DecidableEq R] [Div R] (a b : R) : R :=
  if b = 0 then 0 else a / b







/-- Integer Euclidean division is exact on nonzero right multiples. -/
instance instExactDivLawsInt : ExactDivLaws Int where
  mul_div_cancel_right := Int.mul_ediv_cancel

/-- A nontrivial ring without zero divisors. Proof-only: a certificate checker
that needs no quotient operation states its soundness over this class rather
than over `ExactDivLaws`, so that a consumer re-checking a witness never has
to supply a division. -/
class DomainLaws (R : Type u) [Zero R] [One R] [Mul R] : Prop where
  /-- The ring is nontrivial. -/
  one_ne_zero : (1 : R) ≠ 0
  /-- A vanishing product has a vanishing factor. -/
  no_zero_div : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

/-- The integers form a domain. -/
instance instDomainLawsInt : DomainLaws Int where
  one_ne_zero := by decide
  no_zero_div _ _ h := Int.mul_eq_zero.mp h

/-- Every `Lean.Grind.Field` is a domain. -/
instance instDomainLawsField {K : Type u} [Lean.Grind.Field K] : DomainLaws K where
  one_ne_zero h := Lean.Grind.Field.zero_ne_one h.symm
  no_zero_div _ _ h := Lean.Grind.Field.of_mul_eq_zero h



/-- Every `Lean.Grind.Field` supplies the exact-division law. -/
instance instExactDivLawsField {K : Type u} [Lean.Grind.Field K] :
    ExactDivLaws K where
  mul_div_cancel_right a b hb := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hb, Lean.Grind.Semiring.mul_one]

/-! Instance-contract check for the integer coefficient tower. -/




/-! Value-level pin for the total quotient. -/

#guard exactDiv (7 : Int) 0 = 0

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
General `List.foldl` algebra shared across the Mathlib-free `hex` libraries.

The computational libraries repeatedly fold an accumulator with a single
operation, `xs.foldl (fun acc x => acc + f x) z` or its multiplicative twin.
Lean core already proves the underlying facts — {name}`List.foldl_assoc`,
{name}`List.sum_eq_foldl`, `List.foldl_map` — but those need `Std.Associative` /
`Std.LawfulIdentity` instances on the carrier, which a bare
`Lean.Grind.Semiring` does not carry. This module supplies those four
instances **file-locally** (just enough to prove the lemmas below) and then
states the fold-algebra the libraries actually use.

The lemmas live in the `List` namespace and follow the standard-library
naming: name the operation, not the use site (`foldl_add_*`, `foldl_mul_*`),
mirror {name}`List.foldl_assoc`/`List.foldl_map`, and keep `foldl_add_eq_add_foldl`
symmetric with `foldl_mul_eq_mul_foldl`. The one exception is
`foldl_const_step`: core/Mathlib already use `List.foldl_const` for the
unrelated iterate lemma, so reusing that name here would collide in the
Theory layers (which import both this module and Mathlib). These are
kept here so the computational libraries can use them without importing
Mathlib.
-/

namespace List

universe u v w

variable {α : Type v} {β : Type w} {R : Type u}

/-!
The `Std.Associative` / `Std.LawfulIdentity` instances that
{name}`List.foldl_assoc` and friends need are kept **file-local**: they are used
only to prove the lemmas below, whose conclusions use `Lean.Grind.Semiring`,
with `Ring` or `CommRing` required only where negation or commutative
multiplication is genuinely involved. Keeping them local avoids adding a
second global `Std.Associative` resolution path for every `Grind.Semiring`
(e.g. `Nat`/`Int` in the theory layers, where Mathlib already supplies
its own). Promote / upstream them separately if a consumer ever needs them.
-/

/-- Addition in a `Grind.Semiring` is an associative operation. -/
local instance _root_.List.instAssociativeHAdd_solutions {R : Type u} [Lean.Grind.Semiring R] : Std.Associative (· + · : R → R → R) :=
  ⟨Lean.Grind.Semiring.add_assoc⟩







/-! # Congruence -/

/-- Two folds over `xs` agree when their step functions agree pointwise on the
elements of `xs` (for every accumulator). The fully general fold congruence. -/
theorem foldl_congr (xs : List α) (f g : β → α → β) (z : β)
    (h : ∀ acc x, x ∈ xs → f acc x = g acc x) :
    xs.foldl f z = xs.foldl g z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h z x (List.mem_cons_self ..)]
    exact ih _ fun acc y hy => h acc y (List.mem_cons_of_mem _ hy)

/-- Congruence for an additive fold-sum under its summand `f`. -/
theorem foldl_add_congr [Add R] (xs : List α) (f g : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) z = xs.foldl (fun acc x => acc + g x) z :=
  foldl_congr xs _ _ z fun acc x hx => by rw [h x hx]





/-! # Constant step -/

/-- Folding with a step that discards the element and returns the accumulator
unchanged yields the initial accumulator. (Core's `List.foldl_const` is the
unrelated iterate lemma, hence the name.) -/
theorem foldl_const_step (xs : List α) (z : β) :
    xs.foldl (fun acc _ => acc) z = z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; exact ih z

/-! # Permutation invariance -/





section Semiring

variable [Lean.Grind.Semiring R]

/-! # Accumulator extraction -/



/-! # All-zero collapse -/

/-- An additive fold-sum whose every summand vanishes on `xs` returns the
initial accumulator. -/
theorem foldl_add_eq_self (xs : List α) (f : α → R) (z : R)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) z = z := by
  rw [foldl_add_congr xs f (fun _ => 0) z h]
  simp only [Lean.Grind.Semiring.add_zero]
  exact foldl_const_step xs z



/-! # Scalar factoring -/

/-- Factor a left scalar out of an additive fold-sum. -/
theorem foldl_add_mul_left (xs : List α) (c : R) (f : α → R) (z : R) :
    xs.foldl (fun acc x => acc + c * f x) (c * z) =
      c * xs.foldl (fun acc x => acc + f x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← show c * (z + f x) = c * z + c * f x by grind]
    exact ih (z + f x)





end Semiring

section Ring

variable [Lean.Grind.Ring R]

/-! # Negation -/



end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Additivity -/

/-- An additive fold-sum of a pointwise sum splits into two folds, distributing
the starting accumulator. -/
theorem foldl_add_add_start (xs : List α) (f g : α → R) (a b : R) :
    xs.foldl (fun acc x => acc + (f x + g x)) (a + b) =
      xs.foldl (fun acc x => acc + f x) a + xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc xs.foldl (fun acc x => acc + (f x + g x)) (a + b + (f x + g x))
        = xs.foldl (fun acc x => acc + (f x + g x)) ((a + f x) + (b + g x)) := by
          congr 1; grind
      _ = xs.foldl (fun acc x => acc + f x) (a + f x)
            + xs.foldl (fun acc x => acc + g x) (b + g x) := ih (a + f x) (b + g x)



/-- An additive fold-sum of a pointwise sum from `0` splits into the sum of the
two separate folds from `0`. -/
theorem foldl_add_add (xs : List α) (f g : α → R) :
    xs.foldl (fun acc x => acc + (f x + g x)) 0 =
      xs.foldl (fun acc x => acc + f x) 0 + xs.foldl (fun acc x => acc + g x) 0 := by
  calc xs.foldl (fun acc x => acc + (f x + g x)) 0
      = xs.foldl (fun acc x => acc + (f x + g x)) ((0 : R) + 0) := by congr 1; grind
    _ = xs.foldl (fun acc x => acc + f x) 0 + xs.foldl (fun acc x => acc + g x) 0 :=
        foldl_add_add_start xs f g 0 0

end Semiring

section Ring

variable [Lean.Grind.Ring R]

/-! # Subtraction -/





end Ring

section Semiring

variable [Lean.Grind.Semiring R]

/-! # Fubini -/



end Semiring

section Semiring

variable [Lean.Grind.Semiring R]



end Semiring

/-! # flatMap -/



/-! # Indicator pickout -/



/-! # Monotone bounds (`Nat`) -/









/-! # Multiplicative twins -/



section CommSemiring

variable [Lean.Grind.CommSemiring R]







end CommSemiring

end List

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-! Length bounds for duplicate-free lists, in the Hex namespace. -/

namespace Hex.List

open _root_.List

/-- A duplicate-free list contained in another list is no longer than it. -/
theorem nodup_subset_length_le {α} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    rw [nodup_cons] at h₁
    have ha : a ∈ l₂ := hsub (mem_cons_self ..)
    have htsub : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => h₁.1 (h ▸ hx)
      exact (mem_erase_of_ne hxa).2 (hsub (mem_cons_of_mem _ hx))
    have hih := ih h₁.2 htsub
    have hlen : (l₂.erase a).length = l₂.length - 1 := by rw [length_erase]; simp [ha]
    have hpos : 1 ≤ l₂.length := length_pos_of_mem ha
    simp only [length_cons]; omega

end Hex.List

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Kernel-reducible function tabulation for {name}`Array` and {name}`Vector`.

{name}`Array.ofFn` delegates to its `ofFn.go` auxiliary, which is not exposed, so
under the module system its body is unavailable downstream and
`(Array.ofFn f)` does not reduce in the kernel. {name}`Vector.ofFn` is itself
`@[expose]` but calls {name}`Array.ofFn`, so it inherits the stall.

{name}`List.ofFn` is fully exposed and reduces, so the definitions below go through
it. That is the wrong shape for compiled code, which wants to push into an
array of known capacity rather than build a linked list and convert, so each
carries a `@[csimp]` lemma redirecting the compiler back to the core version.
The {name}`List` route is then paid only in the kernel, which is where it is
needed.

Remove the `Array.ofFn'` and `Vector.ofFn'` shims and migrate their
callers to the core operations when the pinned toolchain reaches Lean
v4.35.0-rc1, which includes
<https://github.com/leanprover/lean4/pull/14989>.
-/

namespace Hex



/-- A {name}`Vector.ofFn` equivalent that reduces in the kernel under the
module system. -/
@[expose] def Vector.ofFn' {n : Nat} {α : Type u} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by simp⟩



@[simp] theorem Vector.ofFn'_eq_ofFn {n : Nat} {α : Type u} (f : Fin n → α) :
    Vector.ofFn' f = Vector.ofFn f := by
  simp [Vector.ofFn', _root_.Vector.ofFn]

/-! # Compatibility lemmas

Core's lemmas ({name}`Array.size_ofFn`, {name}`Vector.getElem_ofFn`, …) are
stated about {name}`Array.ofFn` and {name}`Vector.ofFn` and do not apply
directly to {name}`Hex.Array.ofFn'` or {name}`Hex.Vector.ofFn'`.
{name}`Hex.Array.ofFn'_eq_ofFn` is `@[simp]`, so ordinary `simp` bridges the
gap; these lemmas also support `simp only` proofs and `rfl`-closing steps. -/







@[simp] theorem Vector.getElem_ofFn' {n : Nat} {α : Type u} (f : Fin n → α) (i : Nat)
    (h : i < n) : (Vector.ofFn' f)[i] = f ⟨i, h⟩ := by
  simp [Vector.ofFn']



/-- The {name}`Hex.Vector.ofFn'` analogue of
{name}`Hex.Array.ofFn'_eq_ofFn'`. -/
@[csimp] theorem Vector.ofFn'_eq_ofFn' : @Vector.ofFn' = @_root_.Vector.ofFn := by
  funext n α f; exact Vector.ofFn'_eq_ofFn f

/-! # `Array.map` -/

/-- An {name}`Array.map` equivalent that reduces in the kernel under the
module system: core {name}`Array.map`'s implementation loop is not exposed,
so `(a.map f)` stalls downstream exactly like {name}`Array.ofFn`.
Remove this shim and migrate its callers to core {name}`Array.map` when the
pinned toolchain reaches Lean v4.35.0-rc1, which includes
<https://github.com/leanprover/lean4/pull/14996>. -/
@[expose] def Array.map' {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) : Array β :=
  (a.toList.map f).toArray

@[simp] theorem Array.map'_eq_map {α : Type u} {β : Type v} (f : α → β)
    (a : Array α) : Array.map' f a = a.map f := by
  rw [Array.map', ← Array.toList_map, Array.toArray_toList]





/-- Compiled code uses the core {name}`Array.map`, which writes into an
array in place when uniquely referenced; the {name}`List` route exists only
so that the kernel can reduce it. -/
@[csimp] theorem Array.map'_eq_map' : @Array.map' = @_root_.Array.map := by
  funext α β f a; exact Array.map'_eq_map f a

/-! # `Vector.map` -/

/-- A {name}`Vector.map` equivalent that reduces in the kernel under the
module system: core {name}`Vector.map` delegates to {name}`Array.map`, whose
implementation loop is not exposed, so `(v.map f)` stalls downstream.
Remove this shim and migrate its callers to core {name}`Vector.map` when the
pinned toolchain reaches Lean v4.35.0-rc1, alongside
{name}`Hex.Array.map'`. -/
@[expose] def Vector.map' {α : Type u} {β : Type v} {n : Nat} (f : α → β)
    (v : Vector α n) : Vector β n :=
  ⟨Array.map' f v.toArray, by simp⟩

@[simp] theorem Vector.map'_eq_map {α : Type u} {β : Type v} {n : Nat} (f : α → β)
    (v : Vector α n) : Vector.map' f v = v.map f :=
  _root_.Vector.toArray_inj.mp (by simp [Vector.map'])





/-- Compiled code uses the core {name}`Vector.map`; the {name}`List` route
exists only so that the kernel can reduce it. -/
@[csimp] theorem Vector.map'_eq_map' : @Vector.map' = @_root_.Vector.map := by
  funext α β n f v; exact Vector.map'_eq_map f v

/-! # `Array.zipWith` -/











end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Low-level vector update helper used for efficient code generation.
-/

namespace Vector

/--
In-place update of the element at index `i` via `f`, wrapping `Array.modify`
so the underlying swap-with-placeholder ownership transfer survives codegen.
Calling `xs.set i (f xs[i])` forces a `lean_inc` on the borrowed entry and
loses uniqueness on nested-array shapes (e.g. matrix rows); `modify` avoids
that copy when `xs` is uniquely owned.
-/
@[expose, inline] def modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

/-- Entrywise read of `modify`: the modified index gets `f` applied, every other
index is unchanged. -/
@[grind =] theorem getElem_modify {xs : Vector α n} {i : Nat} {f : α → α}
    {j : Nat} (hj : j < n) :
    (xs.modify i f)[j] = if i = j then f xs[j] else xs[j] := by
  rcases xs with ⟨a, rfl⟩
  simp only [modify, Vector.getElem_mk]
  rw [Array.getElem_modify]

/-- The modified index of `modify` reads back `f` applied to the old value. -/
theorem getElem_modify_self {xs : Vector α n} {i : Nat} {f : α → α} (hi : i < n) :
    (xs.modify i f)[i] = f xs[i] := by
  rw [getElem_modify hi, if_pos rfl]

/-- Any index other than the modified one is unchanged by `modify`. -/
theorem getElem_modify_of_ne {xs : Vector α n} {i j : Nat} {f : α → α}
    (hj : j < n) (h : i ≠ j) :
    (xs.modify i f)[j] = xs[j] := by
  rw [getElem_modify hj, if_neg h]

/-- `modify` agrees with the read-then-{name}`set` form (value-level; `modify` avoids
the copy this form would force). -/
theorem modify_eq_set (xs : Vector α n) (i : Nat) (f : α → α) (h : i < n) :
    xs.modify i f = xs.set i (f xs[i]) := by
  apply Vector.ext
  intro j hj
  rw [getElem_modify hj, Vector.getElem_set]
  grind

/-- A left fold of per-index `modify`s over a list of `Fin n` indices leaves
index `r` untouched when `r` is not among the folded indices. The backing engine
for the in-place indexed row scatter (`Matrix.mapRowsIdx`). -/
theorem getElem_foldl_modify_not_mem (g : Fin n → α → α)
    {r : Nat} (hr : r < n) :
    ∀ (xs : List (Fin n)) (v0 : Vector α n), (∀ i ∈ xs, i.val ≠ r) →
      (xs.foldl (fun v i => v.modify i.val (g i)) v0)[r] = v0[r] := by
  intro xs
  induction xs with
  | nil => intro v0 _; rfl
  | cons x xs ih =>
    intro v0 hnm
    rw [List.foldl_cons, ih _ (fun i hi => hnm i (List.mem_cons_of_mem _ hi)),
      Vector.getElem_modify_of_ne hr (hnm x List.mem_cons_self)]

/-- A left fold of per-index `modify`s over a `Nodup` list writes `g r` at every
member index `r` (reading the value `r` held before the fold, since each index
is visited at most once). -/
theorem getElem_foldl_modify_mem (g : Fin n → α → α) :
    ∀ (xs : List (Fin n)), xs.Nodup → ∀ (v0 : Vector α n) (r : Fin n), r ∈ xs →
      (xs.foldl (fun v i => v.modify i.val (g i)) v0)[r.val]'r.isLt = g r v0[r.val] := by
  intro xs
  induction xs with
  | nil => intro _ v0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd v0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [getElem_foldl_modify_not_mem g r.isLt xs _ (fun i hi heq => by
        apply (List.nodup_cons.mp hnd).1
        rwa [← (Fin.ext heq : i = r)])]
      exact Vector.getElem_modify_self r.isLt
    · have hxr : x.val ≠ r.val := by
        intro heq
        apply (List.nodup_cons.mp hnd).1
        rwa [(Fin.ext heq : x = r)]
      rw [ih (List.nodup_cons.mp hnd).2 _ r hr',
        Vector.getElem_modify_of_ne r.isLt hxr]

/-- `List.finRange n` has no repeated indices (core-only proof; the Batteries
`nodup_finRange` is outside this Mathlib-free module's import closure). -/
 theorem _root_.Vector.nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [Fin.ext_iff], List.Pairwise.map _ (fun _ _ hab h => hab (Fin.succ_inj.mp h)) ih⟩

/-- Reading index `r` of a `Fin.foldl` of per-index `modify`s yields `g r`
applied to the original entry — every index is visited exactly once. This is the
in-place (no intermediate `List.finRange` allocation) scatter form. -/
theorem getElem_finFoldl_modify (v0 : Vector α n)
    (g : Fin n → α → α) (r : Fin n) :
    (Fin.foldl n (fun v i => v.modify i.val (g i)) v0)[r.val]'r.isLt = g r v0[r.val] := by
  rw [Fin.foldl_eq_finRange_foldl]
  exact getElem_foldl_modify_mem g (List.finRange n) (_root_.Vector.nodup_finRange n) v0 r (by simp)

end Vector

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/




namespace Hex
end Hex
namespace Hex.Kernel
end Hex.Kernel
namespace Hex.Kernel.allRange
end Hex.Kernel.allRange
namespace Hex.Kernel.fuelRecImpl
end Hex.Kernel.fuelRecImpl
namespace Hex.Kernel.iterUp
end Hex.Kernel.iterUp
namespace Hex.Kernel.iterUpImpl
end Hex.Kernel.iterUpImpl
namespace Hex.Kernel.iterUpImpl.go
end Hex.Kernel.iterUpImpl.go
namespace Hex.Kernel.iterUp_go
end Hex.Kernel.iterUp_go
namespace Hex.Kernel.mapRange
end Hex.Kernel.mapRange
namespace Hex.List
end Hex.List
namespace Hex.List.go_eq
end Hex.List.go_eq
namespace Hex.List.merge
end Hex.List.merge
namespace Hex.List.merge.match_1
end Hex.List.merge.match_1
namespace Hex.List.sort
end Hex.List.sort
namespace Hex.List.sort.go
end Hex.List.sort.go
namespace Hex.List.sort.go.match_1
end Hex.List.sort.go.match_1
namespace Hex.Rand
end Hex.Rand
namespace Hex.Rand.mk
end Hex.Rand.mk
namespace Hex.Rand.natGo
end Hex.Rand.natGo
namespace Hex.Rand.natGo.match_1
end Hex.Rand.natGo.match_1
namespace Hex.Rand.natGo_lt
end Hex.Rand.natGo_lt
namespace Hex.Rand.words
end Hex.Rand.words
namespace Hex.Rand.words.match_1
end Hex.Rand.words.match_1
namespace Hex.RandError
end Hex.RandError
namespace Hex.RandError.exhausted
end Hex.RandError.exhausted
namespace Hex.RandError.zeroBound
end Hex.RandError.zeroBound
namespace Hex.instDecidableEqRand
end Hex.instDecidableEqRand
namespace Hex.instDecidableEqRand.decEq
end Hex.instDecidableEqRand.decEq
namespace Hex.instReprRand
end Hex.instReprRand
namespace Hex.instReprRandError
end Hex.instReprRandError
namespace Hex.instReprRandError.repr
end Hex.instReprRandError.repr
namespace List
end List
namespace List.compareLex_zipWith
end List.compareLex_zipWith
namespace List.map_unattach
end List.map_unattach
namespace List.map_unattach.match_1
end List.map_unattach.match_1
namespace List.mergeSort
end List.mergeSort
namespace List.mergeSort.match_1
end List.mergeSort.match_1
namespace PSigma
end PSigma
namespace PSigma.casesOn
end PSigma.casesOn
namespace Std
end Std
namespace Std.ExtTreeMap
end Std.ExtTreeMap
namespace Std.ExtTreeMap.foldl
end Std.ExtTreeMap.foldl
namespace Std.ExtTreeMap.foldl₂
end Std.ExtTreeMap.foldl₂
namespace Std.ExtTreeMap.foldl₂.mergeFold
end Std.ExtTreeMap.foldl₂.mergeFold
namespace Std.ExtTreeMap.foldl₂.mergeFold.match_1
end Std.ExtTreeMap.foldl₂.mergeFold.match_1
namespace Std.ExtTreeMap.foldl₂.mergeFold.match_3
end Std.ExtTreeMap.foldl₂.mergeFold.match_3
namespace Std.ExtTreeMap.getElem?_foldl_alter
end Std.ExtTreeMap.getElem?_foldl_alter
namespace Std.ExtTreeMap.getElem?_foldl_alter_of_mem
end Std.ExtTreeMap.getElem?_foldl_alter_of_mem
namespace Std.ExtTreeMap.mergeValue?
end Std.ExtTreeMap.mergeValue?
namespace Std.ExtTreeMap.mergeWith?
end Std.ExtTreeMap.mergeWith?
namespace Std.ExtTreeMap.mergeWith?_empty_left
end Std.ExtTreeMap.mergeWith?_empty_left
namespace Std.ExtTreeMap.mergeWith?_empty_right
end Std.ExtTreeMap.mergeWith?_empty_right


set_option autoImplicit true



section

/-!
Core dense matrix definitions for `hex-matrix`.

This module models matrices with a **flat row-major** backing `Vector R (n * m)`
and provides the basic executable operations needed by later linear-algebra
algorithms: row/column accessors, zero and identity matrices, dot products,
matrix-vector multiplication, matrix-matrix multiplication, and norm-squared
helpers.

The backing is a single contiguous buffer holding the `n * m` entries in
row-major order: entry `(i, j)` lives at flat index `i * m + j`. The structure
stays an opaque one-field record so this representation is invisible to
consumers, who go through `ofFn`/`ofRows`/`getRow`/`rows` and the entry accessor
`M[(i, j)]`.
-/
namespace Hex

universe u v

/-- Dense `n × m` matrices over `R`, backed by a flat row-major buffer of the
`n * m` entries: entry `(i, j)` is stored at flat index `i * m + j`. Opaque
one-field structure; consumers go through `rows`/`getRow`/`ofRows`/`ofFn` and
`M[i]` / `M[(i,j)]`, never the `data` projection, so the representation can
change. -/
structure Matrix (R : Type u) (n m : Nat) where
  /-- Build a matrix from its flat row-major backing buffer. Implementation
  detail — use `ofRows`/`ofFn`, never this constructor. -/
  mk ::
  /-- Implementation detail — the flat row-major backing buffer. Use
  `Matrix.rows`/`getRow`, never this projection. -/
  data : Vector R (n * m)
deriving DecidableEq, BEq

/-- Structural matrix comparison is lawful whenever entry comparison is. -/
instance _root_.Hex.instLawfulBEqMatrix {R : Type u} {n m : Nat} [BEq R] [LawfulBEq R] :
    LawfulBEq (Matrix R n m) where
  eq_of_beq := by
    intro A B h
    cases A with
    | mk a =>
      cases B with
      | mk b =>
        congr
        exact eq_of_beq h
  rfl := by
    intro A
    cases A with
    | mk a =>
      change (a == a) = true
      exact beq_self_eq_true a



end Hex

namespace Vector

/-- Dot product of two vectors.

This {name}`List.finRange` form is the reference definition the entry lemmas reason
about; crucially it kernel-reduces, so `#guard`/`decide` checks over
`dotProduct` (e.g. `memLattice` membership) stay evaluable — core `Fin.foldl`
does not yet reduce in the kernel. Compiled code therefore uses the
allocation-free `Vector.dotProductImpl`, selected by
`Vector.dotProduct_eq_impl`, while logical evaluation retains the
list-based form. -/
-- Once https://github.com/leanprover/lean4/pull/14267 is available in the
-- project toolchain, define `dotProduct` directly with `Fin.foldl` and remove
-- `dotProductImpl` and `dotProduct_eq_impl`.
@[expose]
noncomputable def dotProduct [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  (List.finRange n).foldl (fun acc i => acc + u[i] * v[i]) 0

/-- Allocation-free implementation of `dotProduct`: a `Fin.foldl` loop that never
materializes the `List.finRange n` index list. Swapped in for compiled code by the
`@[csimp]` lemma; `dotProduct` remains the reference form for proofs. -/
@[expose]
def dotProductImpl [Mul R] [Add R] [OfNat R 0] (u v : Vector R n) : R :=
  Fin.foldl n (fun acc i => acc + u[i] * v[i]) 0

@[csimp] theorem dotProduct_eq_impl : @dotProduct = @dotProductImpl := by
  funext R n iMul iAdd iZero u v
  rw [dotProduct, dotProductImpl, Fin.foldl_eq_finRange_foldl]

/-- Squared Euclidean norm of a vector. -/
@[expose]
def normSq [Mul R] [Add R] [OfNat R 0] (v : Vector R n) : R :=
  dotProduct v v





end Vector

namespace Hex

namespace Matrix

variable {R : Type u} {n m k : Nat}

/-! # Flat-index arithmetic

Row-major flattening sends entry `(i, j)` to flat index `i * m + j`. These
helpers give the in-range bound and recover `i`, `j` from the flat index. -/

/-- The flat row-major index `i * m + j` of an in-range entry is in range. -/
theorem flatIdx_lt {i j : Nat} (hi : i < n) (hj : j < m) : i * m + j < n * m := by
  calc i * m + j < i * m + m := Nat.add_lt_add_left hj _
    _ = (i + 1) * m := by rw [Nat.succ_mul]
    _ ≤ n * m := Nat.mul_le_mul_right m hi

/-- Recover the row index from a flat index: `(i * m + j) / m = i` when `j < m`. -/
theorem flatIdx_div {i j m : Nat} (hj : j < m) : (i * m + j) / m = i := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hj, Nat.zero_add]

/-- Recover the column index from a flat index: `(i * m + j) % m = j` when
`j < m`. -/
theorem flatIdx_mod {i j m : Nat} (hj : j < m) : (i * m + j) % m = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- The row index recovered from any in-range flat index is in range. -/
theorem row_of_lt {n m : Nat} (p : Fin (n * m)) : p.val / m < n :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm n m ▸ p.isLt)

/-- The column index recovered from any in-range flat index is in range. -/
theorem col_of_lt {n m : Nat} (p : Fin (n * m)) : p.val % m < m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd p.isLt (by simp)
    · exact h
  exact Nat.mod_lt _ hm

/-! # Entry and row access

Both entry accessors and `getRow` read the flat buffer directly at `i * m + j`,
so a single-entry read is `O(1)` and never materializes a row. -/

/-- Entry access by a `Fin n × Fin m` index: the `O(1)` flat read. -/
instance _root_.Hex.Matrix.instGetElemProdFinTrue : GetElem (Matrix R n m) (Fin n × Fin m) R (fun _ _ => True) where
  getElem M p _ := M.data[p.1.val * m + p.2.val]'(flatIdx_lt p.1.isLt p.2.isLt)

/-- Entry access by a `Nat × Nat` index. -/
instance _root_.Hex.Matrix.instGetElemProdNatAndLtFstSnd : GetElem (Matrix R n m) (Nat × Nat) R (fun _ p => p.1 < n ∧ p.2 < m) where
  getElem M p h := M.data[p.1 * m + p.2]'(flatIdx_lt h.1 h.2)

/-- The `i`-th row of a matrix, materialized from the flat buffer. This copies the
`m` contiguous entries of row `i`; it is the computable row accessor compiled code
uses (single entries go through `M[(i, j)]`, which does not materialize a row). -/
@[inline, expose] def getRow (M : Matrix R n m) (i : Fin n) : Vector R m :=
  Hex.Vector.ofFn' fun j => M.data[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt)

/-- Row access `M[i]` for `i : Fin n`. **Deliberately `noncomputable`**: with the
flat (`Vector R (n*m)`) representation, materializing a whole row just to read it
— and especially `M[i][j]` to read one entry — is the wrong cost model. This
instance exists only so *proofs* may write `M[i]` / `M[i][j]`; executable code
must use the computable `getRow` for rows and `M[(i, j)]` (O(1)) for single
entries. Any compiled definition that reaches for `M[i]` will fail to compile,
which is the intended guard. -/
noncomputable instance _root_.Hex.Matrix.instGetElemFinVectorTrue : GetElem (Matrix R n m) (Fin n) (Vector R m) (fun _ _ => True) where
  getElem M i _ := getRow M i

/-- Row access by a `Nat` index. Also `noncomputable`; see the `Fin n` instance. -/
noncomputable instance _root_.Hex.Matrix.instGetElemNatVectorLt : GetElem (Matrix R n m) Nat (Vector R m) (fun _ i => i < n) where
  getElem M i h := getRow M ⟨i, h⟩

/-- The rows of a matrix as a vector of row-vectors, materialized from the flat
buffer. The only sanctioned way to observe the full row data; `O(n * m)`. -/
@[expose] def rows (M : Matrix R n m) : Vector (Vector R m) n :=
  Hex.Vector.ofFn' fun i => getRow M i

/-- Build a matrix from a vector of its rows, flattening into the row-major
backing buffer. -/
@[expose] def ofRows (v : Vector (Vector R m) n) : Matrix R n m :=
  ⟨Hex.Vector.ofFn' fun p : Fin (n * m) => (v[p.val / m]'(row_of_lt p))[p.val % m]'(col_of_lt p)⟩

/-- Build a matrix from an entry function, filling the flat backing buffer. -/
@[expose]
def ofFn (f : Fin n → Fin m → R) : Matrix R n m :=
  ⟨Hex.Vector.ofFn' fun p : Fin (n * m) =>
    f ⟨p.val / m, row_of_lt p⟩ ⟨p.val % m, col_of_lt p⟩⟩



/-! # Core reduction lemmas -/

/-- Row access `M[i]` normalizes to the computable `getRow M i`. -/
@[simp, grind =] theorem getElem_eq_getRow (M : Matrix R n m) (i : Fin n) : M[i] = getRow M i := rfl

/-- `Nat`-indexed row access normalizes to `getRow`. -/
@[simp, grind =] theorem getElem_nat_eq_getRow (M : Matrix R n m) (i : Nat) (h : i < n) :
    M[i]'h = getRow M ⟨i, h⟩ := rfl

/-- Reading entry `j` of `getRow M i` is the flat read at `i * m + j`. -/
@[grind =] theorem getElem_getRow (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (getRow M i)[j] = M.data[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt) := by
  simp [getRow]

/-- `Nat`-indexed form of `getElem_getRow`, for `Vector.ext` proofs. -/
theorem getElem_getRow_nat (M : Matrix R n m) (i : Fin n) {j : Nat} (hj : j < m) :
    (getRow M i)[j]'hj = M.data[i.val * m + j]'(flatIdx_lt i.isLt hj) := by
  simp [getRow]

/-- The pair entry access (computable, O(1)) agrees with the nested row-then-element
form. The nested form is the simp-normal form the entry lemmas are stated in. -/
@[simp, grind =] theorem getElem_pair_eq_nested (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    M[(i, j)] = M[i][j] := by
  rw [getElem_eq_getRow, getElem_getRow]; rfl







/-- `Nat`-pair entry access, normalized to the row lookup (concrete-index form).
The statement observes rows, not the backing buffer, so it is representation-
independent; the flat read behind it is `getElem_pair_data` below. -/
@[simp] theorem getElem_pair_nat (M : Matrix R n m) (p : Nat × Nat)
    (h : p.1 < n ∧ p.2 < m) : M[p]'h = (M.rows[p.1]'h.1)[p.2]'h.2 := by
  simp only [rows, Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn, getElem_getRow_nat]
  rfl



/-- Two matrices are equal when their flat backing buffers are equal. -/
theorem ext_data {M N : Matrix R n m} (h : M.data = N.data) : M = N := by
  cases M; cases N; simp_all

/-- Two matrices are equal when they agree entrywise. -/
theorem ext_getElem {M N : Matrix R n m}
    (h : ∀ (i : Fin n) (j : Fin m), M[i][j] = N[i][j]) : M = N := by
  apply ext_data
  apply Vector.ext
  intro p hp
  have hi : p / m < n := row_of_lt ⟨p, hp⟩
  have hj : p % m < m := col_of_lt ⟨p, hp⟩
  have hrec : (p / m) * m + p % m = p := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod p m
  have hh := h ⟨p / m, hi⟩ ⟨p % m, hj⟩
  rw [getElem_eq_getRow, getElem_eq_getRow, getElem_getRow, getElem_getRow] at hh
  simp only [hrec] at hh
  exact hh

/-- Entry access for a matrix built from an entry function. -/
@[grind =] theorem getElem_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    (ofFn f)[i][j] = f i j := by
  rw [getElem_eq_getRow, getElem_getRow]
  simp only [ofFn, Hex.Vector.getElem_ofFn']
  exact congr (congrArg f (Fin.ext (flatIdx_div j.isLt))) (Fin.ext (flatIdx_mod j.isLt))

/-- `getRow` on `ofRows` reduces to the underlying vector. -/
@[simp, grind =] theorem getRow_ofRows (v : Vector (Vector R m) n) (i : Fin n) :
    getRow (ofRows v) i = v[i] := by
  apply Vector.ext
  intro j hj
  rw [getElem_getRow_nat]
  simp only [ofRows, Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn, flatIdx_div hj, flatIdx_mod hj, Fin.getElem_fin]

/-- Entry access for a matrix built from a vector of rows. -/
@[grind =] theorem getElem_ofRows (v : Vector (Vector R m) n) (i : Fin n) (j : Fin m) :
    (ofRows v)[i][j] = v[i][j] := by
  rw [getElem_eq_getRow, getRow_ofRows]



/-- Two matrices are equal when their rows are equal. -/
@[ext] theorem ext {M N : Matrix R n m} (h : M.rows = N.rows) : M = N := by
  apply ext_getElem
  intro i j
  rw [getElem_eq_getRow, getElem_eq_getRow]
  have hrow : getRow M i = getRow N i := by
    have := congrArg (fun v => v[i.val]'(by simp) ) h
    simpa only [rows, Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn] using this
  rw [hrow]

/-- The `i`-th row of a matrix. -/
@[expose]
def row (M : Matrix R n m) (i : Fin n) : Vector R m :=
  getRow M i

/-- Entry access for a selected matrix row. -/
@[grind =] theorem getElem_row (M : Matrix R n m) (i : Fin n) (j : Fin m) :
    (row M i)[j] = M[i][j] := by
  rfl

/-- The `j`-th column of a matrix. -/
@[expose]
def col (M : Matrix R n m) (j : Fin m) : Vector R n :=
  Hex.Vector.ofFn' fun i => M[(i, j)]

/-- Entry access for a selected matrix column. -/
@[grind =] theorem getElem_col (M : Matrix R n m) (j : Fin m) (i : Fin n) :
    (col M j)[i] = M[i][j] := by
  simp [col]

/-! # In-place row mutation

The elementary operations update the single backing buffer in place when the
matrix is uniquely referenced. `writeRow` overwrites the `m` entries of one row;
`swapRows` exchanges two rows; both mutate the buffer through `Vector.set` /
`Vector.swap`, which reuse the store rather than copying it when the buffer is
owned. -/

/-- Overwrite the `m` entries of row `dst` of the flat buffer `d` with the entries
of `v`, in place when `d` is uniquely referenced. -/
@[inline]
def writeRow (d : Vector R (n * m)) (dst : Nat) (hdst : dst < n) (v : Vector R m) :
    Vector R (n * m) :=
  Fin.foldl m (fun d (t : Fin m) => d.set (dst * m + t.val) v[t] (flatIdx_lt hdst t.isLt)) d

/-- Replace row `dst` of `M` with the vector `v`. Linear in `M`: the matrix is
consumed, so the backing buffer is owned and `writeRow` updates it in place. -/
@[expose]
def setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨writeRow d dst.val dst.isLt v⟩

/-- Modification of row `i`. The matrix is consumed; the row is read out once
(a borrowed read into a fresh `m`-vector, before the buffer is written), `f` is
applied, and the result is written back through `writeRow`, in place when the
runtime sees the buffer uniquely referenced at the write. -/
@[expose, inline]
def modifyRow (M : Matrix R n m) (i : Nat) (f : Vector R m → Vector R m) : Matrix R n m :=
  if h : i < n then
    match M with
    | ⟨d⟩ =>
      let cur : Vector R m := Hex.Vector.ofFn' fun t : Fin m =>
        d[i * m + t.val]'(flatIdx_lt h t.isLt)
      ⟨writeRow d i h (f cur)⟩
  else M

/-- Swap rows `i` and `j`, in place when `M` is uniquely referenced. -/
@[expose, inline]
def swap (M : Matrix R n m) (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) : Matrix R n m :=
  match M with
  | ⟨d⟩ =>
    ⟨Fin.foldl m (fun d (t : Fin m) =>
      d.swap (i * m + t.val) (j * m + t.val) (flatIdx_lt hi t.isLt) (flatIdx_lt hj t.isLt)) d⟩







/-- Reading a row out of `rows` is `getRow`. The bridge between the
`Vector (Vector R m) n` observation and the flat accessor. -/
@[simp] theorem getElem_rows (M : Matrix R n m) (i : Nat) (hi : i < n) :
    M.rows[i]'hi = getRow M ⟨i, hi⟩ := by
  simp only [rows, Hex.Vector.ofFn'_eq_ofFn, Vector.getElem_ofFn]

/-! # Scatter characterizations of the in-place row loops

`writeRow` and the `swap` loop are `Fin.foldl`s of per-column single-index
updates into the flat buffer. Distinct fold steps touch distinct flat indices
(`i * m + t` determines `(i, t)` by `flatIdx_div` / `flatIdx_mod`), so each loop
is characterized by an entrywise read lemma, proved by the same
list-induction-over-`finRange` scheme as `Vector.getElem_finFoldl_modify`. -/

/-- A left fold of per-index `set`s leaves untouched every position not among
the written indices. -/
theorem foldl_set_ne {N : Nat} (idx : Fin m → Nat) (val : Fin m → R)
    (bd : ∀ t, idx t < N) {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idx t ≠ p) →
      (xs.foldl (fun d t => d.set (idx t) (val t) (bd t)) d0)[p]'hp = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_set_ne (bd x) hp (hne x List.mem_cons_self)]

/-- A left fold of per-index `set`s at injectively-indexed positions over a
`Nodup` list writes `val r` at position `idx r` for every member `r`. -/
theorem foldl_set_mem {N : Nat} (idx : Fin m → Nat) (val : Fin m → R)
    (bd : ∀ t, idx t < N) (hinj : ∀ a b : Fin m, idx a = idx b → a = b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.set (idx t) (val t) (bd t)) d0)[idx r]'(bd r) = val r := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [foldl_set_ne idx val bd (bd r) xs _ (fun t ht heq =>
        (List.nodup_cons.mp hnd).1 ((hinj t r heq) ▸ ht))]
      exact Vector.getElem_set_self (bd r)
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr']

/-- `List.finRange k` has no repeated indices (core-only proof; the Batteries
`nodup_finRange` is outside this Mathlib-free module's import closure). -/
theorem nodup_finRange (k : Nat) : (List.finRange k).Nodup := by
  induction k with
  | zero => simp
  | succ j ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [Fin.ext_iff],
      List.Pairwise.map _ (fun _ _ hab h => hab (Fin.succ_inj.mp h)) ih⟩

/-- Flat row-major indices are injective in the column for a fixed row. -/
 theorem _root_.Hex.Matrix.flatIdx_col_inj {i : Nat} :
    ∀ a b : Fin m, i * m + a.val = i * m + b.val → a = b :=
  fun _ _ h => Fin.ext (by omega)

/-- A left fold of per-index `modify`s leaves untouched every position not among
the modified indices. -/
 theorem _root_.Hex.Matrix.foldl_modify_ne {N : Nat} (idx : Fin m → Nat) (g : Fin m → R → R)
    {p : Nat} (hp : p < N) :
    ∀ (xs : List (Fin m)) (d0 : Vector R N), (∀ t ∈ xs, idx t ≠ p) →
      (xs.foldl (fun d t => d.modify (idx t) (g t)) d0)[p]'hp = d0[p]'hp := by
  intro xs
  induction xs with
  | nil => intro d0 _; rfl
  | cons x xs ih =>
    intro d0 hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht)),
      Vector.getElem_modify_of_ne hp (hne x List.mem_cons_self)]

/-- A left fold of per-index `modify`s at injectively-indexed positions over a
`Nodup` list applies `g r` to the original value at position `idx r` for every
member `r`. -/
 theorem _root_.Hex.Matrix.foldl_modify_mem {N : Nat} (idx : Fin m → Nat) (g : Fin m → R → R)
    (bd : ∀ t, idx t < N) (hinj : ∀ a b : Fin m, idx a = idx b → a = b) :
    ∀ (xs : List (Fin m)), xs.Nodup → ∀ (d0 : Vector R N) (r : Fin m), r ∈ xs →
      (xs.foldl (fun d t => d.modify (idx t) (g t)) d0)[idx r]'(bd r)
        = g r (d0[idx r]'(bd r)) := by
  intro xs
  induction xs with
  | nil => intro _ d0 r hr; simp at hr
  | cons x xs ih =>
    intro hnd d0 r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [_root_.Hex.Matrix.foldl_modify_ne idx g (bd r) xs _ (fun t ht heq =>
        (List.nodup_cons.mp hnd).1 ((hinj t r heq) ▸ ht))]
      exact Vector.getElem_modify_self (bd r)
    · rw [ih (List.nodup_cons.mp hnd).2 _ r hr',
        Vector.getElem_modify_of_ne (bd r) (fun heq =>
          (List.nodup_cons.mp hnd).1 ((hinj x r heq) ▸ hr'))]

/-- Entrywise read of `writeRow`: position `(r, t)` reads `v[t]` in the written
row and the old buffer everywhere else. -/
theorem getElem_writeRow (d : Vector R (n * m)) (dst : Nat) (hdst : dst < n) (v : Vector R m)
    {r t : Nat} (hr : r < n) (ht : t < m) :
    (writeRow d dst hdst v)[r * m + t]'(flatIdx_lt hr ht) =
      if r = dst then v[t]'ht else d[r * m + t]'(flatIdx_lt hr ht) := by
  unfold writeRow
  rw [Fin.foldl_eq_finRange_foldl]
  by_cases hrd : r = dst
  · subst hrd
    rw [if_pos rfl]
    exact foldl_set_mem (fun s : Fin m => r * m + s.val) (fun s => v[s])
      (fun s => flatIdx_lt hr s.isLt) _root_.Hex.Matrix.flatIdx_col_inj
      (List.finRange m) (nodup_finRange m) d ⟨t, ht⟩ (List.mem_finRange _)
  · rw [if_neg hrd]
    exact foldl_set_ne (fun s : Fin m => dst * m + s.val) (fun s => v[s])
      (fun s => flatIdx_lt hdst s.isLt) (flatIdx_lt hr ht)
      (List.finRange m) d (fun s _ heq => by
        have hds : (dst * m + s.val) / m = dst := flatIdx_div s.isLt
        have hrt : (r * m + t) / m = r := flatIdx_div ht
        rw [heq, hrt] at hds
        exact hrd hds)

@[simp, grind =] theorem rows_setRow (M : Matrix R n m) (dst : Fin n) (v : Vector R m) :
    (setRow M dst v).rows = M.rows.set dst v := by
  apply Vector.ext
  intro r hr
  rw [Vector.getElem_set, getElem_rows]
  apply Vector.ext
  intro t ht
  rw [getElem_getRow_nat]
  show (writeRow M.data dst.val dst.isLt v)[r * m + t]'(flatIdx_lt hr ht) = _
  rw [getElem_writeRow M.data dst.val dst.isLt v hr ht]
  by_cases hrd : r = dst.val
  · rw [if_pos hrd, if_pos hrd.symm]
  · rw [if_neg hrd, if_neg (fun h => hrd h.symm), getElem_rows, getElem_getRow_nat]





/-- In-place per-entry update of row `i`: entry `t` becomes `g t` applied to its
old value, written directly into the flat buffer with **no row
materialization**. This is the per-entry engine the elementary row operations
(`rowScale`, `rowAdd`) and the Bareiss row elimination build on: unlike
`modifyRow`, whose whole-row function forces a row copy-out and copy-back, each
entry here is a single in-place `Vector.modify` of the backing buffer when the
matrix is uniquely referenced. -/
@[expose, inline]
def modifyEntries (M : Matrix R n m) (i : Nat) (g : Fin m → R → R) : Matrix R n m :=
  if _h : i < n then
    match M with
    | ⟨d⟩ => ⟨Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d⟩
  else M

/-- Entrywise read of `modifyEntries`: row `i` gets `g` applied entrywise, every
other row is unchanged. -/
@[grind =] theorem getElem_modifyEntries (M : Matrix R n m) (i : Nat) (g : Fin m → R → R)
    (r : Fin n) (c : Fin m) :
    (modifyEntries M i g)[r][c] = if r.val = i then g c M[r][c] else M[r][c] := by
  obtain ⟨d⟩ := M
  by_cases h : i < n
  · have hred : modifyEntries (⟨d⟩ : Matrix R n m) i g =
        ⟨Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d⟩ := by
      simp only [modifyEntries, dif_pos h]
    rw [hred, getElem_eq_getRow, getElem_getRow, getElem_eq_getRow, getElem_getRow]
    show (Fin.foldl m (fun d t => d.modify (i * m + t.val) (g t)) d)[r.val * m + c.val]'_ = _
    rw [Fin.foldl_eq_finRange_foldl]
    by_cases hri : r.val = i
    · subst hri
      rw [if_pos rfl]
      exact _root_.Hex.Matrix.foldl_modify_mem (fun t : Fin m => r.val * m + t.val) g
        (fun t => flatIdx_lt r.isLt t.isLt) _root_.Hex.Matrix.flatIdx_col_inj
        (List.finRange m) (nodup_finRange m) d c (List.mem_finRange _)
    · rw [if_neg hri]
      exact _root_.Hex.Matrix.foldl_modify_ne (fun t : Fin m => i * m + t.val) g
        (flatIdx_lt r.isLt c.isLt) (List.finRange m) d (fun t _ heq => by
          have h1 : (i * m + t.val) / m = i := flatIdx_div t.isLt
          have h2 : (r.val * m + c.val) / m = r.val := flatIdx_div c.isLt
          rw [heq, h2] at h1
          exact hri h1)
  · have hred : modifyEntries (⟨d⟩ : Matrix R n m) i g = ⟨d⟩ := by
      simp only [modifyEntries, dif_neg h]
    rw [hred, if_neg (fun heq => h (by rw [← heq]; exact r.isLt))]

/-- The transpose of a dense matrix. -/
@[expose]
def transpose (M : Matrix R n m) : Matrix R m n :=
  ofFn fun i j => M[(j, i)]

/-- Entry access for the transpose of a dense matrix. -/
@[grind =] theorem getElem_transpose (M : Matrix R n m) (i : Fin m) (j : Fin n) :
    (transpose M)[i][j] = M[j][i] := by
  rw [transpose, getElem_ofFn, getElem_pair_eq_nested]







/-- The all-zero matrix. -/
@[expose]
protected def zero (n m : Nat) [OfNat R 0] : Matrix R n m :=
  ofFn fun _ _ => 0

instance _root_.Hex.Matrix.instZeroOfOfNatOfNatNat [OfNat R 0] : Zero (Matrix R n m) where
  zero := Matrix.zero n m







/-- The identity matrix. -/
@[expose]
protected def identity (n : Nat) [OfNat R 0] [OfNat R 1] : Matrix R n n :=
  ofFn fun i j => if i = j then 1 else 0

/-- Entrywise matrix addition. -/
@[expose]
protected def add [Add R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] + B[(i, j)]

instance _root_.Hex.Matrix.instAdd [Add R] : Add (Matrix R n m) where
  add := Matrix.add

/-- Entrywise matrix negation. -/
@[expose]
protected def neg [Neg R] (A : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => -A[(i, j)]

instance _root_.Hex.Matrix.instNeg [Neg R] : Neg (Matrix R n m) where
  neg := Matrix.neg

/-- Entrywise matrix subtraction. -/
@[expose]
protected def sub [Sub R] (A B : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => A[(i, j)] - B[(i, j)]

instance _root_.Hex.Matrix.instSub [Sub R] : Sub (Matrix R n m) where
  sub := Matrix.sub







/-- Multiply a matrix by a column vector. -/
@[expose]
def mulVec [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (v : Vector R m) :
    Vector R n :=
  Hex.Vector.ofFn' fun i => (row M i).dotProduct v

/-- The `j`-th row of `transpose M` is the `j`-th column of `M`. -/
@[simp, grind =] theorem row_transpose (M : Matrix R n m) (j : Fin m) :
    row (transpose M) j = col M j := by
  ext k hk
  show (row (transpose M) j)[(⟨k, hk⟩ : Fin n)] = (col M j)[(⟨k, hk⟩ : Fin n)]
  rw [getElem_row, getElem_transpose, getElem_col]



/--
Multiply two matrices, using the naive algorithm.

This reads each column `col N j` and is the reference definition the entry
lemmas reason about. Compiled code uses the implementation below, which
transposes `N` once so each column is materialized a single time instead of
being rebuilt for every row of `M`; `Hex.Matrix.mul_eq_impl` selects
`Hex.Matrix.mulImpl` for compiled code.

Strassen-Winograd multiplication, with a customizable base kernel for small
sizes, is available as `Hex.Matrix.mulStrassen`, with equality proved by
`Hex.Matrix.mulStrassen_eq_mul`. It cannot replace this definition
through `@[csimp]`: the Winograd schedule subtracts blocks and therefore needs
`[Sub R]`, while naive multiplication does not. Callers over a ring opt into
the Strassen-Winograd algorithm explicitly.
-/
@[expose]
noncomputable def mul [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  ofFn fun i j => (row M i).dotProduct (col N j)

/-- Cache-friendly implementation of {name}`Hex.Matrix.mul`: transpose `N` once (turning its columns
into contiguous rows), materialize the transposed rows once, then take row-by-row
dot products, so each column is built a single time rather than once per row of
`M`. Swapped in for compiled code by the `@[csimp]` lemma; `mul` stays the
column-based reference form for proofs. -/
@[expose]
def mulImpl [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) (N : Matrix R m k) :
    Matrix R n k :=
  let Ntr := N.transpose.rows
  ofRows (Vector.ofFn fun i =>
    let ri := getRow M i
    Vector.ofFn fun j => ri.dotProduct Ntr[j])

@[csimp] theorem mul_eq_mulImpl : @mul = @mulImpl := by
  funext R n m k iMul iAdd iZero M N
  apply ext_getElem
  intro i j
  show (mul M N)[i][j] = (mulImpl M N)[i][j]
  rw [mul, getElem_ofFn]
  have h : (mulImpl M N)[i][j]
      = (getRow M i).dotProduct (getRow N.transpose j) := by
    show (ofRows (Vector.ofFn fun a : Fin n =>
        Vector.ofFn fun b : Fin k => (getRow M a).dotProduct (N.transpose.rows[b])))[i][j]
      = (getRow M i).dotProduct (getRow N.transpose j)
    rw [getElem_ofRows]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, getElem_rows]
  rw [h, show getRow N.transpose j = row (transpose N) j from rfl, row_transpose]
  rfl

instance _root_.Hex.Matrix.instHMulVectorOfMulOfAddOfOfNatOfNatNat [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Vector R m) (Vector R n) where
  hMul := mulVec

instance _root_.Hex.Matrix.instHMulOfMulOfAddOfOfNatOfNatNat [Mul R] [Add R] [OfNat R 0] : HMul (Matrix R n m) (Matrix R m k) (Matrix R n k) where
  hMul := mul

/-- Homogeneous multiplication on square matrices, agreeing with the
heterogeneous `HMul`. This is the `Mul` instance Mathlib's `Semiring`/`Ring`
structures build on; see `HexMatrixTheory`. -/
instance _root_.Hex.Matrix.instMulOfAddOfOfNatOfNatNat [Mul R] [Add R] [OfNat R 0] : Mul (Matrix R n n) where
  mul := mul

/-- Entry characterization for matrix-vector multiplication. -/
@[grind =] theorem getElem_mulVec [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (v : Vector R m) (i : Fin n) :
    (M * v)[i] = (row M i).dotProduct v := by
  show (mulVec M v)[i] = (row M i).dotProduct v
  simp [mulVec]

/-- Multiply a row vector by a matrix, `v * M`. Equal to `transpose M * v`; the
`j`-th entry is `∑ i, M[i][j] * v[i]`, the combination of the rows of `M` with
coefficients `v`. -/
@[expose]
def vecMul [Mul R] [Add R] [OfNat R 0] (v : Vector R n) (M : Matrix R n m) :
    Vector R m :=
  transpose M * v

instance _root_.Hex.Matrix.instHMulVectorOfMulOfAddOfOfNatOfNatNat_1 [Mul R] [Add R] [OfNat R 0] : HMul (Vector R n) (Matrix R n m) (Vector R m) where
  hMul := vecMul

/-- Entry characterization for vector-matrix multiplication. -/
@[grind =] theorem getElem_vecMul [Mul R] [Add R] [OfNat R 0]
    (v : Vector R n) (M : Matrix R n m) (j : Fin m) :
    (v * M)[j] = (col M j).dotProduct v := by
  show (transpose M * v)[j] = (col M j).dotProduct v
  rw [getElem_mulVec, row_transpose]















@[simp, grind =] theorem rows_modifyRow (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) : (modifyRow M i f).rows = M.rows.modify i f := by
  obtain ⟨d⟩ := M
  by_cases h : i < n
  · have hred : modifyRow (⟨d⟩ : Matrix R n m) i f =
        setRow ⟨d⟩ ⟨i, h⟩ (f (getRow ⟨d⟩ ⟨i, h⟩)) := by
      simp only [modifyRow, dif_pos h, setRow]
      rfl
    rw [hred, rows_setRow, Vector.modify_eq_set _ _ _ h, getElem_rows]
  · have hred : modifyRow (⟨d⟩ : Matrix R n m) i f = ⟨d⟩ := by
      simp only [modifyRow, dif_neg h]
    rw [hred]
    apply Vector.ext
    intro r hr
    rw [Vector.getElem_modify hr, if_neg (fun heq => h (by omega))]















/-- Indexed row map: replace row `i` by `f i (row i)` for every `i`, threading
`M` through a `Fin.foldl` of per-row `modifyRow`s. No intermediate index list is
allocated. The whole-row function forces each visited row to be materialized and
written back (see `modifyRow`); per-entry updates should prefer the
copy-free `modifyEntries` / `setCol` / `modifyCol`. -/
@[expose, inline]
def mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) : Matrix R n m :=
  Fin.foldl n (fun M i => M.modifyRow i.val (f i)) M

/-- The row data of `mapRowsIdx` is the corresponding `Fin.foldl` of `Vector.modify`s. -/
theorem rows_mapRowsIdx (M : Matrix R n m) (f : Fin n → Vector R m → Vector R m) :
    (mapRowsIdx M f).rows = Fin.foldl n (fun d i => d.modify i.val (f i)) M.rows := by
  unfold mapRowsIdx
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl]
  generalize List.finRange n = xs
  induction xs generalizing M with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih (M.modifyRow x.val (f x)), rows_modifyRow]

/-- Row `r` of `mapRowsIdx M f` is `f r` applied to the original row `r`. -/
@[simp, grind =] theorem getRow_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) :
    getRow (mapRowsIdx M f) r = f r (getRow M r) := by
  have h := Vector.getElem_finFoldl_modify M.rows (fun i d => f i d) r
  rw [← rows_mapRowsIdx, getElem_rows, getElem_rows, Fin.eta] at h
  exact h

/-- Entry `(r, c)` of `mapRowsIdx M f` reads from the updated row `f r (row r)`. -/
@[grind =] theorem getElem_mapRowsIdx (M : Matrix R n m)
    (f : Fin n → Vector R m → Vector R m) (r : Fin n) (c : Fin m) :
    (mapRowsIdx M f)[r][c] = (f r (getRow M r))[c] := by
  rw [getElem_eq_getRow, getRow_mapRowsIdx]

/-- Replace column `dst` of `M` with the entry function `v`. In place: one
single-entry `Vector.set` of the flat buffer per row (`O(n)` writes total),
reusing the backing store when `M` is uniquely referenced, rather than
materializing any row or rebuilding the matrix. -/
@[expose]
def setCol (M : Matrix R n m) (dst : Fin m) (v : Fin n → R) : Matrix R n m :=
  match M with
  | ⟨d⟩ =>
    ⟨Fin.foldl n (fun d (i : Fin n) =>
      d.set (i.val * m + dst.val) (v i) (flatIdx_lt i.isLt dst.isLt)) d⟩









/-- In-place per-entry column modify: replace each entry `M[i][dst]` by
`g i M[i][dst]`, every other column unchanged. In place: one single-entry
`Vector.modify` of the flat buffer per row, analogous to `setCol`. -/
@[expose]
def modifyCol (M : Matrix R n m) (dst : Fin m) (g : Fin n → R → R) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨Fin.foldl n (fun d (i : Fin n) => d.modify (i.val * m + dst.val) (g i)) d⟩





/-- Scalar action on a matrix, delegated to the flat backing buffer. The single
sanctioned `SMul` instance for matrices: the theory layer reuses it rather
than declaring its own, so there is no overlapping instance. -/
instance _root_.Hex.Matrix.instSMul {S : Type v} [SMul S R] : SMul S (Matrix R n m) where
  smul c M := ⟨c • M.data⟩







end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Elementary row and column operations.

This module contains the primitive executable row/column operations and their
entrywise access lemmas. Algebraic preservation theorems for multiplication and
inverse tracking live downstream in `HexRowReduce.RowEchelon`.
-/

namespace Hex

universe u

namespace Matrix





/-- Swap rows `i` and `j` in a dense matrix.

Implemented with `Vector.swap`, which updates the dense backing store in place
when `M` is uniquely referenced, rather than reading both rows and writing them
back through two `set`s (which forces a copy of the outer vector). -/
@[expose]
def rowSwap (M : Matrix R n m) (i j : Fin n) : Matrix R n m :=
  M.swap i j



















/-- Replace row `dst` by `row dst + c * row src`.

The source row is read once into `rsrc` (one contiguous copy, a borrowed read
taken before the write); the subsequent {name}`Hex.Matrix.modifyEntries` then holds the only
live reference to the buffer and updates the `dst` row's entries in place when
the runtime sees it uniquely referenced, with no destination-row
materialization. -/
@[expose]
def rowAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin n) (c : R) : Matrix R n m :=
  let rsrc := getRow M src
  M.modifyEntries dst.val fun k x => x + c * rsrc[k]





















/-- Replace column `dst` by `col dst + c * col src`.

The source column is read once into `csrc` (one contiguous copy, a borrowed read
taken before the write); the subsequent `modifyCol` then holds the only live
reference to the buffer and updates the `dst` column entry of each row in place —
one single-entry `Vector.modify` of the flat buffer per row (`O(n)` writes
total) — when the runtime sees it uniquely referenced, with no row
materialization; the source column is first snapshotted into one owned `O(n)`
vector via borrowed reads. This replaces the former `mapRows` pass, which
materialized and reflattened every row. -/
@[expose]
def colAdd [Mul R] [Add R] (M : Matrix R n m) (src dst : Fin m) (c : R) : Matrix R n m :=
  let csrc := M.col src
  M.modifyCol dst fun i x => x + c * csrc[i]























































end Matrix

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Algebraic properties of dense vector dot products.
-/

universe u v

namespace List



end List

namespace Vector









/-- Dot product is additive in its left argument. -/
theorem dotProduct_add_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  simp only [dotProduct]
  rw [show (List.finRange n).foldl
        (fun acc i => acc + (u + v)[i] * w[i]) 0 =
      (List.finRange n).foldl
        (fun acc i => acc + (u[i] * w[i] + v[i] * w[i])) 0 from ?_]
  · rw [List.foldl_add_add (xs := List.finRange n)
        (f := fun i => u[i] * w[i])
        (g := fun i => v[i] * w[i])]
  · apply List.foldl_add_congr
    intro i _
    have hentry : (u + v)[i] = u[i] + v[i] := by
      change (u + v)[i.val] = u[i.val] + v[i.val]
      rw [Vector.getElem_add]
    rw [hentry]
    grind

/-- Dot product is homogeneous in its left argument. -/
theorem dotProduct_smul_left {R : Type u} [Lean.Grind.Ring R]
    (c : R) (u w : Vector R n) :
    dotProduct (c • u) w = c * dotProduct u w := by
  simp only [dotProduct]
  rw [← List.foldl_add_mul_left (xs := List.finRange n)
        (f := fun i => u[i] * w[i]) (c := c)]
  have hzero : c * (0 : R) = 0 := by
    grind
  rw [hzero]
  apply List.foldl_add_congr
  intro i _
  -- `getElem_smul` rewrites the entry to `c • u[i]`, which is defeq to `c * u[i]`
  -- for the scalar action on the coefficient ring.
  have hentry : (c • u)[i] = c * u[i] := by
    simp only [Fin.getElem_fin, Vector.getElem_smul]; rfl
  rw [hentry]
  exact Lean.Grind.Semiring.mul_assoc c u[i] w[i]

/-- Dot product is symmetric over a commutative coefficient type. -/
theorem dotProduct_comm {R : Type u} [Lean.Grind.CommRing R]
    (u v : Vector R n) :
    dotProduct u v = dotProduct v u := by
  simp only [dotProduct]
  apply List.foldl_add_congr
  intro i _
  grind





/-- Dot product is additive over subtraction in its left argument. -/
theorem dotProduct_sub_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) :
    dotProduct (u - v) w = dotProduct u w - dotProduct v w := by
  rw [show u - v = u + (-1 : R) • v by
    ext i hi
    let ii : Fin n := ⟨i, hi⟩
    show (u - v)[ii] = (u + (-1 : R) • v)[ii]
    change (u - v)[i] = (u + (-1 : R) • v)[i]
    rw [Vector.getElem_sub, Vector.getElem_add, Vector.getElem_smul]
    change u[i] - v[i] = u[i] + (-1 : R) * v[i]
    grind]
  rw [dotProduct_add_left, dotProduct_smul_left]
  change dotProduct u w + (-1 : R) * dotProduct v w =
    dotProduct u w - dotProduct v w
  grind



/-- Dot product distributes over subtracting a scalar multiple in the left argument. -/
theorem dotProduct_sub_smul_left {R : Type u} [Lean.Grind.Ring R]
    (u v w : Vector R n) (c : R) :
    dotProduct (u - c • v) w = dotProduct u w - c * dotProduct v w := by
  rw [dotProduct_sub_left, dotProduct_smul_left]





end Vector

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


