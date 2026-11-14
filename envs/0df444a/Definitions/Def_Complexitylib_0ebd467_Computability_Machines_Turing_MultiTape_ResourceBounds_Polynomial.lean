-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:55.095443+00:00
-- url     : https://prove2.me/theorems/d85dc2b2-6df6-4f5e-a82b-8c882914b737
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Polynomial growth relative to an arbitrary input-size function, without machine predicates.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/ResourceBounds/Polynomial.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (independent polynomial-growth algebra)
-- Moved unchanged from Complexity/PolyTime; retain this home when resynchronizing vendored rules.

public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Closure

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! Polynomial growth relative to an arbitrary input-size function, without machine predicates. -/

namespace Turing.MultiTapeTM

/-! ### Polynomial bounds -/

-- vendored: express size-dependent bounds through cslib's `PolynomiallyBounded` and reuse
-- its closure rules; `exists_le` and `of_forall_le` preserve the original explicit-bound contract.
/-- `u` is bounded by a polynomially bounded function of `size`. This adapts
`Cslib.PolynomiallyBounded` to arbitrary inputs; it does not assert computability. -/
@[expose] public def PolyBounded {α : Type*} (size u : α → ℕ) : Prop :=
  ∃ bound : ℕ → ℕ, Cslib.PolynomiallyBounded bound ∧ ∀ a, u a ≤ bound (size a)

namespace PolyBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ}

/-- Recover an explicit polynomial bound valid at every input, including size zero. -/
public theorem exists_le (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hbound, h⟩ := h
  obtain ⟨c, d, hp⟩ := Cslib.polynomiallyBounded_iff_le.mp hbound
  exact ⟨c, d, fun a => (h a).trans (hp (size a))⟩

/-- Supply an explicit polynomial bound in the input size. -/
public theorem of_forall_le (c d : ℕ) (h : ∀ a, u a ≤ c * (size a + 1) ^ d) :
    PolyBounded size u :=
  ⟨_, Cslib.PolynomiallyBounded.of_forall_le c d (fun _ => le_rfl), h⟩

/-- Apply a polynomial bound to any input-size function. -/
public theorem of_polynomiallyBounded (size : α → ℕ) {bound : ℕ → ℕ}
    (hbound : Cslib.PolynomiallyBounded bound) : PolyBounded size (fun a => bound (size a)) :=
  ⟨bound, hbound, fun _ => le_rfl⟩

/-- With the identity size, the adapter gives CSLib's polynomial-growth predicate. -/
public theorem polynomiallyBounded {f : ℕ → ℕ} (h : PolyBounded id f) :
    Cslib.PolynomiallyBounded f :=
  let ⟨_, hbound, h⟩ := h
  hbound.mono_of_le h

public theorem mono (h : PolyBounded size v) (huv : ∀ a, u a ≤ v a) : PolyBounded size u :=
  let ⟨bound, hbound, hv⟩ := h
  ⟨bound, hbound, fun a => (huv a).trans (hv a)⟩

public theorem const (k : ℕ) : PolyBounded size fun _ => k :=
  of_polynomiallyBounded size (.const k)

public theorem self : PolyBounded size size :=
  of_polynomiallyBounded size .id

public theorem add (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a + v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.add hq, fun a => Nat.add_le_add (hu a) (hv a)⟩

public theorem mul (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size fun a => u a * v a :=
  let ⟨_, hp, hu⟩ := hu
  let ⟨_, hq, hv⟩ := hv
  ⟨_, hp.mul hq, fun a => Nat.mul_le_mul (hu a) (hv a)⟩

public theorem pow (hu : PolyBounded size u) (d : ℕ) :
    PolyBounded size fun a => u a ^ d :=
  let ⟨_, hp, hu⟩ := hu
  ⟨_, hp.pow d, fun a => Nat.pow_le_pow_left (hu a) d⟩

/-- Substitution: if `v` is bounded by a polynomial in `size'` and `size' ∘ g` by a polynomial in
`size`, then `v ∘ g` is bounded by a polynomial in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : PolyBounded size' v)
    (hg : PolyBounded size fun a => size' (g a)) : PolyBounded size fun a => v (g a) := by
  obtain ⟨c, d, hv⟩ := hv.exists_le
  obtain ⟨bound, hbound, hg⟩ := hg
  refine ⟨fun n => c * (bound n + 1) ^ d, by fun_prop, fun a => ?_⟩
  exact (hv (g a)).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_left (Nat.add_le_add_right (hg a) 1) d))

end PolyBounded

end Turing.MultiTapeTM


