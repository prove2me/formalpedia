-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Degree
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Degree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:13.012209+00:00
-- url     : https://prove2.me/theorems/ef97db3e-9c06-4a27-93aa-1abf6c06906a
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree — Polynomial degree bounds in an arbitrary size measure
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These bounds and their arithmetic are independent of machine computability.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.DegreeBounded`: a bound by a constant times `(size + 1) ^ d`.
--
--   ### Main results
--
--   * `DegreeBounded.add_max`, `DegreeBounded.mul`, `DegreeBounded.comp`: arithmetic of degree bounds.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Degree`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/ResourceBounds/Degree.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (independent growth-bound algebra)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_PolynomialBound_Closure
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Degree` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial degree bounds in an arbitrary size measure

These bounds and their arithmetic are independent of machine computability.

## Main definitions

* `Turing.MultiTapeTM.DegreeBounded`: a bound by a constant times `(size + 1) ^ d`.

## Main results

* `DegreeBounded.add_max`, `DegreeBounded.mul`, `DegreeBounded.comp`: arithmetic of degree bounds.
-/

namespace Turing.MultiTapeTM

/-! ### Bounds of a given degree -/

/-- `u` is bounded by a polynomial of degree `d` in `size`. -/
@[expose] public def DegreeBounded {α : Type*} (size u : α → ℕ) (d : ℕ) : Prop :=
  ∃ c, ∀ a, u a ≤ c * (size a + 1) ^ d

namespace DegreeBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ} {d d₁ d₂ : ℕ}

public theorem mono (h : DegreeBounded size v d) (huv : ∀ a, u a ≤ v a) :
    DegreeBounded size u d :=
  let ⟨c, hv⟩ := h
  ⟨c, fun a => (huv a).trans (hv a)⟩

public theorem mono_deg (h : DegreeBounded size u d₁) (hd : d₁ ≤ d₂) : DegreeBounded size u d₂ :=
  let ⟨c, hu⟩ := h
  ⟨c, fun a => (hu a).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) hd))⟩

public theorem const (k : ℕ) : DegreeBounded size (fun _ => k) d :=
  ⟨k, fun _ => Nat.le_mul_of_pos_right k (Nat.pow_pos (Nat.succ_pos _))⟩

public theorem self : DegreeBounded size size 1 :=
  ⟨1, fun _ => by simp⟩

public theorem add (hu : DegreeBounded size u d) (hv : DegreeBounded size v d) :
    DegreeBounded size (fun a => u a + v a) d :=
  let ⟨c₁, h₁⟩ := hu
  let ⟨c₂, h₂⟩ := hv
  ⟨c₁ + c₂, fun a => (add_le_add (h₁ a) (h₂ a)).trans_eq (Nat.add_mul _ _ _).symm⟩

/-- Adding bounds of different degrees gives a bound of their maximum degree. -/
public theorem add_max (hu : DegreeBounded size u d₁) (hv : DegreeBounded size v d₂) :
    DegreeBounded size (fun a => u a + v a) (max d₁ d₂) :=
  (hu.mono_deg (le_max_left _ _)).add (hv.mono_deg (le_max_right _ _))

public theorem smul (k : ℕ) (hu : DegreeBounded size u d) :
    DegreeBounded size (fun a => k * u a) d :=
  let ⟨c, h⟩ := hu
  ⟨k * c, fun a => (Nat.mul_le_mul_left k (h a)).trans_eq (Nat.mul_assoc _ _ _).symm⟩

public theorem add_const (k : ℕ) (hu : DegreeBounded size u d) :
    DegreeBounded size (fun a => u a + k) d :=
  hu.add (const k)

public theorem mul (hu : DegreeBounded size u d₁) (hv : DegreeBounded size v d₂) :
    DegreeBounded size (fun a => u a * v a) (d₁ + d₂) :=
  let ⟨c₁, h₁⟩ := hu
  let ⟨c₂, h₂⟩ := hv
  ⟨c₁ * c₂, fun a => (Nat.mul_le_mul (h₁ a) (h₂ a)).trans_eq (by rw [Nat.pow_add]; ring)⟩

/-- Substitution: if `v` has degree `d₂` in `size'` and `size' ∘ g` has degree `d₁` in `size`,
then `v ∘ g` has degree `d₁ * d₂` in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : DegreeBounded size' v d₂)
    (hg : DegreeBounded size (fun a => size' (g a)) d₁) :
    DegreeBounded size (fun a => v (g a)) (d₁ * d₂) :=
  let ⟨c₁, h₁⟩ := hg
  let ⟨c₂, h₂⟩ := hv
  ⟨c₂ * (c₁ + 1) ^ d₂, fun a => by
    have h : size' (g a) + 1 ≤ (c₁ + 1) * (size a + 1) ^ d₁ := by
      have := h₁ a
      dsimp only at this
      have := Nat.one_le_pow d₁ (size a + 1) (Nat.succ_pos _)
      rw [Nat.add_one_mul]
      omega
    refine (h₂ (g a)).trans ((Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left h d₂)).trans_eq ?_)
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]⟩

end DegreeBounded

namespace DegreeBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ} {d d₁ d₂ : ℕ}

public theorem polyBounded (h : DegreeBounded size u d) : PolyBounded size u :=
  let ⟨c, hu⟩ := h
  .of_forall_le c d hu

end DegreeBounded

end Turing.MultiTapeTM


