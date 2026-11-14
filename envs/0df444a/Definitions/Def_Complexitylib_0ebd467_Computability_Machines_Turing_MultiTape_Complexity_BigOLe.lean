-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigOLe
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigOLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:39.751071+00:00
-- url     : https://prove2.me/theorems/7c9c5876-31cc-4fc7-9722-ab68d908b887
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigOLe — Pointwise bounds up to constants
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigOLe` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `u ≼ v` says that `u a ≤ c * (v a + 1)` for some constant `c` and every `a`: the bounds of
--   `Turing.MultiTapeTM.ComputableTidilyInO`. The relation is a preorder, closed under sums, constant
--   factors, products and powers of padded bounds, and composition. The tactic `bigO` splits a goal
--   `u ≼ v` along sums, case distinctions, constant factors and powers of `u` and closes the parts by
--   assumption, through two assumptions, by reflexivity or as constants.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.BigOLe`: pointwise bounds up to constants, with the notation `u ≼ v`.
--
--   **Contents.** The module is published as a whole: 18 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigOLe`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigOLe.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigOLe` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Pointwise bounds up to constants

`u ≼ v` says that `u a ≤ c * (v a + 1)` for some constant `c` and every `a`: the bounds of
`Turing.MultiTapeTM.ComputableTidilyInO`. The relation is a preorder, closed under sums, constant
factors, products and powers of padded bounds, and composition. The tactic `bigO` splits a goal
`u ≼ v` along sums, case distinctions, constant factors and powers of `u` and closes the parts by
assumption, through two assumptions, by reflexivity or as constants.

## Main definitions

* `Turing.MultiTapeTM.BigOLe`: pointwise bounds up to constants, with the notation `u ≼ v`.
-/

namespace Turing.MultiTapeTM

/-- `u ≼ v`: `u` is pointwise at most a constant times `v + 1`. -/
@[expose] public def BigOLe {α : Type*} (u v : α → ℕ) : Prop := ∃ c, ∀ a, u a ≤ c * (v a + 1)

@[inherit_doc] scoped infix:50 " ≼ " => BigOLe

namespace BigOLe

variable {α β : Type*} {u v w u' v' : α → ℕ}

public theorem of_le (h : ∀ a, u a ≤ v a) : u ≼ v :=
  ⟨1, fun a => by have := h a; omega⟩

/-- A linear pointwise bound. -/
public theorem of_le_linear (k k' : ℕ) (h : ∀ a, u a ≤ k * v a + k') : u ≼ v :=
  ⟨k + k', fun a => by nlinarith [h a]⟩

@[refl] public theorem refl (u : α → ℕ) : u ≼ u := of_le fun _ => le_rfl

public theorem trans (h₁ : u ≼ v) (h₂ : v ≼ w) : u ≼ w := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  exact ⟨c * (d + 1), fun a => by nlinarith [hc a, hd a, Nat.zero_le (c * (w a + 1))]⟩

public instance : @Trans (α → ℕ) (α → ℕ) (α → ℕ) BigOLe BigOLe BigOLe := ⟨trans⟩

/-- A bound followed by a larger function. -/
public theorem trans_le (h : u ≼ v) (h' : ∀ a, v a ≤ w a) : u ≼ w := h.trans (of_le h')

public theorem const (k : ℕ) (v : α → ℕ) : (fun _ => k) ≼ v :=
  ⟨k, fun a => by nlinarith⟩

public theorem add (h₁ : u ≼ w) (h₂ : v ≼ w) : (fun a => u a + v a) ≼ w := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  exact ⟨c + d, fun a => by nlinarith [hc a, hd a]⟩

/-- Case distinctions, within the larger of the bounds. -/
public theorem ite (c : α → Prop) [DecidablePred c] (h₁ : u ≼ w) (h₂ : v ≼ w) :
    (fun a => if c a then u a else v a) ≼ w := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  refine ⟨k + l, fun a => ?_⟩
  dsimp only
  split_ifs <;> nlinarith [hk a, hl a]

public theorem const_mul (k : ℕ) (h : u ≼ v) : (fun a => k * u a) ≼ v := by
  obtain ⟨c, hc⟩ := h
  exact ⟨k * c, fun a => by nlinarith [hc a]⟩

public theorem comp (h : u ≼ v) (g : β → α) : (fun b => u (g b)) ≼ fun b => v (g b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun b => hc (g b)⟩

/-- A factor bounded by a positive function. -/
public theorem mul_left (u : α → ℕ) (h : v ≼ w) (hw : ∀ a, 1 ≤ w a) :
    (fun a => u a * v a) ≼ fun a => u a * w a := by
  obtain ⟨c, hc⟩ := h
  refine ⟨2 * c, fun a => ?_⟩
  have h₁ : v a ≤ 2 * c * w a := (hc a).trans (by nlinarith [hw a])
  calc u a * v a ≤ u a * (2 * c * w a) := Nat.mul_le_mul_left _ h₁
    _ ≤ 2 * c * (u a * w a + 1) := by nlinarith

/-- Products, of padded bounds: a bound by `0` says nothing about a factor. -/
public theorem mul (h₁ : u ≼ u') (h₂ : v ≼ v') :
    (fun a => u a * v a) ≼ fun a => (u' a + 1) * (v' a + 1) := by
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  exact ⟨c * d, fun a => by nlinarith [Nat.mul_le_mul (hc a) (hd a)]⟩

/-- Powers, of padded bounds. -/
public theorem pow (h : u ≼ v) (n : ℕ) : (fun a => u a ^ n) ≼ fun a => (v a + 1) ^ n := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c ^ n, fun a => ?_⟩
  calc u a ^ n ≤ (c * (v a + 1)) ^ n := Nat.pow_le_pow_left (hc a) n
    _ = c ^ n * (v a + 1) ^ n := Nat.mul_pow c _ n
    _ ≤ _ := by nlinarith [Nat.zero_le (c ^ n)]

/-- A bound below a positive power of itself. -/
public theorem le_pow (v : α → ℕ) {n : ℕ} (hn : n ≠ 0) : v ≼ fun a => (v a + 1) ^ n :=
  of_le fun _ => (Nat.le_succ _).trans (Nat.le_self_pow hn _)

/-- A bound below a positive power of a larger bound. -/
public theorem le_pow_of {n : ℕ} (h : u ≼ v) (hn : n ≠ 0 := by norm_num) :
    u ≼ fun a => (v a + 1) ^ n :=
  h.trans (le_pow v hn)

/-- Powers into a larger power, of padded bounds. -/
public theorem pow_le {n m : ℕ} (h : u ≼ v) (hnm : n ≤ m := by norm_num) :
    (fun a => u a ^ n) ≼ fun a => (v a + 1) ^ m :=
  (h.pow n).trans_le fun _ => Nat.pow_le_pow_right (Nat.succ_pos _) hnm

end BigOLe

end Turing.MultiTapeTM


